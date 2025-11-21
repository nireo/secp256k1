use std::fmt;
use std::ops::{Add, Mul, Sub};

// --- Field Element ---

// p = 2^256 - 2^32 - 977
const MODULUS: [u64; 4] = [
    0xFFFFFFFEFFFFFC2F,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
];

// -1/p mod 2^64
const INV: u64 = 0xd838091dd2253531;

// R^2 mod p
const R2: [u64; 4] = [0x7A2000E90A1, 1, 0, 0];

/// A field element represents one value in the field defined F_p.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FieldElement {
    // we can split a large 256-bit number into 4 64-bit numbers. however this number is not stored
    // simply, we store the montgomery representation.
    pub limbs: [u64; 4],
}

impl FieldElement {
    // every field element is stored as aR mod p
    pub const ZERO: Self = Self { limbs: [0; 4] };
    pub const ONE: Self = Self {
        limbs: [0x1000003D1, 0, 0, 0],
    }; // 1 * R mod p

    pub fn new(limbs: [u64; 4]) -> Self {
        Self { limbs }
    }

    /// from_int converts a number in normal form to Montgomery form.
    pub fn from_int(limbs: [u64; 4]) -> Self {
        let x = Self::new(limbs);
        let r2 = Self::new(R2);
        x * r2
    }

    /// we store the element as A = aR mod p, like mentioned before, therefore to get the the
    /// number in normal form we can just do multiplication to do A * R^(-1) = a mod p. Since the
    /// mont_reduce takes in a 512-bit number we zero out the rest that is not part of the 256-bit
    /// number.
    pub fn to_int(&self) -> [u64; 4] {
        Self::mont_reduce(&[
            self.limbs[0],
            self.limbs[1],
            self.limbs[2],
            self.limbs[3],
            0,
            0,
            0,
            0,
        ])
        .limbs
    }

    /// doubles field point using montgomery multiplication
    pub fn square(&self) -> Self {
        self.mul_mont(self)
    }

    /// double calculates a + a
    pub fn double(&self) -> Self {
        self.add(*self)
    }

    /// fermat's little theorem says that a^(p-1) is congruent 1 mod p and therefore we can
    /// calculate a^(p-2) is congurent a^(-1)
    pub fn invert(&self) -> Self {
        // p - 2
        let p_minus_2 = [
            0xFFFFFFFEFFFFFC2D,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFF,
        ];
        self.pow(&p_minus_2)
    }

    /// pow performs binary exponentation this keeps the value in montgomery form
    fn pow(&self, exponent: &[u64; 4]) -> Self {
        let mut res = Self::ONE;
        let mut base = *self;

        for i in 0..4 {
            let mut limb = exponent[i];
            for _ in 0..64 {
                if (limb & 1) == 1 {
                    res = res * base;
                }
                base = base.square();
                limb >>= 1;
            }
        }
        res
    }

    fn mul_mont(&self, other: &Self) -> Self {
        let product = Self::mul_512(&self.limbs, &other.limbs);
        Self::mont_reduce(&product)
    }

    // Standard Operand Scanning Multiplication
    fn mul_512(a: &[u64; 4], b: &[u64; 4]) -> [u64; 8] {
        let mut res = [0u64; 8];

        for i in 0..4 {
            let mut carry = 0u64;
            for j in 0..4 {
                let prod = (a[i] as u128) * (b[j] as u128);
                let sum = (res[i + j] as u128) + prod + (carry as u128);
                res[i + j] = sum as u64;
                carry = (sum >> 64) as u64;
            }
            let mut k = i + 4;
            let mut c = carry;
            while c != 0 {
                let (new_val, overflow) = res[k].overflowing_add(c);
                res[k] = new_val;
                c = overflow as u64;
                k += 1;
                if k >= 8 {
                    break;
                }
            }
        }

        res
    }

    /// mont reduce calculates t * R^(-1) mod p
    fn mont_reduce(t: &[u64; 8]) -> Self {
        let mut t = *t;
        let mut extra_carry = 0u64;

        for i in 0..4 {
            let k = t[i].wrapping_mul(INV);
            let mut carry_inner = 0u128;

            for j in 0..4 {
                let m = (k as u128) * (MODULUS[j] as u128);
                let sum = (t[i + j] as u128) + m + carry_inner;
                t[i + j] = sum as u64;
                carry_inner = sum >> 64;
            }

            // Propagate the carry up to the higher limbs
            let mut j = i + 4;
            while carry_inner != 0 {
                if j < 8 {
                    let sum = (t[j] as u128) + carry_inner;
                    t[j] = sum as u64;
                    carry_inner = sum >> 64;
                    j += 1;
                } else {
                    // Overflow beyond 512 bits
                    extra_carry += carry_inner as u64;
                    carry_inner = 0;
                }
            }
        }

        let mut result = [t[4], t[5], t[6], t[7]];

        // If result >= P, subtract P.
        // Note: The "extra_carry" logic combined with wrapping subtraction handles
        // the case where the result is > 2^256 (which is > P).
        if extra_carry != 0 || Self::is_ge(&result, &MODULUS) {
            result = Self::sub_limbs(&result, &MODULUS);
        }

        Self::new(result)
    }

    fn sub_limbs(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
        let mut result = [0u64; 4];
        let mut borrow = 0u64;
        for i in 0..4 {
            let (diff, b1) = a[i].overflowing_sub(b[i]);
            let (diff_total, b2) = diff.overflowing_sub(borrow);
            result[i] = diff_total;
            borrow = (b1 as u64) + (b2 as u64);
        }
        result
    }

    fn is_ge(a: &[u64; 4], b: &[u64; 4]) -> bool {
        for i in (0..4).rev() {
            if a[i] > b[i] {
                return true;
            }
            if a[i] < b[i] {
                return false;
            }
        }
        true
    }
}

impl Add for FieldElement {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut result = [0u64; 4];
        let mut carry = 0u64;
        for i in 0..4 {
            let (sum, c1) = self.limbs[i].overflowing_add(other.limbs[i]);
            let (sum_total, c2) = sum.overflowing_add(carry);
            result[i] = sum_total;
            carry = (c1 as u64) + (c2 as u64);
        }
        if carry != 0 || Self::is_ge(&result, &MODULUS) {
            return Self::new(Self::sub_limbs(&result, &MODULUS));
        }
        Self::new(result)
    }
}

impl Sub for FieldElement {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        if Self::is_ge(&self.limbs, &other.limbs) {
            Self::new(Self::sub_limbs(&self.limbs, &other.limbs))
        } else {
            let diff = Self::sub_limbs(&other.limbs, &self.limbs);
            let res = Self::sub_limbs(&MODULUS, &diff);
            Self::new(res)
        }
    }
}

impl Mul for FieldElement {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        self.mul_mont(&other)
    }
}

impl fmt::Debug for FieldElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.to_int();
        write!(
            f,
            "0x{:016x}{:016x}{:016x}{:016x}",
            val[3], val[2], val[1], val[0]
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Point {
    pub x: FieldElement,
    pub y: FieldElement,
    pub z: FieldElement,
}

impl Point {
    pub const INFINITY: Self = Self {
        x: FieldElement::ZERO,
        y: FieldElement::ZERO,
        z: FieldElement::ZERO,
    };

    pub fn generator() -> Self {
        // Secp256k1 Generator constants (Big Endian Hex -> Little Endian [u64; 4])
        let gx = FieldElement::from_int([
            0x59F2815B16F81798,
            0x029BFCDB2DCE28D9,
            0x55A06295CE870B07,
            0x79BE667EF9DCBBAC,
        ]);
        let gy = FieldElement::from_int([
            0x9C47D08FFB10D4B8,
            0xFD17B448A6855419,
            0x5DA4FBFC0E1108A8,
            0x483ADA7726A3C465,
        ]);

        Self {
            x: gx,
            y: gy,
            z: FieldElement::ONE,
        }
    }

    pub fn new(x: FieldElement, y: FieldElement) -> Self {
        // points should satisfy the equation
        // y^2 = x^3 + 7
        let lhs = y.square();
        let rhs = x.square() * x + FieldElement::from_int([7, 0, 0, 0]);

        if lhs != rhs {
            println!("Curve Equation Check Failed:");
            println!("LHS (y^2):   {:?}", lhs);
            println!("RHS (x^3+7): {:?}", rhs);
            panic!("Point is not on secp256k1 curve!");
        }

        Self {
            x,
            y,
            z: FieldElement::ONE,
        }
    }

    // convert jacobian point to affine
    // in jacobian form the points are in (X/Z^2, Y/Z^3)
    pub fn to_affine(&self) -> Option<(FieldElement, FieldElement)> {
        if self.z == FieldElement::ZERO {
            return None;
        }
        let z_inv = self.z.invert(); // 1/Z
        let z_inv2 = z_inv.square(); // 1/Z^2
        let z_inv3 = z_inv2 * z_inv; // 1/Z^3

        let x = self.x * z_inv2; // x = X/Z^2 * Z^2 = X
        let y = self.y * z_inv3; // y = Y/Z^3 * Z^3 = Y
        Some((x, y))
    }

    pub fn add(&self, other: &Point) -> Point {
        if self.z == FieldElement::ZERO {
            return *other;
        }
        if other.z == FieldElement::ZERO {
            return *self;
        }

        let z1z1 = self.z.square(); // Z1^2
        let z2z2 = other.z.square(); // Z2^2

        // U1 = X1 * Z2^2
        let u1 = self.x * z2z2;
        // U2 = X2 * Z1^2
        let u2 = other.x * z1z1;

        // S1 = Y1 * Z2^3
        let s1 = self.y * other.z * z2z2;
        // S2 = Y2 * Z1^3
        let s2 = other.y * self.z * z1z1;

        if u1 == u2 {
            if s1 == s2 {
                // Points are identical → doubling
                return self.double();
            } else {
                // Same X but opposite Y → infinity
                return Point::INFINITY;
            }
        }

        let h = u2 - u1; // H = U2 - U1
        let r = s2 - s1; // R = S2 - S1

        let h_sq = h.square(); // H^2
        let h_cu = h * h_sq; // H^3
        let u1_h_sq = u1 * h_sq; // U1 * H^2

        // X3 = R^2 - H^3 - 2*U1*H^2
        let x3 = r.square() - h_cu - u1_h_sq.double();

        // Y3 = R*(U1*H^2 - X3) - S1*H^3
        let y3 = r * (u1_h_sq - x3) - s1 * h_cu;

        // Z3 = H * Z1 * Z2
        let z3 = h * self.z * other.z;

        Point {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// double doubles a given point
    /// the general doubling formula involves M = 3X^2 +aZ^4, but since in secp256k1 a=0, then we
    /// get M = 3X^2. The formulas can be derived via this process:
    /// normally: (x, y) | t_slope = (3x^2+a)/2y and from that x'=t_slope^2 - 2x
    /// y' = t_slope(x - x') - y
    /// then when we rewrite as jacobian coordinates we obviously need to replace everything with
    /// x=X/Z^2 and y=Y/Z^2. The general short-Weierstrass Jacobian doubling is:
    /// A=X^2 , B=Y^2 , C=B^2 , D=2((X + B)^2-A-C) , E=3A+aZ^4, X'=E^2-2D, Y'=E(D-X')-8C Z'=2YZ
    /// here we see that when a = 0, the formulas collapse so we get:
    /// M=3X^2 (E without aZ^4 single it cancels out), S=4XY^2, and 8C=8Y^4 and then the formulas
    /// in the function. the benefit of this approach is that we avoid the modular inverse when
    /// calculating the tangent slope.
    pub fn double(&self) -> Self {
        // point is at infinity when z = 0, then doubling also gives infinity
        if self.z == FieldElement::ZERO {
            return Self::INFINITY;
        }
        // point is at y = 0 so the tangent is vertical so that should also be infinity
        if self.y == FieldElement::ZERO {
            return Self::INFINITY;
        }

        let x = self.x;
        let y = self.y;
        let z = self.z;

        let y_sq = y.square(); // Y^2
        let s = (x * y_sq).double().double(); // 4*X*Y^2
        let m = x.square();
        let m = m + m.double(); // 3*X^2

        // X' = M^2 - 2S
        let x_prime = m.square() - s.double();

        // Y^4
        let y_pow4 = y_sq.square();
        // 8 * Y^4
        let y_pow4_8 = y_pow4.double().double().double();

        // Y' = M(S - X') - 8Y^4
        let y_prime = m * (s - x_prime) - y_pow4_8;
        // Z' = 2*Y*Z
        let z_prime = (y * z).double();

        Self {
            x: x_prime,
            y: y_prime,
            z: z_prime,
        }
    }
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        // Both points at infinity
        if self.z == FieldElement::ZERO && other.z == FieldElement::ZERO {
            return true;
        }

        // One is infinity, the other is not
        if self.z == FieldElement::ZERO || other.z == FieldElement::ZERO {
            return false;
        }

        // Compare X1/Z1^2 ?= X2/Z2^2 without inversion
        let z1_sq = self.z.square();
        let z2_sq = other.z.square();
        let u1 = self.x * z2_sq;
        let u2 = other.x * z1_sq;
        if u1 != u2 {
            return false;
        }

        // Compare Y1/Z1^3 ?= Y2/Z2^3 without inversion
        let z1_cu = z1_sq * self.z;
        let z2_cu = z2_sq * other.z;
        let s1 = self.y * z2_cu;
        let s2 = other.y * z1_cu;
        s1 == s2
    }
}

impl Eq for Point {}

#[cfg(test)]
mod tests {
    use super::*;

    fn negate_point(p: &Point) -> Point {
        if p == &Point::INFINITY {
            return Point::INFINITY;
        }

        let (x, y) = p.to_affine().expect("not infinity");
        let neg_y = FieldElement::ZERO - y;
        Point::new(x, neg_y)
    }

    #[test]
    fn test_add_inverse_is_infinity() {
        let g = Point::generator();
        let neg_g = negate_point(&g);

        let r1 = g.add(&neg_g);
        let r2 = neg_g.add(&g);

        assert_eq!(r1, Point::INFINITY, "G + (-G) should be ∞");
        assert_eq!(r2, Point::INFINITY, "(-G) + G should be ∞");
    }

    #[test]
    fn test_add_associative_sample() {
        let g = Point::generator();
        let g2 = g.double();
        let g3 = g.add(&g2); // 3G

        let left = g.add(&g2).add(&g3); // (G + 2G) + 3G
        let right = g.add(&g2.add(&g3)); // G + (2G + 3G)

        assert_eq!(left, right, "Point addition should be associative (sample)");
    }

    #[test]
    fn test_add_commutative() {
        let g = Point::generator();
        let g2 = g.double();
        let g3 = g.add(&g2); // 3G

        let r1 = g2.add(&g3); // 2G + 3G
        let r2 = g3.add(&g2); // 3G + 2G

        assert_eq!(r1, r2, "Point addition should be commutative");
    }

    #[test]
    fn test_add_generator_chain() {
        let g = Point::generator();

        // 2G
        let g2 = g.double();
        assert_ne!(g2, Point::INFINITY, "2G should not be infinity");

        // 3G = G + 2G
        let g3_a = g.add(&g2);
        let g3_b = g2.add(&g);

        assert_eq!(g3_a, g3_b, "G + 2G must equal 2G + G");
        assert_ne!(g3_a, Point::INFINITY, "3G should not be infinity");

        // sanity: (3G) + (-3G) = ∞
        let neg_g3 = negate_point(&g3_a);
        let inf = g3_a.add(&neg_g3);
        assert_eq!(inf, Point::INFINITY, "3G + (-3G) should be infinity");
    }

    #[test]
    fn test_add_equals_double() {
        let g = Point::generator();
        let g2_from_double = g.double();
        let g2_from_add = g.add(&g);

        assert_eq!(g2_from_double, g2_from_add, "G + G must equal 2G");
    }

    #[test]
    fn test_field_inversion() {
        let a = FieldElement::from_int([5, 0, 0, 0]);
        let inv = a.invert();
        let prod = a * inv;
        assert_eq!(prod, FieldElement::ONE);
    }

    #[test]
    fn test_generator_on_curve() {
        let g = Point::generator();
        let (x, y) = g.to_affine().unwrap();
        // This will panic if invalid
        let _ = Point::new(x, y);
    }

    #[test]
    fn test_double_generator() {
        let g = Point::generator();
        let g2 = g.double();
        let (x2, _) = g2.to_affine().expect("Result should not be infinity");

        // Correct 2G X coordinate for secp256k1 (Little Endian Limbs)
        // Hex: C6047F9441ED7D6D 3045406E95C07CD8 5C778E4B8CEF3CA7 ABAC09B95C709EE5
        let expected_x = FieldElement::from_int([
            0xABAC09B95C709EE5,
            0x5C778E4B8CEF3CA7,
            0x3045406E95C07CD8,
            0xC6047F9441ED7D6D,
        ]);

        assert_eq!(x2, expected_x, "2G X-coordinate mismatch");
    }

    #[test]
    fn test_double_infinity() {
        let inf = Point::INFINITY;
        let res = inf.double();
        assert_eq!(res, Point::INFINITY);
    }

    #[test]
    fn test_field_one_to_int() {
        assert_eq!(FieldElement::ONE.to_int(), [1, 0, 0, 0]);
    }

    #[test]
    fn test_generator_coordinates() {
        let g = Point::generator();
        let (x, y) = g.to_affine().expect("Generator is not at infinity");

        let expected_x = [
            0x59F2815B16F81798,
            0x029BFCDB2DCE28D9,
            0x55A06295CE870B07,
            0x79BE667EF9DCBBAC,
        ];
        let expected_y = [
            0x9C47D08FFB10D4B8,
            0xFD17B448A6855419,
            0x5DA4FBFC0E1108A8,
            0x483ADA7726A3C465,
        ];

        assert_eq!(x.to_int(), expected_x);
        assert_eq!(y.to_int(), expected_y);
    }
}
