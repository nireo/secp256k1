use crate::field::FieldElement;
use crate::scalar::Scalar;

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

    /// Simple double-and-add scalar multiplication.
    pub fn mul_scalar(&self, scalar: &Scalar) -> Self {
        let bits = scalar.to_int(); // canonical representation
        let mut acc = Point::INFINITY;

        for i in (0..4).rev() {
            let word = bits[i];
            for j in (0..64).rev() {
                acc = acc.double();
                if ((word >> j) & 1) == 1 {
                    acc = acc.add(self);
                }
            }
        }

        acc
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
