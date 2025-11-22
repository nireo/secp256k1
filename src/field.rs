use std::fmt;
use std::ops::{Add, Mul, Sub};

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

/// Big-endian 32-byte encoding of a field element (non-Montgomery).
pub fn field_to_bytes(f: &FieldElement) -> [u8; 32] {
    let limbs = f.to_int();
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_be_bytes());
    }
    out
}
