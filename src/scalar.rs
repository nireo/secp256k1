use std::fmt;
use std::ops::{Add, Mul, Sub};

// n = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141
pub(crate) const ORDER: [u64; 4] = [
    0xBFD25E8CD0364141,
    0xBAAEDCE6AF48A03B,
    0xFFFFFFFFFFFFFFFE,
    0xFFFFFFFFFFFFFFFF,
];

// n/2 rounded down (used for low-s normalization)
pub(crate) const ORDER_HALF: [u64; 4] = [
    0xDFE92F46681B20A0,
    0x5D576E7357A4501D,
    0xFFFFFFFFFFFFFFFF,
    0x7FFFFFFFFFFFFFFF,
];

// -1/n mod 2^64
const ORDER_INV: u64 = 0x4b0dff665588b13f;

// R^2 mod n
const ORDER_R2: [u64; 4] = [
    0x896CF21467D7D140,
    0x741496C20E7CF878,
    0xE697F5E45BCD07C6,
    0x9D671CD581C69BC5,
];

// n - 2 for inversion via exponentiation
const ORDER_MINUS_2: [u64; 4] = [
    0xBFD25E8CD036413F,
    0xBAAEDCE6AF48A03B,
    0xFFFFFFFFFFFFFFFE,
    0xFFFFFFFFFFFFFFFF,
];

/// Scalar modulo the curve order.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Scalar {
    pub limbs: [u64; 4],
}

impl Scalar {
    pub const ZERO: Self = Self { limbs: [0; 4] };
    pub const ONE: Self = Self {
        limbs: [0x402DA1732FC9BEBF, 0x4551231950B75FC4, 0x1, 0],
    }; // 1 * R mod n

    pub fn new(limbs: [u64; 4]) -> Self {
        Self { limbs }
    }

    /// Converts a canonical (non-Montgomery) number into Montgomery form.
    pub fn from_int(limbs: [u64; 4]) -> Self {
        let x = Self::new(limbs);
        let r2 = Self::new(ORDER_R2);
        x * r2
    }

    /// Converts from Montgomery form back to canonical representation.
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

    pub fn square(&self) -> Self {
        self.mul_mont(self)
    }

    pub fn double(&self) -> Self {
        self.add(*self)
    }

    pub fn invert(&self) -> Self {
        self.pow(&ORDER_MINUS_2)
    }

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

    fn mont_reduce(t: &[u64; 8]) -> Self {
        let mut t = *t;
        let mut extra_carry = 0u64;

        for i in 0..4 {
            let k = t[i].wrapping_mul(ORDER_INV);
            let mut carry_inner = 0u128;

            for j in 0..4 {
                let m = (k as u128) * (ORDER[j] as u128);
                let sum = (t[i + j] as u128) + m + carry_inner;
                t[i + j] = sum as u64;
                carry_inner = sum >> 64;
            }

            let mut j = i + 4;
            while carry_inner != 0 {
                if j < 8 {
                    let sum = (t[j] as u128) + carry_inner;
                    t[j] = sum as u64;
                    carry_inner = sum >> 64;
                    j += 1;
                } else {
                    extra_carry += carry_inner as u64;
                    carry_inner = 0;
                }
            }
        }

        let mut result = [t[4], t[5], t[6], t[7]];

        if extra_carry != 0 || Self::is_ge(&result, &ORDER) {
            result = Self::sub_limbs(&result, &ORDER);
        }

        Self::new(result)
    }

    pub(crate) fn sub_limbs(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
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

    pub(crate) fn is_ge(a: &[u64; 4], b: &[u64; 4]) -> bool {
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

    /// Interpret 32 bytes (big-endian) as a scalar reduced mod n.
    pub fn from_bytes_mod_order(bytes: [u8; 32]) -> Self {
        let mut limbs = [
            u64::from_be_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_be_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_be_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_be_bytes(bytes[0..8].try_into().unwrap()),
        ];

        if Self::is_ge(&limbs, &ORDER) {
            limbs = Self::sub_limbs(&limbs, &ORDER);
        }

        Self::from_int(limbs)
    }

    pub fn is_zero(&self) -> bool {
        self.limbs == [0; 4]
    }
}

impl Add for Scalar {
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
        if carry != 0 || Self::is_ge(&result, &ORDER) {
            return Self::new(Self::sub_limbs(&result, &ORDER));
        }
        Self::new(result)
    }
}

impl Sub for Scalar {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        if Self::is_ge(&self.limbs, &other.limbs) {
            Self::new(Self::sub_limbs(&self.limbs, &other.limbs))
        } else {
            let diff = Self::sub_limbs(&other.limbs, &self.limbs);
            let res = Self::sub_limbs(&ORDER, &diff);
            Self::new(res)
        }
    }
}

impl Mul for Scalar {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        self.mul_mont(&other)
    }
}

impl fmt::Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.to_int();
        write!(
            f,
            "0x{:016x}{:016x}{:016x}{:016x}",
            val[3], val[2], val[1], val[0]
        )
    }
}

/// Big-endian 32-byte encoding of a scalar in canonical form (non-Montgomery).
pub fn scalar_to_bytes(s: &Scalar) -> [u8; 32] {
    let limbs = s.to_int();
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_be_bytes());
    }
    out
}
