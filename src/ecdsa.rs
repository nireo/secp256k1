use crate::field::field_to_bytes;
use crate::point::Point;
use crate::scalar::{ORDER, ORDER_HALF, Scalar, scalar_to_bytes};
use hmac::{Hmac, Mac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

/// Generate a keypair from 32 bytes of entropy.
/// Returns None if the derived scalar is zero (invalid secret key).
pub fn generate_keypair(secret: [u8; 32]) -> Option<(Scalar, Point)> {
    let sk = Scalar::from_bytes_mod_order(secret);
    if sk.is_zero() {
        return None;
    }
    let pk = Point::generator().mul_scalar(&sk);
    Some((sk, pk))
}

/// Deterministic nonce generator per RFC6979 using HMAC-SHA256.
fn rfc6979_nonce(sk: &Scalar, msg_hash: &[u8; 32]) -> Scalar {
    let x = scalar_to_bytes(sk);
    let mut v = [0x01u8; 32];
    let mut k = [0x00u8; 32];

    // K = HMAC(K, V || 0x00 || x || h1)
    let mut mac = HmacSha256::new_from_slice(&k).unwrap();
    mac.update(&v);
    mac.update(&[0x00]);
    mac.update(&x);
    mac.update(msg_hash);
    k.copy_from_slice(&mac.finalize().into_bytes());

    // V = HMAC(K, V)
    let mut mac = HmacSha256::new_from_slice(&k).unwrap();
    mac.update(&v);
    v.copy_from_slice(&mac.finalize().into_bytes());

    // K = HMAC(K, V || 0x01 || x || h1)
    let mut mac = HmacSha256::new_from_slice(&k).unwrap();
    mac.update(&v);
    mac.update(&[0x01]);
    mac.update(&x);
    mac.update(msg_hash);
    k.copy_from_slice(&mac.finalize().into_bytes());

    // V = HMAC(K, V)
    let mut mac = HmacSha256::new_from_slice(&k).unwrap();
    mac.update(&v);
    v.copy_from_slice(&mac.finalize().into_bytes());

    loop {
        // V = HMAC(K, V)
        let mut mac = HmacSha256::new_from_slice(&k).unwrap();
        mac.update(&v);
        v.copy_from_slice(&mac.finalize().into_bytes());

        let k_scalar = Scalar::from_bytes_mod_order(v);
        if !k_scalar.is_zero() {
            return k_scalar;
        }

        // Reseed: K = HMAC(K, V || 0x00); V = HMAC(K, V)
        let mut mac = HmacSha256::new_from_slice(&k).unwrap();
        mac.update(&v);
        mac.update(&[0x00]);
        k.copy_from_slice(&mac.finalize().into_bytes());

        let mut mac = HmacSha256::new_from_slice(&k).unwrap();
        mac.update(&v);
        v.copy_from_slice(&mac.finalize().into_bytes());
    }
}

fn normalize_low_s(s: Scalar) -> Scalar {
    let s_int = s.to_int();
    if Scalar::is_ge(&s_int, &ORDER_HALF) {
        let n_minus_s = Scalar::sub_limbs(&ORDER, &s_int);
        return Scalar::from_int(n_minus_s);
    }
    s
}

/// ECDSA sign. Returns (r, s) in Montgomery form. Expects a 32-byte message hash.
pub fn ecdsa_sign(sk: &Scalar, msg_hash: [u8; 32]) -> Option<(Scalar, Scalar)> {
    if sk.is_zero() {
        return None;
    }

    let z = Scalar::from_bytes_mod_order(msg_hash);

    loop {
        let k = rfc6979_nonce(sk, &msg_hash);
        let r_point = Point::generator().mul_scalar(&k);
        let (x, _) = match r_point.to_affine() {
            Some(pair) => pair,
            None => continue,
        };
        let r = Scalar::from_bytes_mod_order(field_to_bytes(&x));
        if r.is_zero() {
            continue;
        }

        let kinv = k.invert();
        let s = kinv * (z + r * *sk);
        if s.is_zero() {
            continue;
        }

        let s = normalize_low_s(s);
        return Some((r, s));
    }
}

/// ECDSA verify. Takes (r, s) as Scalars (Montgomery form) and a public key point.
pub fn ecdsa_verify(pk: &Point, sig: (Scalar, Scalar), msg_hash: [u8; 32]) -> bool {
    let (r, s) = sig;
    if r.is_zero() || s.is_zero() {
        return false;
    }
    let r_int = r.to_int();
    let s_int = s.to_int();
    if Scalar::is_ge(&r_int, &ORDER) || Scalar::is_ge(&s_int, &ORDER) {
        return false;
    }

    let w = s.invert();
    let z = Scalar::from_bytes_mod_order(msg_hash);
    let u1 = z * w;
    let u2 = r * w;

    let p = Point::generator().mul_scalar(&u1).add(&pk.mul_scalar(&u2));
    let (x, _) = match p.to_affine() {
        Some(pair) => pair,
        None => return false,
    };
    let v = Scalar::from_bytes_mod_order(field_to_bytes(&x));
    v == r
}

/// Helper to sign using raw bytes.
pub fn ecdsa_sign_bytes(secret: [u8; 32], msg_hash: [u8; 32]) -> Option<([u8; 32], [u8; 32])> {
    let sk = Scalar::from_bytes_mod_order(secret);
    let (r, s) = ecdsa_sign(&sk, msg_hash)?;
    Some((scalar_to_bytes(&r), scalar_to_bytes(&s)))
}

/// Helper to verify using raw byte encodings of r and s.
pub fn ecdsa_verify_bytes(
    pk: &Point,
    r_bytes: [u8; 32],
    s_bytes: [u8; 32],
    msg_hash: [u8; 32],
) -> bool {
    let r = Scalar::from_bytes_mod_order(r_bytes);
    let s = Scalar::from_bytes_mod_order(s_bytes);
    ecdsa_verify(pk, (r, s), msg_hash)
}
