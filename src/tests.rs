use super::*;
use crate::scalar::{ORDER, ORDER_HALF};
use sha2::{Digest, Sha256};
use secp256k1_ref as secp_ref;

fn negate_point(p: &Point) -> Point {
    if p == &Point::INFINITY {
        return Point::INFINITY;
    }

    let (x, y) = p.to_affine().expect("not infinity");
    Point::new(x, -y).unwrap()
}

fn limbs_to_be_bytes(limbs: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..8].copy_from_slice(&limbs[3].to_be_bytes());
    out[8..16].copy_from_slice(&limbs[2].to_be_bytes());
    out[16..24].copy_from_slice(&limbs[1].to_be_bytes());
    out[24..32].copy_from_slice(&limbs[0].to_be_bytes());
    out
}

fn point_to_uncompressed_bytes(point: &Point) -> [u8; 65] {
    let (x, y) = point.to_affine().expect("point should be affine");
    let mut out = [0u8; 65];
    out[0] = 0x04;
    out[1..33].copy_from_slice(&field_to_bytes(&x));
    out[33..65].copy_from_slice(&field_to_bytes(&y));
    out
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
fn test_scalar_one_to_int() {
    assert_eq!(Scalar::ONE.to_int(), [1, 0, 0, 0]);
}

#[test]
fn test_scalar_from_bytes_reduces() {
    // This value is > n, ensure reduction brings it inside the field.
    let mut bytes = [0xFFu8; 32];
    let scalar = Scalar::from_bytes_mod_order(bytes);
    assert!(!scalar.is_zero(), "reduced scalar should not be zero");
    // Make sure a known in-range value round-trips.
    bytes[31] = 1;
    for b in &mut bytes[0..31] {
        *b = 0;
    }
    let one = Scalar::from_bytes_mod_order(bytes);
    assert_eq!(one, Scalar::ONE);
}

#[test]
fn test_scalar_from_bytes_canonical_rejects_high() {
    let n_bytes = limbs_to_be_bytes(&ORDER);
    assert!(Scalar::from_bytes_canonical(n_bytes).is_none());

    let n_minus_one_limbs = Scalar::sub_limbs(&ORDER, &[1, 0, 0, 0]);
    let n_minus_one_bytes = limbs_to_be_bytes(&n_minus_one_limbs);
    assert!(Scalar::from_bytes_canonical(n_minus_one_bytes).is_some());
}

#[test]
fn test_generate_keypair_rejects_non_canonical_secret() {
    let n_bytes = limbs_to_be_bytes(&ORDER);
    assert!(generate_keypair(n_bytes).is_none());
}

#[test]
fn test_ecdsa_verify_bytes_rejects_non_canonical_sig() {
    let g = Point::generator();
    let pk = g.mul_scalar(&Scalar::ONE);
    let msg = Sha256::digest(b"invalid encoding");
    let mut r_bytes = limbs_to_be_bytes(&ORDER); // non-canonical (== n)
    let mut s_bytes = [0u8; 32];
    s_bytes[31] = 1;
    assert!(!ecdsa_verify_bytes(&pk, r_bytes, s_bytes, msg.into()));

    // s >= n should also be rejected
    r_bytes[31] = 1;
    let s_bad = limbs_to_be_bytes(&ORDER);
    assert!(!ecdsa_verify_bytes(&pk, r_bytes, s_bad, msg.into()));
}

#[test]
fn test_scalar_multiplication_matches_double() {
    let g = Point::generator();
    let two_bytes = {
        let mut b = [0u8; 32];
        b[31] = 2;
        b
    };
    let two = Scalar::from_bytes_mod_order(two_bytes);
    let from_mul = g.mul_scalar(&two);
    let from_double = g.double();
    assert_eq!(from_mul, from_double);
}

#[test]
fn test_key_generation() {
    let mut bytes = [0u8; 32];
    bytes[31] = 1;
    let (sk, pk) = generate_keypair(bytes).expect("valid keypair");
    assert_eq!(sk, Scalar::ONE);
    assert_eq!(pk, Point::generator());
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

#[test]
fn test_from_sec1_generator_compressed() {
    let g = Point::generator();
    let (x, y) = g.to_affine().unwrap();
    let mut bytes = [0u8; 33];
    bytes[0] = if y.is_odd() { 0x03 } else { 0x02 };
    bytes[1..].copy_from_slice(&field_to_bytes(&x));

    let decoded = Point::from_sec1(&bytes).expect("compressed generator should decode");
    assert_eq!(decoded, g);
}

#[test]
fn test_from_sec1_generator_uncompressed() {
    let g = Point::generator();
    let (x, y) = g.to_affine().unwrap();
    let mut bytes = [0u8; 65];
    bytes[0] = 0x04;
    bytes[1..33].copy_from_slice(&field_to_bytes(&x));
    bytes[33..].copy_from_slice(&field_to_bytes(&y));

    let decoded = Point::from_sec1(&bytes).expect("uncompressed generator should decode");
    assert_eq!(decoded, g);
}

#[test]
fn test_from_sec1_rejects_invalid_encodings() {
    assert!(Point::from_sec1(&[0x02]).is_none(), "compressed length");
    assert!(
        Point::from_sec1(&[0x00, 0x00]).is_none(),
        "infinity must be 1 byte"
    );
}

#[test]
fn test_ecdsa_sign_and_verify_roundtrip() {
    let mut msg = Sha256::new();
    msg.update(b"deterministic message");
    let hash: [u8; 32] = msg.finalize().into();

    let mut sk_bytes = [0u8; 32];
    sk_bytes[31] = 1;
    let sk = Scalar::from_bytes_mod_order(sk_bytes);
    let pk = Point::generator().mul_scalar(&sk);

    let (r, s) = ecdsa_sign(&sk, hash).expect("signing should succeed");
    assert!(ecdsa_verify(&pk, (r, s), hash));
}

#[test]
fn test_ecdsa_sign_deterministic() {
    let mut msg = Sha256::new();
    msg.update(b"same message");
    let hash: [u8; 32] = msg.finalize().into();

    let mut sk_bytes = [0u8; 32];
    sk_bytes[31] = 5;
    let sk = Scalar::from_bytes_mod_order(sk_bytes);

    let sig1 = ecdsa_sign(&sk, hash).expect("first signature");
    let sig2 = ecdsa_sign(&sk, hash).expect("second signature");
    assert_eq!(sig1, sig2, "RFC6979 signatures must be deterministic");
}

#[test]
fn test_ecdsa_sign_low_s() {
    let mut msg = Sha256::new();
    msg.update(b"low s check");
    let hash: [u8; 32] = msg.finalize().into();

    let mut sk_bytes = [0u8; 32];
    sk_bytes[31] = 9;
    let sk = Scalar::from_bytes_mod_order(sk_bytes);
    let (r, s) = ecdsa_sign(&sk, hash).expect("signatures should be generated");
    assert!(ecdsa_verify(
        &Point::generator().mul_scalar(&sk),
        (r, s),
        hash
    ));

    let s_int = s.to_int();
    assert!(
        !Scalar::is_ge(&s_int, &ORDER_HALF),
        "s should be in low half of order"
    );
    assert!(!Scalar::is_ge(&r.to_int(), &ORDER));
}

#[test]
fn test_field_element_from_bytes() {
    let fe = FieldElement::from_int([7, 0, 0, 0]);
    let by = fe.to_bytes();
    let fe_got = FieldElement::from_bytes(&by).unwrap();

    assert!(fe_got == fe)
}

#[test]
fn test_sec1_encoding_roundtrip() {
    let g = Point::generator();

    let compressed = g.to_sec1(true);
    let decompressed = Point::from_sec1(&compressed).expect("should decode compressed");
    assert_eq!(decompressed, g, "compressed sec1 roundtrip");

    let uncompressed = g.to_sec1(false);
    let decompressed = Point::from_sec1(&uncompressed).expect("should decode uncompressed");
    assert_eq!(decompressed, g, "uncompressed sec1 roundtrip");
}

#[test]
fn test_public_key_matches_secp256k1_ref() {
    let sk_bytes = [0x11u8; 32];
    let sk = Scalar::from_bytes_nonzero(sk_bytes).expect("valid secret key");
    let pk = Point::generator().mul_scalar(&sk);

    let secp = secp_ref::Secp256k1::new();
    let ref_sk = secp_ref::SecretKey::from_slice(&sk_bytes).expect("ref secret key");
    let ref_pk = secp_ref::PublicKey::from_secret_key(&secp, &ref_sk);
    let ref_bytes = ref_pk.serialize_uncompressed();

    assert_eq!(point_to_uncompressed_bytes(&pk), ref_bytes);
}

#[test]
fn test_ecdsa_sign_verifies_with_secp256k1_ref() {
    let sk_bytes = [0x22u8; 32];
    let sk = Scalar::from_bytes_nonzero(sk_bytes).expect("valid secret key");
    let msg_hash: [u8; 32] = Sha256::digest(b"cross verify ours -> ref").into();

    let (r, s) = ecdsa_sign(&sk, msg_hash).expect("signature");
    let mut sig_bytes = [0u8; 64];
    sig_bytes[0..32].copy_from_slice(&scalar_to_bytes(&r));
    sig_bytes[32..64].copy_from_slice(&scalar_to_bytes(&s));

    let secp = secp_ref::Secp256k1::new();
    let ref_sk = secp_ref::SecretKey::from_slice(&sk_bytes).expect("ref secret key");
    let ref_pk = secp_ref::PublicKey::from_secret_key(&secp, &ref_sk);
    let msg = secp_ref::Message::from_slice(&msg_hash).expect("msg");
    let sig = secp_ref::ecdsa::Signature::from_compact(&sig_bytes).expect("sig");

    assert!(secp.verify_ecdsa(&msg, &sig, &ref_pk).is_ok());
}

#[test]
fn test_ecdsa_verify_accepts_secp256k1_ref_signature() {
    let sk_bytes = [0x33u8; 32];
    let msg_hash: [u8; 32] = Sha256::digest(b"cross verify ref -> ours").into();

    let secp = secp_ref::Secp256k1::new();
    let ref_sk = secp_ref::SecretKey::from_slice(&sk_bytes).expect("ref secret key");
    let msg = secp_ref::Message::from_slice(&msg_hash).expect("msg");
    let sig = secp.sign_ecdsa(&msg, &ref_sk);
    let sig_bytes = sig.serialize_compact();

    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&sig_bytes[0..32]);
    s.copy_from_slice(&sig_bytes[32..64]);

    let sk = Scalar::from_bytes_nonzero(sk_bytes).expect("valid secret key");
    let pk = Point::generator().mul_scalar(&sk);
    assert!(ecdsa_verify_bytes(&pk, r, s, msg_hash));
}
