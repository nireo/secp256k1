use super::*;
use crate::scalar::{ORDER, ORDER_HALF};
use sha2::{Digest, Sha256};

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
