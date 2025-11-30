# secp256k1

Small, self contained Rust implementation of the secp256k1 curve. The crate includes finite field and scalar arithmetic, elliptic curve point operations, and ECDSA signing and verification with deterministic RFC6979 nonces. It is meant for learning and experimentation rather than production use; the code has not been audited and does not attempt to be constant time.

## Example

```rust
use secp256k1::{generate_keypair, ecdsa_sign, ecdsa_verify, Point};

fn main() {
    let secret = [42u8; 32];
    let msg = [1u8; 32];
    let (sk, pk) = generate_keypair(secret).expect("valid keypair");
    let sig = ecdsa_sign(&sk, msg).expect("signature");
    assert!(ecdsa_verify(&pk, sig, msg));

    // Public keys are points; you can serialize them using affine coordinates.
    let (x, y) = pk.to_affine().expect("on curve");
    println!("pubkey x = {:?}", x);
    println!("pubkey y = {:?}", y);
}
```

## Testing

Run `cargo test` from the project root to exercise arithmetic, point operations, and ECDSA checks.

## Constants

Magic constants (Montgomery parameters, curve order data, and generator limbs) can be recomputed with:

```
python3 scripts/generate_constants.py
```

