#!/usr/bin/env python3

from __future__ import annotations

R = 1 << 256
P = (1 << 256) - (1 << 32) - 977
N = int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16)
GX = int("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", 16)
GY = int("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8", 16)


def split_u64_le(value: int) -> list[int]:
    limbs = []
    for _ in range(4):
        limbs.append(value & ((1 << 64) - 1))
        value >>= 64
    return limbs


def fmt_array(limbs: list[int]) -> str:
    return "[\n" + "\n".join(f"    0x{limb:X}," for limb in limbs) + "\n]"


def print_section(title: str, rows: list[tuple[str, list[int] | int]]) -> None:
    print(f"--- {title} ---")
    for name, val in rows:
        if isinstance(val, list):
            print(f"{name} = {fmt_array(val)}")
        else:
            print(f"{name} = 0x{val:X}")
    print()


def main() -> None:
    field_inv = (-pow(P, -1, 1 << 64)) % (1 << 64)
    field_r2 = (R * R) % P
    field_r = R % P

    order_inv = (-pow(N, -1, 1 << 64)) % (1 << 64)
    order_r2 = (R * R) % N
    order_r = R % N

    print_section(
        "field (mod p)",
        [
            ("MODULUS", split_u64_le(P)),
            ("INV (-p^{-1} mod 2^64)", field_inv),
            ("R2 (R^2 mod p)", split_u64_le(field_r2)),
            ("R mod p (Montgomery ONE)", split_u64_le(field_r)),
            ("p - 2", split_u64_le(P - 2)),
            ("(p + 1) / 4", split_u64_le((P + 1) // 4)),
        ],
    )

    print_section(
        "scalar field (mod n)",
        [
            ("ORDER", split_u64_le(N)),
            ("ORDER_HALF (n // 2)", split_u64_le(N // 2)),
            ("ORDER_INV (-n^{-1} mod 2^64)", order_inv),
            ("ORDER_R2 (R^2 mod n)", split_u64_le(order_r2)),
            ("R mod n (Montgomery ONE)", split_u64_le(order_r)),
            ("ORDER - 2", split_u64_le(N - 2)),
        ],
    )

    print_section(
        "base point (affine, little-endian limbs)",
        [
            ("Gx", split_u64_le(GX)),
            ("Gy", split_u64_le(GY)),
        ],
    )


if __name__ == "__main__":
    main()
