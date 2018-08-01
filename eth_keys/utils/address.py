from eth_utils import (
    keccak,
    blake2b,
    blake2b_raw
)


def public_key_bytes_to_address(public_key_bytes: bytes) -> bytes:
    print(blake2b(public_key_bytes)[:32])
    return bytes.fromhex('a0') + blake2b(public_key_bytes)[:31]
