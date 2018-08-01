from hashlib import blake2b as BLAKE2B

from typing import (Any, Callable, Optional, Tuple,)  # noqa: F401
#
# From http://github.com/vbuterin/ed25519/blob/master/ed25519.py
# http://ed25519.cr.yp.to/ed25519-20110926.pdf
#
# Known issues: http://github.com/vbuterin/ed25519/issues


from eth_keys.constants import (
    ED25519_Q as Q,
    ED25519_B as B,
    ED25519_Bx as Bx,
    ED25519_By as By,
    ED25519_D as D,
    ED25519_L as L,
    ED25519_BITS as BITS,
)

from eth_utils import (
    int_to_big_endian,
    big_endian_to_int,
)
from eth_keys.utils.padding import pad32

from ..native.jacobian import (
    fast_multiply
)


# Modular inverse
def inv(a, n):
    if a == 0:
        return 0
    lm, hm = 1, 0
    low, high = a % n, n
    while low > 1:
        r = high//low
        nm, new = hm-lm*r, high-low*r
        lm, low, hm, high = nm, new, lm, low
    return lm % n


# http://eli.thegreenplace.net/2009/03/07/computing-modular-square-roots-in-python/
def modular_sqrt(a, p):
    """ Find a quadratic residue (mod p) of 'a'. p
        must be an odd prime.

        Solve the congruence of the form:
            x^2 = a (mod p)
        And returns x. Note that p - x is also a root.

        0 is returned is no square root exists for
        these a and p.

        The Tonelli-Shanks algorithm is used (except
        for some simple cases in which the solution
        is known from an identity). This algorithm
        runs in polynomial time (unless the
        generalized Riemann hypothesis is false).
    """
    # Simple cases
    #
    if legendre_symbol(a, p) != 1:
        return 0
    elif a == 0:
        return 0
    elif p == 2:
        return p
    elif p % 4 == 3:
        return pow(a, (p + 1) / 4, p)

    # Partition p-1 to s * 2^e for an odd s (i.e.
    # reduce all the powers of 2 from p-1)
    #
    s = p - 1
    e = 0
    while s % 2 == 0:
        s /= 2
        e += 1

    # Find some 'n' with a legendre symbol n|p = -1.
    # Shouldn't take long.
    #
    n = 2
    while legendre_symbol(n, p) != -1:
        n += 1

    # Here be dragons!
    # Read the paper "Square roots from 1; 24, 51,
    # 10 to Dan Shanks" by Ezra Brown for more
    # information
    #

    # x is a guess of the square root that gets better
    # with each iteration.
    # b is the "fudge factor" - by how much we're off
    # with the guess. The invariant x^2 = ab (mod p)
    # is maintained throughout the loop.
    # g is used for successive powers of n to update
    # both a and b
    # r is the exponent - decreases with each update
    #
    x = pow(a, (s + 1) / 2, p)
    b = pow(a, s, p)
    g = pow(n, s, p)
    r = e

    while True:
        t = b
        m = 0
        for m in xrange(r):
            if t == 1:
                break
            t = pow(t, 2, p)

        if m == 0:
            assert pow(x, 2, p) == a
            return x

        gs = pow(g, 2 ** (r - m - 1), p)
        g = (gs * gs) % p
        x = (x * gs) % p
        b = (b * g) % p
        r = m


def legendre_symbol(a, p):
    """ Compute the Legendre symbol a|p using
        Euler's criterion. p is a prime, a is
        relatively prime to p (if p divides
        a, then a|p = 0)

        Returns 1 if a has a square root modulo
        p, -1 otherwise.
    """
    ls = pow(a, (p - 1) / 2, p)
    return -1 if ls == p - 1 else ls


# Check if a point is on the curve
def is_on_curve(p):
    return (-p[0] ** 2 + p[1] ** 2) % Q == (1 + D * p[0] ** 2 * p[1] ** 2) % Q


# Add two points
def add(p, q):
    den_factor = (D * p[0] * p[1] * q[0] * q[1]) % Q
    x_num = (p[0] * q[1] + p[1] * q[0]) % Q
    y_num = (p[0] * q[0] + p[1] * q[1]) % Q
    o = ((x_num * inv(1 + den_factor, Q)) % Q,
         (y_num * inv(1 - den_factor, Q)) % Q)
    return o


# Multiply a point by a scalar using the double-and-add algorithm
def multiply(p, n, adder=add):
    if n == 0:
        return (0, 1)
    elif n == 1:
        return p
    else:
        x = multiply(adder(p, p), n/2, adder)
        if n % 2:
            x = adder(x, p)
        return x


# Convert a point to extended format, see
# http://eprint.iacr.org/2008/522.pdf
def to_extended(p):
    return (p[0], p[1], p[0] * p[1] % Q, 1)


# Convert back from extended format
def from_extended(p):
    zinv = inv(p[3], Q)
    return (p[0] * zinv % Q, p[1] * zinv % Q)


# Add two points in extended format. The reason this algorithm is
# used is that modular inverses are very expensive, and the extended
# form essentially keeps track of a denominator and numerators
# separately, allowing all the required divisions to be "batched"
# together at the end with only one inverse (instead of an average
# of 384 inverse operations using the normal algorithm)
def add_extended(p, q):
    _A = p[0] * q[0] % Q
    _B = p[1] * q[1] % Q
    _C = D * p[2] * q[2] % Q
    _D = p[3] * q[3] % Q
    _E = ((p[0] + p[1]) * (q[0] + q[1]) - _A - _B) % Q
    _F = _D - _C
    _G = _D + _C
    _H = _B + _A  # _B - a * _A, but a = -1
    return (_E * _F % Q, _G * _H % Q, _E * _H % Q, _F * _G % Q)


# def fast_multiply(p, n):
#     return from_extended(multiply(to_extended(p), n, adder=add_extended))


def blake2b(msg_hash: bytes) -> bytes:
    return BLAKE2B(msg_hash).digest()


# Standard-form encoding for a public key
def encode_raw_public_key(raw_public_key: Tuple[int, int]) -> bytes:
    left, right = raw_public_key
    if left > Q - left:
        right |= 2**255
    return int_to_big_endian(right)

# def encode_raw_public_key(raw_public_key: Tuple[int, int]) -> bytes:
#     left, right = raw_public_key
#     return b''.join((
#         pad32(int_to_big_endian(left)),
#         pad32(int_to_big_endian(right)),
#     ))


def x_from_y(y):
    # -x^2 + y^2 = 1 + d * x^2 * y^2
    # implies
    # (y^2 - 1) / (d * y^2 + 1) = x^2
    nom = (y*y-1) % Q
    den = (D*y*y+1) % Q
    return modular_sqrt((nom * inv(den, Q)) % Q, Q)


def decode_public_key(public_key_bytes: bytes) -> Tuple[int, int]:
    v = big_endian_to_int(public_key_bytes)
    right = v % 2**255
    left = x_from_y(right)
    if (left > Q - left) ^ (v >> 255):
        left = Q - left
    return (left, right)


def privtopub(k):
    # h = blake2b(k)
    a = 2 ** (BITS - 2) + (big_endian_to_int(k[:32]) % 2 ** (BITS - 2))
    a -= (a % 8)
    temp = fast_multiply(B, a)
    print('MULTIPLY RESULT: ')
    print(temp)
    return temp


# Signature algorithm
def sign(k, m):
    h = blake2b(k)
    a = 2 ** (BITS - 2) + (big_endian_to_int(h[:32]) % 2 ** (BITS - 2))
    a -= (a % 8)
    A = fast_multiply(B, a)
    r = big_endian_to_int(h[32:])
    R = fast_multiply(B, r)
    h2 = blake2b(encode_raw_public_key(R) + encode_raw_public_key(A) + m)
    s = (r + big_endian_to_int(h2) * a) % L
    return encode_raw_public_key(R) + int_to_big_endian(s)


# Verification algorithm
def verify(pub, sig, m):
    R = decode_public_key(sig[:32])
    s = big_endian_to_int(sig[32:])
    if s >= L:
        return False
    A = encode_raw_public_key(pub)
    h2 = blake2b(sig[:32] + A + m)
    assert is_on_curve(R)
    return fast_multiply(B, 8 * s) == add(fast_multiply(R, 8), fast_multiply(pub, 8 * big_endian_to_int(h2)))


def ecdsa_raw_recover(*args, **kwargs):
    raise Exception("Not Implemented")


def ecdsa_raw_sign(msg_hash: bytes,
                   private_key_bytes: bytes) -> Tuple[int, int, int]:
    raise Exception("Not Implemented")


def private_key_to_public_key(private_key_bytes: bytes) -> bytes:
    raw_public_key = privtopub(private_key_bytes)
    public_key_bytes = encode_raw_public_key(raw_public_key)
    print(public_key_bytes)
    return public_key_bytes
