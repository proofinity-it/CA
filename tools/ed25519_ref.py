"""Ed25519 (RFC 8032) in Python's standard library, for tools/registry_ref.py.

Verification only needs `verify`; `sign` and `public_key` are here so the
checker's own tests can round-trip. Not constant-time: it checks public
signatures, it does not hold keys.
"""
from __future__ import annotations

import hashlib

p = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
d = (-121665 * pow(121666, p - 2, p)) % p
Bx = 15112221349535400772501151409588531511454012693041857206046113283949847762202
By = (4 * pow(5, p - 2, p)) % p
B = (Bx, By, 1, Bx * By % p)
ZERO = (0, 1, 1, 0)

def add(P, Q):
    x1, y1, z1, t1 = P; x2, y2, z2, t2 = Q
    a = (y1 - x1) * (y2 - x2) % p
    b = (y1 + x1) * (y2 + x2) % p
    c = t1 * 2 * d * t2 % p
    dd = z1 * 2 * z2 % p
    e, f, g, h = b - a, dd - c, dd + c, b + a
    return (e * f % p, g * h % p, f * g % p, e * h % p)

def double(P):
    x1, y1, z1, _ = P
    a = x1 * x1 % p; b = y1 * y1 % p; c = 2 * z1 * z1 % p
    h = a + b; e = h - (x1 + y1) ** 2; g = a - b; f = c + g
    return (e * f % p, g * h % p, f * g % p, e * h % p)

def mul(P, n):
    r, q = ZERO, P
    while n > 0:
        if n & 1: r = add(r, q)
        q = double(q); n >>= 1
    return r

def encode(P):
    x, y, z, _ = P
    zi = pow(z, p - 2, p)
    x, y = x * zi % p, y * zi % p
    return (y | ((x & 1) << 255)).to_bytes(32, "little")

def decode(b: bytes):
    if len(b) != 32: return None
    n = int.from_bytes(b, "little")
    sign, y = n >> 255, n & ((1 << 255) - 1)
    if y >= p: return None
    y2 = y * y % p
    u, v = (y2 - 1) % p, (d * y2 + 1) % p
    x2 = u * pow(v, p - 2, p) % p
    x = pow(x2, (p + 3) // 8, p)
    if x * x % p != x2: x = x * pow(2, (p - 1) // 4, p) % p
    if x * x % p != x2: return None
    if x == 0 and sign: return None
    if x & 1 != sign: x = (-x) % p
    return (x, y, 1, x * y % p)

def _clamp(h: bytes) -> int:
    h = bytearray(h[:32]); h[0] &= 248; h[31] &= 63; h[31] |= 64
    return int.from_bytes(bytes(h), "little")

def public_key(seed: bytes) -> bytes:
    return encode(mul(B, _clamp(hashlib.sha512(seed).digest())))

def sign(seed: bytes, msg: bytes) -> bytes:
    h = hashlib.sha512(seed).digest()
    s, prefix = _clamp(h), h[32:]
    pk = encode(mul(B, s))
    r = int.from_bytes(hashlib.sha512(prefix + msg).digest(), "little") % L
    R = encode(mul(B, r))
    k = int.from_bytes(hashlib.sha512(R + pk + msg).digest(), "little") % L
    return R + ((r + k * s) % L).to_bytes(32, "little")

def verify(pk: bytes, msg: bytes, sig: bytes) -> bool:
    if len(sig) != 64 or len(pk) != 32: return False
    R, A = decode(sig[:32]), decode(pk)
    if R is None or A is None: return False
    s = int.from_bytes(sig[32:], "little")
    if s >= L: return False
    k = int.from_bytes(hashlib.sha512(sig[:32] + pk + msg).digest(), "little") % L
    return encode(mul(B, s)) == encode(add(R, mul(A, k)))

if __name__ == "__main__":   # RFC 8032 §7.1 test 1
    seed = bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
    pk = bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
    sig = bytes.fromhex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
    assert public_key(seed) == pk and sign(seed, b"") == sig and verify(pk, b"", sig) and not verify(pk, b"x", sig)
    print("ed25519_ref: RFC 8032 test 1 ok")
