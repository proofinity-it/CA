"""Independent reference implementation of CA content identity, scheme 1.

Written from docs/spec.md alone, not from CA/RefHash.lean, to show that the
specification is enough to reproduce the ids. Python 3 standard library
only. Run it to check the golden vectors of spec.md §12:

    python3 -I tools/refhash_ref.py

Scope: everything the specification defines (primitives, level
normalisation, canonicalisation, expression ids, declaration encodings,
blocks). Input is built by hand below; there is no .olean reader.
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Callable, Optional, Union

SCHEME = 1

# ── §3 primitives ────────────────────────────────────────────────────────

def H(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()

def u8(x: int) -> bytes:
    return bytes([x])

def u64(n: int) -> bytes:
    return (n % 2**64).to_bytes(8, "little")

def nbytes(b: bytes) -> bytes:
    return u64(len(b)) + b

def string(s: str) -> bytes:
    return nbytes(s.encode("utf-8"))

def bignat(n: int) -> bytes:
    return nbytes(n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b"")

B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

def b58(b: bytes) -> str:
    n = int.from_bytes(b, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + out

# ── §4 input model ───────────────────────────────────────────────────────
# Names are dotted strings; only resolution and level parameters use them.

@dataclass(frozen=True)
class Level:
    k: str                      # zero | succ | max | imax | param
    a: Optional["Level"] = None
    b: Optional["Level"] = None
    name: str = ""

ZERO = Level("zero")
def succ(l): return Level("succ", l)
def lmax(a, b): return Level("max", a, b)
def imax(a, b): return Level("imax", a, b)
def param(n): return Level("param", name=n)

@dataclass(frozen=True)
class Expr:
    k: str                      # bvar const sort app lam forall let litnat litstr proj mdata
    n: int = 0                  # bvar index, literal, proj index
    s: str = ""                 # const name, string literal, proj struct name
    levels: tuple = ()
    lvl: Optional[Level] = None
    a: Optional["Expr"] = None  # app fn / binder type / let type / proj struct / mdata body
    b: Optional["Expr"] = None  # app arg / binder body / let value
    c: Optional["Expr"] = None  # let body
    bi: int = 0                 # 0 default, 1 implicit, 2 strictImplicit, 3 instImplicit

def bvar(i): return Expr("bvar", n=i)
def const(n, *ls): return Expr("const", s=n, levels=tuple(ls))
def sort(l): return Expr("sort", lvl=l)
def app(f, *xs):
    for x in xs:
        f = Expr("app", a=f, b=x)
    return f
def lam(t, body, bi=0): return Expr("lam", a=t, b=body, bi=bi)
def pi(t, body, bi=0): return Expr("forall", a=t, b=body, bi=bi)

@dataclass
class Const:
    name: str
    kind: str                   # axiom defn thm opaque quot induct ctor rec
    level_params: list
    type: Expr
    value: Optional[Expr] = None
    all: list = field(default_factory=list)
    safety: int = 0             # defn: 0 safe 1 unsafe 2 partial
    unsafe: bool = False
    quot_kind: int = 0
    # inductive
    num_params: int = 0
    num_indices: int = 0
    num_nested: int = 0
    is_rec: bool = False
    is_reflexive: bool = False
    ctors: list = field(default_factory=list)
    # constructor
    induct: str = ""
    cidx: int = 0
    num_fields: int = 0
    # recursor
    num_motives: int = 0
    num_minors: int = 0
    k_flag: bool = False
    rules: list = field(default_factory=list)   # (ctor, nfields, rhs)

# ── §5 levels: normal form (Lean 4 Level.normalize) ──────────────────────

def name_lt(x: str, y: str) -> bool:
    return x.split(".") < y.split(".")          # string components only

def offset(l):
    k = 0
    while l.k == "succ":
        l, k = l.a, k + 1
    return k

def base(l):
    while l.k == "succ":
        l = l.a
    return l

def add_offset(l, k):
    for _ in range(k):
        l = succ(l)
    return l

CTOR = {"zero": 0, "param": 1, "mvar": 2, "succ": 3, "max": 4, "imax": 5}

def norm_lt(l1, k1, l2, k2) -> bool:
    if l1.k == "succ":
        return norm_lt(l1.a, k1 + 1, l2, k2)
    if l2.k == "succ":
        return norm_lt(l1, k1, l2.a, k2 + 1)
    if l1.k == l2.k and l1.k in ("max", "imax"):
        if l1 == l2:
            return k1 < k2
        if l1.a != l2.a:
            return norm_lt(l1.a, 0, l2.a, 0)
        return norm_lt(l1.b, 0, l2.b, 0)
    if l1.k == l2.k == "param":
        return k1 < k2 if l1.name == l2.name else name_lt(l1.name, l2.name)
    return k1 < k2 if l1 == l2 else CTOR[l1.k] < CTOR[l2.k]

def never_zero(l) -> bool:
    if l.k == "succ": return True
    if l.k == "max": return never_zero(l.a) or never_zero(l.b)
    if l.k == "imax": return never_zero(l.b)
    return False

def cheap_normal(l) -> bool:
    return l.k in ("zero", "param") or (l.k == "succ" and cheap_normal(l.a))

def max_args(l, done, acc):
    if l.k == "max":
        return max_args(l.b, done, max_args(l.a, done, acc))
    if not done:
        return max_args(normalize(l), True, acc)
    acc.append(l)
    return acc

def normalize(l: Level) -> Level:
    if cheap_normal(l):
        return l
    k, u = offset(l), base(l)
    if u.k == "max":
        import functools
        lv = max_args(u.b, False, max_args(u.a, False, []))
        lv.sort(key=functools.cmp_to_key(
            lambda x, y: -1 if norm_lt(x, 0, y, 0) else (1 if norm_lt(y, 0, x, 0) else 0)))
        first = 0
        while first < len(lv) and base(lv[first]).k == "zero":
            first += 1
        subsumed = first != 0 and any(offset(x) >= offset(lv[first - 1]) for x in lv[first:])
        i = first if subsumed else first - 1
        prev, prevk, result = base(lv[i]), offset(lv[i]), ZERO
        def acc(result, prev, off):
            return add_offset(prev, off) if result == ZERO else lmax(result, add_offset(prev, off))
        for x in lv[i + 1:]:
            if base(x) != prev:
                result = acc(result, prev, k + prevk)
            prev, prevk = base(x), offset(x)
        return acc(result, prev, k + prevk)
    assert u.k == "imax"
    if never_zero(u.b):
        return add_offset(normalize(lmax(u.a, u.b)), k)
    a, b = normalize(u.a), normalize(u.b)
    if b == ZERO: r = ZERO
    elif a == ZERO or a == succ(ZERO): r = b
    elif a == b: r = a
    else: r = imax(a, b)
    return add_offset(r, k)

# ── §6 canonicalisation ──────────────────────────────────────────────────

def level_params_in(e: Expr, out: list):
    def lv(l):
        if l is None: return
        if l.k == "param" and l.name not in out: out.append(l.name)
        lv(l.a); lv(l.b)
    if e is None: return
    if e.k == "const":
        for l in e.levels: lv(l)
    if e.k == "sort": lv(e.lvl)
    for c in (e.a, e.b, e.c): level_params_in(c, out)

def canonical(level_params: list, e: Expr) -> Expr:
    occurring = []
    level_params_in(e, occurring)
    order = list(level_params) + [p for p in occurring if p not in level_params]
    ren = {p: f"u_{i}" for i, p in enumerate(order)}
    def L(l):
        def go(l):
            if l.k == "param": return param(ren.get(l.name, l.name))
            if l.k == "succ": return succ(go(l.a))
            if l.k in ("max", "imax"): return Level(l.k, go(l.a), go(l.b))
            return l
        return normalize(go(l))
    def E(e):
        if e is None: return None
        if e.k == "mdata": return E(e.a)
        if e.k == "const": return Expr("const", s=e.s, levels=tuple(L(l) for l in e.levels))
        if e.k == "sort": return Expr("sort", lvl=L(e.lvl))
        return Expr(e.k, n=e.n, s=e.s, a=E(e.a), b=E(e.b), c=E(e.c), bi=e.bi)
    return E(e)

# ── §7 expression ids ────────────────────────────────────────────────────

RefEnc = Union[bytes, int, str]     # 32-byte id | block-local index | unresolved name

def refenc(r: RefEnc) -> bytes:
    if isinstance(r, bytes): return u8(0x31) + r
    if isinstance(r, int): return u8(0x32) + u64(r)
    return u8(0x33) + string(r)

def level_enc(l: Level) -> bytes:
    if l.k == "zero": return u8(0x10)
    if l.k == "succ": return u8(0x11) + level_enc(l.a)
    if l.k == "max": return u8(0x12) + level_enc(l.a) + level_enc(l.b)
    if l.k == "imax": return u8(0x13) + level_enc(l.a) + level_enc(l.b)
    return u8(0x14) + string(l.name)

def depth(e: Expr) -> int:
    if e.k in ("app", "lam", "forall"): return max(depth(e.a), depth(e.b)) + 1
    if e.k == "let": return max(depth(e.a), depth(e.b), depth(e.c)) + 1
    if e.k == "proj": return depth(e.a) + 1
    return 0

TAG = {"bvar": 0x21, "sort": 0x24, "const": 0x25, "app": 0x26, "lam": 0x27,
       "forall": 0x28, "let": 0x29, "litnat": 0x2A, "litstr": 0x2B, "proj": 0x2C}

def leaf(e, R) -> bytes:
    t = u8(TAG[e.k])
    if e.k == "bvar": return t + u64(e.n)
    if e.k == "sort": return t + level_enc(e.lvl)
    if e.k == "const":
        return t + refenc(R(e.s)) + u64(len(e.levels)) + b"".join(level_enc(l) for l in e.levels)
    if e.k == "litnat": return t + bignat(e.n)
    if e.k == "litstr": return t + string(e.s)
    raise ValueError(e.k)

def flat(e, R) -> bytes:
    t = u8(TAG.get(e.k, 0))
    if e.k == "app": return t + flat(e.a, R) + flat(e.b, R)
    if e.k in ("lam", "forall"): return t + u8(e.bi) + flat(e.a, R) + flat(e.b, R)
    if e.k == "let": return t + flat(e.a, R) + flat(e.b, R) + flat(e.c, R)
    if e.k == "proj": return t + refenc(R(e.s)) + u64(e.n) + flat(e.a, R)
    return leaf(e, R)

def eid(e: Expr, R: Callable[[str], RefEnc]) -> bytes:
    if depth(e) <= 6:
        return H(u8(0x2F) + flat(e, R))
    t = u8(TAG[e.k])
    if e.k == "app": return H(t + eid(e.a, R) + eid(e.b, R))
    if e.k in ("lam", "forall"): return H(t + u8(e.bi) + eid(e.a, R) + eid(e.b, R))
    if e.k == "let": return H(t + eid(e.a, R) + eid(e.b, R) + eid(e.c, R))
    if e.k == "proj": return H(t + refenc(R(e.s)) + u64(e.n) + eid(e.a, R))
    return H(leaf(e, R))

# ── §8 declaration encodings ─────────────────────────────────────────────

KIND = {"axiom": 1, "defn": 2, "thm": 3, "opaque": 4, "quot": 5, "induct": 6, "ctor": 7, "rec": 8}

def stmt_hash(c: Const, R) -> bytes:
    return H(u8(0xA1) + u8(SCHEME) + u64(len(c.level_params)) + eid(canonical(c.level_params, c.type), R))

def tail(c: Const, R, with_proofs=True) -> bytes:
    v = lambda e: eid(canonical(c.level_params, e), R)
    if c.kind == "axiom": return u8(c.unsafe)
    if c.kind == "defn": return u8(c.safety) + v(c.value)
    if c.kind == "thm": return v(c.value) if with_proofs else b""
    if c.kind == "opaque": return u8(c.unsafe) + v(c.value)
    if c.kind == "quot": return u8(c.quot_kind)
    if c.kind == "induct":
        return (u64(c.num_params) + u64(c.num_indices) + u64(c.num_nested) + u8(c.is_rec)
                + u8(c.unsafe) + u8(c.is_reflexive) + u64(len(c.ctors))
                + b"".join(refenc(R(x)) for x in c.ctors))
    if c.kind == "ctor":
        return refenc(R(c.induct)) + u64(c.cidx) + u64(c.num_params) + u64(c.num_fields) + u8(c.unsafe)
    if c.kind == "rec":
        b = (u64(c.num_params) + u64(c.num_indices) + u64(c.num_motives) + u64(c.num_minors)
             + u8(c.k_flag) + u8(c.unsafe) + u64(len(c.rules)))
        for ctor, nfields, rhs in c.rules:
            b += refenc(R(ctor)) + u64(nfields) + v(rhs)
        return b
    raise ValueError(c.kind)

def member_enc(c: Const, R) -> bytes:
    return u8(KIND[c.kind]) + stmt_hash(c, R) + tail(c, R)

# ── §9 reference graph and blocks ────────────────────────────────────────

def refs_of(c: Const) -> set:
    acc = set()
    def walk(e):
        if e is None: return
        if e.k == "const": acc.add(e.s)
        for x in (e.a, e.b, e.c): walk(x)
    walk(c.type)
    if c.kind in ("defn", "thm", "opaque"): walk(c.value)
    others = [n for n in c.all if n != c.name]
    if c.kind == "induct": acc.update(c.ctors + others)
    if c.kind == "ctor": acc.add(c.induct)
    if c.kind == "rec":
        acc.update(c.all)
        for ctor, _, rhs in c.rules:
            acc.add(ctor); walk(rhs)
    if c.kind in ("defn", "opaque", "thm"): acc.update(others)
    return acc

def sccs(names, succ_):
    index, low, stack, on, out = {}, {}, [], set(), []
    counter = [0]
    def strong(v):
        index[v] = low[v] = counter[0]; counter[0] += 1
        stack.append(v); on.add(v)
        for w in succ_(v):
            if w not in index:
                strong(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); on.discard(w); comp.append(w)
                if w == v: break
            out.append(comp)
    for n in names:
        if n not in index: strong(n)
    return out

@dataclass
class Ids:
    stmt: bytes
    decl: bytes
    ref: bytes
    block: Optional[tuple] = None
    unresolved: list = field(default_factory=list)

def src_key(n, decls):
    c = decls[n]
    if c.kind == "ctor":
        ind = decls.get(c.induct)
        all_ = ind.all if ind and ind.kind == "induct" else []
        return (all_.index(c.induct) if c.induct in all_ else len(all_)) * 1000 + c.cidx + 1
    if c.kind == "induct": return c.all.index(n) * 1000
    if c.kind == "rec":
        pre = n.rsplit(".", 1)[0]
        return len(c.all) * 1000 + 900 + (c.all.index(pre) if pre in c.all else len(c.all))
    if c.kind in ("defn", "opaque", "thm"): return c.all.index(n) if n in c.all else len(c.all)
    return 0

def compute_ids(decls: dict, base: dict) -> dict:
    succ_ = lambda n: [m for m in refs_of(decls[n]) if m in decls]
    table, out = dict(base), {}
    for comp in sccs(list(decls), succ_):
        n0 = comp[0]
        if len(comp) == 1 and n0 not in succ_(n0):
            c, unres = decls[n0], []
            def R(m):
                if m in table: return table[m]
                unres.append(m); return m
            s = stmt_hash(c, R)
            d = H(u8(0xA2) + u8(SCHEME) + u8(KIND[c.kind]) + s + tail(c, R))
            out[n0] = Ids(s, d, s if c.kind == "thm" else d, None, unres)
            table[n0] = out[n0].ref
            continue
        inblock = set(comp)
        anon = lambda m: 0 if m in inblock else table.get(m, m)
        shaped = sorted((H(member_enc(decls[n], anon)), src_key(n, decls), n) for n in comp)
        members = [n for _, _, n in shaped]
        pos = {n: i for i, n in enumerate(members)}
        local = lambda m: pos[m] if m in pos else table.get(m, m)
        block = H(u8(0xA3) + u8(SCHEME) + u64(len(members))
                  + b"".join(member_enc(decls[n], local) for n in members))
        mdecl = {n: H(u8(0xA4) + u8(SCHEME) + block + u64(i)) for i, n in enumerate(members)}
        full = lambda m: mdecl[m] if m in mdecl else table.get(m, m)
        for i, n in enumerate(members):
            c = decls[n]
            s = stmt_hash(c, full)
            out[n] = Ids(s, mdecl[n], s if c.kind == "thm" else mdecl[n], (block, i))
        for n in members:
            table[n] = out[n].ref
    return out

# ── §12 golden vectors ───────────────────────────────────────────────────

def golden():
    T = const("T")
    u = param("u")
    decls = {
        "T": Const("T", "induct", [], sort(succ(ZERO)), all=["T"], ctors=["T.a", "T.b"]),
        "T.a": Const("T.a", "ctor", [], T, induct="T", cidx=0),
        "T.b": Const("T.b", "ctor", [], T, induct="T", cidx=1),
        # T.rec.{u} : {motive : T → Sort u} → motive T.a → motive T.b → (t : T) → motive t
        "T.rec": Const("T.rec", "rec", ["u"],
            pi(pi(T, sort(u)),
               pi(app(bvar(0), const("T.a")),
                  pi(app(bvar(1), const("T.b")),
                     pi(T, app(bvar(3), bvar(0)))))
               , bi=1),
            all=["T"], num_motives=1, num_minors=2,
            rules=[("T.a", 0, lam(pi(T, sort(u)), lam(app(bvar(0), const("T.a")),
                                   lam(app(bvar(1), const("T.b")), bvar(1))), bi=1)),
                   ("T.b", 0, lam(pi(T, sort(u)), lam(app(bvar(0), const("T.a")),
                                   lam(app(bvar(1), const("T.b")), bvar(0))), bi=1))]),
        "idT": Const("idT", "defn", [], pi(T, T), value=lam(T, bvar(0)), all=["idT"]),
    }
    ids = compute_ids(decls, {})
    want = [("T.decl", ids["T"].decl, "AwbguQQn99uqMeaCaqyKHw57myYCFN8QxPuucQ8xeZTJ"),
            ("T.a.decl", ids["T.a"].decl, "39W2PKpM7xCyj9RyTYDNjnibqnAuCUqBJxgewcAvjYQK"),
            ("T.rec.stmt", ids["T.rec"].stmt, "6cqensD4yYH2bdFVSE3GAzBGexXV2M5NHCLiV4DjfAYD"),
            ("idT.decl", ids["idT"].decl, "2L8HHtdHc1GnBSmsACbRew9etEWEo1y4ZnNhX8XjGn1N")]
    ok = True
    for label, got, w in want:
        good = b58(got) == w
        ok &= good
        print(f"  {'ok  ' if good else 'FAIL'} {label:11} {b58(got)}" + ("" if good else f"  (want {w})"))
    # Vector 2: Nat.add_zero's stmt over seven Init refs (toolchain v4.35.0).
    base = {n: bytes.fromhex(h) for n, h in [
        ("Nat", "7fb2a329273091b1cab1d0de5ae79287b656d4020e9aaf6f6cf5f8d2856abcef"),
        ("Eq", "b04c703d0fd427681207151d10bd619905146c4f2e566493ee5bc5a9621a74d9"),
        ("HAdd.hAdd", "21d224e41b0d36e25396c57f1d564e6dc0cbfc79fb01e0f8b0593f357709ca25"),
        ("instHAdd", "56e6e06da7817bade49ac08cf4dce572c72d97df527ed032daab175cf390cebe"),
        ("instAddNat", "1e73d434775b9fa30f6d65a3f35b8f02aab17f65ae3971b0992129295ee37538"),
        ("OfNat.ofNat", "90ec041fa5e8dde1f15d3897e134d66a439f76c61f05e4b2dd9a591ba833cd78"),
        ("instOfNatNat", "dd09eafbd1b3ad4621cd607b940fcc7475acab7e6c9c70323d56fdbed60e7fc0")]}
    N, z = const("Nat"), Expr("litnat", n=0)
    add_zero_ty = pi(N, app(const("Eq", succ(ZERO)), N,
        app(const("HAdd.hAdd", ZERO, ZERO, ZERO), N, N, N,
            app(const("instHAdd", ZERO), N, const("instAddNat")), bvar(0),
            app(const("OfNat.ofNat", ZERO), N, z, app(const("instOfNatNat"), z))),
        bvar(0)))
    P = const("P")
    decls2 = {
        "Nat.add_zero": Const("Nat.add_zero", "thm", [], add_zero_ty, value=bvar(0), all=["Nat.add_zero"]),
        "big": Const("big", "defn", [], N, all=["big"], value=app(const("OfNat.ofNat", ZERO), N,
            Expr("litnat", n=2**64), app(const("instOfNatNat"), Expr("litnat", n=2**64)))),
        "P": Const("P", "induct", [], sort(succ(ZERO)), all=["P"], ctors=["P.mk"]),
        "P.mk": Const("P.mk", "ctor", [], pi(N, pi(N, P)), induct="P", num_fields=2),
        # P.x / P.y deliberately absent from the base: by-name fallback (§10).
        "P.swap": Const("P.swap", "defn", [], pi(P, P), all=["P.swap"],
            value=lam(P, app(const("P.mk"), app(const("P.y"), bvar(0)), app(const("P.x"), bvar(0))))),
    }
    ids2 = compute_ids(decls2, base)
    want += [("Nat.add_zero.stmt", ids2["Nat.add_zero"].stmt, "ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn"),
             ("big.decl", ids2["big"].decl, "qyC5XoBvrSDTbcPawy59p4fiT1VjSvamo8gK2JpVqX5"),
             ("P.decl", ids2["P"].decl, "6PnwNkHkkfzYiTRZ4x4UUTERSjCf6xurDiChq8Rax7Kx"),
             ("P.mk.decl", ids2["P.mk"].decl, "kVBJfYjxoUkBgJ7gp694anFkxBtmdqNvbFP3QzHYJKo"),
             ("P.swap.decl", ids2["P.swap"].decl, "EaQQWNhTHis186MUGjrX12waDF2RGqJn85jojKQk3j7m")]
    for label, got, w in want[4:]:
        good = b58(got) == w
        ok &= good
        print(f"  {'ok  ' if good else 'FAIL'} {label:17} {b58(got)}" + ("" if good else f"  (want {w})"))
    good = sorted(ids2["P.swap"].unresolved) == ["P.x", "P.y"]
    ok &= good
    print(f"  {'ok  ' if good else 'FAIL'} P.swap unresolved = [P.x, P.y]")
    # Level normal form: the §5 examples.
    v = param("v")
    checks = [(lmax(u, v), lmax(v, u)), (lmax(u, u), u), (imax(u, succ(v)), lmax(u, succ(v))),
              (lmax(succ(ZERO), succ(ZERO)), succ(ZERO))]
    for a, b in checks:
        good = normalize(a) == normalize(b)
        ok &= good
        print(f"  {'ok  ' if good else 'FAIL'} normalize equal: {a} ~ {b}" if not good else "  ok   level normal form example")
    return ok

if __name__ == "__main__":
    import sys
    sys.exit(0 if golden() else 1)
