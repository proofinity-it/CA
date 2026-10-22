"""Independent checker for CA payloads and node files.

Written from docs/payload.md and docs/spec.md, not from CA/Payload.lean or
CA/Node.lean, to show that the documents are enough to check what CA
writes. Python 3 standard library only (sqlite3, hashlib, json).

    python3 -I tools/registry_ref.py node.sqlite          # a node file (ca pack)
    python3 -I tools/registry_ref.py registry/statements.json
    python3 -I tools/registry_ref.py --vectors            # payload.md §9

For every unit it decodes the bytes (payload.md §2-§3), recomputes the ids
bottom-up over the node table (payload.md §5, spec.md §7-§9), and compares
them with the key the unit is filed under. For a node file it also checks
each unit's variant digest, every member / declaration / witness / entry
row against the units, and that every decoration parses and names every
slot of its unit (rebuilding a declaration from a decoration needs Lean,
and is `ca check`'s job). Exit status 1 on any fault.
"""
from __future__ import annotations

import base64
import hashlib
import json
import sqlite3
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.dont_write_bytecode = True   # importing refhash_ref must not leave __pycache__ in tools/
sys.path.insert(0, str(Path(__file__).resolve().parent))
from refhash_ref import H, SCHEME, b58, u8, u64  # noqa: E402  (spec.md §3 primitives)

PAYLOAD_FORMAT = 1

# ── payload.md §2 primitives ─────────────────────────────────────────────

class Reader:
    def __init__(self, b: bytes):
        self.b, self.p = b, 0

    def u8(self) -> int:
        if self.p >= len(self.b): raise ValueError(f"truncated at byte {self.p}")
        x = self.b[self.p]; self.p += 1
        return x

    def uv(self) -> int:
        acc, shift, count = 0, 0, 0
        while True:
            x = self.u8(); count += 1
            acc |= (x & 0x7F) << shift
            shift += 7
            if x < 0x80:
                if x == 0 and count > 1: raise ValueError("non-minimal LEB128")
                return acc

    def bytes_(self) -> bytes:
        n = self.uv()
        if self.p + n > len(self.b): raise ValueError("truncated byte string")
        out = self.b[self.p:self.p + n]; self.p += n
        return out

    def sv(self) -> str:
        return self.bytes_().decode("utf-8")

    def nm(self) -> tuple:
        comps = []
        for _ in range(self.uv()):
            t = self.u8()
            if t == 0: comps.append(self.sv())
            elif t == 1: comps.append(self.uv())
            else: raise ValueError(f"bad name component tag {t}")
        return tuple(comps)

    def bool_(self) -> bool:
        x = self.u8()
        if x not in (0, 1): raise ValueError(f"bad boolean {x}")
        return x == 1

    def done(self) -> bool:
        return self.p == len(self.b)


def name_str(n: tuple) -> str:
    """Dotted rendering (spec.md §3 `name`), used only for unresolved references.
    Components that are not plain identifiers would need Lean's «» escaping,
    which this checker does not reproduce: such ids are reported inexact anyway."""
    return ".".join(str(c) for c in n)

# ── payload.md §3 units ──────────────────────────────────────────────────

def read_rref(r: Reader):
    t = r.u8()
    if t == 0x30: return ("self",)
    if t == 0x31: return ("ref", r.uv())
    if t == 0x32: return ("member", r.uv())
    if t == 0x33: return ("byName", r.nm())
    raise ValueError(f"bad reference tag {t:#x}")

def read_level(r: Reader):
    t = r.u8()
    if t == 0x10: return ("zero",)
    if t == 0x11: return ("succ", read_level(r))
    if t in (0x12, 0x13): return ("max" if t == 0x12 else "imax", read_level(r), read_level(r))
    if t == 0x14: return ("param", r.uv())
    raise ValueError(f"bad level tag {t:#x}")

def read_node(r: Reader, self_ix: int):
    def child():
        d = r.uv()
        if d == 0 or d > self_ix: raise ValueError(f"node {self_ix}: bad child distance {d}")
        return self_ix - d
    t = r.u8()
    if t == 0x21: return ("bvar", r.uv())
    if t == 0x24: return ("sort", read_level(r))
    if t == 0x25:
        ref = read_rref(r)
        return ("const", ref, [read_level(r) for _ in range(r.uv())])
    if t == 0x26: return ("app", child(), child())
    if t in (0x27, 0x28):
        bi = r.u8()
        if bi > 3: raise ValueError(f"bad binder info {bi}")
        r.uv()                                   # binder slot: not hashed
        return ("lam" if t == 0x27 else "forall", bi, child(), child())
    if t == 0x29:
        r.uv(); r.bool_()                        # binder slot, nonDep: not hashed
        return ("let", child(), child(), child())
    if t == 0x2A:
        b = r.bytes_()
        if b and b[0] == 0: raise ValueError("non-minimal natural literal")
        return ("litnat", b)
    if t == 0x2B: return ("litstr", r.sv())
    if t == 0x2C:
        ref = read_rref(r); i = r.uv()
        return ("proj", ref, i, child())
    raise ValueError(f"node {self_ix}: bad tag {t:#x}")

KINDS = {1: "axiom", 2: "defn", 3: "thm", 4: "opaque", 5: "quot", 6: "induct", 7: "ctor", 8: "rec"}

def read_rrefs(r: Reader) -> list:
    return [read_rref(r) for _ in range(r.uv())]

def read_member(r: Reader) -> dict:
    kind = r.u8()
    if kind not in KINDS: raise ValueError(f"bad kind {kind}")
    m = {"kind": KINDS[kind], "nl": r.uv(), "type": r.uv()}
    k = m["kind"]
    if k == "axiom": m["unsafe"] = r.bool_()
    elif k == "defn": m["safety"] = r.u8(); m["value"] = r.uv(); m["all"] = read_rrefs(r)
    elif k == "thm":
        m["value"] = r.uv() if r.bool_() else None; m["all"] = read_rrefs(r)
    elif k == "opaque": m["unsafe"] = r.bool_(); m["value"] = r.uv(); m["all"] = read_rrefs(r)
    elif k == "quot": m["quot"] = r.u8()
    elif k == "induct":
        m["np"], m["ni"], m["nn"] = r.uv(), r.uv(), r.uv()
        m["rec"], m["unsafe"], m["refl"] = r.bool_(), r.bool_(), r.bool_()
        m["ctors"] = read_rrefs(r); m["all"] = read_rrefs(r)
    elif k == "ctor":
        m["induct"] = read_rref(r)
        m["cidx"], m["np"], m["nf"] = r.uv(), r.uv(), r.uv()
        m["unsafe"] = r.bool_()
    elif k == "rec":
        m["np"], m["ni"], m["nmot"], m["nmin"] = r.uv(), r.uv(), r.uv(), r.uv()
        m["k"], m["unsafe"] = r.bool_(), r.bool_()
        m["rules"] = [(read_rref(r), r.uv(), r.uv()) for _ in range(r.uv())]
        m["all"] = read_rrefs(r)
    return m

@dataclass
class Unit:
    form: int
    refs: list
    nodes: list
    members: list = field(default_factory=list)

def decode_unit(b: bytes) -> Unit:
    r = Reader(b)
    if r.u8() != PAYLOAD_FORMAT: raise ValueError("unknown payload format")
    form = r.u8()
    if form not in (0, 1, 2): raise ValueError(f"bad form {form}")
    refs = [r.uv() for _ in range(r.uv())]
    nodes = [read_node(r, i) for i in range(r.uv())]
    if form == 0:
        members = [{"kind": "thm", "nl": r.uv(), "type": r.uv(), "value": None, "all": []}]
    elif form == 1:
        members = [read_member(r)]
    else:
        n = r.uv()
        if n == 0: raise ValueError("empty block")
        members = [read_member(r) for _ in range(n)]
    if not r.done(): raise ValueError(f"{len(b) - r.p} trailing bytes")
    for m in members:
        for k in ("type", "value"):
            if m.get(k) is not None and m[k] >= len(nodes): raise ValueError("term index out of range")
    return Unit(form, refs, nodes, members)

# ── payload.md §5: ids from the node table (spec.md §7-§9) ───────────────

def level_enc(l) -> bytes:
    if l[0] == "zero": return u8(0x10)
    if l[0] == "succ": return u8(0x11) + level_enc(l[1])
    if l[0] == "max": return u8(0x12) + level_enc(l[1]) + level_enc(l[2])
    if l[0] == "imax": return u8(0x13) + level_enc(l[1]) + level_enc(l[2])
    s = f"u_{l[1]}".encode()                     # positional names, spec.md §5.1
    return u8(0x14) + u64(len(s)) + s

def make_renc(slot_ids: list, member_enc_mode, unresolved: set):
    """`member_enc_mode(i)` gives the spec reference for block member i:
    a 32-byte id, or an int (local index)."""
    def renc(ref) -> bytes:
        if ref[0] == "ref": return u8(0x31) + slot_ids[ref[1]]
        if ref[0] in ("member", "self"):
            m = member_enc_mode(ref[1] if ref[0] == "member" else 0)
            return u8(0x31) + m if isinstance(m, bytes) else u8(0x32) + u64(m)
        s = name_str(ref[1]).encode()
        unresolved.add(name_str(ref[1]))
        return u8(0x33) + u64(len(s)) + s
    return renc

TAG = {"bvar": 0x21, "sort": 0x24, "const": 0x25, "app": 0x26, "lam": 0x27,
       "forall": 0x28, "let": 0x29, "litnat": 0x2A, "litstr": 0x2B, "proj": 0x2C}

def node_ids(nodes: list, renc) -> list:
    """Each node's ⟦·⟧, children first: flat form for depth ≤ 6, Merkle above."""
    depth, flat, ids = [0] * len(nodes), [None] * len(nodes), [None] * len(nodes)
    for i, n in enumerate(nodes):
        k = n[0]; t = u8(TAG[k])
        if k == "bvar": scal, kids = u64(n[1]), []
        elif k == "sort": scal, kids = level_enc(n[1]), []
        elif k == "const": scal, kids = renc(n[1]) + u64(len(n[2])) + b"".join(level_enc(l) for l in n[2]), []
        elif k == "app": scal, kids = b"", [n[1], n[2]]
        elif k in ("lam", "forall"): scal, kids = u8(n[1]), [n[2], n[3]]
        elif k == "let": scal, kids = b"", [n[1], n[2], n[3]]
        elif k == "litnat": scal, kids = u64(len(n[1])) + n[1], []
        elif k == "litstr":
            s = n[1].encode(); scal, kids = u64(len(s)) + s, []
        else: scal, kids = renc(n[1]) + u64(n[2]), [n[3]]
        depth[i] = 1 + max(depth[c] for c in kids) if kids else 0
        if depth[i] <= 6:
            flat[i] = t + scal + b"".join(flat[c] for c in kids)
            ids[i] = H(u8(0x2F) + flat[i])
        else:
            ids[i] = H(t + scal + b"".join(ids[c] for c in kids))
    return ids

KIND_TAG = {"axiom": 1, "defn": 2, "thm": 3, "opaque": 4, "quot": 5, "induct": 6, "ctor": 7, "rec": 8}

def stmt_of(m, ids) -> bytes:
    return H(u8(0xA1) + u8(SCHEME) + u64(m["nl"]) + ids[m["type"]])

def tail_of(m, ids, renc) -> bytes:
    k = m["kind"]
    if k == "axiom": return u8(m["unsafe"])
    if k == "defn": return u8(m["safety"]) + ids[m["value"]]
    if k == "thm": return ids[m["value"]] if m["value"] is not None else b""
    if k == "opaque": return u8(m["unsafe"]) + ids[m["value"]]
    if k == "quot": return u8(m["quot"])
    if k == "induct":
        return (u64(m["np"]) + u64(m["ni"]) + u64(m["nn"]) + u8(m["rec"]) + u8(m["unsafe"])
                + u8(m["refl"]) + u64(len(m["ctors"])) + b"".join(renc(c) for c in m["ctors"]))
    if k == "ctor":
        return renc(m["induct"]) + u64(m["cidx"]) + u64(m["np"]) + u64(m["nf"]) + u8(m["unsafe"])
    b = (u64(m["np"]) + u64(m["ni"]) + u64(m["nmot"]) + u64(m["nmin"]) + u8(m["k"])
         + u8(m["unsafe"]) + u64(len(m["rules"])))
    for ctor, nf, rhs in m["rules"]:
        b += renc(ctor) + u64(nf) + ids[rhs]
    return b

def member_enc(m, ids, renc) -> bytes:
    return u8(KIND_TAG[m["kind"]]) + stmt_of(m, ids) + tail_of(m, ids, renc)

def unit_ids(u: Unit, file_refs: list):
    """(key, [(stmt, decl, ref)] per member, unresolved names)."""
    slot_ids = []
    for t in u.refs:
        if t >= len(file_refs): raise ValueError(f"file ref {t} out of range")
        slot_ids.append(file_refs[t])
    unresolved: set = set()
    if u.form == 0:
        ids = node_ids(u.nodes, make_renc(slot_ids, lambda i: 0, unresolved))
        s = stmt_of(u.members[0], ids)
        return s, [(s, s, s)], unresolved
    if u.form == 1:
        renc = make_renc(slot_ids, lambda i: 0, unresolved)
        ids = node_ids(u.nodes, renc)
        m = u.members[0]
        s = stmt_of(m, ids)
        d = H(u8(0xA2) + u8(SCHEME) + u8(KIND_TAG[m["kind"]]) + s + tail_of(m, ids, renc))
        return d, [(s, d, s if m["kind"] == "thm" else d)], unresolved
    # Block, spec.md §9.4: shapes (every member local 0), order, block id, members.
    anon = make_renc(slot_ids, lambda i: 0, unresolved)
    ids0 = node_ids(u.nodes, anon)
    shapes = [H(member_enc(m, ids0, anon)) for m in u.members]
    if any(shapes[i] > shapes[i + 1] for i in range(len(shapes) - 1)):
        raise ValueError("members are not in canonical (shape) order")
    local = make_renc(slot_ids, lambda i: i, unresolved)
    idsL = node_ids(u.nodes, local)
    block = H(u8(0xA3) + u8(SCHEME) + u64(len(u.members))
              + b"".join(member_enc(m, idsL, local) for m in u.members))
    mdecl = [H(u8(0xA4) + u8(SCHEME) + block + u64(i)) for i in range(len(u.members))]
    full = make_renc(slot_ids, lambda i: mdecl[i], unresolved)
    idsF = node_ids(u.nodes, full)
    out = []
    for i, m in enumerate(u.members):
        s = stmt_of(m, idsF)
        out.append((s, mdecl[i], s if m["kind"] == "thm" else mdecl[i]))
    return block, out, unresolved

# ── payload.md §4 decorations (parsed, not rebuilt) ──────────────────────

def decode_decoration(b: bytes) -> dict:
    r = Reader(b)
    if r.u8() != PAYLOAD_FORMAT: raise ValueError("unknown payload format")
    d = {"own": r.nm(), "member": r.uv()}
    d["refNames"] = [r.uv() for _ in range(r.uv())]
    d["levelParams"] = [r.nm() for _ in range(r.uv())]
    d["binders"] = [r.nm() for _ in range(r.uv())]
    h = r.u8()
    if h == 2: r.uv()
    elif h not in (0, 1, 0xFF): raise ValueError(f"bad hints {h}")
    if not r.done(): raise ValueError("trailing bytes")
    return d

# ── checking ─────────────────────────────────────────────────────────────

@dataclass
class Report:
    units: int = 0
    members: int = 0
    decorations: int = 0
    variants: int = 0
    inexact: int = 0
    faults: list = field(default_factory=list)

def check_node_file(path: str) -> Report:
    db = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    rep = Report()
    file_refs = [r for (r,) in db.execute("SELECT ref FROM refs ORDER BY ix")]
    names = [Reader(n).nm() for (n,) in db.execute("SELECT name FROM names ORDER BY ix")]
    units, ids_of_unit, keys = {}, {}, {}
    for uid, key, variant, form, bts in db.execute("SELECT id, key, variant, form, bytes FROM units"):
        rep.units += 1
        keys[key] = keys.get(key, 0) + 1
        k = b58(key)
        if hashlib.sha256(bts).digest() != variant:
            rep.faults.append(f"unit {k}: variant is not the digest of its bytes"); continue
        try:
            u = decode_unit(bts)
            if u.form != form: raise ValueError("form column disagrees with the bytes")
            got, ids, unres = unit_ids(u, file_refs)
        except ValueError as e:
            rep.faults.append(f"unit {k}: {e}"); continue
        if got != key:
            rep.faults.append(f"unit {k}: checks to {b58(got)}"); continue
        if unres: rep.inexact += 1
        units[uid], ids_of_unit[uid] = u, ids
    rep.variants = sum(1 for c in keys.values() if c > 1)
    decl_ids = {d: (s, r) for ids in ids_of_unit.values() for (s, d, r) in ids}
    for decl, name, uid, member in db.execute("SELECT decl, name, unit, member FROM members"):
        rep.members += 1
        nm = name_str(names[name]) if name < len(names) else f"#{name}"
        if uid not in ids_of_unit:
            rep.faults.append(f"member {nm}: its unit is missing or faulty"); continue
        ids = ids_of_unit[uid]
        if member >= len(ids) or ids[member][1] != decl:
            rep.faults.append(f"member {nm}: listed decl is not member {member}'s")
    member_unit = {(d, n): uid for d, n, uid in db.execute("SELECT decl, name, unit FROM members")}
    for decl, name, bts in db.execute("SELECT decl, name, bytes FROM decorations"):
        rep.decorations += 1
        nm = name_str(names[name]) if name < len(names) else f"#{name}"
        try:
            d = decode_decoration(bts)
            uid = member_unit.get((decl, name))
            if uid is None: raise ValueError("no member row")
            u = units.get(uid)
            if u is not None:
                if len(d["refNames"]) != len(u.refs): raise ValueError("does not name every reference slot")
                if any(i >= len(names) for i in d["refNames"]): raise ValueError("name out of range")
                if d["own"] != names[name]: raise ValueError("own name differs from the member's")
        except ValueError as e:
            rep.faults.append(f"decoration {nm}: {e}")
    for decl, stmt, ref in db.execute("SELECT decl, stmt, ref FROM declarations"):
        if decl_ids.get(decl) != (stmt, ref):
            rep.faults.append(f"declaration {b58(decl)}: stmt / ref disagree with its unit")
    for stmt, decl in db.execute("SELECT stmt, decl FROM witnesses"):
        if decl_ids.get(decl, (None,))[0] != stmt:
            rep.faults.append(f"witness {b58(decl)}: not a witness of {b58(stmt)}")
    for name, stmt in db.execute("SELECT name, stmt FROM entries"):
        if stmt not in keys:
            rep.faults.append(f"entry {name_str(names[name])}: no statement unit")
    return rep

def check_statements_json(path: str) -> Report:
    j = json.loads(Path(path).read_text())
    rep = Report()
    file_refs = [b58_decode(r) for r in j["refs"]]
    for st in j["statements"]:
        rep.units += 1
        try:
            u = decode_unit(base64.b64decode(st["unit"], validate=True))
            if u.form != 0: raise ValueError("not a statement unit")
            got, _, unres = unit_ids(u, file_refs)
            decode_decoration(base64.b64decode(st["decoration"], validate=True))
            rep.decorations += 1
        except ValueError as e:
            rep.faults.append(f"{st.get('name')}: {e}"); continue
        if b58(got) != st["stmt"]:
            rep.faults.append(f"{st.get('name')}: checks to {b58(got)}, listed as {st['stmt']}")
        if unres: rep.inexact += 1
    return rep

ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

def b58_decode(s: str) -> bytes:
    n = 0
    for c in s: n = n * 58 + ALPHABET.index(c)
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    return b"\x00" * (len(s) - len(s.lstrip("1"))) + body

# ── payload.md §9 test vectors ───────────────────────────────────────────

def vectors() -> bool:
    """Decode the units of payload.md §9 and reproduce spec.md §12's ids from them."""
    text = (Path(__file__).resolve().parent.parent / "docs" / "payload.md").read_text()
    sec = text.split("## 9. Test vectors", 1)[1]
    blocks = [b.split("```", 1)[0] for b in sec.split("```text")[1:]]
    ok = True
    for blk in blocks:
        fields = {}
        for line in blk.strip().splitlines():
            k, _, v = line.partition(":")
            fields[k.strip()] = v.strip()
        refs = [b58_decode(r) for r in fields.get("refs", "").split()]
        u = decode_unit(bytes.fromhex(fields["unit"]))
        key, ids, _ = unit_ids(u, refs)
        want = fields["expect"].split()
        got = [b58(key)] + [b58(ids[int(i)][int(j)]) for i, j in
                            (x.split(",") for x in fields.get("members", "").split())]
        good = got == want
        ok &= good
        print(f"  {'ok  ' if good else 'FAIL'} {fields['name']}: {' '.join(got)}")
        if not good: print(f"       expected {' '.join(want)}")
    return ok

def main(argv: list) -> int:
    if not argv:
        print(__doc__); return 2
    if argv[0] == "--vectors":
        ok = vectors()
        print("all vectors reproduced" if ok else "vectors FAILED")
        return 0 if ok else 1
    path = argv[0]
    rep = check_statements_json(path) if path.endswith(".json") else check_node_file(path)
    print(f"{path}: {rep.units} units, {rep.members} members, {rep.decorations} decorations; "
          f"naming variants {rep.variants}; inexact units {rep.inexact}")
    if rep.faults:
        print(f"  {len(rep.faults)} FAULTS:")
        for f in rep.faults[:50]: print(f"    {f}")
        return 1
    print("  no faults: every unit's ids recomputed from its bytes")
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
