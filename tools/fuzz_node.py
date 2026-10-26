"""Fuzz the node-file checkers (docs/plan.md item 4).

Packs the example project `examples/publish`, then mutates copies of the node file:
random bytes flipped in units and decorations, rows re-pointed, ids
replaced, tables emptied. Every mutation must leave `ca check` and
`registry_ref.py` with a clean exit status of 0 (the mutation changed
nothing they check) or 1 (a fault reported); a crash (any other status, or
a traceback) is the failure this script hunts. Mutations that touch a
checked column must be reported by both.

    python3 -I tools/fuzz_node.py --ca cli/.lake/build/bin/ca [--rounds N] [--seed S]
"""
from __future__ import annotations

import argparse
import hashlib
import os
import random
import shutil
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REF = HERE / "registry_ref.py"

def run(cmd, cwd=None):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr

def pack(ca: Path, work: Path) -> Path:
    fixture = HERE.parent / "examples" / "publish"
    rc, out = run(["lake", "build"], cwd=fixture)
    if rc != 0: sys.exit(f"fixture build failed:\n{out}")
    node = work / "node.sqlite"
    rc, out = run(["lake", "env", str(ca.resolve()), "pack", "-m", "Publish", "--own", "-o", str(node)], cwd=fixture)
    if rc != 0: sys.exit(f"pack failed:\n{out}")
    return node

# ── mutations: (label, checked?, fn(cursor, rng)) ─────────────────────────
def flip_unit_byte(c, rng):
    uid, b = rng.choice(c.execute("SELECT id, bytes FROM units").fetchall())
    b = bytearray(b); i = rng.randrange(len(b)); b[i] ^= 1 << rng.randrange(8)
    c.execute("UPDATE units SET bytes = ? WHERE id = ?", (bytes(b), uid))

def flip_unit_byte_fix_variant(c, rng):
    uid, b = rng.choice(c.execute("SELECT id, bytes FROM units").fetchall())
    b = bytearray(b); i = rng.randrange(len(b)); b[i] ^= 1 << rng.randrange(8)
    c.execute("UPDATE units SET bytes = ?, variant = ? WHERE id = ?", (bytes(b), hashlib.sha256(bytes(b)).digest(), uid))

def truncate_unit(c, rng):
    uid, b = rng.choice(c.execute("SELECT id, bytes FROM units").fetchall())
    n = rng.randrange(len(b))
    c.execute("UPDATE units SET bytes = ?, variant = ? WHERE id = ?", (b[:n], hashlib.sha256(b[:n]).digest(), uid))

def flip_decoration_byte(c, rng):
    decl, name, b = rng.choice(c.execute("SELECT decl, name, bytes FROM decorations").fetchall())
    b = bytearray(b); i = rng.randrange(len(b)); b[i] ^= 1 << rng.randrange(8)
    c.execute("UPDATE decorations SET bytes = ? WHERE decl = ? AND name = ?", (bytes(b), decl, name))

def swap_ref(c, rng):
    rows = c.execute("SELECT ix, ref FROM refs").fetchall()
    (i, a), (j, b) = rng.sample(rows, 2)
    c.execute("UPDATE refs SET ref = ? WHERE ix = ?", (b, i)); c.execute("UPDATE refs SET ref = ? WHERE ix = ?", (a, j))

def random_ref(c, rng):
    ix = rng.choice(c.execute("SELECT ix FROM refs").fetchall())[0]
    c.execute("UPDATE refs SET ref = ? WHERE ix = ?", (os.urandom(32), ix))

def repoint_member(c, rng):
    decl, name = rng.choice(c.execute("SELECT decl, name FROM members").fetchall())
    c.execute("UPDATE members SET member = member + 1 WHERE decl = ? AND name = ?", (decl, name))

def wrong_stmt(c, rng):
    d = rng.choice(c.execute("SELECT decl FROM declarations").fetchall())[0]
    c.execute("UPDATE declarations SET stmt = ? WHERE decl = ?", (os.urandom(32), d))

def wrong_witness(c, rng):
    s, d = rng.choice(c.execute("SELECT stmt, decl FROM witnesses").fetchall())
    c.execute("UPDATE witnesses SET stmt = ? WHERE decl = ?", (os.urandom(32), d))

def wrong_dep(c, rng):
    d, r = rng.choice(c.execute("SELECT decl, ref FROM deps").fetchall())
    c.execute("UPDATE deps SET ref = ? WHERE decl = ? AND ref = ?", (os.urandom(32), d, r))

def entry_without_statement(c, rng):
    n, s = rng.choice(c.execute("SELECT name, stmt FROM entries").fetchall())
    c.execute("UPDATE entries SET stmt = ? WHERE name = ? AND stmt = ?", (os.urandom(32), n, s))

def garbage_name(c, rng):
    ix = rng.choice(c.execute("SELECT ix FROM names").fetchall())[0]
    c.execute("UPDATE names SET name = ? WHERE ix = ?", (os.urandom(rng.randrange(1, 6)), ix))

def drop_rows(c, rng):
    table = rng.choice(["members", "decorations", "declarations", "witnesses", "deps", "refs", "names"])
    c.execute(f"DELETE FROM {table} WHERE rowid IN (SELECT rowid FROM {table} ORDER BY RANDOM() LIMIT 3)") \
        if table not in ("members", "declarations", "witnesses", "deps") else \
        c.execute(f"DELETE FROM {table} WHERE (SELECT COUNT(*) FROM {table}) > 0 AND decl IN (SELECT decl FROM {table} ORDER BY RANDOM() LIMIT 1)")

def empty_table(c, rng):
    table = rng.choice(["units", "members", "decorations", "declarations", "witnesses", "deps", "entries", "refs"])
    c.execute(f"DELETE FROM {table}")

def bad_form(c, rng):
    uid = rng.choice(c.execute("SELECT id FROM units").fetchall())[0]
    c.execute("UPDATE units SET form = ? WHERE id = ?", (rng.choice([3, 7, 255, -1]), uid))

MUTATIONS = [
    ("flip a unit byte", True, flip_unit_byte),
    ("flip a unit byte, variant recomputed", True, flip_unit_byte_fix_variant),
    ("truncate a unit", True, truncate_unit),
    ("flip a decoration byte", False, flip_decoration_byte),   # may hit an unchecked name byte
    ("swap two refs", True, swap_ref),
    ("random ref", True, random_ref),
    ("re-point a member", True, repoint_member),
    ("wrong stmt on a declaration", True, wrong_stmt),
    ("wrong stmt on a witness", True, wrong_witness),
    ("wrong dep", True, wrong_dep),
    ("entry without statement unit", True, entry_without_statement),
    ("garbage name bytes", False, garbage_name),
    ("drop rows", False, drop_rows),
    ("empty a table", False, empty_table),
    ("bad form", True, bad_form),
]

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ca", required=True)
    ap.add_argument("--rounds", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    ca = Path(a.ca)
    work = Path(tempfile.mkdtemp(prefix="ca-fuzz-"))
    node = pack(ca, work)
    crashes, missed, reported, clean = [], [], 0, 0
    for i in range(a.rounds):
        label, checked, fn = rng.choice(MUTATIONS)
        path = work / f"m{i}.sqlite"
        shutil.copy(node, path)
        c = sqlite3.connect(path)
        try:
            fn(c, rng); c.commit()
        except (sqlite3.Error, ValueError, IndexError):
            c.close(); path.unlink(); continue
        c.close()
        rc1, out1 = run([str(ca), "check", str(path)])
        rc2, out2 = run([sys.executable, "-I", str(REF), str(path)])
        for who, rc, out in (("ca check", rc1, out1), ("registry_ref.py", rc2, out2)):
            if rc not in (0, 1) or "Traceback" in out or "PANIC" in out or "INTERNAL" in out:
                crashes.append((i, label, who, rc, out[-400:]))
        if checked and (rc1 != 1 or rc2 != 1):
            missed.append((i, label, rc1, rc2))
        if rc1 == 1 or rc2 == 1: reported += 1
        else: clean += 1
        path.unlink()
    shutil.rmtree(work, ignore_errors=True)
    print(f"fuzz: {a.rounds} mutations; {reported} reported as faults, {clean} left the checked content intact; "
          f"{len(crashes)} crashes, {len(missed)} checked mutations missed")
    for c in crashes[:10]: print("  CRASH", c)
    for m in missed[:10]: print("  MISSED", m)
    return 1 if crashes or missed else 0

if __name__ == "__main__":
    sys.exit(main())
