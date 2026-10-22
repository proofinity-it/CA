#!/usr/bin/env bash
# End-to-end test of `ca pack` / `ca check` (docs/payload.md, registry-protocol.md §12).
#
# Builds the fixture project (Init + CA only), packs it three ways, checks
# each node file, then tampers with a copy three ways and requires
# `ca check` to report each as a fault. Run from anywhere, after
# `lake build` in cli/.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ca="$here/../.lake/build/bin/ca"
cd "$here/fixture"
lake build >/dev/null
fail=0
ok()  { echo "  ok   $1"; }
bad() { echo "  FAIL $1"; fail=1; }

for mode in "" --own --no-proofs; do
  out="node${mode}.sqlite"
  lake env "$ca" pack -m Fixture $mode -o "$out" >/dev/null 2>&1 || { bad "pack $mode"; continue; }
  if lake env "$ca" check "$out" >/dev/null 2>&1; then ok "pack ${mode:-(entries)} + check: no faults"; else bad "check $mode"; fi
  # The independent Python checker (written from the documents) must agree.
  if python3 -I "$here/../../tools/registry_ref.py" "$out" >/dev/null 2>&1; then ok "  and tools/registry_ref.py agrees"; else bad "registry_ref.py $mode"; fi
done
if python3 -I "$here/../../tools/registry_ref.py" registry/statements.json >/dev/null 2>&1; then
  ok "registry/statements.json: tools/registry_ref.py agrees"; else bad "registry_ref.py statements.json"; fi

# Tampering: each copy must fail `ca check`.
tamper() {  # $1 label, $2 python statement over cursor c
  cp node.sqlite tampered.sqlite
  python3 -I - tampered.sqlite "$2" <<'PY'
import sqlite3, sys, hashlib
c = sqlite3.connect(sys.argv[1]); exec(sys.argv[2]); c.commit()
PY
  if lake env "$ca" check tampered.sqlite >/dev/null 2>&1; then bad "$1 not detected by ca check"; else ok "$1 detected"; fi
  if python3 -I "$here/../../tools/registry_ref.py" tampered.sqlite >/dev/null 2>&1; then bad "$1 not detected by registry_ref.py"; fi
  rm -f tampered.sqlite
}
# A unit whose last node payload byte changes, with its variant digest
# recomputed so only the content check can catch it.
tamper "changed unit bytes (variant recomputed)" '
row = c.execute("SELECT id, bytes FROM units WHERE form = 1 ORDER BY id LIMIT 1").fetchone()
b = bytearray(row[1]); b[-2] ^= 1
c.execute("UPDATE units SET bytes = ?, variant = ? WHERE id = ?", (bytes(b), hashlib.sha256(bytes(b)).digest(), row[0]))'
# A declaration row claiming another statement.
tamper "declaration row with a wrong stmt" '
d = c.execute("SELECT decl FROM declarations ORDER BY decl LIMIT 1").fetchone()[0]
c.execute("UPDATE declarations SET stmt = ? WHERE decl = ?", (b"\x00" * 32, d))'
# A ref table entry replaced: every unit citing it checks to another key.
tamper "replaced ref id" '
c.execute("UPDATE refs SET ref = ? WHERE ix = 0", (b"\x11" * 32,))'

rm -f node*.sqlite
if [ "$fail" = 0 ]; then echo "node-test: all passed"; else echo "node-test: FAILED"; exit 1; fi
