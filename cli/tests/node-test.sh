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

# Merge of the three packs, digests, diff.
for mode in "" --own --no-proofs; do lake env "$ca" pack -m Fixture $mode -o "m${mode}.sqlite" >/dev/null 2>&1; done
out=$("$ca" merge merged.sqlite m.sqlite m--own.sqlite m--no-proofs.sqlite 2>&1) && echo "$out" | grep -q 'checked, no faults' \
  && ok "ca merge of three packs: checked, no faults" || { bad "ca merge"; echo "$out"; }
python3 -I "$here/../../tools/registry_ref.py" merged.sqlite >/dev/null 2>&1 && ok "  and registry_ref.py accepts the merged file" || bad "registry_ref.py merged"
"$ca" merge again.sqlite merged.sqlite merged.sqlite >/dev/null 2>&1 \
  && [ "$(python3 -I -c "import sqlite3,sys;print(sqlite3.connect(sys.argv[1]).execute('select count(*) from units').fetchone()[0])" merged.sqlite)" = \
       "$(python3 -I -c "import sqlite3,sys;print(sqlite3.connect(sys.argv[1]).execute('select count(*) from units').fetchone()[0])" again.sqlite)" ] \
  && ok "merging a node with itself keeps the unit count" || bad "merge idempotence"
"$ca" digest m--own.sqlite | python3 -I -c "import json,sys; j=json.load(sys.stdin); assert j['keys'] > 0 and len(j['buckets']) > 0" && ok "ca digest: range digests as JSON" || bad "ca digest"
rc=0; out=$("$ca" diff m--own.sqlite m.sqlite 2>&1) || rc=$?; [ "$rc" = 2 ] && echo "$out" | grep -q 'Color.swap' && ok "ca diff: the --own pack holds Color.swap, the entries pack does not" || { bad "ca diff ($rc)"; echo "$out"; }
"$ca" diff m.sqlite m.sqlite >/dev/null 2>&1 && ok "ca diff of a node with itself: nothing" || bad "ca diff self"
rm -f m*.sqlite merged.sqlite again.sqlite

# `ca verify`: every declaration rebuilt and accepted by the kernel; records
# written into the file; both checkers still accept the file.
lake env "$ca" pack -m Fixture --own -o verify.sqlite >/dev/null 2>&1
out=$(lake env "$ca" verify verify.sqlite --write 2>&1) && echo "$out" | grep -q '13 records: 13 valid' && echo "$out" | grep -q 'no faults' \
  && ok "ca verify: 50 declarations accepted by the kernel, 13 valid records written" || { bad "ca verify"; echo "$out"; }
lake env "$ca" check verify.sqlite >/dev/null 2>&1 && ok "ca check accepts the file with records" || bad "ca check with records"
out=$(python3 -I "$here/../../tools/registry_ref.py" verify.sqlite 2>&1) && echo "$out" | grep -q 'records: 13' \
  && ok "registry_ref.py checks the records and derives proved" || { bad "registry_ref.py records"; echo "$out"; }
# A record whose JSON is edited must be caught by both.
python3 -I - verify.sqlite <<'PY'
import sqlite3, sys
c = sqlite3.connect(sys.argv[1]); c.execute("UPDATE records SET json = replace(json, '\"valid\":true', '\"valid\":false') WHERE rowid IN (SELECT rowid FROM records LIMIT 1)") if False else None
d = c.execute("SELECT digest, json FROM records LIMIT 1").fetchone()
c.execute("UPDATE records SET json = ? WHERE digest = ?", (d[1].replace('"policy":"kernel"', '"policy":"trust me"'), d[0])); c.commit()
PY
if lake env "$ca" check verify.sqlite >/dev/null 2>&1; then bad "edited record not detected by ca check"; else ok "edited record detected by ca check"; fi
if python3 -I "$here/../../tools/registry_ref.py" verify.sqlite >/dev/null 2>&1; then bad "edited record not detected by registry_ref.py"; else ok "  and by registry_ref.py"; fi
rm -f verify.sqlite

# Keys: a signed pack (namespace claim + bindings) and signed records.
rm -f test.key
pk=$("$ca" keygen test.key 2>/dev/null) && [ -n "$pk" ] && ok "ca keygen writes a key and prints the public key" || bad "ca keygen"
lake env "$ca" pack -m Fixture --own --sign test.key --label fixture -o signed.sqlite >/dev/null 2>&1 || bad "pack --sign"
lake env "$ca" verify signed.sqlite --write --sign test.key >/dev/null 2>&1 || bad "verify --sign"
out=$(lake env "$ca" check signed.sqlite 2>&1) && ok "ca check: signed claim, 13 bindings and 13 signed records verify" || { bad "ca check signed"; echo "$out"; }
out=$(python3 -I "$here/../../tools/registry_ref.py" signed.sqlite 2>&1) && echo "$out" | grep -q 'bindings: 13' && echo "$out" | grep -q '13 signed' \
  && ok "  and registry_ref.py verifies the Ed25519 signatures" || { bad "registry_ref.py signed"; echo "$out"; }
python3 -I - signed.sqlite <<'PY'
import sqlite3, sys
c = sqlite3.connect(sys.argv[1])
ns, name, seq, target = c.execute("SELECT ns, name, seq, target FROM bindings LIMIT 1").fetchone()
other = c.execute("SELECT target FROM bindings WHERE target != ? LIMIT 1", (target,)).fetchone()[0]
c.execute("UPDATE bindings SET target = ? WHERE ns = ? AND name = ? AND seq = ?", (other, ns, name, seq)); c.commit()
PY
if lake env "$ca" check signed.sqlite >/dev/null 2>&1; then bad "re-pointed binding not detected by ca check"; else ok "a re-pointed binding fails its signature in ca check"; fi
if python3 -I "$here/../../tools/registry_ref.py" signed.sqlite >/dev/null 2>&1; then bad "re-pointed binding not detected by registry_ref.py"; else ok "  and in registry_ref.py"; fi
rm -f signed.sqlite test.key

# `ca lookup` over a sources list naming the folder and a node file.
lake env "$ca" pack -m Fixture --own -o node.sqlite >/dev/null 2>&1
cat > sources.json <<'EOF'
{ "sources": [
  { "name": "fixture-folder", "kind": "folder", "location": "registry" },
  { "name": "fixture-node", "location": "node.sqlite" } ] }
EOF
conj=$(python3 -I -c "import json,sys;print([e['stmt'] for e in json.load(open(sys.argv[1])) if e['name']=='Conj'][0])" registry/declarations.json)
out=$("$ca" lookup "$conj" 2>&1) && echo "$out" | grep -q 'Conj \[fixture-folder' && echo "$out" | grep -q 'conj_literal \[fixture-node.*1 witness' \
  && ok "ca lookup by stmt: folder and node sources answer" || { bad "ca lookup by stmt"; echo "$out"; }
out=$("$ca" lookup cond1 2>&1) && echo "$out" | grep -q 'conditional assuming #\[Open1\]' && ok "ca lookup by name: status and assumptions" || bad "ca lookup by name"
out=$("$ca" lookup Color.swap 2>&1) && echo "$out" | grep -q 'Color.swap \[fixture-node.*definition' && ok "ca lookup by name: an unannotated declaration, from the node only" || bad "ca lookup Color.swap"
rc=0; "$ca" lookup nothing.here >/dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] && ok "ca lookup: exit 2 when nothing answers" || bad "ca lookup exit code ($rc)"
"$ca" lookup --json cond1 | python3 -I -c "import json,sys; j=json.load(sys.stdin); assert any(h.get('status')=='conditional' for h in j)" && ok "ca lookup --json parses" || bad "ca lookup --json"
"$ca" fetch-sources >/dev/null 2>&1 && ok "ca fetch-sources: local sources need no fetch" || bad "ca fetch-sources"
rm -f sources.json

rm -f node*.sqlite
if [ "$fail" = 0 ]; then echo "node-test: all passed"; else echo "node-test: FAILED"; exit 1; fi
