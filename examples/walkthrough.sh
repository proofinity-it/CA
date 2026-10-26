#!/usr/bin/env bash
# The two example projects, end to end: publish a registry, consume it,
# then pack, check, verify, sign, merge and compare node files.
# Needs the CLI built (cd cli && lake build). Every command is printed
# before its output; CI runs this script.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ca="$here/../cli/.lake/build/bin/ca"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
step() { echo; echo "## $*"; }
run()  { echo "\$ $*"; "$@"; }

step "1. publish: lake build writes registry/ (open points, proved, conditional, definition, axiom)"
cd "$here/publish"; run lake build
run python3 -I -c "import json; [print(f\"{e['name']:14} {e['status']:12} {e['stmt'][:12]}…\") for e in json.load(open('registry/declarations.json'))]"
run python3 -I "$here/../tools/registry_ref.py" registry/statements.json

step "2. consume: sources.json names ../publish/registry; #ca_lookup and resolve% run during lake build"
cd "$here/consume"; run cat sources.json; run lake build

step "3. consume's registry: solves_open1 proves publish's Open1, so cond1 and uses_wrap are proved in the union"
run python3 -I -c "import json; [print(f\"{e['name']:14} {e['status']:12} proves={e.get('proves',[])} proved_by={e.get('proved_by',[])}\") for e in json.load(open('registry/declarations.json')) if e['name'] in ('Open1','solves_open1','cond1','uses_wrap')]"

step "4. node files: pack publish (its own declarations), check without trusting it, in Lean and in Python"
cd "$here/publish"
run lake env "$ca" pack -m Publish --own -o "$work/publish.sqlite"
run "$ca" check "$work/publish.sqlite"
run python3 -I "$here/../tools/registry_ref.py" "$work/publish.sqlite"

step "5. a key, and a signed pack: a namespace claim and one binding per entry"
run "$ca" keygen "$work/example.key"
run lake env "$ca" pack -m Publish --own --sign "$work/example.key" --label publish -o "$work/publish-signed.sqlite"
run "$ca" check "$work/publish-signed.sqlite"

step "6. the kernel's verdict: every declaration rebuilt and re-checked; a signed record per theorem, written into the file"
run lake env "$ca" verify "$work/publish-signed.sqlite" --write --sign "$work/example.key"
run python3 -I "$here/../tools/registry_ref.py" "$work/publish-signed.sqlite"

step "7. consume's node, merged with publish's: one file, ids unchanged, records and bindings carried, checked"
cd "$here/consume"
run lake env "$ca" pack -m Consume --own -o "$work/consume.sqlite"
run "$ca" merge "$work/union.sqlite" "$work/publish-signed.sqlite" "$work/consume.sqlite"
run python3 -I "$here/../tools/registry_ref.py" "$work/union.sqlite"

step "8. what one node holds that the other lacks, through range digests"
run "$ca" diff "$work/publish-signed.sqlite" "$work/consume.sqlite" || true

step "9. ask every source about a statement, a name, a coarse hash"
cat > "$work/sources.json" <<JSON
{ "sources": [
  { "name": "publish-folder", "kind": "folder", "location": "$here/publish/registry" },
  { "name": "union-node", "location": "$work/union.sqlite" } ] }
JSON
run "$ca" lookup --sources "$work/sources.json" ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn
run "$ca" lookup --sources "$work/sources.json" solves_open1
echo; echo "walkthrough: done"
