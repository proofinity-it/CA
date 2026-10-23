#!/usr/bin/env bash
# Measurements for docs/plan.md item 4, over Init (the library every toolchain ships).
#
#   tools/measure.sh A            # full-mode versus statement-mode ids, one toolchain
#   tools/measure.sh B OLD NEW    # stmt / type_hash survival across a toolchain bump:
#                                 # OLD and NEW are node files of Init packed on two toolchains
#                                 # (lake env ca pack -m Init --all -o init-<version>.sqlite under each)
#
# Needs the CLI built (cd cli && lake build). Writes nothing outside $OUT.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ca="$here/../cli/.lake/build/bin/ca"
OUT="${OUT:-/tmp/ca-measure}"; mkdir -p "$OUT"
case "${1:-}" in
  A)
    cd "$here/../cli"
    for mode in full stmt; do
      flag=""; [ $mode = stmt ] && flag=--no-proofs
      /usr/bin/time -f "$mode: %e s, %M KB" lake env "$ca" pack -m Init --all $flag --fast -o "$OUT/init-$mode.sqlite" 2>&1 | grep -E 'Wrote|: [0-9.]+ s'
    done
    "$ca" migrate "$OUT/init-full.sqlite" "$OUT/init-stmt.sqlite" ;;
  B)
    "$ca" migrate "$2" "$3" ;;
  *) sed -n 2,12p "$0"; exit 2 ;;
esac
