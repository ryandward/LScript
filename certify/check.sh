#!/usr/bin/env bash
# Has Lean's kernel check one compiled program: F.ls and the F.mjs beside it, read from disk. Exits 0
# only if the proved parser and compiler, run on F.ls, give exactly F.mjs, and the proof rests on Lean's
# standard axioms alone. Run with LAKE=/path/to/lake if lake isn't on the PATH.
set -u
[ $# = 1 ] || { echo "usage: certify/check.sh F.ls"; exit 2; }
src=$(realpath "$1"); out="${src%.ls}.mjs"
[ -f "$out" ] || { echo "no $out beside $src: compile it first"; exit 2; }
cd "$(dirname "$0")/.."
LSCRIPT_SOURCE="$src" LSCRIPT_OUTPUT="$out" "${LAKE:-lake}" env lean certify/Check.lean
