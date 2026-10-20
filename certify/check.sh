#!/usr/bin/env bash
# Has Lean's kernel check one compiled program: F.ls and the F.mjs beside it, read from disk. Exits 0
# only if the proved parser and compiler, run on F.ls, give exactly F.mjs, and the proof rests on Lean's
# standard axioms alone. It rebuilds the LScript library from this checkout's sources first, and prints
# the commit it checked against. Run with LAKE=/path/to/lake if lake isn't on the PATH.
set -u
[ $# = 1 ] || { echo "usage: certify/check.sh F.ls"; exit 2; }
arg=$1
case "$arg" in *.ls) ;; *) echo "$arg isn't a .ls file"; exit 2 ;; esac
# The compiler writes F.mjs beside the path it was given, so the output is found from that path, and
# only then are both resolved.
given_out="${arg%.ls}.mjs"
[ -f "$arg" ] || { echo "no $arg"; exit 2; }
[ -f "$given_out" ] || { echo "no $given_out: compile $arg first"; exit 2; }
src=$(realpath "$arg"); out=$(realpath "$given_out")
lake=${LAKE:-lake}
cd "$(dirname "$0")/.."
against=$(git rev-parse HEAD 2>/dev/null || echo "this checkout, which isn't a git repository")
if git rev-parse HEAD >/dev/null 2>&1 && [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  against="$against with uncommitted changes"
fi
"$lake" build LScript >/dev/null 2>&1 || { echo "the LScript library at $against doesn't build"; exit 1; }
LSCRIPT_SOURCE="$src" LSCRIPT_OUTPUT="$out" "$lake" env lean certify/Check.lean || exit 1
echo "checked against $against"
