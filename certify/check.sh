#!/usr/bin/env bash
# Has Lean's kernel check one compiled program: F.ls and the F.mjs beside it, read from disk. Exits 0
# only if the proved parser and compiler, run on F.ls, give exactly F.mjs, and the proof rests on Lean's
# standard axioms alone. It prints the commit the check was made against.
#
#   certify/check.sh F.ls           rebuilds this checkout's LScript library from its sources, then checks
#   certify/check.sh --fresh F.ls   builds the commit from a clean export, ignoring this checkout's build
#
# The check is against a commit, so it refuses a checkout with uncommitted changes to tracked files,
# unless LSCRIPT_ALLOW_DIRTY=1, and then it says so. Run with LAKE=/path/to/lake if lake isn't on the PATH.
set -u
fresh=0
if [ "${1:-}" = "--fresh" ]; then fresh=1; shift; fi
[ $# = 1 ] || { echo "usage: certify/check.sh [--fresh] F.ls"; exit 2; }
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
commit=$(git rev-parse HEAD 2>/dev/null) || { echo "$(pwd) isn't a git checkout, so there is no commit to check against"; exit 2; }
against=$commit
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  if [ "${LSCRIPT_ALLOW_DIRTY:-}" != 1 ]; then echo "refusing: this checkout has uncommitted changes, so it isn't $commit"; exit 2; fi
  [ $fresh = 1 ] || against="$commit with uncommitted changes"
fi
work=
if [ $fresh = 1 ]; then
  work=$(mktemp -d)
  git archive HEAD | tar -x -C "$work"
  cd "$work"
  against="$commit, built fresh"
fi
status=1
if ! "$lake" build LScript >/dev/null 2>&1; then
  echo "the LScript library at $against doesn't build"
elif LSCRIPT_SOURCE="$src" LSCRIPT_OUTPUT="$out" "$lake" env lean certify/Check.lean; then
  echo "checked against $against"
  status=0
fi
[ -n "$work" ] && rm -rf "$work"
exit $status
