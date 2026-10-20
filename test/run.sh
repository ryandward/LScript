#!/usr/bin/env bash
# Builds the compiler, then: every program in accept/ compiles to its .expected text, runs in Node, holds
# what it declares, and has a certificate Lean's kernel accepts; a certificate with one byte of its
# output changed is refused; every program in reject/ is refused for the reason its first line names;
# and the JavaScript model agrees with Node.
set -u
cd "$(dirname "$0")/.."
LAKE=${LAKE:-lake}
"$LAKE" build >/dev/null || { echo "build failed"; exit 2; }
bin=.lake/build/bin/lscript
fail=0
for f in test/accept/*.ls; do
  if ! out=$("$bin" "$f"); then echo "REJECTED $f"; fail=1; continue; fi
  if ! diff -q "$out" "${f%.ls}.expected" >/dev/null; then echo "EMITTED DIFFERENTLY $f"; diff "$out" "${f%.ls}.expected"; fail=1; continue; fi
  if ! node test/values.mjs "$f" "$out"; then echo "WRONG VALUES $f"; fail=1; continue; fi
  "$bin" --certificate "$f" >/dev/null
  cert="${f%.ls}.cert.lean"
  if ! checked=$("$LAKE" env lean "$cert" 2>&1) || ! grep -qxF "'sound' depends on axioms: [propext, Quot.sound]" <<<"$checked"; then
    echo "CERTIFICATE REFUSED $cert"; fail=1; continue
  fi
  echo "ok   $f (certificate checked)"
done
first=$(ls test/accept/*.cert.lean | head -1)
tampered=$(mktemp --suffix=.cert.lean)
sed '/^def output/s/export const/export  const/' "$first" > "$tampered"
if "$LAKE" env lean "$tampered" >/dev/null 2>&1; then echo "TAMPERED CERTIFICATE ACCEPTED $first"; fail=1; else echo "ok   a certificate with its output changed is refused"; fi
rm -f "$tampered"
for f in test/reject/*.ls; do
  want=$(head -1 "$f" | sed 's|^// expect: ||')
  if msg=$("$bin" "$f" 2>&1); then echo "ACCEPTED $f"; fail=1; continue; fi
  if ! grep -qF -- "$want" <<<"$msg"; then echo "WRONG REASON $f: $msg"; fail=1; continue; fi
  echo "ok   $f: $want"
done
node test/v8.mjs >/dev/null || { echo "the JavaScript model disagrees with Node: run node test/v8.mjs"; fail=1; }
[ $fail = 0 ] && echo "all passed"
exit $fail
