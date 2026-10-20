#!/usr/bin/env bash
# Builds the compiler, then: every program in accept/ compiles to its .expected text, runs in Node, holds
# what it declares, and passes certify/check.sh, which has Lean's kernel check the run from the files on
# disk; the check refuses a compiled file with a line appended, a source with a byte changed, and a
# symlinked source whose output beside the link differs from the one beside its target; every
# program in reject/ is refused for the reason its first line names; and the JavaScript model agrees
# with Node.
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
  if ! LAKE="$LAKE" certify/check.sh "$f" >/dev/null 2>&1; then echo "CHECK REFUSED $f"; fail=1; continue; fi
  echo "ok   $f (checked by Lean's kernel)"
done
w=$(mktemp -d)
cp test/accept/age.ls test/accept/age.mjs "$w/"
echo 'throw new TypeError("not what the check read");' >> "$w/age.mjs"
if LAKE="$LAKE" certify/check.sh "$w/age.ls" >/dev/null 2>&1; then echo "CHECK ACCEPTED an appended line"; fail=1; else echo "ok   the check refuses a compiled file with a line appended"; fi
cp test/accept/age.mjs "$w/"; sed -i 's/= 10/= 11/' "$w/age.ls"
if LAKE="$LAKE" certify/check.sh "$w/age.ls" >/dev/null 2>&1; then echo "CHECK ACCEPTED a changed source"; fail=1; else echo "ok   the check refuses a source with a byte changed"; fi
mkdir "$w/lib" "$w/app"
cp test/accept/age.ls test/accept/age.mjs "$w/lib/"
ln -s "$w/lib/age.ls" "$w/app/age.ls"
{ cat test/accept/age.mjs; echo 'globalThis.injected = true;'; } > "$w/app/age.mjs"
if LAKE="$LAKE" certify/check.sh "$w/app/age.ls" >/dev/null 2>&1; then echo "CHECK ACCEPTED the output beside a symlink's target"; fail=1; else echo "ok   the check reads the output beside the path it was given"; fi
rm -rf "$w"
for f in test/reject/*.ls; do
  want=$(head -1 "$f" | sed 's|^// expect: ||')
  if msg=$("$bin" "$f" 2>&1); then echo "ACCEPTED $f"; fail=1; continue; fi
  if ! grep -qF -- "$want" <<<"$msg"; then echo "WRONG REASON $f: $msg"; fail=1; continue; fi
  echo "ok   $f: $want"
done
node test/v8.mjs >/dev/null || { echo "the JavaScript model disagrees with Node: run node test/v8.mjs"; fail=1; }
[ $fail = 0 ] && echo "all passed"
exit $fail
