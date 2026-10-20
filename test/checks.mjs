// Holds every check in LScript/Check.lean to the kind it is tagged with.
//
//   every check     a program in test/reject/ names it, so it can fire (test/run.sh checks the message)
//   load-bearing    LScript/Counterexamples.lean has a program for it. With the check removed, Lean
//                   proves by `decide` that the compiler accepts the program and its output goes wrong,
//                   so compile_sound is false for that compiler. In the real build the same proof must
//                   fail: the program is wrong only without its check.
//   policy          with the check removed, compile_sound still builds: the theorem holds without it
//   partial         only a `none` arm may be partial: the program names something that doesn't exist,
//                   and there is nothing to continue with
//
// A check is removed by making its condition false, or, for a check written as a match arm, by
// replacing its error with the `off:` expression its tag gives. Removal happens in a copy of the
// repository, one check at a time. Run with LAKE=/path/to/lake if lake isn't on the PATH.
import { spawnSync } from 'node:child_process';
import { cpSync, mkdtempSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const repo = new URL('..', import.meta.url).pathname;
const read = (f) => readFileSync(join(repo, f), 'utf8');
const lines = read('LScript/Check.lean').split('\n');
const tags = lines.flatMap((l, i) => {
  const m = /-- check: ([\w-]+) \((load-bearing|policy|partial)\)(?: off: (.*))?$/.exec(l);
  return m ? [{ name: m[1], kind: m[2], i, off: m[3] }] : [];
});
let failed = 0;
const fail = (msg) => { failed++; console.log(`FAIL ${msg}`); };

const names = tags.map((t) => t.name);
for (const n of names.filter((n, i) => names.indexOf(n) !== i)) fail(`${n} tags two checks`);
for (const t of tags.filter((t) => t.kind === 'partial')) {
  if (!/^\s*\| none =>/.test(lines[t.i])) fail(`${t.name} is tagged partial, and isn't a none arm`);
}

const expects = readdirSync(join(repo, 'test/reject')).filter((f) => f.endsWith('.ls'))
  .map((f) => ({ f, code: /^\/\/ expect: \[([\w-]+)\]/.exec(read(`test/reject/${f}`))?.[1] }));
for (const { f, code } of expects) if (code !== 'parse' && !names.includes(code)) fail(`test/reject/${f} expects [${code}], which no check reports`);
for (const t of tags) if (!expects.some((e) => e.code === t.name)) fail(`${t.name}: no program in test/reject/ is rejected by it`);

const cexSource = read('LScript/Counterexamples.lean');
const registry = [...cexSource.slice(cexSource.indexOf('def counterexamples')).matchAll(/\("([\w-]+)", \[/g)].map((m) => m[1]);
const loadBearing = tags.filter((t) => t.kind === 'load-bearing');
for (const t of loadBearing) if (!registry.includes(t.name)) fail(`${t.name} is load-bearing, and Counterexamples.lean has no program for it`);
for (const n of registry) if (!loadBearing.some((t) => t.name === n)) fail(`Counterexamples.lean has a program for ${n}, which isn't a load-bearing check`);

const lake = process.env.LAKE ?? 'lake';
const work = mkdtempSync(join(tmpdir(), 'lscript-checks-'));
cpSync(repo, work, { recursive: true, filter: (src) => !src.includes(`${repo}.git`) });
const run = (args) => spawnSync(lake, args, { cwd: work, stdio: 'pipe' }).status === 0;
const builds = (target) => run(['build', target]);
const refutes = (name) => {
  writeFileSync(join(work, 'Refute.lean'), `import LScript.Counterexamples
open LScript
theorem refuted : ¬ ∀ {p : Program} {out : JS.Program}, compile p = .ok out → Conclusion p out :=
  wrong_refutes (p := counterexample "${name}") (by decide)
`);
  return run(['env', 'lean', 'Refute.lean']);
};
if (!builds('LScript.Sound') || !builds('LScript.Counterexamples')) { console.log('FAIL the unchanged repository does not build'); process.exit(1); }
for (const t of loadBearing) if (registry.includes(t.name) && refutes(t.name)) fail(`${t.name}: its program is wrong even with every check in place`);

for (const t of tags.filter((t) => t.kind !== 'partial')) {
  const mutated = lines.slice();
  const before = mutated[t.i];
  mutated[t.i] = t.off ? before.replace(/\.error s!"[^"]*"/, t.off) : before.replace(/\bif (.*?) then \.error/, 'if false then .error');
  if (mutated[t.i] === before) { fail(`${t.name}: couldn't remove it`); continue; }
  writeFileSync(join(work, 'LScript/Check.lean'), mutated.join('\n'));
  if (!builds('LScript.Check')) { fail(`${t.name}: the checker doesn't compile without it`); continue; }
  if (t.kind === 'load-bearing') {
    if (!builds('LScript.Counterexamples')) { fail(`${t.name}: Counterexamples.lean doesn't build without it`); continue; }
    if (refutes(t.name)) console.log(`ok   ${t.name.padEnd(22)} load-bearing  without it, its program is accepted and wrong: soundness is false`);
    else fail(`${t.name} is tagged load-bearing, and without it its program isn't both accepted and wrong`);
  } else {
    if (builds('LScript.Sound')) console.log(`ok   ${t.name.padEnd(22)} policy        without it, compile_sound still holds`);
    else fail(`${t.name} is tagged policy, and compile_sound fails without it`);
  }
}
writeFileSync(join(work, 'LScript/Check.lean'), lines.join('\n'));
for (const t of tags.filter((t) => t.kind === 'partial')) console.log(`ok   ${t.name.padEnd(22)} partial       a none arm, fired by a test`);
console.log(failed ? `${failed} check(s) don't match their tags` : `all ${tags.length} checks match their tags`);
process.exit(failed ? 1 : 0);
