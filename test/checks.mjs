// Holds every check in LScript/Check.lean to the kind it is tagged with.
//
//   every check        a program in test/reject/ names it, so it can fire (test/run.sh checks the message)
//   load-bearing       LScript/Examples.lean shows what it prevents, and compile_sound fails to build
//                      without it
//   policy             compile_sound still builds without it: it rejects a program that says two
//                      things, not one that would go wrong
//   partial            the program names something that doesn't exist; nothing to remove
//
// A check is removed by making its condition false, or, for a check written as a match branch, by
// replacing its error with the `off:` expression its tag gives. The removal happens in a copy of the
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

const expects = readdirSync(join(repo, 'test/reject')).filter((f) => f.endsWith('.ls'))
  .map((f) => ({ f, code: /^\/\/ expect: \[([\w-]+)\]/.exec(read(`test/reject/${f}`))?.[1] }));
for (const { f, code } of expects) if (code !== 'parse' && !names.includes(code)) fail(`test/reject/${f} expects [${code}], which no check reports`);
for (const t of tags) if (!expects.some((e) => e.code === t.name)) fail(`${t.name}: no program in test/reject/ is rejected by it`);

const shows = [...read('LScript/Examples.lean').matchAll(/-- shows: ([\w-]+)/g)].map((m) => m[1]);
for (const t of tags.filter((t) => t.kind === 'load-bearing')) if (!shows.includes(t.name)) fail(`${t.name} is load-bearing, and Examples.lean doesn't show what it prevents`);
for (const s of shows) if (!tags.some((t) => t.name === s && t.kind === 'load-bearing')) fail(`Examples.lean shows ${s}, which isn't a load-bearing check`);

const lake = process.env.LAKE ?? 'lake';
const work = mkdtempSync(join(tmpdir(), 'lscript-checks-'));
cpSync(repo, work, { recursive: true, filter: (src) => !src.includes(`${repo}.git`) });
const builds = (target) => spawnSync(lake, ['build', target], { cwd: work, stdio: 'pipe' }).status === 0;
if (!builds('LScript.Sound')) { console.log('FAIL the unchanged repository does not build'); process.exit(1); }

for (const t of tags.filter((t) => t.kind !== 'partial')) {
  const mutated = lines.slice();
  const before = mutated[t.i];
  mutated[t.i] = t.off ? before.replace(/\.error s!"[^"]*"/, t.off) : before.replace(/\bif (.*?) then \.error/, 'if false then .error');
  if (mutated[t.i] === before) { fail(`${t.name}: couldn't remove it`); continue; }
  writeFileSync(join(work, 'LScript/Check.lean'), mutated.join('\n'));
  if (!builds('LScript.Check')) { fail(`${t.name}: the checker doesn't compile without it`); continue; }
  const proved = builds('LScript.Sound');
  if (t.kind === 'load-bearing' && proved) fail(`${t.name} is tagged load-bearing, and compile_sound builds without it`);
  else if (t.kind === 'policy' && !proved) fail(`${t.name} is tagged policy, and compile_sound needs it`);
  else console.log(`ok   ${t.name.padEnd(22)} ${t.kind.padEnd(13)} compile_sound ${proved ? 'builds' : 'fails'} without it`);
}
writeFileSync(join(work, 'LScript/Check.lean'), lines.join('\n'));
for (const t of tags.filter((t) => t.kind === 'partial')) console.log(`ok   ${t.name.padEnd(22)} partial       tested`);
console.log(failed ? `${failed} check(s) don't match their tags` : `all ${tags.length} checks match their tags`);
process.exit(failed ? 1 : 0);
