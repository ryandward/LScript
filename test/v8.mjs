// Checks LScript/JS.lean's model of the emitted module against Node. Exits 1 on any disagreement.
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const dir = mkdtempSync(join(tmpdir(), 'lscript-v8-'));
let n = 0;
// What V8 does with a module: 'ok', or the name of the error it throws, and when (parse or run).
const outcome = (source) => {
  const file = join(dir, `m${n++}.mjs`);
  writeFileSync(file, source);
  try { execFileSync(process.execPath, ['--check', file], { stdio: 'pipe' }); }
  catch (e) { return `parse ${/(\w+Error)/.exec(String(e.stderr))?.[1]}`; }
  try { execFileSync(process.execPath, [file], { stdio: 'pipe' }); return 'ok'; }
  catch (e) { return `run ${/(\w+Error)/.exec(String(e.stderr))?.[1]}`; }
};
let failed = 0;
const expect = (label, got, want) => {
  const ok = got === want;
  if (!ok) failed++;
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${label.padEnd(58)} ${got}${ok ? '' : ` (the model says ${want})`}`);
};

const lean = readFileSync(new URL('../LScript/JS.lean', import.meta.url), 'utf8');
const reserved = JSON.parse(/def reservedWords : List String :=\s*(\[[^\]]*\])/.exec(lean)[1]);
for (const w of reserved) expect(`export const ${w} = 1;`, outcome(`export const ${w} = 1;\n`), 'parse SyntaxError');
for (const w of ['undefined', 'NaN', 'Infinity', 'async', 'of', 'get', 'set', 'from', 'as', 'console', 'Int', 'type']) {
  expect(`export const ${w} = 1; (not reserved)`, outcome(`export const ${w} = 1;\n`), 'ok');
}
expect('a name read before its line', outcome('export const a = b;\nexport const b = 1;\n'), 'run ReferenceError');
expect('a name read on its own line', outcome('export const a = a;\n'), 'run ReferenceError');
expect('a name never declared', outcome('export const a = b;\n'), 'run ReferenceError');
expect('a name declared twice', outcome('export const a = 1;\nexport const a = 2;\n'), 'parse SyntaxError');

const exact = (text) => String(Number(text)) === text;
expect('9007199254740991 is held exactly', String(exact('9007199254740991')), 'true');
expect('-9007199254740991 is held exactly', String(exact('-9007199254740991')), 'true');
expect('9007199254740993 is not', String(exact('9007199254740993')), 'false');

const printable = Array.from({ length: 95 }, (_, i) => String.fromCharCode(32 + i)).filter((c) => c !== '"' && c !== '\\').join('');
const file = join(dir, 'strings.mjs');
writeFileSync(file, `export const s = "${printable}";\n`);
const { s } = await import(file);
expect('every printable ASCII but " and \\ prints as itself', String(s === printable), 'true');

console.log(failed ? `${failed} disagreement(s) with the model` : 'the model agrees with Node');
process.exit(failed ? 1 : 0);
