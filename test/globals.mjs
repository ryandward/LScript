// The globals the printed JavaScript reads must be exactly the ones LScript/JS.lean lists in
// emittedGlobals, which the model refuses to let a module bind: a global missing from the list could be
// shadowed by a module constant, and one listed but never read refuses a name for nothing. Scans the
// compiled text of every program in test/accept/, which between them use every form the printer has.
import { readFileSync, readdirSync } from 'node:fs';

const lean = readFileSync(new URL('../LScript/JS.lean', import.meta.url), 'utf8');
const listed = JSON.parse(/def emittedGlobals : List String := (\[[^\]]*\])/.exec(lean)[1]);
const keywords = new Set(['const', 'export', 'typeof', 'null', 'return', 'if', 'try', 'catch', 'void']);
const read = new Set();
const dir = new URL('accept/', import.meta.url);
for (const f of readdirSync(dir).filter((f) => f.endsWith('.expected'))) {
  const text = readFileSync(new URL(f, dir), 'utf8').replace(/"(?:[^"\\]|\\.)*"/g, '""');
  // Names the module binds: its constants and every arrow's parameter.
  const bound = new Set([...text.matchAll(/\bconst\s+([A-Za-z_$][\w$]*)/g), ...text.matchAll(/\(([A-Za-z_$][\w$]*)\)\s*=>/g)].map((m) => m[1]));
  for (const m of text.matchAll(/[A-Za-z_$][\w$]*/g)) {
    const before = text[m.index - 1];
    const after = text[m.index + m[0].length];
    if (before === '.' || after === ':' || keywords.has(m[0]) || bound.has(m[0])) continue;  // a property, a key, a keyword, or bound
    if (before !== undefined && /[\w$]/.test(before)) continue;  // inside a number such as 1e5
    read.add(m[0]);
  }
}
const missing = [...read].filter((g) => !listed.includes(g));
const unused = listed.filter((g) => !read.has(g));
for (const g of missing) console.log(`FAIL the printed code reads the global ${g}, and emittedGlobals doesn't list it, so a module could shadow it`);
for (const g of unused) console.log(`FAIL emittedGlobals lists ${g}, and no printed module reads it`);
if (missing.length || unused.length) process.exit(1);
console.log(`the printed code reads exactly the globals the model protects: ${[...read].sort().join(', ')}`);
