// Holds the model to Node on modules no one wrote. test/Diff.lean generates random modules of the
// model's fragment, each one the model runs without an error, and says what each export holds and what
// calls of the exported functions return. This imports each module in Node, builds the same arguments,
// makes the same calls, and fails on any value that isn't the one the model gave, on any throw, and on
// an import that never settles. Where the model gives an error, Node isn't asked: a stricter model isn't
// a wrong one.
//
// The names and labels come from the engine, not from a list someone imagined: every global, every
// property along the prototype chain of each kind of value the model holds, and of a promise, since
// import() treats a module as one; the spec's reserved and contextual words; and, added by Diff.lean,
// every identifier the printer writes. SEED and COUNT pick the modules (default 1 and 10000). Run with
// LAKE=/path/to/lake if lake isn't on the PATH.
import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { inspect } from 'node:util';

const repo = new URL('..', import.meta.url).pathname;
const seed = process.env.SEED ?? '1';
const count = process.env.COUNT ?? '10000';
const lake = process.env.LAKE ?? 'lake';

const ident = /^[A-Za-z_][A-Za-z0-9_]*$/;
const props = new Set();
for (const v of [{}, [], 'a', 0, true, (x) => x, Promise.resolve()]) {
  for (let o = Object(v); o !== null; o = Object.getPrototypeOf(o)) for (const k of Object.getOwnPropertyNames(o)) props.add(k);
}
const words = [
  'await', 'break', 'case', 'catch', 'class', 'const', 'continue', 'debugger', 'default', 'delete', 'do', 'else', 'enum',
  'export', 'extends', 'false', 'finally', 'for', 'function', 'if', 'import', 'in', 'instanceof', 'new', 'null', 'return',
  'super', 'switch', 'this', 'throw', 'true', 'try', 'typeof', 'var', 'void', 'while', 'with', 'yield', 'implements',
  'interface', 'let', 'package', 'private', 'protected', 'public', 'static', 'arguments', 'eval', 'async', 'of', 'get',
  'set', 'as', 'from', 'target', 'meta', 'using', 'accessor', 'undefined', 'NaN', 'Infinity',
];
const names = [...new Set([...Object.getOwnPropertyNames(globalThis), ...props, ...words])].filter((k) => ident.test(k));
const labels = [...new Set([...props, ...words])].filter((k) => ident.test(k));
const dir = mkdtempSync(join(tmpdir(), 'lscript-diff-'));
writeFileSync(join(dir, 'pools'), `${names.join(' ')}\n${labels.join(' ')}\n`);

if (spawnSync(lake, ['build', 'difftest'], { cwd: repo, stdio: 'pipe' }).status !== 0) { console.log('FAIL difftest does not build'); process.exit(2); }
const gen = spawnSync(join(repo, '.lake/build/bin/difftest'), [seed, count, join(dir, 'pools')], { maxBuffer: 1 << 30, encoding: 'utf8' });
if (gen.status !== 0) { console.log(`FAIL difftest exited ${gen.status}: ${gen.stderr}`); process.exit(2); }

const hostile = {
  proxy: () => new Proxy({}, new Proxy({}, { get: () => () => { throw new Error('trap'); } })),
  stringObject: () => new String('{}'),
  symbol: () => Symbol('s'),
  bigint: () => 1n,
  function: () => () => '{}',
};
const build = (d, m) => {
  switch (d.t) {
    case 'num': case 'notInt': return Number(d.v);
    case 'negZero': return -0;
    case 'str': case 'bool': return d.v;
    case 'null': return null;
    case 'undef': return undefined;
    case 'arr': return d.v.map((x) => build(x, m));
    case 'obj': {
      const o = {};
      for (const [k, x] of d.v) Object.defineProperty(o, k, { value: build(x, m), writable: true, enumerable: true, configurable: true });
      return d.frozen ? Object.freeze(o) : o;
    }
    case 'ref': return m[d.v];
    case 'hostile': return hostile[d.v]();
  }
  throw new Error(`can't build ${JSON.stringify(d)}`);
};

const show = (v) => inspect(v, { depth: 4 });
// null if v is what the model says, or why not.
const same = (w, v, at) => {
  const want = (what) => `${at}: the model says ${what}, and Node gives ${show(v)}`;
  switch (w.t) {
    case 'any': return null;
    case 'fn': return typeof v === 'function' ? null : want('a function');
    case 'num': return Object.is(v, Number(w.v)) ? null : want(w.v);
    case 'notInt': return typeof v === 'number' && !Object.is(v, -0) && !Number.isSafeInteger(v) ? null : want('a number that is not a safe integer, nor -0');
    case 'negZero': return Object.is(v, -0) ? null : want('-0');
    case 'str': case 'bool': return v === w.v ? null : want(JSON.stringify(w.v));
    case 'null': return v === null ? null : want('null');
    case 'undef': return v === undefined ? null : want('undefined');
    case 'arr': {
      if (!Array.isArray(v) || Object.getPrototypeOf(v) !== Array.prototype || v.length !== w.v.length) return want(`an array of ${w.v.length}`);
      for (let i = 0; i < w.v.length; i++) { const r = same(w.v[i], v[i], `${at}[${i}]`); if (r) return r; }
      return null;
    }
    case 'obj': {
      if (typeof v !== 'object' || v === null || Array.isArray(v) || Object.getPrototypeOf(v) !== Object.prototype) return want('a plain object');
      if (Object.isFrozen(v) !== w.frozen) return want(w.frozen ? 'a frozen object' : 'an object that is not frozen');
      const keys = Reflect.ownKeys(v);
      if (keys.length !== w.v.length || !w.v.every(([k]) => Object.hasOwn(v, k))) return want(`own keys ${JSON.stringify(w.v.map(([k]) => k))}`);
      for (const [k, x] of w.v) {
        const p = Object.getOwnPropertyDescriptor(v, k);
        if (!('value' in p)) return want(`a data field ${k}`);
        const r = same(x, p.value, `${at}.${k}`);
        if (r) return r;
      }
      return null;
    }
  }
  return `${at}: no such description ${JSON.stringify(w)}`;
};

const settle = (url) => Promise.race([
  import(url).then((m) => ({ m }), (e) => ({ e })),
  new Promise((r) => setTimeout(() => r({ hung: true }), 2000)),
]);

let failed = 0;
let calls = 0;
let values = 0;
const cases = gen.stdout.split('\n').filter((l) => l !== '');
for (const [i, line] of cases.entries()) {
  const c = JSON.parse(line);
  const found = [];
  const r = await settle(`data:text/javascript;base64,${Buffer.from(c.src).toString('base64')}`);
  if (r.hung) found.push('import() never settled');
  else if (r.e) found.push(`the import threw ${show(r.e)}`);
  else {
    const m = r.m;
    const want = c.exports.map(([k]) => k).sort();
    const got = Object.keys(m).sort();
    if (JSON.stringify(got) !== JSON.stringify(want)) found.push(`the module exports ${JSON.stringify(got)}, and the model says ${JSON.stringify(want)}`);
    for (const [k, w] of c.exports) { values++; const d = same(w, m[k], k); if (d) found.push(d); }
    for (const pr of c.probes) {
      calls++;
      const args = pr.args.map((a) => build(a, m));
      const at = `${pr.f}${args.map((a) => `(${show(a)})`).join('')}`;
      let v = m[pr.f];
      try { for (const a of args) v = v(a); } catch (e) { found.push(`${at} threw ${show(e)}`); continue; }
      const d = same(pr.want, v, at);
      if (d) found.push(d);
    }
  }
  if (found.length) {
    failed++;
    if (failed <= (Number(process.env.SHOW) || 10)) console.log(`FAIL module ${i} of seed ${seed}:\n${c.src.replace(/^/gm, '    ')}\n${found.map((f) => `  ${f}`).join('\n')}\n`);
  }
}
console.log(gen.stderr.trim().split('\n').sort((a, b) => parseInt(b) - parseInt(a)).map((l) => `  ${l}`).join('\n'));
console.log(`${cases.length} modules, ${values} exported values, ${calls} calls: ${failed ? `${failed} module(s) where Node disagrees with the model` : 'Node agrees with the model on every one'}`);
process.exit(failed ? 1 : 0);
