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
for (const w of reserved) {
  expect(`a reserved word as a label: { ${w}: 1 } and o.${w}`, outcome(`export const o = { ${w}: 1 };\nexport const r = o.${w};\n`), 'ok');
}
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

// Records: what V8 does with the object literals and property reads the compiler emits.
const value = (expr) => { try { return JSON.stringify(eval(`(${expr})`)) ?? 'undefined'; } catch (e) { return e.constructor.name; } };
expect('({ a: 1, a: "x" }).a  (V8 keeps the last; the model refuses it)', value('({ a: 1, a: "x" }).a'), '"x"');
expect('Object.keys({ __proto__: 1 })  (no field; the model refuses it)', value('Object.keys({ __proto__: 1 })'), '[]');
expect('({ __proto__: {} }).__proto__ is not an own field', value('Object.hasOwn({ __proto__: {} }, "__proto__")'), 'false');
expect('({ name: "a" }).email  (not an error: untracked)', value('({ name: "a" }).email'), 'undefined');
expect('typeof ({}).toString  (inherited: untracked)', value('typeof ({}).toString'), '"function"');
expect('(42).name  (not an error: untracked)', value('(42).name'), 'undefined');
expect('"Ann".length  (a value, but not a field: untracked)', value('"Ann".length'), '3');
expect('((x) => x).length  (a function\'s property: untracked)', value('((x) => x).length'), '1');
expect('({ a: 1 }).b.c  (a read through undefined; the model refuses it)', value('({ a: 1 }).b.c'), 'TypeError');
expect('({}).toString.name  (a read through a method; refused all the same)', value('({}).toString.name'), '"toString"');
expect('o.1, a property that isn\'t an identifier', outcome('export const o = { a: 1 };\nexport const r = o.1;\n'), 'parse SyntaxError');
expect('Object.keys({ b: 1, a: 2 }) are the literal\'s fields', value('Object.keys({ b: 1, a: 2 })'), '["b","a"]');
expect('a literal\'s prototype is Object.prototype', value('Object.getPrototypeOf({ a: 1 }) === Object.prototype'), 'true');

// Freezing: what an importer can do to a record the module exports.
const frozenLib = join(dir, 'frozen.mjs');
writeFileSync(frozenLib, 'export const ann = Object.freeze({ name: "Ann", age: 42 });\n');
const tryImport = (body) => outcome(`import { ann } from ${JSON.stringify(frozenLib)};\n${body}\n`);
expect('an importer writes a field of a frozen record', tryImport('ann.age = "x";'), 'run TypeError');
expect('an importer adds a field', tryImport('ann.admin = true;'), 'run TypeError');
expect('an importer deletes a field', tryImport('delete ann.age;'), 'run TypeError');
expect('an importer redefines a field', tryImport('Object.defineProperty(ann, "age", { value: "x" });'), 'run TypeError');
expect('an importer changes its prototype', tryImport('Object.setPrototypeOf(ann, null);'), 'run TypeError');
expect('Object.freeze returns the object it froze', value('(() => { const o = {}; return Object.freeze(o) === o && Object.isFrozen(o); })()'), 'true');
expect('a module binding Object, then a record (the model refuses it)', outcome('export const Object = 1;\nexport const r = Object.freeze({ a: 1 });\n'), 'run TypeError');

// Functions: arrows, calls, and what V8 checks before running any of the module.
const moduleValue = async (source, name) => {
  const f = join(dir, `m${n++}.mjs`);
  writeFileSync(f, source);
  try { return JSON.stringify((await import(f))[name]) ?? 'undefined'; } catch (e) { return e.constructor.name; }
};
expect('a call runs the body with the argument', await moduleValue('const id = (x) => x;\nexport const r = id(7);\n', 'r'), '7');
expect('a curried call, f(a)(b)', await moduleValue('const k = (x) => (y) => x;\nexport const r = k(1)(2);\n', 'r'), '1');
expect('a closure sees the names declared before it', await moduleValue('const a = 5;\nconst f = (x) => a;\nexport const r = f(0);\n', 'r'), '5');
expect('a parameter shadows a name declared before', await moduleValue('const x = 1;\nconst f = (x) => x;\nexport const r = f(2);\n', 'r'), '2');
expect('a body making a record: frozen', await moduleValue('const mk = (x) => Object.freeze({ a: x });\nexport const r = Object.isFrozen(mk(1));\n', 'r'), 'true');
expect('calling a number', outcome('const n = 1;\nexport const r = n(2);\n'), 'run TypeError');
expect('calling a string', outcome('const s = "f";\nexport const r = s(2);\n'), 'run TypeError');
expect('calling a field that isn\'t there', outcome('const o = Object.freeze({});\nexport const r = o.f(1);\n'), 'run TypeError');
expect('calling an inherited method (the model refuses it)', outcome('const o = Object.freeze({});\nexport const r = o.toString(1);\n'), 'ok');
expect('a body that isn\'t valid syntax, never called', outcome('const f = (x) => class;\nexport const r = 1;\n'), 'parse SyntaxError');
expect('a body reading a property that isn\'t an identifier, never called', outcome('const f = (x) => x.1;\nexport const r = 1;\n'), 'parse SyntaxError');
expect('a body with a string broken across lines, never called', outcome('const f = (x) => "a\nb";\nexport const r = 1;\n'), 'parse SyntaxError');
for (const w of ['eval', 'arguments', 'class', 'let', 'yield', 'await']) {
  expect(`a parameter named ${w}`, outcome(`const f = (${w}) => 1;\nexport const r = 1;\n`), 'parse SyntaxError');
}
expect('a parameter named Object, then a record (the model refuses it)', outcome('const f = (Object) => Object.freeze({ a: 1 });\nexport const r = f(1);\n'), 'run TypeError');
expect('a body reading a name declared after it (the model refuses it)', outcome('const f = (x) => y;\nconst y = 2;\nexport const r = f(1);\n'), 'ok');
expect('...and called before that name\'s line', outcome('const f = (x) => y;\nexport const r = f(1);\nconst y = 2;\n'), 'run ReferenceError');
const chain = (depth) => ['const f0 = (x) => x;', ...Array.from({ length: depth - 1 }, (_, i) => `const f${i + 1} = (x) => f${i}(x);`), `export const v = f${depth - 1}(1);`].join('\n') + '\n';
expect('calls nested 1,000 deep', outcome(chain(1000)), 'ok');
expect('calls nested 100,000 deep (V8\'s stack, which the model leaves out)', outcome(chain(100000)), 'run RangeError');
const fnLib = join(dir, 'fn.mjs');
writeFileSync(fnLib, 'const f = (x) => x;\nexport const r = f(1);\n');
expect('an importer naming a const that isn\'t exported', outcome(`import { f } from ${JSON.stringify(fnLib)};\n`), 'run SyntaxError');

// JSON: what JSON.parse returns, and the tests the parse makes of it. The test texts are the ones
// Examples.lean pins as the printer's output.
const J = (text) => JSON.parse(text);
const run = (fn) => { try { return JSON.stringify(fn()) ?? 'undefined'; } catch (e) { return e.constructor.name; } };
expect('JSON.parse("-0") is -0', run(() => Object.is(J('-0'), -0)), 'true');
expect('JSON.parse("1e400") is Infinity', run(() => J('1e400') === Infinity), 'true');
expect('JSON.parse makes "__proto__" an own key', run(() => Object.hasOwn(J('{"__proto__": 1}'), '__proto__')), 'true');
expect('...and leaves the prototype alone', run(() => Object.getPrototypeOf(J('{"__proto__": 1}')) === Object.prototype), 'true');
expect('...and reading it gives the parsed value', run(() => J('{"__proto__": 1}').__proto__), '1');
expect('of two equal keys, the last stays, once', run(() => { const o = J('{"a": 1, "a": 2}'); return [o.a, Object.keys(o).length]; }), '[2,1]');
expect('a lone surrogate parses into a one-unit string', run(() => { const s = J('"\\ud800"'); return [typeof s, s.length, s.charCodeAt(0)]; }), '["string",1,55296]');
expect('JSON.parse makes plain objects, not frozen', run(() => { const o = J('{"a": 1}'); return [Object.getPrototypeOf(o) === Object.prototype, Object.isFrozen(o)]; }), '[true,false]');
expect('JSON.parse makes arrays', run(() => Array.isArray(J('[1]'))), 'true');
expect('reading a property of null', run(() => J('null').a), 'TypeError');
expect('reading a property of undefined', run(() => undefined.a), 'TypeError');
const test = (text, v) => run(() => new Function('v', `return ${text};`)(v));
const isStr = '(typeof v === "string")';
const isInt = '(Number.isSafeInteger(v) && !Object.is(v, -0))';
const isShape = '(typeof v === "object" && v !== null && !Array.isArray(v) && Object.keys(v).length === 2 && Object.hasOwn(v, "name") && Object.hasOwn(v, "age"))';
for (const [label, v, want] of [['"a"', 'a', 'true'], ['a lone surrogate', J('"\\ud800"'), 'true'], ['1', 1, 'false'], ['null', null, 'false'],
    ['undefined', undefined, 'false'], ['{}', {}, 'false'], ['[]', [], 'false'], ['true', true, 'false']]) {
  expect(`string test of ${label}`, test(isStr, v), want);
}
for (const [label, v, want] of [['1', 1, 'true'], ['0', 0, 'true'], ['9007199254740991', J('9007199254740991'), 'true'],
    ['-9007199254740991', J('-9007199254740991'), 'true'], ['-0', J('-0'), 'false'], ['1e400', J('1e400'), 'false'],
    ['1.5', J('1.5'), 'false'], ['9007199254740992', J('9007199254740992'), 'false'], ['"1"', '1', 'false'],
    ['null', null, 'false'], ['true', true, 'false'], ['undefined', undefined, 'false']]) {
  expect(`integer test of ${label}`, test(isInt, v), want);
}
for (const [label, v, want] of [['exactly name and age', J('{"name": "a", "age": 1}'), 'true'],
    ['the same keys in another order', J('{"age": 1, "name": "a"}'), 'true'],
    ['name twice and age', J('{"name": "a", "name": "b", "age": 1}'), 'true'],
    ['a frozen record of them', Object.freeze({ name: 'a', age: 1 }), 'true'],
    ['a missing key', J('{"name": "a"}'), 'false'], ['an extra key', J('{"name": "a", "age": 1, "x": 0}'), 'false'],
    ['an extra "__proto__" key', J('{"name": "a", "age": 1, "__proto__": {}}'), 'false'],
    ['an array', J('["a", 1]'), 'false'], ['null', null, 'false'], ['a string', 'name', 'false'], ['undefined', undefined, 'false']]) {
  expect(`shape test of ${label}`, test(isShape, v), want);
}
expect('a conditional with an arrow branch', await moduleValue('const f = ((typeof "s" === "string") ? ((x) => x) : 0);\nexport const r = f(5);\n', 'r'), '5');
expect('an arrow called where it is written', await moduleValue('export const r = ((x) => x)(5);\n', 'r'), '5');

// Entries: the boundary helper and the glue around a parse, as Examples.lean pins them. The parse here
// returns what it is handed, so this measures what an entry hands its parse.
const helper = 'const $json = (s) => { if (typeof s !== "string") return undefined; try { return JSON.parse(s); } catch { return undefined; } };';
const glueLib = join(dir, 'glue.mjs');
writeFileSync(glueLib, `${helper}\nexport const seen = ((p) => (input) => p($json(input)))((j) => j);\n`);
const { seen } = await import(glueLib);
const deep = '['.repeat(1000000) + ']'.repeat(1000000);
expect('an entry hands its parse JSON.parse of a string', run(() => seen('{"a": [1, null, true]}')), '{"a":[1,null,true]}');
expect('...undefined for text that doesn\'t parse', run(() => seen('{a: 1}')), 'undefined');
expect('...undefined for anything but a string', run(() => seen(42)), 'undefined');
expect('...undefined for a String object', run(() => seen(new String('1'))), 'undefined');
expect('...undefined for a Proxy, without running a trap', run(() => seen(new Proxy({}, new Proxy({}, { get: () => () => { throw new Error('trap'); } })))), 'undefined');
expect('...and never throws, even for nesting a million deep', run(() => { const v = seen(deep); return v === undefined || Array.isArray(v); }), 'true');
const settles = async (source) => {
  const f = join(dir, `m${n++}.mjs`);
  writeFileSync(f, source);
  return Promise.race([import(f).then(() => 'resolved', () => 'rejected'), new Promise((r) => setTimeout(() => r('still waiting'), 500))]);
};
expect('import() of a module exporting a function named then (the model refuses it)', await settles(`${helper}\nexport const then = ((p) => (input) => p($json(input)))((j) => 0);\n`), 'still waiting');
expect('...and of one exporting the number then', await settles('export const then = 1;\n'), 'resolved');

console.log(failed ? `${failed} disagreement(s) with the model` : 'the model agrees with Node');
process.exit(failed ? 1 : 0);
