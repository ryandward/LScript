// Calls the entries of test/accept/entry.mjs the way an importer would, with JSON text that parses to
// the input type, text that doesn't, and values that aren't text at all. Each call must return the
// success function's result on a fresh frozen record, or the failure value, and never throw.
import { resolve } from 'node:path';

const m = await import(resolve('test/accept/entry.mjs'));
let failed = 0;
const check = (label, got, want) => {
  const ok = Object.is(got, want) || JSON.stringify(got) === JSON.stringify(want);
  if (!ok) { failed++; console.log(`FAIL ${label}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`); }
};
const call = (f, x) => { try { return f(x); } catch (e) { return `threw ${e.constructor.name}`; } };

const hostile = new Proxy({}, new Proxy({}, { get: () => () => { throw new Error('trap'); } }));
const bad = 'not a user';
for (const [label, input, want] of [
  ['a user', '{"name": "Ann", "age": 42}', 'Ann'],
  ['the keys in another order', '{"age": 42, "name": "Ann"}', 'Ann'],
  ['spaces around it', ' \n{ "name" : "Ann" , "age" : 42 } ', 'Ann'],
  ['name twice: the last stays', '{"name": "A", "name": "B", "age": 1}', 'B'],
  ['a lone surrogate in the name', '{"name": "\\ud800", "age": 1}', '\ud800'],
  ['a missing key', '{"name": "Ann"}', bad],
  ['an extra key', '{"name": "Ann", "age": 42, "admin": true}', bad],
  ['an extra "__proto__" key', '{"name": "Ann", "age": 42, "__proto__": {}}', bad],
  ['age -0', '{"name": "Ann", "age": -0}', bad],
  ['age 1.5', '{"name": "Ann", "age": 1.5}', bad],
  ['age 1e400', '{"name": "Ann", "age": 1e400}', bad],
  ['age 2^53', '{"name": "Ann", "age": 9007199254740992}', bad],
  ['age as text', '{"name": "Ann", "age": "42"}', bad],
  ['name as a number', '{"name": 7, "age": 42}', bad],
  ['an array', '["Ann", 42]', bad],
  ['null', 'null', bad],
  ['a string', '"Ann"', bad],
  ['text that isn\'t JSON', '{name: "Ann"}', bad],
  ['empty text', '', bad],
  ['deeply nested text', '['.repeat(100000) + ']'.repeat(100000), bad],
  ['a number, not text', 42, bad],
  ['undefined', undefined, bad],
  ['an object, not text', { name: 'Ann', age: 42 }, bad],
  ['a String object', new String('{"name": "Ann", "age": 42}'), bad],
  ['a Proxy whose every trap throws', hostile, bad],
]) check(`greet: ${label}`, call(m.greet, input), want);

const ann = call(m.echo, '{"name": "Ann", "age": 42, "name": "Ann"}');
check('echo: a fresh frozen plain object', [Object.isFrozen(ann), Object.getPrototypeOf(ann) === Object.prototype, Object.keys(ann).sort()],
  [true, true, ['age', 'name']]);
check('echo: its fields', [ann.name, ann.age], ['Ann', 42]);
check('echo: the failure value is the declared record', call(m.echo, '{}') === m.nobody, true);
check('age: a user\'s age', call(m.age, '{"name": "Ann", "age": 42}'), 42);
check('age: not a user', call(m.age, '[]'), -1);
check('number: 42', call(m.number, '42'), 42);
check('number: the largest safe integer', call(m.number, '9007199254740991'), 9007199254740991);
check('number: -0 is refused, so the failure value 0, not -0', Object.is(call(m.number, '-0'), 0), true);
check('number: 2^53 is refused', call(m.number, '9007199254740992'), 0);
check('text: a string', call(m.text, '"hi"'), 'hi');
check('text: a number is refused', call(m.text, '5'), '');
const keys = Object.keys(m).sort();
check('the module exports its entries and its data, not its functions', keys, ['age', 'echo', 'greet', 'nobody', 'number', 'text']);
check('import() resolves: no export is a callable then', typeof (await import(resolve('test/accept/entry.mjs'))).greet, 'function');
if (failed) { console.log(`${failed} entry check(s) failed`); process.exit(1); }
