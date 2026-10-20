// Imports a compiled module and checks each name against its declaration in the .ls source. Every
// value must have its declared type: an Int is a safe integer, a String a string, and a record a plain
// object with exactly the record's fields, each of its declared type. And every value must be the one
// written: a literal, a name's value, a field read's result, or, for an update, a new object holding
// the new values and the old record's other fields.
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const [source, compiled] = process.argv.slice(2);
const m = await import(resolve(compiled));
const types = new Map([['Int', { kind: 'Int' }], ['String', { kind: 'String' }]]);
const recs = new Map();
const fieldsOf = (text) => [...text.matchAll(/(\w+)\s*:\s*("[^"]*"|-?\d+|\w+)/g)].map((f) => [f[1], f[2]]);
let failed = 0;
const fail = (msg) => { failed++; console.error(msg); };

const hasType = (v, t) => {
  if (t.kind === 'Int') return Number.isSafeInteger(v);
  if (t.kind === 'String') return typeof v === 'string';
  const fs = recs.get(t.name);
  return typeof v === 'object' && v !== null && Object.getPrototypeOf(v) === Object.prototype &&
    JSON.stringify(Object.keys(v).sort()) === JSON.stringify(fs.map(([l]) => l).sort()) &&
    fs.every(([l, ft]) => hasType(v[l], ft));
};
const atomValue = (a) => (/^-?\d+$/.test(a) ? Number(a) : a.startsWith('"') ? a.slice(1, -1) : m[a]);
const sameAtom = (v, a) => (/^-?\d+$/.test(a) ? String(v) === a : v === atomValue(a));

for (const line of readFileSync(source, 'utf8').split('\n')) {
  let d;
  if ((d = /^type (\w+) = \{(.*)\}$/.exec(line))) {
    recs.set(d[1], fieldsOf(d[2]).map(([l, t]) => [l, types.get(t)]));
    types.set(d[1], { kind: 'record', name: d[1] });
  } else if ((d = /^type (\w+) = (\w+)$/.exec(line))) {
    types.set(d[1], types.get(d[2]));
  } else if ((d = /^(\w+): (\w+) = (.*)$/.exec(line))) {
    const [, name, tyName, e] = d;
    const t = types.get(tyName);
    const v = m[name];
    if (!hasType(v, t)) { fail(`${name}: declared ${tyName}, holds ${JSON.stringify(v)}`); continue; }
    let u;
    if ((u = /^\{\s*(\w+)\s+with\s*(.*)\}$/.exec(e))) {
      const base = m[u[1]];
      const given = new Map(fieldsOf(u[2]));
      if (v === base) fail(`${name}: an update returned the old object`);
      for (const [l] of recs.get(t.name)) {
        const ok = given.has(l) ? sameAtom(v[l], given.get(l)) : v[l] === base[l];
        if (!ok) fail(`${name}.${l}: holds ${JSON.stringify(v[l])}`);
      }
    } else if ((u = /^\{(.*)\}$/.exec(e))) {
      for (const [l, a] of fieldsOf(u[1])) if (!sameAtom(v[l], a)) fail(`${name}.${l}: holds ${JSON.stringify(v[l])}`);
    } else if ((u = /^(\w+)((?:\.\w+)+)$/.exec(e))) {
      const read = u[2].slice(1).split('.').reduce((acc, l) => acc[l], m[u[1]]);
      if (v !== read) fail(`${name}: holds ${JSON.stringify(v)}, and ${e} is ${JSON.stringify(read)}`);
    } else if (!sameAtom(v, e)) {
      fail(`${name}: holds ${JSON.stringify(v)}, where ${e} was written`);
    }
  }
}
process.exit(failed ? 1 : 0);
