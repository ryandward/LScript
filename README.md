# LScript

An experiment: a language whose compiler is written in Lean, with a proof that what it emits is sound.
It grows one slice at a time, and a slice exists only once its proof does.

## Slice 1

Every binding is immutable, so there is no `const`: a declaration is `name: Type = value`, and it
compiles to `export const`. The types are `Int`, `String` and aliases of them.

```
type Age = Int
myAge: Age = 10
greeting: String = "hi"
copy: Age = myAge
```

```js
export const myAge = 10;
export const greeting = "hi";
export const copy = myAge;
```

`compile_sound` (LScript/Sound.lean): if the compiler accepts a program, the module it emits runs
without a SyntaxError or a ReferenceError, and every name holds a value of its declared type. An `Int`
is a double that is exactly the integer written, so a literal beyond ±(2^53 − 1) is rejected; a
`String` is the text written. `checkFrom_declares` says that covers every name in the source.
LScript/Examples.lean shows each check is load-bearing: every program it rejects would crash, or hold
the wrong value, in the model of V8.

What is trusted rather than proved:

- the parser, LScript/Parse.lean;
- the model of the emitted JavaScript, LScript/JS.lean, which `test/v8.mjs` checks against Node;
- the printer, `JS.render`, which `test/run.sh` checks by running every accepted program.

## Slice 2

Closed records, in place of classes. A record type is nominal and closed: its values have exactly
the declared fields. There are no methods. A record is data, and an update is a new record.

```
type User = { name: String, age: Int }
ann: User = { name: "Ann", age: 42 }
annName: String = ann.name
bob: User = { ann with name: "Bob" }
```

```js
export const ann = { name: "Ann", age: 42 };
export const annName = ann.name;
export const bob = { name: "Bob", age: ann.age };
```

An update lists every declared field, reading the ones it doesn't change from the old record, so
the new object holds exactly the record's fields and never whatever else the old object might hold.
A record's fields, and an update's new values, are literals or names: every intermediate value has a
name.

`compile_sound` now says a record's value is an object whose own fields are exactly the declared ones,
each of its declared type, so no field read the checker accepts gives `undefined`. The examples show
what each check prevents: a missing field, a smuggled field, a read of a field the record doesn't
declare, and an update with a value of the wrong type all hold the wrong value in the model; two equal
keys and a `__proto__` label are ones V8 treats specially, which the model refuses. Two records with
the same fields are different types. Functions come in slice 3, with values from outside.

## Building

Lean 4.22.0 (`lean-toolchain`), no Mathlib.

```
lake build                    # the compiler, and every proof
.lake/build/bin/lscript F.ls  # writes F.mjs, or says why F.ls is rejected
test/run.sh                   # accepted and rejected programs, run in Node, and the model against V8
```
