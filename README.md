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
name. `type` and `with` are keywords only where the grammar puts them, as TypeScript
treats `type`, so `type: Int = 1` and `{ type: "click" }` parse; and a field label may be any
identifier JavaScript allows as a property name, reserved words such as `class` included.

`compile_sound` now says a record's value is an object whose own fields are exactly the declared ones,
each of its declared type, so no field read the checker accepts gives `undefined`. Two records with
the same fields are different types. Functions come in slice 3, with values from outside.

## Checks

Every rejection ends with the code of the check that made it, as in `User needs its field age
[literal-complete]`, and every check in LScript/Check.lean is tagged with one of three kinds:

- **load-bearing**: without it, the compiler would accept a program that goes wrong.
  LScript/Counterexamples.lean holds one such program per check.
- **policy**: it rejects a program that says two things, such as an update giving one field twice or
  an alias declared twice, and `compile_sound` still holds without it.
- **partial**: a `none` arm, where the program names something that doesn't exist and there is nothing
  to continue with.

`test/checks.mjs` holds every tag to its kind, in a copy of the repository, one check at a time. Every
check must be fired by a program in `test/reject/`. For a load-bearing check, it removes the check and
has Lean prove by `decide` that the compiler then accepts the check's counterexample and its output
fails in the model of V8 or holds a value of the wrong type, so `compile_sound` is false for that
compiler; in the real build, Lean must prove the same program isn't wrong. For a policy check,
`compile_sound` must still build without it. Only a `none` arm may be partial.

Removing a check is mechanical, never authored. An `if` check is removed by making its condition
false, so the code falls through to its own continuation. A check written as a match arm names its
removal with `off:`, and that expression must appear word for word in a sibling arm of the same match,
which is where the check's own success path continues.

The proof takes each check's result only through the fact it establishes, never by matching its
condition. Facts a declaration establishes, that a record's labels are ones an object can carry and
that every record type in scope was declared, are proved once where the record is declared and kept in
the proof's invariant, so no check repeats them.

## Choices, not necessities

Restrictions the language makes that neither soundness nor V8 requires, kept for now:

- Names and labels are ASCII letters, digits and `_`. JavaScript also allows `$` and Unicode.
- Integer literals are decimal.
- A string literal can't hold an escape or a character outside printable ASCII. Lifting this needs a
  printer that writes escapes, and a V8 measurement for each.

## Building

Lean 4.22.0 (`lean-toolchain`), no Mathlib.

```
lake build                    # the compiler, and every proof
.lake/build/bin/lscript F.ls  # writes F.mjs, or says why F.ls is rejected
test/run.sh                   # accepted and rejected programs, run in Node, and the model against V8
node test/checks.mjs          # every check against its kind: fired by a test, and refuting soundness when removed
```
