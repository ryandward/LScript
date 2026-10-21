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

- the parser, LScript/Parse.lean, and the native `lscript` binary Lean and clang build from the proved
  functions, unless the run is checked with `certify/check.sh` (below);
- the model of the emitted JavaScript, LScript/JS.lean, which `test/v8.mjs` checks against Node;
- the printer, `JS.render`, which `test/run.sh` checks by running every accepted program;
- the built-ins the emitted code calls: `Object.freeze`, and for entries `JSON.parse`, `Array.isArray`,
  `Object.keys`, `Object.hasOwn`, `Number.isSafeInteger` and `Object.is`. Code that runs before the
  module could replace one, and the module trusts that none did. The module itself can't shadow one:
  the names `Object`, `Array`, `Number` and `JSON` are refused, and `test/globals.mjs` checks that the
  printed code reads no other global;
- for an entry, that the printed helper `$json` gives `JSON.parse` of a string, or `undefined`, and
  never runs the caller's code: `test/v8.mjs` measures it on text, non-text, a hostile Proxy and
  nesting a million deep;
- V8's stack, which the model leaves unbounded: calls nested deeper than it allows throw a RangeError,
  which on Node 22 takes about 10,000 declarations.

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
export const ann = Object.freeze({ name: "Ann", age: 42 });
export const annName = ann.name;
export const bob = Object.freeze({ name: "Bob", age: ann.age });
```

An update lists every declared field, reading the ones it doesn't change from the old record, so
the new object holds exactly the record's fields and never whatever else the old object might hold.
Every record is frozen when it is made, so code that imports one can't write, add or delete a field,
or change its prototype: V8 throws, and the value stays what it was declared. `Object.freeze` is
shallow, but a record's type requires the records in its fields to be frozen too, and every object
the module makes is frozen, so records are frozen all the way down. A value can't be named
`Object`, which would shadow the `Object.freeze` the emitted code calls.
A record's fields, and an update's new values, are literals or names, as in
`{ order with status: "shipped" }`; a nested record or a field read gets its own declaration first. `type` and `with` are keywords only where the grammar puts them, as TypeScript
treats `type`, so `type: Int = 1` and `{ type: "click" }` parse; and a field label may be any
identifier JavaScript allows as a property name, reserved words such as `class` included.

`compile_sound` now says a record's value is a frozen object whose own fields are exactly the declared
ones, each of its declared type, so no field read the checker accepts gives `undefined`. Two records with
the same fields are different types. Functions come in slice 3, with values from outside.

## Slice 3: functions

Functions of one parameter, curried, used inside the module. A function type is `A -> B`, grouping to
the right; a function is `(x) => body`; and a call is `f(a)` or `f(a)(b)`, whose arguments, like a
record's fields, are literals or names.

```
type User = { name: String, age: Int }
rename: String -> User -> User = (n) => (u) => { u with name: n }
mk: String -> Int -> User = (n) => (a) => { name: n, age: a }
ann: User = mk("Ann")(42)
bob: User = rename("Bob")(ann)
```

```js
const rename = (n) => (u) => Object.freeze({ name: n, age: u.age });
const mk = (n) => (a) => Object.freeze({ name: n, age: a });
export const ann = mk("Ann")(42);
export const bob = rename("Bob")(ann);
```

A name of a function type is emitted without `export`, and a record's fields can't be functions, so
only data leaves the module. An exported function could be called with anything, while the proof of
its body assumes an argument of its parameter type. A call may give fewer arguments than the function
takes and get a function back, as `konst(3)` does in `test/accept/functions.ls`. A function sees only
the names declared before it, so it can't call itself, and every call finishes.

`compile_sound` now says the module finishes at some fuel, one unit per call; that a function's value
is a closure that, given any value of its parameter type, finishes with a value of its result type;
and that every name the module exports holds data, never a function. The function case is a logical
relation, the standard way to prove that calls finish: a call needs no argument about termination, and
the proof for a function is the proof for its body. The model of V8 grew closures, calls and fuel
first, and `test/v8.mjs` measures each claim, including the SyntaxError V8 raises for a function body
that isn't valid syntax even when nothing calls it.

## Slice 3b: entries

An entry is how data comes in: an exported function an importer calls with anything. Text that
`JSON.parse` reads as a value of the entry's input type is parsed into a fresh frozen value and handed
to the entry's success function; anything else gets its failure value.

```
type User = { name: String, age: Int }
nameOf: User -> String = (u) => u.name
entry greet: User -> String = nameOf else "not a user"
```

```js
const $json = (s) => { if (typeof s !== "string") return undefined; try { return JSON.parse(s); } catch { return undefined; } };
const nameOf = (u) => u.name;
export const greet = ((p) => (input) => p($json(input)))(((k) => (f) => (j) =>
  (<j is a plain object with exactly name and age, a string and a safe integer> ? k(Object.freeze({ name: j.name, age: j.age })) : f))(nameOf)("not a user"));
```

The parse never reads a field before the shape test has found it, never hands on the parsed object,
and never invents a value for a missing field. It refuses an extra key, `__proto__` included, since a
sender and a receiver that disagree about a record should hear about it; it refuses `-0`, which an
`Int` can't be; and of two equal keys it takes the last, as `JSON.parse` does. An entry's input is
`Int`, `String`, or a record of those, for now. Its name can't be `then`, since `import()` would take
the module for a promise and wait forever.

`compile_sound` needs no new part for entries: an entry's type says that its parse, given anything
`JSON.parse` returns or `undefined`, finishes with data of its result type, so "every name holds a
value of its type" covers it. The parse is proved through the model of V8, test by test; what is
trusted is `$json` and the built-ins the tests call, each measured.

## Checking a run

`certify/check.sh F.ls` has Lean's kernel check one compiled program, `F.ls` and the `F.mjs` beside it.
Lean reads both files from disk, runs the proved parser and compiler on the source text, and checks
that the program is accepted and that its JavaScript prints as exactly the output file; the module in
it then satisfies `compile_sound`. The statement and the axiom check belong to `certify/Check.lean`,
not to the compiler that wrote `F.mjs`, and it fails if the proof rests on anything but Lean's
standard axioms. A line added to `F.mjs`, or a byte changed in `F.ls`, makes it fail. It finds `F.mjs`
beside the path it was given, as the compiler writes it, so a symlinked `F.ls` is checked against the
output beside the link. Nothing needs keeping but the two files, and any pair can be checked at any
time.

It rebuilds the LScript library from the checkout's sources first, so an older build left in `.lake`
isn't what gets checked, and it prints the commit it checked against, noting uncommitted changes.

The check costs the kernel time and memory in proportion to the program, about 30 ms and 5 MB per line
with Lean 4.22: 200 lines take 6 s and 2 GB, 1,600 lines 45 s and 8 GB, and 6,400 lines 205 s and
30 GB. If Lean is killed for running out of memory, the check says so. The kernel evaluates every
definition as written, without the faster code Lean compiles for it, so three things are written for
it: the printer builds strings from the right, since appending onto a growing left side is quadratic;
the checker's scopes are tries (LScript/Scope.lean), since looking names up in a list is quadratic and
comparing strings is slow; and nothing the check runs recurses once per character, since that
overflows the kernel's stack.

A checked run doesn't rest on the parser, the `lscript` binary, or the C toolchain that built it. It
rests on the printer and the model of V8 together, since `compile_sound` is about the program the
printer prints and the step from that text to what V8 does is the model's; on `Object.freeze` being
the built-in, Node behaving as `test/v8.mjs` measures, and calls nesting no deeper than V8's stack
allows; and on the machine it runs on: Lean's
kernel, Lake's build of the commit, and the files as they were on disk when it ran.

A check is evidence for whoever runs it. The project's job is soundness, not making compiled code
tamper-proof: someone who wants assurance about a program, an auditor for instance, runs
`certify/check.sh` themselves on a fresh clone of the commit they reviewed. A result someone else
reports is only as good as their word.

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
certify/check.sh F.ls         # Lean's kernel checks that run, from F.ls and F.mjs on disk
test/run.sh                   # accepted and rejected programs, run in Node and checked, and the model against V8
node test/checks.mjs          # every check against its kind: fired by a test, and refuting soundness when removed
```
