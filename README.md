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

## Building

Lean 4.22.0 (`lean-toolchain`), no Mathlib.

```
lake build                    # the compiler, and every proof
.lake/build/bin/lscript F.ls  # writes F.mjs, or says why F.ls is rejected
test/run.sh                   # accepted and rejected programs, run in Node, and the model against V8
```
