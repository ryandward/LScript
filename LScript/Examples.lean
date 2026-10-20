import LScript.Sound

/-!
# What the real build shows

A program compiling to the JavaScript the README shows, and every counterexample in
`Counterexamples.lean` rejected by the real checker. `test/checks.mjs` removes each load-bearing check
in a copy and proves its counterexample accepted and wrong there; here, with every check in place,
none of them is accepted and none is wrong.
-/

namespace LScript

def users : Program :=
  [user, ann,
   .val "annName" .str (.path "ann" ["name"]),
   .val "bob" (.named "User") (.update "ann" [("name", .str "Bob")])]

/-- A frozen object literal, a property read, and a frozen update that lists every declared field: the
    new name, and the old age read from `ann`. -/
example : JS.render ((compile users).toOption.getD []) =
    "export const ann = Object.freeze({ name: \"Ann\", age: 42 });\nexport const annName = ann.name;\nexport const bob = Object.freeze({ name: \"Bob\", age: ann.age });\n" := rfl

/-- The model of closures, ahead of the language having functions: `k` returns a function that
    ignores its argument, so `k(1)(2)` is 1. This is the text `test/v8.mjs` runs in Node. -/
def curried : JS.Program :=
  [⟨"k", .arrow "x" (.arrow "y" (.atom (.path "x" []))), false⟩,
   ⟨"r", .app (.app (.atom (.path "k" [])) (.atom (.num 1))) (.atom (.num 2)), true⟩]

example : JS.render curried = "const k = (x) => (y) => x;\nexport const r = k(1)(2);\n" := rfl

def numAt (r : Except JS.Err (List (String × JS.Val))) (x : String) : Option Int :=
  match r with
  | .ok env => match lookup env x with
    | some (.num n) => some n
    | _ => none
  | .error _ => none

/-- Fuel bounds how deeply evaluation nests: `k(1)(2)` evaluates `k(1)` one level down, and `k` and
    its body one further, so the module finishes at fuel 3 and runs out at fuel 1. -/
example : numAt (JS.run 3 curried) "r" = some 1 := by decide
example : (match JS.run 1 curried with | .error .outOfFuel => true | _ => false) = true := by decide

/-- The text of each test the parse makes, which `test/v8.mjs` runs in Node on the values `JSON.parse`
    returns. -/
example : JS.renderTest (.isStr (.path "v" [])) = "(typeof v === \"string\")" := rfl
example : JS.renderTest (.isInt (.path "v" [])) = "(Number.isSafeInteger(v) && !Object.is(v, -0))" := rfl
example : JS.renderTest (.isShape (.path "v" []) ["name", "age"]) =
    "(typeof v === \"object\" && v !== null && !Array.isArray(v) && Object.keys(v).length === 2 && Object.hasOwn(v, \"name\") && Object.hasOwn(v, \"age\"))" := rfl
example : JS.renderExpr (.cond (.isStr (.path "v" [])) (.arrow "x" (.atom (.path "x" []))) (.atom (.num 0))) =
    "((typeof v === \"string\") ? ((x) => x) : 0)" := rfl

/-- The boundary helper and an entry's glue, as printed; `test/v8.mjs` measures both. -/
example : JS.jsonHelper =
    "const $json = (s) => { if (typeof s !== \"string\") return undefined; try { return JSON.parse(s); } catch { return undefined; } };\n" := rfl
example : JS.renderExpr (.entry (.arrow "j" (.atom (.path "j" [])))) = "((p) => (input) => p($json(input)))((j) => j)" := rfl

/-- The real checker rejects every counterexample, so none of them is wrong here. -/
example : counterexamples.all (fun e => (compile e.2).toOption.isNone && !wrong e.2) = true := by decide

end LScript
