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

/-- An object literal, a property read, and an update that lists every declared field: the new name,
    and the old age read from `ann`. -/
example : JS.render ((compile users).toOption.getD []) =
    "export const ann = { name: \"Ann\", age: 42 };\nexport const annName = ann.name;\nexport const bob = { name: \"Bob\", age: ann.age };\n" := rfl

/-- The real checker rejects every counterexample, so none of them is wrong here. -/
example : counterexamples.all (fun e => (compile e.2).toOption.isNone && !wrong e.2) = true := by decide

end LScript
