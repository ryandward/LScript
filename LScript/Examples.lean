import LScript.Sound

/-!
# The checks are what the theorem rests on

Each rejected program below would break `compile_sound`'s conclusion if the checker let it through:
its module, emitted unchecked, either fails in the model of V8 or holds a value that isn't of its
declared type. And the checker rejects each one.
-/

namespace LScript

open JS (Val Err)

def ages : Program :=
  [.type "Age" .int, .val "myAge" (.alias "Age") (.int 10), .val "greeting" .str (.str "hi"),
   .val "copy" (.alias "Age") (.var "myAge")]

/-- The program in the README compiles to three `export const` lines. -/
example : (compile ages).toOption = some [⟨"myAge", .num 10⟩, ⟨"greeting", .str "hi"⟩, ⟨"copy", .ident "myAge"⟩] := rfl
example : JS.render (emit ages) =
    "export const myAge = 10;\nexport const greeting = \"hi\";\nexport const copy = myAge;\n" := rfl

/-- Reading a name before its line: a ReferenceError in V8. -/
def forward : Program := [.val "a" .int (.var "b"), .val "b" .int (.int 1)]
example : JS.run (emit forward) = .error (.reference "b") := rfl
example : (check forward).toOption = none := rfl

/-- Reading a name on its own line: the same ReferenceError. -/
def selfRef : Program := [.val "a" .int (.var "a")]
example : JS.run (emit selfRef) = .error (.reference "a") := rfl
example : (check selfRef).toOption = none := rfl

/-- A name declared twice: a SyntaxError. -/
def twice : Program := [.val "a" .int (.int 1), .val "a" .int (.int 2)]
example : JS.run (emit twice) = .error (.syntax "a is declared twice") := rfl
example : (check twice).toOption = none := rfl

/-- A reserved word: a SyntaxError. -/
def reserved : Program := [.val "class" .int (.int 1)]
example : JS.run (emit reserved) = .error (.syntax "class is not an identifier") := rfl
example : (check reserved).toOption = none := rfl

/-- An integer V8 can't hold: no error, but the value isn't the integer written. -/
def big : Program := [.val "big" .int (.int 9007199254740993)]
example : JS.run (emit big) = .ok [("big", .imprecise)] := rfl
example : ¬ ValOf .imprecise .int := fun h => h
example : (check big).toOption = none := rfl

/-- A string where an `Int` was declared: no error, but the value isn't an `Int`. -/
def mismatch : Program := [.type "Age" .int, .val "age" (.alias "Age") (.str "ten")]
example : JS.run (emit mismatch) = .ok [("age", .str "ten")] := rfl
example : ¬ ValOf (.str "ten") .int := fun h => h
example : (check mismatch).toOption = none := rfl

/-- A string that wouldn't print as itself. -/
def backslash : Program := [.val "s" .str (.str "a\\b")]
example : (match JS.run (emit backslash) with | .error (.syntax _) => true | _ => false) = true := rfl
example : (check backslash).toOption = none := rfl

/-- The largest safe integers are accepted, and held exactly. -/
def edges : Program := [.val "hi" .int (.int 9007199254740991), .val "lo" .int (.int (-9007199254740991))]
example : JS.run (emit edges) = .ok [("lo", .num (-9007199254740991)), ("hi", .num 9007199254740991)] := rfl
example : (check edges).toOption.isSome = true := rfl

end LScript
