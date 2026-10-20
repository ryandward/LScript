import LScript.Sound

/-!
# The checks are what the theorem rests on

Each check below is shown two ways: the module a compiler without that check would emit either fails
in the model of V8 or holds a value that isn't of its declared type; and the checker rejects the
program that would produce it.
-/

namespace LScript

open JS (Val Err)

def userDecl : Decl := .record "User" [("name", .str), ("age", .int)]
def annDecl : Decl := .val "ann" (.named "User") (.record [("name", .str "Ann"), ("age", .int 42)])

def users : Program :=
  [userDecl, annDecl,
   .val "annName" .str (.path "ann" ["name"]),
   .val "bob" (.named "User") (.update "ann" [("name", .str "Bob")])]

/-- The program compiles to an object literal, a property read, and an update that lists every
    declared field: the new name, and the old age read from `ann`. -/
example : JS.render ((compile users).toOption.getD []) =
    "export const ann = { name: \"Ann\", age: 42 };\nexport const annName = ann.name;\nexport const bob = { name: \"Bob\", age: ann.age };\n" := rfl

def userRecs : Recs := [("User", [("name", .str), ("age", .int)])]

/-- Slice 1's checks still hold: a name read before its line is a ReferenceError. -/
example : JS.run [⟨"a", .atom (.path "b" [])⟩, ⟨"b", .atom (.num 1)⟩] = .error (.reference "b") := rfl
example : (check [.val "a" .int (.atom (.var "b")), .val "b" .int (.atom (.int 1))]).toOption = none := rfl

/-! ### Reading a field the record doesn't declare -/

/-- V8 gives `undefined`, and the model a value of no type. -/
example : JS.run [⟨"ann", .obj [("name", .str "Ann"), ("age", .num 42)]⟩, ⟨"e", .atom (.path "ann" ["email"])⟩] =
    .ok [("e", .notOwn), ("ann", .obj [("name", .str "Ann"), ("age", .num 42)])] := rfl
theorem notOwn_untyped {recs τ} : ¬ ValOf recs .notOwn τ := fun h => by cases h
example : (check (users ++ [.val "e" .str (.path "ann" ["email"])])).toOption = none := rfl

/-- Reading a field of an `Int` is the same: no error, and no value. -/
example : JS.readPath (.num 42) ["name"] = .notOwn := rfl
example : (check (users ++ [.val "n" .int (.atom (.int 1)), .val "e" .str (.path "n" ["name"])])).toOption = none := rfl

/-! ### A literal missing a field, or carrying one more -/

/-- Missing `age`: the object isn't a `User`. -/
example : ¬ ValOf userRecs (.obj [("name", .str "Ann")]) (.record "User") := by
  intro h; cases h with
  | obj hl hk _ =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hk "age"; simp [lookup] at this
example : (check [userDecl, .val "a" (.named "User") (.record [("name", .str "Ann")])]).toOption = none := rfl

/-- A smuggled `admin` field: the object isn't a `User` either, since a record has exactly its fields. -/
example : ¬ ValOf userRecs (.obj [("name", .str "Ann"), ("age", .num 42), ("admin", .num 1)]) (.record "User") := by
  intro h; cases h with
  | obj hl hk _ =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hk "admin"; simp [lookup] at this
example : (check [userDecl, .val "a" (.named "User")
    (.record [("name", .str "Ann"), ("age", .int 42), ("admin", .int 1)])]).toOption = none := rfl

/-! ### Labels V8 treats specially -/

/-- Two equal keys: V8 keeps the last. The model refuses it. -/
example : JS.run [⟨"a", .obj [("age", .num 1), ("age", .str "x")]⟩] =
    .error (.unmodeled "two equal keys: V8 keeps the last") := rfl
example : (check [userDecl, .val "a" (.named "User")
    (.record [("name", .str "Ann"), ("age", .int 1), ("age", .int 2)])]).toOption = none := rfl

/-- `__proto__: v` sets the prototype instead of making a field. The model refuses it. -/
example : (match JS.run [⟨"a", .obj [("__proto__", .num 1)]⟩] with | .error (.unmodeled _) => true | _ => false) = true := rfl
example : (check [.record "P" [("__proto__", .int)]]).toOption = none := rfl

/-! ### An update -/

/-- A new value of the wrong type: the object isn't a `User`. -/
example : ¬ ValOf userRecs (.obj [("name", .str "Bob"), ("age", .str "old")]) (.record "User") := by
  intro h; cases h with
  | obj hl _ hp =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hp "age" (.str "old") .int (by simp [lookup]) (by simp [lookup]); cases this
example : (check [userDecl, annDecl, .val "b" (.named "User") (.update "ann" [("age", .str "old")])]).toOption = none := rfl

/-- A field the record doesn't declare. -/
example : (check [userDecl, annDecl, .val "b" (.named "User") (.update "ann" [("email", .str "x")])]).toOption = none := rfl

/-! ### Nominal records -/

/-- Two records with the same fields are different types: a `Pet` is not a `User`. -/
example : (check [userDecl, .record "Pet" [("name", .str), ("age", .int)],
    .val "p" (.named "Pet") (.record [("name", .str "Rex"), ("age", .int 3)]),
    .val "u" (.named "User") (.atom (.var "p"))]).toOption = none := rfl

end LScript
