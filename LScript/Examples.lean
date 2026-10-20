import LScript.Sound

/-!
# What each load-bearing check prevents

Every check `Check.lean` tags `load-bearing` is shown here, tagged `shows:` with its code, two ways:
the module a compiler without that check would emit either fails in the model of V8 or holds a value
that isn't of its declared type; and the checker rejects the program that would produce it.
`test/checks.sh` requires one example per load-bearing check.
-/

namespace LScript

open JS (Val Err)

def userDecl : Decl := .record "User" [("name", .str), ("age", .int)]
def annDecl : Decl := .val "ann" (.named "User") (.record [("name", .str "Ann"), ("age", .int 42)])
def userRecs : Recs := [("User", [("name", .str), ("age", .int)])]

def users : Program :=
  [userDecl, annDecl,
   .val "annName" .str (.path "ann" ["name"]),
   .val "bob" (.named "User") (.update "ann" [("name", .str "Bob")])]

/-- The program compiles to an object literal, a property read, and an update that lists every
    declared field: the new name, and the old age read from `ann`. -/
example : JS.render ((compile users).toOption.getD []) =
    "export const ann = { name: \"Ann\", age: 42 };\nexport const annName = ann.name;\nexport const bob = { name: \"Bob\", age: ann.age };\n" := rfl

theorem notOwn_untyped {recs τ} : ¬ ValOf recs .notOwn τ := fun h => by cases h

/-! ### Names -/

-- shows: val-ident
/-- A reserved word: a SyntaxError. -/
example : JS.run [⟨"class", .atom (.num 1)⟩] = .error (.syntax "class is not an identifier") := rfl
example : (check [.val "class" .int (.atom (.int 1))]).toOption = none := rfl

-- shows: val-fresh
/-- A name declared twice: a SyntaxError. -/
example : JS.run [⟨"a", .atom (.num 1)⟩, ⟨"a", .atom (.num 2)⟩] = .error (.syntax "a is declared twice") := rfl
example : (check [.val "a" .int (.atom (.int 1)), .val "a" .int (.atom (.int 2))]).toOption = none := rfl

/-! ### Literals -/

-- shows: int-safe
/-- An integer V8 can't hold: no error, but the value isn't the integer written. -/
example : JS.run [⟨"big", .atom (.num 9007199254740993)⟩] = .ok [("big", .imprecise)] := rfl
example : ¬ ValOf [] .imprecise .int := fun h => by cases h
example : (check [.val "big" .int (.atom (.int 9007199254740993))]).toOption = none := rfl

-- shows: string-printable
/-- A string that wouldn't print as itself: a SyntaxError in the model. -/
example : (match JS.run [⟨"s", .atom (.str "a\\b")⟩] with | .error (.syntax _) => true | _ => false) = true := rfl
example : (check [.val "s" .str (.atom (.str "a\\b"))]).toOption = none := rfl

/-! ### Types of values -/

-- shows: atom-type
/-- A `Pet` where a `User` is declared: the object lacks `age`, so it isn't a `User`. -/
example : ¬ ValOf (("Pet", [("name", .str)]) :: userRecs) (.obj [("name", .str "Rex")]) (.record "User") := by
  intro h; cases h with
  | obj hl hk _ =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hk "age"; simp [lookup] at this
example : (check [userDecl, .record "Pet" [("name", .str)],
    .val "rex" (.named "Pet") (.record [("name", .str "Rex")]),
    .val "u" (.named "User") (.atom (.var "rex"))]).toOption = none := rfl

-- shows: read-type
/-- A `String` read where an `Int` is declared. -/
example : ¬ ValOf [] (.str "Ann") .int := fun h => by cases h
example : (check (users ++ [.val "age" .int (.path "ann" ["name"])])).toOption = none := rfl

/-! ### Record literals -/

-- shows: literal-complete
/-- Missing `age`: the object isn't a `User`. -/
example : ¬ ValOf userRecs (.obj [("name", .str "Ann")]) (.record "User") := by
  intro h; cases h with
  | obj hl hk _ =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hk "age"; simp [lookup] at this
example : (check [userDecl, .val "a" (.named "User") (.record [("name", .str "Ann")])]).toOption = none := rfl

-- shows: field-declared
/-- A smuggled `admin` field: the object isn't a `User`, since a record has exactly its fields. -/
example : ¬ ValOf userRecs (.obj [("name", .str "Ann"), ("age", .num 42), ("admin", .num 1)]) (.record "User") := by
  intro h; cases h with
  | obj hl hk _ =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hk "admin"; simp [lookup] at this
example : (check [userDecl, .val "a" (.named "User")
    (.record [("name", .str "Ann"), ("age", .int 42), ("admin", .int 1)])]).toOption = none := rfl

-- shows: field-type
/-- A field of the wrong type: the object isn't a `User`. -/
example : ¬ ValOf userRecs (.obj [("name", .str "Bob"), ("age", .str "old")]) (.record "User") := by
  intro h; cases h with
  | obj hl _ hp =>
    simp only [userRecs, lookup] at hl; cases hl
    have := hp "age" (.str "old") .int (by simp [lookup]) (by simp [lookup]); cases this
example : (check [userDecl, annDecl, .val "b" (.named "User") (.update "ann" [("age", .str "old")])]).toOption = none := rfl

-- shows: literal-distinct
/-- Two equal keys: V8 keeps the last. The model refuses it. -/
example : JS.run [⟨"a", .obj [("age", .num 1), ("age", .str "x")]⟩] =
    .error (.unmodeled "two equal keys: V8 keeps the last") := rfl
example : (check [userDecl, .val "a" (.named "User")
    (.record [("name", .str "Ann"), ("age", .int 1), ("age", .int 2)])]).toOption = none := rfl

/-! ### Updates -/

-- shows: update-type
/-- An update of a `Pet` declared a `User`: the new object has the `Pet`'s fields, so it lacks `age`. -/
example : JS.run [⟨"rex", .obj [("name", .str "Rex")]⟩, ⟨"u", .obj [("name", .path "rex" ["name"])]⟩] =
    .ok [("u", .obj [("name", .str "Rex")]), ("rex", .obj [("name", .str "Rex")])] := rfl
example : (check [userDecl, .record "Pet" [("name", .str)],
    .val "rex" (.named "Pet") (.record [("name", .str "Rex")]),
    .val "u" (.named "User") (.update "rex" [])]).toOption = none := rfl

/-! ### Record declarations -/

-- shows: record-labels
/-- A `__proto__` label sets the prototype instead of making a field. The model refuses it. -/
example : (match JS.run [⟨"a", .obj [("__proto__", .num 1)]⟩] with | .error (.unmodeled _) => true | _ => false) = true := rfl
example : (check [.record "P" [("__proto__", .int)]]).toOption = none := rfl

-- shows: record-fresh
/-- A record declared again with other fields: an earlier value of the first `R` would be read as the
    second, and its field `b` isn't there. -/
example : JS.run [⟨"x", .obj [("a", .num 1)]⟩, ⟨"y", .atom (.path "x" ["b"])⟩] =
    .ok [("y", .notOwn), ("x", .obj [("a", .num 1)])] := rfl
example : (check [.record "R" [("a", .int)], .val "x" (.named "R") (.record [("a", .int 1)]),
    .record "R" [("b", .str)], .val "y" .str (.path "x" ["b"])]).toOption = none := rfl

end LScript
