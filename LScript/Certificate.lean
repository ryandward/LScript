import LScript.Parse
import LScript.Check

/-!
# What `certify/check.sh` has the kernel decide

`compilesTo src out` runs the proved parser and compiler on `src` and compares the JavaScript it prints
with `out`. The kernel decides it by running it, so it is written to run in constant stack: Lean's own
equality of strings inspects the comparison of the rest of the string before it can answer, which
makes the kernel recurse once per character and overflow on a module of a few thousand lines.
`compilesTo_spec` turns its answer back into the equation the check states.
-/

namespace LScript

/-- Equality of character lists by their codes. The recursive call is the result, not something
    inspected, so the kernel runs it as a loop. -/
def charsEq : List Char → List Char → Bool
  | [], [] => true
  | c :: cs, d :: ds => if c.toNat = d.toNat then charsEq cs ds else false
  | _, _ => false

theorem charsEq_eq : ∀ (as bs : List Char), charsEq as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [charsEq] at h
  | _ :: _, [], h => by simp [charsEq] at h
  | c :: cs, d :: ds, h => by
    simp only [charsEq] at h
    split at h
    · rename_i hc
      rw [Char.eq_of_val_eq (UInt32.toNat_inj.mp hc), charsEq_eq cs ds h]
    · cases h

/-- `src` parses, the checker accepts it, and its JavaScript prints as exactly `out`. -/
def compilesTo (src out : String) : Bool :=
  match parse src >>= compile with
  | .ok js => charsEq (JS.render js).data out.data
  | .error _ => false

theorem compilesTo_spec {src out : String} (h : compilesTo src out = true) :
    (parse src >>= compile).toOption.map JS.render = some out := by
  unfold compilesTo at h
  split at h
  · rename_i js hjs
    rw [hjs]
    simp only [Except.toOption, Option.map_some]
    exact congrArg some (String.ext (charsEq_eq _ _ h))
  · cases h

end LScript
