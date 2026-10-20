import LScript
import Lean

/-!
# Checking one compiled program

`certify/check.sh F.ls` runs this file with `LSCRIPT_SOURCE` and `LSCRIPT_OUTPUT` naming `F.ls` and the
`F.mjs` beside it. Lean reads both files from disk, and its kernel runs the proved parser and compiler on
the source text and checks that the program is accepted and that its JavaScript prints as exactly the
output file. The statement and the axiom check belong to this file, not to the compiler that wrote
`F.mjs`, so a run checked here rests on neither the compiler binary nor the parser.
-/

open Lean Elab Term in
/-- The text of the file the environment variable names, read when this file is checked. -/
elab "include_str_env% " var:str : term => do
  let name := var.getString
  let some path ← IO.getEnv name | throwError s!"{name} is not set"
  return mkStrLit (← IO.FS.readFile path)

namespace LScript.Certify
open LScript

def source : String := include_str_env% "LSCRIPT_SOURCE"
def output : String := include_str_env% "LSCRIPT_OUTPUT"

/-- Lean's kernel runs the proved parser and compiler on the source file: it parses, the checker
    accepts it, and its JavaScript prints as exactly the output file. -/
theorem compiled : (parse source >>= compile).toOption.map JS.render = some output :=
  compilesTo_spec (by decide +kernel : compilesTo source output = true)

/-- So the module in the output file runs without an error, and every name holds a value of its
    declared type. -/
theorem sound : ∃ p js, parse source = .ok p ∧ compile p = .ok js ∧ JS.render js = output ∧
    Conclusion p js := by
  have h := compiled
  cases hp : parse source with
  | error _ => rw [hp] at h; cases h
  | ok p =>
    rw [hp] at h
    cases hc : compile p with
    | error _ => simp [bind, Except.bind, hc, Except.toOption] at h
    | ok js =>
      simp only [bind, Except.bind, hc, Except.toOption, Option.map_some, Option.some.injEq] at h
      exact ⟨p, js, rfl, hc, h, compile_sound_conclusion hc⟩

end LScript.Certify

/-- info: 'LScript.Certify.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LScript.Certify.sound
