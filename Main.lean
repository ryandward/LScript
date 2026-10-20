import LScript

open LScript

/-- The certificate for one compiled file: a Lean file in which Lean's kernel runs the proved
    compiler on the source text and checks the output text, so the run doesn't rest on the binary. -/
def certificate (name source mjs : String) : String := s!"import LScript
open LScript

/-- The text of {name}.ls. -/
def source : String := {repr source}

/-- The text of {name}.mjs. -/
def output : String := {repr mjs}

/-- Lean's kernel runs the proved compiler on the source text: it parses, the checker accepts it, and
    its JavaScript prints as exactly the output text. -/
theorem compiled : (parse source >>= compile).toOption.map JS.render = some output := by decide +kernel

/-- So that module runs without an error, and every name holds a value of its declared type. -/
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

#print axioms sound
"

/-- `lscript FILE.ls` writes FILE.mjs and prints its path, or prints why the program is rejected.
    `lscript --certificate FILE.ls` also writes FILE.cert.lean, which `lake env lean` checks. -/
def main (args : List String) : IO UInt32 := do
  let (cert, path) ← match args with
    | [path] => pure (false, path)
    | ["--certificate", path] => pure (true, path)
    | _ => do
      IO.eprintln "usage: lscript [--certificate] FILE.ls"
      return 2
  let src ← IO.FS.readFile path
  match parse src >>= compile with
  | .ok js =>
    let file := System.FilePath.mk path
    let out := file.withExtension "mjs"
    let mjs := JS.render js
    IO.FS.writeFile out mjs
    IO.println out
    if cert then
      let certFile := file.withExtension "cert.lean"
      IO.FS.writeFile certFile (certificate (file.fileStem.getD "program") src mjs)
      IO.println certFile
    return 0
  | .error e =>
    IO.eprintln s!"{path}: {e}"
    return 1
