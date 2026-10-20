import LScript

open LScript

/-- `lscript FILE.ls` writes FILE.mjs and prints its path, or prints why the program is rejected. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let src ← IO.FS.readFile path
    match parse src >>= compile with
    | .ok js =>
      let out := (System.FilePath.mk path).withExtension "mjs"
      IO.FS.writeFile out (JS.render js)
      IO.println out
      return 0
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      return 1
  | _ =>
    IO.eprintln "usage: lscript FILE.ls"
    return 2
