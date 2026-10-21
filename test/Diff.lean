import LScript.JS

/-!
# The model against Node, on modules no one wrote

`test/v8.mjs` checks the model on cases chosen by hand, and every break a review has found in the model
was a case no one had written down. This executable writes the cases instead. It generates random
modules of the model's fragment, `JS.Program` rather than LScript source, so it reaches rules no
accepted program uses yet. It draws names and labels from pools `test/diff.mjs` takes from the engine:
every global, every property along the prototype chain of each kind of value the model holds, the
spec's reserved and contextual words, and every identifier the printer itself writes.

Each declaration is run by the model as it is generated, and one the model refuses is drawn again, so
every module printed is one the model runs without an error. For each, it prints the module's text,
what the model says each export holds, and calls of the exported functions, with what the model says
each call returns. An entry is called with text: the model gets the value `JSON.parse` gives for it,
or `undefined` for text that doesn't parse and for anything that isn't a string.

Only one direction is checked. Where the model gives an error, V8 may still run the module, which
makes the model stricter, not wrong, so those are only counted. Where the model gives a value, V8 must
give the same one.

    difftest SEED COUNT POOLS
-/

open LScript.JS
open LScript (lookup)

namespace Diff

instance : Inhabited Val := ⟨.null⟩

structure St where
  gen : StdGen
  tally : List (String × Nat) := []

abbrev G := StateM St

def below (n : Nat) : G Nat := do
  if n == 0 then return 0
  let st ← get
  let (k, g) := randNat st.gen 0 (n - 1)
  set { st with gen := g }
  return k

def pct (p : Nat) : G Bool := return (← below 100) < p

def pick {α : Type} [Inhabited α] (xs : Array α) : G α := do
  let i ← below xs.size
  return xs[i]!

def shuffle {α : Type} (xs : Array α) : G (Array α) := do
  let mut a := xs
  for i in [0:a.size] do
    let j ← below (a.size - i)
    a := a.swapIfInBounds i (i + j)
  return a

def bump (k : String) : List (String × Nat) → List (String × Nat)
  | [] => [(k, 1)]
  | (k', n) :: rest => if k == k' then (k', n + 1) :: rest else (k', n) :: bump k rest

def count (k : String) : G Unit := modify fun st => { st with tally := bump k st.tally }

/-! ## Strings as UTF-16

The model holds a string as code units, one Lean character each. A surrogate, which a Lean character
can't be, is held here as the character 0xF0000 above it, in a private-use plane. -/

def unitChar (u : Nat) : Char := if 0xD800 ≤ u ∧ u ≤ 0xDFFF then Char.ofNat (0xF0000 + u) else Char.ofNat u

def charUnits (c : Char) : List Nat :=
  let n := c.toNat
  if 0xFD800 ≤ n ∧ n ≤ 0xFDFFF then [n - 0xF0000]
  else if n < 0x10000 then [n]
  else [0xD800 + (n - 0x10000) / 0x400, 0xDC00 + (n - 0x10000) % 0x400]

def strOfUnits (us : List Nat) : String := String.mk (us.map unitChar)

def unitsOf (s : String) : List Nat := s.toList.flatMap charUnits

def hex4 (u : Nat) : String :=
  let s := String.mk (Nat.toDigits 16 u)
  "".pushn '0' (4 - s.length) ++ s

/-- A JSON string literal holding exactly the code units of `s`. -/
def quote (s : String) : String := Id.run do
  let mut out := "\""
  for u in unitsOf s do
    if u == 34 then out := out ++ "\\\""
    else if u == 92 then out := out ++ "\\\\"
    else if u < 32 || u > 126 then out := out ++ "\\u" ++ hex4 u
    else out := out.push (Char.ofNat u)
  return out ++ "\""

def jobj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map fun (k, v) => quote k ++ ":" ++ v) ++ "}"

def jarr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def tag (t : String) : String := jobj [("t", quote t)]

/-- What the model says a value is, for `test/diff.mjs` to hold Node's value to. -/
partial def desc : Val → String
  | .num n => jobj [("t", quote "num"), ("v", quote (toString n))]
  | .notInt => tag "notInt"
  | .negZero => tag "negZero"
  | .str s => jobj [("t", quote "str"), ("v", quote s)]
  | .bool b => jobj [("t", quote "bool"), ("v", toString b)]
  | .null => tag "null"
  | .undef => tag "undef"
  | .arr vs => jobj [("t", quote "arr"), ("v", jarr (vs.map desc))]
  | .obj fs frozen => jobj [("t", quote "obj"), ("frozen", toString frozen), ("v", jarr (fs.map fun (l, v) => jarr [quote l, desc v]))]
  | .untracked => tag "any"
  | .clos .. => tag "fn"
  | .entryOf _ => tag "fn"

def kindOf : Val → String
  | .num _ => "num" | .notInt => "notInt" | .negZero => "negZero" | .str _ => "str" | .bool _ => "bool"
  | .null => "null" | .undef => "undef" | .arr _ => "arr" | .obj _ _ => "obj" | .untracked => "untracked"
  | .clos .. => "function" | .entryOf _ => "entry"

def errKind : Err → String
  | .syntax _ => "syntax" | .reference _ => "reference" | .unmodeled _ => "unmodeled"
  | .notCallable => "notCallable" | .nullRead _ => "nullRead" | .outOfFuel => "outOfFuel"

/-! ## Modules -/

structure Pools where
  names : Array String
  labels : Array String

/-- What generation knows at a point in a module. -/
structure Sc where
  top : List (String × Val) := []          -- the names declared so far, with the values the model gave them
  params : List String := []               -- the parameters in scope, whose values aren't known
  labels : Array String := #["a", "b", "name", "age"]  -- labels the module has used

def nums : Array Int :=
  #[0, 1, -1, 7, 42, maxSafe, -maxSafe, maxSafe + 1, -(maxSafe + 1), 2 ^ 53 + 1, 10 ^ 21, 10 ^ 400, -(10 ^ 400)]

def strs : Array String :=
  #["", "a", "Ann", " ", "then", "__proto__", "constructor", "x y", "'", "`${x}`", "-0", "1e400", "\"", "\\", "é", "\n"]

def paramNames : Array String := #["x", "y", "z", "j", "v"]

def declNames : Array String := #["a", "b", "c", "d", "f", "g", "h", "k", "m", "n", "u", "w"]

def genName (p : Pools) (sc : Sc) : G String := do
  let near := sc.params ++ sc.top.map Prod.fst
  if !near.isEmpty && (← pct 85) then pick near.toArray else pick p.names

/-- A label to read from a value: usually one of its own fields, if the model knows it. -/
def genLabel (p : Pools) (sc : Sc) (v : Option Val) : G String := do
  if let some (.obj fs _) := v then
    if !fs.isEmpty && (← pct 70) then return ← pick (fs.map Prod.fst).toArray
  if (← pct 60) then pick sc.labels else pick p.labels

def genPath (p : Pools) (sc : Sc) : G Atom := do
  let x ← genName p sc
  let k ← pick #[0, 0, 0, 1, 1, 2]
  let mut v := lookup sc.top x
  let mut ls : Array String := #[]
  for _ in [0:k] do
    let l ← genLabel p sc v
    ls := ls.push l
    v := v.bind fun w => (readField w l).toOption
  return .path x ls.toList

def genAtom (p : Pools) (sc : Sc) : G Atom := do
  match ← below 10 with
  | 0 | 1 => return .num (← pick nums)
  | 2 => return .str (← pick strs)
  | _ => genPath p sc

def genShapeLabels (p : Pools) (sc : Sc) (a : Atom) : G (List String) := do
  if let .path x ls := a then
    if let some (.obj fs _) := (lookup sc.top x).bind fun v => (readPath v ls).toOption then
      if (← pct 60) then return fs.map Prod.fst
  let n ← below 3
  let mut ls : Array String := #[]
  for _ in [0:n] do
    ls := ls.push (← genLabel p sc none)
  return ls.toList

def genLeafTest (p : Pools) (sc : Sc) : G Test := do
  let a ← genAtom p sc
  match ← below 3 with
  | 0 => return .isStr a
  | 1 => return .isInt a
  | _ => return .isShape a (← genShapeLabels p sc a)

def genTest (p : Pools) (sc : Sc) : Nat → G Test
  | 0 => genLeafTest p sc
  | d + 1 => do
    if (← pct 25) then return .and (← genTest p sc d) (← genTest p sc d)
    genLeafTest p sc

def genObj (p : Pools) (sc : Sc) : G Expr := do
  let n ← below 4
  let mut fs : Array (String × Atom) := #[]
  for _ in [0:n] do
    let l ← if (← pct 70) then pick sc.labels else pick p.labels
    fs := fs.push (l, ← genAtom p sc)
  return .obj fs.toList

def genExpr (p : Pools) : Sc → Nat → G Expr
  | sc, 0 => do
    if (← pct 80) then return .atom (← genAtom p sc)
    genObj p sc
  | sc, d + 1 => do
    match ← below 12 with
    | 0 | 1 | 2 => return .atom (← genAtom p sc)
    | 3 => genObj p sc
    | 4 | 5 =>
      let x ← if (← pct 70) then pick paramNames else pick p.names
      return .arrow x (← genExpr p { sc with params := x :: sc.params } d)
    | 6 | 7 | 8 =>
      let fns := ((sc.top.filter fun (_, v) => callable v).map Prod.fst ++ sc.params).toArray
      let f ← match ← below 10 with
        | 0 | 1 | 2 | 3 | 4 =>
          if fns.isEmpty then genExpr p sc d else do return .atom (.path (← pick fns) [])
        | 5 | 6 | 7 => do
          let x ← pick paramNames
          return .arrow x (← genExpr p { sc with params := x :: sc.params } d)
        | _ => genExpr p sc d
      return .app f (← genExpr p sc d)
    | 9 | 10 => return .cond (← genTest p sc 2) (← genExpr p sc d) (← genExpr p sc d)
    | _ =>
      if (← pct 70) then
        let x ← pick paramNames
        return .entry (.arrow x (← genExpr p { sc with params := x :: sc.params } d))
      return .entry (← genExpr p sc d)

def objLabels : Expr → List String
  | .obj fs => fs.map Prod.fst
  | .arrow _ b => objLabels b
  | .app f a => objLabels f ++ objLabels a
  | .cond _ a b => objLabels a ++ objLabels b
  | .entry e => objLabels e
  | .atom _ => []

def testShapes : Test → List (List String)
  | .isShape _ ls => [ls]
  | .and t u => testShapes t ++ testShapes u
  | _ => []

/-- The label lists the module's shape tests look for, so that an entry can be given text that passes. -/
def shapes : Expr → List (List String)
  | .cond t a b => testShapes t ++ shapes a ++ shapes b
  | .arrow _ b => shapes b
  | .app f a => shapes f ++ shapes a
  | .entry e => shapes e
  | _ => []

def fuel : Nat := 16

def genDecl (p : Pools) (sc : Sc) : G Decl := do
  let name ← if (← pct 35) then pick p.names else pick declNames
  let e ← genExpr p sc (← pick #[1, 2, 2, 3, 3, 4])
  return { name, e, exported := ← pct 75 }

/-- A module the model runs without an error: a declaration it refuses is drawn again. -/
def genModule (p : Pools) : G (Program × List (String × Val)) := do
  let n ← pick #[1, 2, 3, 4, 5, 6, 8]
  let mut sc : Sc := {}
  let mut prog : Array Decl := #[]
  for _ in [0:n] do
    for _ in [0:30] do
      let d ← genDecl p sc
      match runFrom fuel sc.top [d] with
      | .ok env =>
        sc := { sc with top := env, labels := sc.labels ++ (objLabels d.e).toArray }
        prog := prog.push d
        break
      | .error e => count s!"declaration refused: {errKind e}"
  return (prog.toList, sc.top)

/-! ## Arguments, and text for entries -/

def safeNums : Array Int := #[0, 1, -1, 42, maxSafe, -maxSafe]

def notInts : Array String := #["1.5", "NaN", "Infinity", "-Infinity", "1e400", "9007199254740992", "-9007199254740993"]

def someUnits : Array Nat :=
  #[97, 98, 65, 32, 34, 92, 0, 10, 31, 127, 0xE9, 0x2028, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xFEFF, 0xFFFF]

def genUnits : G (List Nat) := do
  let n ← below 5
  let mut us : Array Nat := #[]
  for _ in [0:n] do
    if (← pct 10) then us := us ++ #[0xD83D, 0xDE00]
    else us := us.push (← pick someUnits)
  return us.toList

def genScalar : G (String × Val) := do
  match ← below 7 with
  | 0 => let n ← pick safeNums; return (desc (.num n), .num n)
  | 1 => return (desc .negZero, .negZero)
  | 2 => let t ← pick notInts; return (jobj [("t", quote "notInt"), ("v", quote t)], .notInt)
  | 3 => let s := strOfUnits (← genUnits); return (desc (.str s), .str s)
  | 4 => let b ← pct 50; return (desc (.bool b), .bool b)
  | 5 => return (desc .null, .null)
  | _ => return (desc .undef, .undef)

/-- A value an importer can build, described for `test/diff.mjs`, with the value the model gets. -/
def genData (keys : Array String) : Nat → G (String × Val)
  | 0 => genScalar
  | d + 1 => do
    match ← below 10 with
    | 0 =>
      let mut ds : Array String := #[]
      let mut vs : Array Val := #[]
      for _ in [0:← below 3] do
        let (a, w) ← genData keys d
        ds := ds.push a
        vs := vs.push w
      return (jobj [("t", quote "arr"), ("v", jarr ds.toList)], .arr vs.toList)
    | 1 | 2 | 3 =>
      let mut fs : Array (String × String × Val) := #[]
      for _ in [0:← below 4] do
        let l ← pick keys
        if !fs.any (·.1 == l) then
          let (a, w) ← genData keys d
          fs := fs.push (l, a, w)
      let frozen ← pct 50
      return (jobj [("t", quote "obj"), ("frozen", toString frozen), ("v", jarr (fs.toList.map fun (l, a, _) => jarr [quote l, a]))],
        .obj (fs.toList.map fun (l, _, w) => (l, w)) frozen)
    | _ => genScalar

def jsonNums : Array (String × Val) :=
  #[("0", .num 0), ("-0", .negZero), ("42", .num 42), ("4.2e1", .num 42), ("1.0", .num 1), ("1E2", .num 100),
    ("0.0", .num 0), ("-0.0", .negZero), ("1.5", .notInt), ("1e400", .notInt), ("-1e400", .notInt), ("1e-400", .num 0),
    ("-1e-400", .negZero), ("9007199254740991", .num maxSafe), ("-9007199254740991", .num (-maxSafe)),
    ("9007199254740992", .notInt), ("9007199254740993", .notInt), ("5e-1", .notInt), ("123456789012345678901234567890", .notInt)]

/-- Text `JSON.parse` refuses. -/
def badTexts : Array String :=
  #["", " ", "{", "}", "[1,]", "{\"a\":1,}", "01", "+1", "NaN", "Infinity", "'a'", "{a:1}", "\"\\x41\"", "\"\t\"",
    "1 2", "undefined", ".5", "1.", "[", "\"\\ud800", "\uFEFF1", "{\"a\" 1}", "tru", "-", "1e", "0x10", "[1,,2]"]

def ws : G String := pick #["", "", "", " ", "\n", "\t", "\r\n"]

/-- A JSON string literal for the code units, each written as itself or escaped. -/
def jsonStr (us : List Nat) : G String := do
  let mut out := "\""
  for u in us do
    if u == 34 then out := out ++ (← pick #["\\\"", "\\u0022"])
    else if u == 92 then out := out ++ (← pick #["\\\\", "\\u005C"])
    else if u < 32 || (← pct 40) then out := out ++ "\\u" ++ hex4 u
    else out := out.push (unitChar u)
  return out ++ "\""

/-- Of two equal keys, `JSON.parse` keeps the last value, where the first was. -/
def lastWins (fs : List (String × Val)) : List (String × Val) :=
  (fs.map Prod.fst).eraseDups.map fun k => (k, (lookup fs.reverse k).get!)

def genJsonLeaf : G (String × Val) := do
  match ← below 6 with
  | 0 | 1 => pick jsonNums
  | 2 | 3 => let us ← genUnits; return (← jsonStr us, .str (strOfUnits us))
  | 4 => pick #[("true", .bool true), ("false", .bool false)]
  | _ => return ("null", .null)

def genJson (keys : Array String) (shapes : Array (List String)) : Nat → G (String × Val)
  | 0 => genJsonLeaf
  | d + 1 => do
    match ← below 10 with
    | 0 | 1 | 2 | 3 => genJsonLeaf
    | 4 =>
      let mut ts : Array String := #[]
      let mut vs : Array Val := #[]
      for _ in [0:← below 3] do
        let (t, v) ← genJson keys shapes d
        ts := ts.push ((← ws) ++ t ++ (← ws))
        vs := vs.push v
      return ("[" ++ ",".intercalate ts.toList ++ "]", .arr vs.toList)
    | _ =>
      let base ← if !shapes.isEmpty && (← pct 70) then pick shapes else do
        let mut ks : Array String := #[]
        for _ in [0:← below 4] do
          ks := ks.push (← pick keys)
        pure ks.toList
      let mut ks ← shuffle base.toArray
      if (← pct 15) then ks := ks.push (← pick keys)
      let mut ts : Array String := #[]
      let mut fs : Array (String × Val) := #[]
      for k in ks do
        let (t, v) ← genJson keys shapes d
        ts := ts.push ((← ws) ++ (← jsonStr (unitsOf k)) ++ (← ws) ++ ":" ++ (← ws) ++ t ++ (← ws))
        fs := fs.push (k, v)
      return ("{" ++ ",".intercalate ts.toList ++ "}", .obj (lastWins fs.toList) false)

/-- What an importer hands an entry, and the value the model's parse function gets for it. -/
def genInput (keys : Array String) (shapes : Array (List String)) : G (String × Val) := do
  match ← below 20 with
  | 0 | 1 | 2 => let t ← pick badTexts; return (desc (.str t), .undef)
  | 3 | 4 | 5 =>
    let (a, w) ← genData keys 2
    match w with
    | .str _ => return (desc .undef, .undef)
    | _ => return (a, .undef)
  | 6 => return (jobj [("t", quote "hostile"), ("v", quote (← pick #["proxy", "stringObject", "symbol", "bigint", "function"]))], .undef)
  | _ => let (t, j) ← genJson keys shapes 3; let t := (← ws) ++ t ++ (← ws); return (desc (.str t), j)

def probe (f : String) (args : List String) (r : Val) : String :=
  jobj [("f", quote f), ("args", jarr args), ("want", desc r)]

/-- Calls of an exported function, with what the model says each returns. -/
def genProbe (keys : Array String) (shapes : Array (List String)) (exports : List (String × Val)) (f : String) :
    Val → G (Option String)
  | .entryOf c => do
    let (a, j) ← genInput keys shapes
    match applyVal fuel c j with
    | .ok r => count s!"call returned {kindOf r}"; return some (probe f [a] r)
    | .error e => count s!"call refused: {errKind e}"; return none
  | v@(.clos ..) => do
    let mut cur := v
    let mut args : Array String := #[]
    for _ in [0:← pick #[1, 1, 1, 2]] do
      let (a, w) ← if !exports.isEmpty && (← pct 20) then do
          let (x, w) ← pick exports.toArray
          pure (jobj [("t", quote "ref"), ("v", quote x)], w)
        else genData keys 2
      args := args.push a
      match applyVal fuel cur w with
      | .ok r => cur := r
      | .error e => count s!"call refused: {errKind e}"; return none
    count s!"call returned {kindOf cur}"
    return some (probe f args.toList cur)
  | _ => return none

def genCase (p : Pools) : G String := do
  let (prog, env) ← genModule p
  count "module"
  let exports := prog.filter (·.exported) |>.filterMap fun d => (lookup env d.name).map (d.name, ·)
  for (_, v) in exports do count s!"export {kindOf v}"
  let labels := (prog.flatMap fun d => objLabels d.e) ++ (prog.flatMap fun d => (shapes d.e).flatten)
  let keys := (labels ++ ["a", "name", "__proto__", "then", "constructor", "", strOfUnits [97, 0xD800]]).toArray
  let shapeList := (prog.flatMap fun d => shapes d.e).toArray
  let mut probes : Array String := #[]
  for (f, v) in exports do
    for _ in [0:4] do
      if let some pr ← genProbe keys shapeList exports f v then probes := probes.push pr
  return jobj [("src", quote (render prog)), ("exports", jarr (exports.map fun (x, v) => jarr [quote x, desc v])),
    ("probes", jarr probes.toList)]

/-- A module that uses every form the printer has, whose text gives the identifiers the printer writes. -/
def sample : Program :=
  [{ name := "q", exported := true, e := .entry (.arrow "x" (.cond
      (.and (.isStr (.path "x" [])) (.and (.isInt (.path "x" [])) (.isShape (.path "x" []) ["l"])))
      (.obj [("l", .num 0)]) (.app (.atom (.path "x" [])) (.atom (.path "x" [])))))}]

def printerWords : Array String :=
  let words := ((render sample).split fun c => !isIdentRest c).filter identShape
  (words.eraseDups.filter fun w => !["q", "x", "l"].contains w).toArray

end Diff

open Diff in
def main (args : List String) : IO UInt32 := do
  match args with
  | [seed, n, poolsPath] =>
    let lines := (← IO.FS.readFile poolsPath).splitOn "\n"
    let words (i : Nat) := ((lines.getD i "").splitOn " ").filter (· ≠ "") |>.toArray
    let p : Pools := { names := words 0 ++ printerWords, labels := words 1 ++ printerWords }
    let mut st : St := { gen := mkStdGen seed.toNat! }
    for _ in [0:n.toNat!] do
      let (line, st') := (genCase p).run st
      st := st'
      IO.println line
    for (k, c) in st.tally do IO.eprintln s!"{c} {k}"
    return 0
  | _ =>
    IO.eprintln "usage: difftest SEED COUNT POOLS"
    return 2
