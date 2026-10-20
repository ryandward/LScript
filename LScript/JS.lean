import LScript.Syntax

/-!
# The JavaScript we emit, and a model of how V8 runs it

The compiler emits a module of `export const name = value;` lines, where a value is a literal, a name,
a chain of property reads, or an object literal of those. This file models exactly that fragment:
what each line can evaluate to, and every way it can go wrong. `test/v8.mjs` checks the model against
Node.

* A name that isn't a JavaScript identifier, or is a reserved word, is a SyntaxError. A field label
  may be a reserved word: JavaScript allows those as property names.
* A name declared twice is a SyntaxError.
* Reading a name before its line, or a name never declared, is a ReferenceError.
* A numeric literal denotes a double. Within ±(2^53 − 1) the double is exactly the integer written;
  outside it, V8 rounds, and the model says only that the value isn't the integer written.
* A string literal is printed between double quotes as it is, so it may hold only printable ASCII
  other than `"` and `\`.
* Reading a property the object doesn't hold as its own gives `undefined`, or something inherited
  from a prototype, and reading a property of a number or a string gives `undefined` or a method or a
  length. None of these throws, and the model says only that the value isn't one the object holds
  (`notOwn`).
* In an object literal, V8 keeps the last of two equal keys, and `__proto__: v` sets the prototype
  instead of making a field. The model refuses both (`unmodeled`): it is stricter than V8, so for any
  module it runs without an error, it agrees with V8.
* Every object the module makes is frozen: it is printed as `Object.freeze({ … })`. Writing, adding,
  deleting or redefining a field of it, or changing its prototype, then throws, so code that imports a
  record can't change what it holds. This rests on `Object.freeze` being the built-in; a module that
  binds the name `Object` would shadow it, so the model refuses that name.
-/

namespace LScript.JS

/-- A literal, a name, or a name followed by property reads. -/
inductive Atom where
  | num (n : Int)
  | str (s : String)
  | path (x : String) (labels : List String)      -- x, x.l, x.l.m, …
  deriving Repr, DecidableEq

inductive Expr where
  | atom (a : Atom)
  | obj (fields : List (String × Atom))           -- { l: a, … }
  deriving Repr, DecidableEq

/-- `export const name = e;` -/
structure Decl where
  name : String
  e : Expr
  deriving Repr, DecidableEq

abbrev Program := List Decl

inductive Val where
  | num (n : Int)                       -- a double that is exactly the integer n
  | imprecise                           -- a double that is not the integer the literal wrote
  | str (s : String)
  | obj (fields : List (String × Val)) (frozen : Bool)  -- an object whose own fields are exactly these
  | notOwn                              -- a property the value doesn't hold as its own
  deriving Repr

inductive Err where
  | syntax (msg : String)
  | reference (name : String)
  | unmodeled (msg : String)            -- V8 runs it, differently from what was written
  deriving Repr, DecidableEq

/-- `Number.MAX_SAFE_INTEGER`. -/
def maxSafe : Int := 9007199254740991

def isSafe (n : Int) : Bool := decide (-maxSafe ≤ n) && decide (n ≤ maxSafe)

/-- Reserved words in an ES module, plus `eval` and `arguments`, which strict code can't bind. -/
def reservedWords : List String :=
  ["await", "break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete",
   "do", "else", "enum", "export", "extends", "false", "finally", "for", "function", "if", "import",
   "in", "instanceof", "new", "null", "return", "super", "switch", "this", "throw", "true", "try",
   "typeof", "var", "void", "while", "with", "yield", "implements", "interface", "let", "package",
   "private", "protected", "public", "static", "eval", "arguments"]

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_'

/-- `[A-Za-z_][A-Za-z0-9_]*`. -/
def identShape (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentRest

/-- A name a `const` can bind: the shape, and not reserved. -/
def validIdent (s : String) : Bool := identShape s && !reservedWords.contains s

/-- Globals the emitted code calls. A module binding one of these names would shadow it. -/
def emittedGlobals : List String := ["Object"]

/-- A name a declaration may bind: a valid identifier, not a global the emitted code calls. -/
def bindable (s : String) : Bool := validIdent s && !emittedGlobals.contains s

/-- A field label. JavaScript allows reserved words as property names (`{ class: 1 }`, `o.class`), so a
    label needs only the shape; `__proto__` is excluded, since an object literal treats it specially. -/
def validLabel (s : String) : Bool := identShape s && s != "__proto__"

/-- Printable ASCII other than `"` and `\`: a string that prints between quotes as itself. -/
def validStr (s : String) : Bool :=
  s.toList.all fun c => decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) && c != '"' && c != '\\'

/-- `v.l`: the object's own field, or `notOwn`. -/
def readField : Val → String → Val
  | .obj fs _, l => (lookup fs l).getD .notOwn
  | _, _ => .notOwn

def readPath (v : Val) (ls : List String) : Val := ls.foldl readField v

def evalAtom (env : List (String × Val)) : Atom → Except Err Val
  | .num n => .ok (if isSafe n then .num n else .imprecise)
  | .str s => if validStr s then .ok (.str s) else .error (.syntax s!"string literal {repr s} can't be printed as itself")
  | .path x ls =>
    match lookup env x with
    | some v => .ok (readPath v ls)
    | none => .error (.reference x)

def evalFields (env : List (String × Val)) : List (String × Atom) → Except Err (List (String × Val))
  | [] => .ok []
  | (l, a) :: rest =>
    match evalAtom env a, evalFields env rest with
    | .ok v, .ok vs => .ok ((l, v) :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def evalExpr (env : List (String × Val)) : Expr → Except Err Val
  | .atom a => evalAtom env a
  | .obj fs =>
    if !(fs.map Prod.fst).all validLabel then .error (.unmodeled "a label that isn't a plain identifier, or __proto__, which sets the prototype")
    else if !decide (fs.map Prod.fst).Nodup then .error (.unmodeled "two equal keys: V8 keeps the last")
    else
      match evalFields env fs with
      | .ok vs => .ok (.obj vs true)
      | .error e => .error e

/-- Run the module from an environment of names already declared. -/
def runFrom (env : List (String × Val)) : Program → Except Err (List (String × Val))
  | [] => .ok env
  | d :: ds =>
    if !validIdent d.name then .error (.syntax s!"{d.name} is not an identifier")
    else if emittedGlobals.contains d.name then .error (.unmodeled s!"{d.name} shadows a global the emitted code calls")
    else if (lookup env d.name).isSome then .error (.syntax s!"{d.name} is declared twice")
    else
      match evalExpr env d.e with
      | .ok v => runFrom ((d.name, v) :: env) ds
      | .error e => .error e

def run (p : Program) : Except Err (List (String × Val)) := runFrom [] p

def renderAtom : Atom → String
  | .num n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .path x ls => String.join (x :: ls.map (fun l => "." ++ l))

def renderExpr : Expr → String
  | .atom a => renderAtom a
  | .obj [] => "Object.freeze({})"
  | .obj fs => "Object.freeze({ " ++ ", ".intercalate (fs.map fun (l, a) => l ++ ": " ++ renderAtom a) ++ " })"

/-- The text of the module. -/
def render (p : Program) : String :=
  String.join (p.map fun d => s!"export const {d.name} = {renderExpr d.e};\n")

end LScript.JS
