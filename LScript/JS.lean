import LScript.Syntax

/-!
# The JavaScript we emit, and a model of how V8 runs it

The compiler emits a module of `export const name = value;` lines. This file models exactly that
fragment: what each line can evaluate to, and every way it can fail. `test/v8.mjs` checks the model
against Node.

* A name that isn't a JavaScript identifier, or is a reserved word, is a SyntaxError.
* A name declared twice is a SyntaxError.
* Reading a name before its line, or a name never declared, is a ReferenceError.
* A numeric literal denotes a double. Within ±(2^53 − 1) the double is exactly the integer written;
  outside it, V8 rounds, and the model says only that the value isn't the integer written.
* A string literal is printed between double quotes as it is, so it may hold only printable ASCII
  other than `"` and `\`; anything else is a SyntaxError here, since the printed text would not
  denote the same string.
-/

namespace LScript.JS

inductive Expr where
  | num (n : Int)
  | str (s : String)
  | ident (name : String)
  deriving Repr, DecidableEq

/-- `export const name = e;` -/
structure Decl where
  name : String
  e : Expr
  deriving Repr, DecidableEq

abbrev Program := List Decl

inductive Val where
  | num (n : Int)     -- a double that is exactly the integer n
  | imprecise         -- a double that is not the integer the literal wrote
  | str (s : String)
  deriving Repr, DecidableEq

inductive Err where
  | syntax (msg : String)
  | reference (name : String)
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

/-- `[A-Za-z_][A-Za-z0-9_]*`, not reserved: a subset of JavaScript's identifiers. -/
def validIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentRest && !reservedWords.contains s

/-- Printable ASCII other than `"` and `\`: a string that prints between quotes as itself. -/
def validStr (s : String) : Bool :=
  s.toList.all fun c => decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) && c != '"' && c != '\\'

def evalExpr (env : List (String × Val)) : Expr → Except Err Val
  | .num n => .ok (if isSafe n then .num n else .imprecise)
  | .str s => if validStr s then .ok (.str s) else .error (.syntax s!"string literal {repr s} can't be printed as itself")
  | .ident x =>
    match lookup env x with
    | some v => .ok v
    | none => .error (.reference x)

/-- Run the module from an environment of names already declared. -/
def runFrom (env : List (String × Val)) : Program → Except Err (List (String × Val))
  | [] => .ok env
  | d :: ds =>
    if !validIdent d.name then .error (.syntax s!"{d.name} is not an identifier")
    else if (lookup env d.name).isSome then .error (.syntax s!"{d.name} is declared twice")
    else
      match evalExpr env d.e with
      | .ok v => runFrom ((d.name, v) :: env) ds
      | .error e => .error e

def run (p : Program) : Except Err (List (String × Val)) := runFrom [] p

/-- The text of an expression. -/
def renderExpr : Expr → String
  | .num n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .ident x => x

/-- The text of the module. -/
def render (p : Program) : String :=
  String.join (p.map fun d => s!"export const {d.name} = {renderExpr d.e};\n")

end LScript.JS
