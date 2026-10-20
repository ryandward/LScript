import LScript.JS

/-!
# The checker and the emitter

The checker reads declarations in order. A name is usable only after its declaration, so there is
no reading before initialization; a name is declared once; and a value's type must be the declared
type exactly, after aliases are followed. An integer literal must be one JavaScript holds exactly.
-/

namespace LScript

structure Ctx where
  types : List (String × Ty)    -- aliases declared so far, resolved
  vals : List (String × Ty)     -- values declared so far

def Ctx.empty : Ctx := ⟨[], []⟩

def resolve (types : List (String × Ty)) : TyName → Except String Ty
  | .int => .ok .int
  | .str => .ok .str
  | .alias a =>
    match lookup types a with
    | some t => .ok t
    | none => .error s!"type {a} is not declared before this line"

def typeOf (ctx : Ctx) : Expr → Except String Ty
  | .int n =>
    if JS.isSafe n then .ok .int
    else .error s!"{n} is outside the safe integers, -(2^53 - 1) to 2^53 - 1, so JavaScript would hold a different number"
  | .str s =>
    if JS.validStr s then .ok .str
    else .error s!"string literal {repr s} may hold only printable ASCII other than \" and \\"
  | .var x =>
    match lookup ctx.vals x with
    | some t => .ok t
    | none => .error s!"{x} is not declared before this line"

def tyName : Ty → String
  | .int => "Int"
  | .str => "String"

def checkDecl (ctx : Ctx) : Decl → Except String Ctx
  | .type a rhs =>
    if a == "Int" || a == "String" then .error s!"{a} is a base type and can't be redeclared"
    else if (lookup ctx.types a).isSome then .error s!"type {a} is declared twice"
    else
      match resolve ctx.types rhs with
      | .ok t => .ok { ctx with types := (a, t) :: ctx.types }
      | .error e => .error e
  | .val x tn e =>
    if !JS.validIdent x then .error s!"{x} is not a name JavaScript allows"
    else if (lookup ctx.vals x).isSome then .error s!"{x} is declared twice"
    else
      match resolve ctx.types tn, typeOf ctx e with
      | .ok t, .ok t' =>
        if t' = t then .ok { ctx with vals := (x, t) :: ctx.vals }
        else .error s!"{x} is declared {tyName t}, and its value is {tyName t'}"
      | .error err, _ => .error err
      | .ok _, .error err => .error err

def checkFrom (ctx : Ctx) : Program → Except String Ctx
  | [] => .ok ctx
  | d :: ds =>
    match checkDecl ctx d with
    | .ok ctx' => checkFrom ctx' ds
    | .error e => .error e

def check (p : Program) : Except String Ctx := checkFrom .empty p

def emitExpr : Expr → JS.Expr
  | .int n => .num n
  | .str s => .str s
  | .var x => .ident x

/-- Types are erased; each value declaration becomes one `export const`. -/
def emit : Program → JS.Program
  | [] => []
  | .type .. :: ds => emit ds
  | .val x _ e :: ds => ⟨x, emitExpr e⟩ :: emit ds

def compile (p : Program) : Except String JS.Program :=
  match check p with
  | .ok _ => .ok (emit p)
  | .error e => .error e

end LScript
