import LScript.JS

/-!
# The checker, which emits as it checks

The checker reads declarations in order. A name is usable only after its declaration; a name is
declared once; a value's type must be its declared type exactly, after aliases are followed; and an
integer literal must be one JavaScript holds exactly.

A record type is closed and nominal. A record literal gives every declared field once and no other,
each with a value of the field's type. A field read names a declared field. An update builds a new
record of the same type: the fields it names get new values, and every other field is read from the
old record, so the emitted object lists exactly the declared fields, never what the old object might
also hold.
-/

namespace LScript

structure Ctx where
  types : List (String × Ty)                     -- every type name declared so far, resolved
  recs : List (String × List (String × Ty))      -- each record's fields, in declaration order
  vals : List (String × Ty)                      -- values declared so far

def Ctx.empty : Ctx := ⟨[], [], []⟩

def tyName : Ty → String
  | .int => "Int"
  | .str => "String"
  | .record r => r

def resolve (types : List (String × Ty)) : TyName → Except String Ty
  | .int => .ok .int
  | .str => .ok .str
  | .named a =>
    match lookup types a with
    | some t => .ok t
    | none => .error s!"type {a} is not declared before this line"

def resolveFields (types : List (String × Ty)) : List (String × TyName) → Except String (List (String × Ty))
  | [] => .ok []
  | (l, tn) :: rest =>
    match resolve types tn, resolveFields types rest with
    | .ok t, .ok ts => .ok ((l, t) :: ts)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def inferAtom (ctx : Ctx) : Atom → Except String Ty
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

/-- The type at the end of a chain of field reads. -/
def fieldPath (recs : List (String × List (String × Ty))) : Ty → List String → Except String Ty
  | t, [] => .ok t
  | .record r, l :: ls =>
    match lookup recs r with
    | some tfs =>
      match lookup tfs l with
      | some t => fieldPath recs t ls
      | none => .error s!"{r} has no field {l}"
    | none => .error s!"record {r} is not declared"
  | t, l :: _ => .error s!"{tyName t} has no fields, so .{l} reads nothing"

/-- Every given field is declared, with a value of its declared type. -/
def checkFields (ctx : Ctx) (r : String) (tfs : List (String × Ty)) : List (String × Atom) → Except String Unit
  | [] => .ok ()
  | (l, a) :: rest =>
    match lookup tfs l, inferAtom ctx a with
    | some τ, .ok τ' =>
      if τ' = τ then checkFields ctx r tfs rest
      else .error s!"field {l} of {r} is {tyName τ}, and its value is {tyName τ'}"
    | none, _ => .error s!"{r} has no field {l}"
    | some _, .error e => .error e

def emitAtom : Atom → JS.Atom
  | .int n => .num n
  | .str s => .str s
  | .var x => .path x []

/-- Labels the emitted object may carry: identifiers, not `__proto__`, none twice. -/
def labelsOk (ls : List String) : Bool := ls.all JS.validLabel && decide ls.Nodup

/-- Check `e` against the declared type `τ`, and give the JavaScript for it. -/
def checkExpr (ctx : Ctx) (e : Expr) (τ : Ty) : Except String JS.Expr :=
  match e with
  | .atom a =>
    match inferAtom ctx a with
    | .ok t => if t = τ then .ok (.atom (emitAtom a)) else .error s!"the value is {tyName t}, where {tyName τ} is declared"
    | .error err => .error err
  | .path x ls =>
    match lookup ctx.vals x with
    | none => .error s!"{x} is not declared before this line"
    | some t =>
      match fieldPath ctx.recs t ls with
      | .ok t' => if t' = τ then .ok (.atom (.path x ls)) else .error s!"the value is {tyName t'}, where {tyName τ} is declared"
      | .error err => .error err
  | .record fs =>
    match τ with
    | .record r =>
      match lookup ctx.recs r with
      | none => .error s!"record {r} is not declared"
      | some tfs =>
        if !labelsOk (fs.map Prod.fst) then .error s!"a field of {r} is given twice, or isn't a plain identifier"
        else
          match checkFields ctx r tfs fs with
          | .error err => .error err
          | .ok () =>
            match tfs.find? (fun p => (lookup fs p.1).isNone) with
            | some (l, _) => .error s!"{r} needs its field {l}"
            | none => .ok (.obj (fs.map fun (l, a) => (l, emitAtom a)))
    | t => .error s!"a record literal is not {tyName t}"
  | .update x fs =>
    match lookup ctx.vals x with
    | none => .error s!"{x} is not declared before this line"
    | some (.record r) =>
      if .record r ≠ τ then .error s!"{x} is {r}, where {tyName τ} is declared"
      else
        match lookup ctx.recs r with
        | none => .error s!"record {r} is not declared"
        | some tfs =>
          if !labelsOk (fs.map Prod.fst) then .error s!"a field of {r} is given twice, or isn't a plain identifier"
          else if !labelsOk (tfs.map Prod.fst) then .error s!"record {r} has a label the emitted object can't carry"
          else
            match checkFields ctx r tfs fs with
            | .error err => .error err
            | .ok () =>
              .ok (.obj (tfs.map fun (l, _) =>
                (l, match lookup fs l with
                    | some a => emitAtom a
                    | none => .path x [l])))
    | some t => .error s!"{x} is {tyName t}, which has no fields to update"

def isBase (a : String) : Bool := a == "Int" || a == "String"

/-- Check one declaration, and give the JavaScript for it, if it is a value. -/
def checkDecl (ctx : Ctx) : Decl → Except String (Ctx × Option JS.Decl)
  | .alias a rhs =>
    if isBase a then .error s!"{a} is a base type and can't be redeclared"
    else if (lookup ctx.types a).isSome then .error s!"type {a} is declared twice"
    else
      match resolve ctx.types rhs with
      | .ok t => .ok ({ ctx with types := (a, t) :: ctx.types }, none)
      | .error e => .error e
  | .record r fields =>
    if isBase r then .error s!"{r} is a base type and can't be redeclared"
    else if (lookup ctx.types r).isSome then .error s!"type {r} is declared twice"
    else if !labelsOk (fields.map Prod.fst) then .error s!"a field of {r} is declared twice, isn't an identifier, or is __proto__"
    else
      match resolveFields ctx.types fields with
      | .ok tfs => .ok ({ ctx with types := (r, .record r) :: ctx.types, recs := (r, tfs) :: ctx.recs }, none)
      | .error e => .error e
  | .val x tn e =>
    if !JS.validIdent x then .error s!"{x} is not a name JavaScript allows"
    else if (lookup ctx.vals x).isSome then .error s!"{x} is declared twice"
    else
      match resolve ctx.types tn with
      | .error err => .error err
      | .ok τ =>
        match checkExpr ctx e τ with
        | .ok je => .ok ({ ctx with vals := (x, τ) :: ctx.vals }, some ⟨x, je⟩)
        | .error err => .error s!"{x}: {err}"

def checkFrom (ctx : Ctx) : Program → Except String (Ctx × JS.Program)
  | [] => .ok (ctx, [])
  | d :: ds =>
    match checkDecl ctx d with
    | .error e => .error e
    | .ok (ctx', jd) =>
      match checkFrom ctx' ds with
      | .ok (ctx'', js) => .ok (ctx'', match jd with | some d' => d' :: js | none => js)
      | .error e => .error e

def check (p : Program) : Except String (Ctx × JS.Program) := checkFrom .empty p

def compile (p : Program) : Except String JS.Program :=
  match check p with
  | .ok (_, js) => .ok js
  | .error e => .error e

end LScript
