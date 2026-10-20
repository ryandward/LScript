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
also hold. A record's fields are data, never functions.

A function is checked against its declared type, which must be a function type: its body is checked
against the result type with its parameter in scope at the parameter type. A call's function must
have exactly the type its arguments and the declared result call for, `A -> B -> T` for `f(a)(b)` of
type `T`, so a call may give fewer arguments than the function takes and get a function back. A name
of a function type is emitted without `export`: only data leaves the module.

Every rejection ends with the code of the check that made it, and every check is tagged with its
kind: `load-bearing` (without it, the compiler accepts the check's program in `Counterexamples.lean`
and that program goes wrong, so `compile_sound` is false), `policy` (it rejects a program that says
two things, and `compile_sound` still holds without it), or `partial` (a `none` arm: the program names
something that doesn't exist, so there is nothing to continue with). `test/checks.mjs` holds each tag
to its kind.
-/

namespace LScript

structure Ctx where
  types : Scope Ty                               -- every type name declared so far, resolved
  recs : Scope (List (String × Ty))              -- each record's fields, in declaration order
  vals : Scope Ty                                -- values declared so far

def Ctx.empty : Ctx := ⟨.empty, .empty, .empty⟩

def tyName : Ty → String
  | .int => "Int"
  | .str => "String"
  | .record r => r
  | .fn a b => (match a with | .fn _ _ => "(" ++ tyName a ++ ")" | _ => tyName a) ++ " -> " ++ tyName b

/-- A record's declared fields. Every record type in scope was declared, so they are always there. -/
def fieldsOf (ctx : Ctx) (r : String) : List (String × Ty) := (ctx.recs.find r).getD []

def isRecord : Ty → Bool
  | .record _ => true
  | _ => false

/-- A type's fields: a record's declared fields, and none for anything else. -/
def fieldsOfTy (ctx : Ctx) : Ty → List (String × Ty)
  | .record r => fieldsOf ctx r
  | _ => []

def isFn : Ty → Bool
  | .fn _ _ => true
  | _ => false

/-- A function type's parameter and result. Anything else is its own, which nothing uses: a function
    checked against it is rejected first. -/
def paramTy : Ty → Ty
  | .fn a _ => a
  | t => t

def resultTy : Ty → Ty
  | .fn _ b => b
  | t => t

/-- The type of a function that takes arguments of these types and gives `τ`. -/
def arrowTy : List Ty → Ty → Ty
  | [], τ => τ
  | t :: ts, τ => .fn t (arrowTy ts τ)

def resolve (types : Scope Ty) : TyName → Except String Ty
  | .int => .ok .int
  | .str => .ok .str
  | .named a =>
    match types.find a with
    | some t => .ok t
    | none => .error s!"type {a} is not declared before this line [type-declared]"  -- check: type-declared (partial)
  | .fn a b =>
    match resolve types a, resolve types b with
    | .ok ta, .ok tb => .ok (.fn ta tb)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def resolveFields (types : Scope Ty) : List (String × TyName) → Except String (List (String × Ty))
  | [] => .ok []
  | (l, tn) :: rest =>
    match resolve types tn, resolveFields types rest with
    | .ok t, .ok ts => .ok ((l, t) :: ts)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def inferAtom (ctx : Ctx) : Atom → Except String Ty
  | .int n =>
    if !JS.isSafe n then .error s!"{n} is outside the safe integers, -(2^53 - 1) to 2^53 - 1, so JavaScript would hold a different number [int-safe]"  -- check: int-safe (load-bearing)
    else .ok .int
  | .str s =>
    if !JS.validStr s then .error s!"string literal {repr s} may hold only printable ASCII other than \" and \\ [string-printable]"  -- check: string-printable (load-bearing)
    else .ok .str
  | .var x =>
    match ctx.vals.find x with
    | some t => .ok t
    | none => .error s!"{x} is not declared before this line [name-declared]"  -- check: name-declared (partial)

/-- The type at the end of a chain of field reads. -/
def fieldPath (ctx : Ctx) : Ty → List String → Except String Ty
  | t, [] => .ok t
  | t, l :: ls =>
    match lookup (fieldsOfTy ctx t) l with
    | some t' => fieldPath ctx t' ls
    | none => .error s!"{tyName t} has no field {l} [read-declared]"  -- check: read-declared (partial)

/-- Every given field is declared, with a value of its declared type. -/
def checkFields (ctx : Ctx) (t : Ty) : List (String × Atom) → Except String Unit
  | [] => .ok ()
  | (l, a) :: rest =>
    match lookup (fieldsOfTy ctx t) l with
    | none => .error s!"{tyName t} has no field {l} [field-declared]"  -- check: field-declared (load-bearing) off: checkFields ctx t rest
    | some τ =>
      match inferAtom ctx a with
      | .error e => .error e
      | .ok τ' =>
        if τ' ≠ τ then .error s!"field {l} of {tyName t} is {tyName τ}, and its value is {tyName τ'} [field-type]"  -- check: field-type (load-bearing)
        else checkFields ctx t rest

def inferArgs (ctx : Ctx) : List Atom → Except String (List Ty)
  | [] => .ok []
  | a :: rest =>
    match inferAtom ctx a, inferArgs ctx rest with
    | .ok t, .ok ts => .ok (t :: ts)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def emitAtom : Atom → JS.Atom
  | .int n => .num n
  | .str s => .str s
  | .var x => .path x []

/-- `f(a)(b)…`: the function applied to one argument at a time. -/
def emitCall (f : JS.Expr) : List Atom → JS.Expr
  | [] => f
  | a :: rest => emitCall (.app f (.atom (emitAtom a))) rest

/-- Labels a record may declare: identifiers, not `__proto__`, none twice. -/
def labelsOk (ls : List String) : Bool := ls.all JS.validLabel && decide ls.Nodup

/-- A field the record doesn't give, for the message when one is missing. -/
def missingField (fs : List (String × Atom)) (tfs : List (String × Ty)) : String :=
  match tfs.find? (fun p => (lookup fs p.1).isNone) with
  | some (l, _) => l
  | none => "?"

/-- Check `e` against the declared type `τ`, and give the JavaScript for it. -/
def checkExpr (ctx : Ctx) (e : Expr) (τ : Ty) : Except String JS.Expr :=
  match e with
  | .atom a =>
    match inferAtom ctx a with
    | .error err => .error err
    | .ok t =>
      if t ≠ τ then .error s!"the value is {tyName t}, where {tyName τ} is declared [atom-type]"  -- check: atom-type (load-bearing)
      else .ok (.atom (emitAtom a))
  | .path x ls =>
    match ctx.vals.find x with
    | none => .error s!"{x} is not declared before this line [path-name-declared]"  -- check: path-name-declared (partial)
    | some t =>
      match fieldPath ctx t ls with
      | .error err => .error err
      | .ok t' =>
        if t' ≠ τ then .error s!"the value is {tyName t'}, where {tyName τ} is declared [read-type]"  -- check: read-type (load-bearing)
        else .ok (.atom (.path x ls))
  | .record fs =>
    if !isRecord τ then .error s!"a record literal is not {tyName τ} [literal-record]"  -- check: literal-record (load-bearing)
    else if !decide (fs.map Prod.fst).Nodup then .error s!"a field of {tyName τ} is given twice [literal-distinct]"  -- check: literal-distinct (load-bearing)
    else
      match checkFields ctx τ fs with
      | .error err => .error err
      | .ok () =>
        if !((fieldsOfTy ctx τ).all fun p => (lookup fs p.1).isSome) then .error s!"{tyName τ} needs its field {missingField fs (fieldsOfTy ctx τ)} [literal-complete]"  -- check: literal-complete (load-bearing)
        else .ok (.obj (fs.map fun (l, a) => (l, emitAtom a)))
  | .update x fs =>
    match ctx.vals.find x with
    | none => .error s!"{x} is not declared before this line [update-name-declared]"  -- check: update-name-declared (partial)
    | some t =>
      if !isRecord t then .error s!"{x} is {tyName t}, which has no fields to update [update-record]"  -- check: update-record (load-bearing)
      else if t ≠ τ then .error s!"{x} is {tyName t}, where {tyName τ} is declared [update-type]"  -- check: update-type (load-bearing)
      else if !decide (fs.map Prod.fst).Nodup then .error s!"a field of {tyName t} is given twice [update-distinct]"  -- check: update-distinct (policy)
      else
        match checkFields ctx t fs with
        | .error err => .error err
        | .ok () =>
          .ok (.obj ((fieldsOfTy ctx t).map fun (l, _) =>
            (l, match lookup fs l with
                | some a => emitAtom a
                | none => .path x [l])))
  | .lam x body =>
    if !isFn τ then .error s!"a function is not {tyName τ} [lambda-type]"  -- check: lambda-type (load-bearing)
    else if !JS.bindable x then .error s!"parameter {x} is reserved, or a global the emitted code calls [param-ident]"  -- check: param-ident (load-bearing)
    else
      match checkExpr { ctx with vals := ctx.vals.insert x (paramTy τ) } body (resultTy τ) with
      | .ok jb => .ok (.arrow x jb)
      | .error err => .error err
  | .app f a more =>
    match ctx.vals.find f with
    | none => .error s!"{f} is not declared before this line [call-name-declared]"  -- check: call-name-declared (partial)
    | some t =>
      match inferArgs ctx (a :: more) with
      | .error err => .error err
      | .ok ts =>
        if t ≠ arrowTy ts τ then .error s!"{f} is {tyName t}, and this call needs {tyName (arrowTy ts τ)} [call-type]"  -- check: call-type (load-bearing)
        else .ok (emitCall (.atom (.path f [])) (a :: more))

def isBase (a : String) : Bool := a == "Int" || a == "String"

/-- Check one declaration, and give the JavaScript for it, if it is a value. -/
def checkDecl (ctx : Ctx) : Decl → Except String (Ctx × Option JS.Decl)
  | .alias a rhs =>
    if isBase a then .error s!"{a} is a base type and can't be redeclared [alias-not-base]"  -- check: alias-not-base (policy)
    else if (ctx.types.find a).isSome then .error s!"type {a} is declared twice [alias-fresh]"  -- check: alias-fresh (policy)
    else
      match resolve ctx.types rhs with
      | .ok t => .ok ({ ctx with types := ctx.types.insert a t }, none)
      | .error e => .error e
  | .record r fields =>
    if isBase r then .error s!"{r} is a base type and can't be redeclared [record-not-base]"  -- check: record-not-base (policy)
    else if (ctx.types.find r).isSome then .error s!"type {r} is declared twice [record-fresh]"  -- check: record-fresh (load-bearing)
    else if !labelsOk (fields.map Prod.fst) then .error s!"a field of {r} is declared twice, isn't an identifier, or is __proto__ [record-labels]"  -- check: record-labels (load-bearing)
    else
      match resolveFields ctx.types fields with
      | .ok tfs =>
        if !tfs.all (fun p => isData p.2) then .error s!"a field of {r} is a function, and a record holds only data [record-data]"  -- check: record-data (load-bearing)
        else .ok ({ ctx with types := ctx.types.insert r (.record r), recs := ctx.recs.insert r tfs }, none)
      | .error e => .error e
  | .val x tn e =>
    if !JS.bindable x then .error s!"{x} is reserved, or a global the emitted code calls [val-ident]"  -- check: val-ident (load-bearing)
    else if (ctx.vals.find x).isSome then .error s!"{x} is declared twice [val-fresh]"  -- check: val-fresh (load-bearing)
    else
      match resolve ctx.types tn with
      | .error err => .error err
      | .ok τ =>
        match checkExpr ctx e τ with
        | .ok je => .ok ({ ctx with vals := ctx.vals.insert x τ }, some ⟨x, je, isData τ⟩)
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
