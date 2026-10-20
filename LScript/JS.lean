import LScript.Syntax

/-!
# The JavaScript we emit, and a model of how V8 runs it

The compiler emits a module of `const name = value;` lines, each exported or not, where a value is a
literal, a name, a chain of property reads, an object literal of those, an arrow function, or a call.
This file models exactly that fragment: what each line can evaluate to, and every way it can go wrong.
`test/v8.mjs` checks the model against Node.

* A name that isn't a JavaScript identifier, or is a reserved word, is a SyntaxError. A field label
  may be a reserved word: JavaScript allows those as property names.
* A name declared twice is a SyntaxError.
* Reading a name before its line, or a name never declared, is a ReferenceError.
* A numeric literal denotes a double. Within ±(2^53 − 1) the double is exactly the integer written;
  outside it, V8 rounds, and the model says only that the value isn't the integer written.
* A string literal is printed between double quotes as it is, so it may hold only printable ASCII
  other than `"` and `\`.
* Reading a property an object holds as its own gives its value. Reading one it doesn't hold gives
  `undefined` or something inherited from a prototype, and reading a property of a number, a string or
  a function gives `undefined`, a method or a length. None of these throws, and the model says only
  that the value is one it doesn't track (`untracked`). Reading a property of an untracked value
  throws if the value is `undefined`, so the model refuses it (`unmodeled`).
* In an object literal, V8 keeps the last of two equal keys, and `__proto__: v` sets the prototype
  instead of making a field. The model refuses both (`unmodeled`): it is stricter than V8, so for any
  module it runs without an error, it agrees with V8.
* Every object the module makes is frozen: it is printed as `Object.freeze({ … })`. Writing, adding,
  deleting or redefining a field of it, or changing its prototype, then throws, so code that imports a
  record can't change what it holds. This rests on `Object.freeze` being the built-in; a module that
  binds the name `Object` would shadow it, so the model refuses that name.
* An arrow function `(x) => body` is a closure. Calling it runs its body with `x` bound to the argument
  and the names declared before the arrow; in V8 the body can also see names declared after it, once
  they are initialized, so the model is stricter. Calling anything else is a TypeError, or, for a
  method a value inherits, something the model doesn't track; the model refuses both. A parameter
  follows the naming rules of a declaration.
* V8 parses a function's body along with the rest of the module, so a body that isn't valid syntax is
  a SyntaxError even if the function is never called. The model checks the body when it evaluates the
  arrow, which comes to the same thing: every line is evaluated in order, and a module that hits any
  error gives no claim.

A call runs a body, so evaluation takes fuel: one unit per call. Running out is the model's own limit,
not anything V8 does. `evalExpr_mono` and `runFrom_mono` prove that any other result stays the same
with more fuel, so a module that finishes at some fuel finishes the same way at every larger one.
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
  | arrow (param : String) (body : Expr)          -- (param) => body
  | call (f : Atom) (arg : Atom) (more : List Atom)  -- f(arg)(a₂)…: at least one argument
  deriving Repr, DecidableEq

/-- `export const name = e;`, or `const name = e;` when it isn't exported. -/
structure Decl where
  name : String
  e : Expr
  exported : Bool
  deriving Repr, DecidableEq

abbrev Program := List Decl

inductive Val where
  | num (n : Int)                       -- a double that is exactly the integer n
  | imprecise                           -- a double that is not the integer the literal wrote
  | str (s : String)
  | obj (fields : List (String × Val)) (frozen : Bool)  -- an object whose own fields are exactly these
  | untracked                           -- a value the model doesn't track: see `readField`
  | clos (env : List (String × Val)) (param : String) (body : Expr)  -- an arrow function, and the names it sees
  deriving Repr

/-- What an importer can be handed: numbers, strings, and frozen objects of those, never a function. -/
inductive Data : Val → Prop where
  | num {n} : Data (.num n)
  | str {s} : Data (.str s)
  | obj {fs} : (∀ l v, lookup fs l = some v → Data v) → Data (.obj fs true)

inductive Err where
  | syntax (msg : String)
  | reference (name : String)
  | unmodeled (msg : String)            -- V8 runs it, differently from what was written, or may
  | notCallable                         -- a TypeError: calling something that isn't a function
  | outOfFuel                           -- the model's own limit, not an error in V8
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

/-- `v.l`. An object's own field gives its value. Anything else V8 gives without throwing, so the model
    gives `untracked`; but reading a property of an untracked value throws if it is `undefined`, so the
    model refuses that. -/
def readField : Val → String → Except Err Val
  | .obj fs _, l => .ok ((lookup fs l).getD .untracked)
  | .untracked, l => .error (.unmodeled s!"reading {l} of a value the model doesn't track, which may be undefined")
  | _, _ => .ok .untracked

def readPath : Val → List String → Except Err Val
  | v, [] => .ok v
  | v, l :: ls =>
    match readField v l with
    | .ok w => readPath w ls
    | .error e => .error e

def evalAtom (env : List (String × Val)) : Atom → Except Err Val
  | .num n => .ok (if isSafe n then .num n else .imprecise)
  | .str s => if validStr s then .ok (.str s) else .error (.syntax s!"string literal {repr s} can't be printed as itself")
  | .path x ls =>
    if !ls.all identShape then .error (.syntax s!"a property read from {x} isn't an identifier")
    else
      match lookup env x with
      | some v => readPath v ls
      | none => .error (.reference x)

def evalFields (env : List (String × Val)) : List (String × Atom) → Except Err (List (String × Val))
  | [] => .ok []
  | (l, a) :: rest =>
    match evalAtom env a, evalFields env rest with
    | .ok v, .ok vs => .ok ((l, v) :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def evalArgs (env : List (String × Val)) : List Atom → Except Err (List Val)
  | [] => .ok []
  | a :: rest =>
    match evalAtom env a, evalArgs env rest with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

/-- The text of an atom parses as that atom. -/
def atomOk : Atom → Bool
  | .num _ => true
  | .str s => validStr s
  | .path x ls => validIdent x && ls.all identShape

/-- The text of an expression parses as that expression. -/
def staticOk : Expr → Bool
  | .atom a => atomOk a
  | .obj fs => (fs.map Prod.fst).all validLabel && fs.all (fun p => atomOk p.2)
  | .arrow x body => validIdent x && staticOk body
  | .call f a more => atomOk f && atomOk a && more.all atomOk

/-- Apply a function value to each argument in turn, running each body with `ev`. -/
def applyAll (ev : List (String × Val) → Expr → Except Err Val) : Except Err Val → List Val → Except Err Val
  | acc, [] => acc
  | .ok (.clos cenv x body), w :: ws => applyAll ev (ev ((x, w) :: cenv) body) ws
  | .ok _, _ :: _ => .error .notCallable
  | .error e, _ :: _ => .error e

/-- Evaluate an expression with `n` units of fuel: one per call. -/
def evalExpr : Nat → List (String × Val) → Expr → Except Err Val
  | 0, _, _ => .error .outOfFuel
  | _ + 1, env, .atom a => evalAtom env a
  | _ + 1, env, .obj fs =>
    if !(fs.map Prod.fst).all validLabel then .error (.unmodeled "a label that isn't a plain identifier, or __proto__, which sets the prototype")
    else if !decide (fs.map Prod.fst).Nodup then .error (.unmodeled "two equal keys: V8 keeps the last")
    else
      match evalFields env fs with
      | .ok vs => .ok (.obj vs true)
      | .error e => .error e
  | _ + 1, env, .arrow x body =>
    if !validIdent x then .error (.syntax s!"{x} is not an identifier")
    else if emittedGlobals.contains x then .error (.unmodeled s!"{x} shadows a global the emitted code calls")
    else if !staticOk body then .error (.syntax "the body of an arrow function isn't valid syntax")
    else .ok (.clos env x body)
  | n + 1, env, .call f a more =>
    match evalAtom env f, evalArgs env (a :: more) with
    | .ok fv, .ok vs => applyAll (fun env' e' => evalExpr n env' e') (.ok fv) vs
    | .error e, _ => .error e
    | .ok _, .error e => .error e

/-- Run the module from an environment of names already declared, with `n` units of fuel per line. -/
def runFrom (n : Nat) (env : List (String × Val)) : Program → Except Err (List (String × Val))
  | [] => .ok env
  | d :: ds =>
    if !validIdent d.name then .error (.syntax s!"{d.name} is not an identifier")
    else if emittedGlobals.contains d.name then .error (.unmodeled s!"{d.name} shadows a global the emitted code calls")
    else if (lookup env d.name).isSome then .error (.syntax s!"{d.name} is declared twice")
    else
      match evalExpr n env d.e with
      | .ok v => runFrom n ((d.name, v) :: env) ds
      | .error e => .error e

def run (n : Nat) (p : Program) : Except Err (List (String × Val)) := runFrom n [] p

def renderAtom : Atom → String
  | .num n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .path x ls => String.join (x :: ls.map (fun l => "." ++ l))

def renderExpr : Expr → String
  | .atom a => renderAtom a
  | .obj [] => "Object.freeze({})"
  | .obj fs => "Object.freeze({ " ++ ", ".intercalate (fs.map fun (l, a) => l ++ ": " ++ renderAtom a) ++ " })"
  | .arrow x body => "(" ++ x ++ ") => " ++ renderExpr body
  | .call f a more => renderAtom f ++ String.join ((a :: more).map fun b => "(" ++ renderAtom b ++ ")")

/-- The text of the module. -/
def render (p : Program) : String :=
  String.join (p.map fun d => s!"{if d.exported then "export " else ""}const {d.name} = {renderExpr d.e};\n")

/-! ## Fuel: any result other than running out stays the same with more fuel -/

theorem applyAll_error (ev : List (String × Val) → Expr → Except Err Val) (e : Err) :
    ∀ ws, applyAll ev (.error e) ws = .error e
  | [] => rfl
  | _ :: _ => rfl

theorem applyAll_mono {ev₁ ev₂ : List (String × Val) → Expr → Except Err Val}
    (h : ∀ env e r, ev₁ env e = r → r ≠ .error .outOfFuel → ev₂ env e = r) :
    ∀ (ws : List Val) {acc r}, applyAll ev₁ acc ws = r → r ≠ .error .outOfFuel → applyAll ev₂ acc ws = r := by
  intro ws
  induction ws with
  | nil => intro acc r h₁ _; simpa [applyAll] using h₁
  | cons w ws ih =>
    intro acc r h₁ h₂
    cases acc with
    | error e => simpa [applyAll] using h₁
    | ok v =>
      cases v with
      | clos cenv x body =>
        simp only [applyAll] at h₁ ⊢
        cases hb : ev₁ ((x, w) :: cenv) body with
        | error e =>
          rw [hb, applyAll_error] at h₁
          have he : Except.error e ≠ (Except.error .outOfFuel : Except Err Val) := by rw [h₁]; exact h₂
          rw [h _ _ _ hb he, applyAll_error]; exact h₁
        | ok r₁ =>
          rw [hb] at h₁
          rw [h _ _ _ hb (by simp)]
          exact ih h₁ h₂
      | _ => simpa [applyAll] using h₁

theorem evalExpr_mono : ∀ (n : Nat) {env e r}, evalExpr n env e = r → r ≠ .error .outOfFuel →
    ∀ m, n ≤ m → evalExpr m env e = r := by
  intro n
  induction n with
  | zero => intro env e r h hr; simp [evalExpr] at h; subst h; exact absurd rfl hr
  | succ n ih =>
    intro env e r h hr m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases e with
    | atom a => simpa [evalExpr] using h
    | obj fs => simpa [evalExpr] using h
    | arrow x body => simpa [evalExpr] using h
    | call f a more =>
      simp only [evalExpr] at h ⊢
      cases hf : evalAtom env f with
      | error e => simpa [hf] using h
      | ok fv =>
        cases ha : evalArgs env (a :: more) with
        | error e => simpa [hf, ha] using h
        | ok vs =>
          simp only [hf, ha] at h ⊢
          exact applyAll_mono (fun env' e' r' h₁ h₂ => ih h₁ h₂ m (by omega)) vs h hr

theorem runFrom_mono : ∀ (ds : Program) {n env r}, runFrom n env ds = r → r ≠ .error .outOfFuel →
    ∀ m, n ≤ m → runFrom m env ds = r := by
  intro ds
  induction ds with
  | nil => intro n env r h _ m _; simpa [runFrom] using h
  | cons d ds ih =>
    intro n env r h hr m hm
    unfold runFrom at h ⊢
    split at h
    · rename_i h₁; rw [if_pos h₁]; exact h
    · rename_i h₁; rw [if_neg h₁]
      split at h
      · rename_i h₂; rw [if_pos h₂]; exact h
      · rename_i h₂; rw [if_neg h₂]
        split at h
        · rename_i h₃; rw [if_pos h₃]; exact h
        · rename_i h₃; rw [if_neg h₃]
          split at h
          · rename_i v he
            rw [evalExpr_mono n he (by simp) m hm]
            exact ih h hr m hm
          · rename_i e he
            rw [evalExpr_mono n he (fun hx => hr (by rw [← h]; injection hx with hx; rw [hx])) m hm]
            exact h

/-- A run never changes a name already declared: declaring it again is an error. -/
theorem runFrom_keeps : ∀ (ds : Program) {n env env' x v}, runFrom n env ds = .ok env' →
    lookup env x = some v → lookup env' x = some v := by
  intro ds
  induction ds with
  | nil => intro n env env' x v h hx; simp only [runFrom, Except.ok.injEq] at h; subst h; exact hx
  | cons d ds ih =>
    intro n env env' x v h hx
    unfold runFrom at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hfresh
          split at h
          · rename_i w _
            apply ih h
            have hne : d.name ≠ x := fun e => by subst e; simp [hx] at hfresh
            simp [lookup, hne, hx]
          · cases h

theorem run_mono {n p r} (h : run n p = r) (hr : r ≠ .error .outOfFuel) : ∀ m, n ≤ m → run m p = r :=
  runFrom_mono p h hr

end LScript.JS
