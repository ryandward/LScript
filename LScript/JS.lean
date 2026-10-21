import LScript.Syntax
import LScript.Scope

/-!
# The JavaScript we emit, and a model of how V8 runs it

The compiler emits a module of `const name = value;` lines, each exported or not, where a value is a
literal, a name, a chain of property reads, an object literal of those, an arrow function, a call of
one expression with another, or a conditional on one of the tests below. This file models exactly that
fragment: what each line can evaluate to, and every way it can go wrong. `test/v8.mjs` checks the model
against Node.

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
  record can't change what it holds. This rests on `Object.freeze` being the built-in.
* The emitted code reads the globals `Object`, `Array`, `Number` and `JSON` (`emittedGlobals`). A
  module that binds one of those names shadows it for the whole module, so the model refuses them as
  names and as parameters. `test/globals.mjs` checks that the printed modules read no other global;
  where the code needs `undefined`, it writes `void 0`, which no binding can shadow.
* An arrow function `(x) => body` is a closure. Calling it runs its body with `x` bound to the argument
  and the names declared before the arrow; in V8 the body can also see names declared after it, once
  they are initialized, so the model is stricter. Calling anything else is a TypeError, or, for a
  method a value inherits, something the model doesn't track; the model refuses both. A parameter
  follows the naming rules of a declaration.
* V8 parses a function's body along with the rest of the module, so a body that isn't valid syntax is
  a SyntaxError even if the function is never called. The model checks the body when it evaluates the
  arrow, which comes to the same thing: every line is evaluated in order, and a module that hits any
  error gives no claim.
* The values `JSON.parse` returns (`IsJson`) are null, booleans, numbers, strings, arrays, and plain
  objects that aren't frozen, each own key once: of two equal keys in the text, the last one stays, and
  `"__proto__"` is an ordinary own key. A number is a safe integer, `-0`, or another double, which
  includes `Infinity` for `1e400`. A string or a key may hold any UTF-16 code units; the model holds
  each unit as one Lean character, the surrogates, which a Lean character can't be, as characters no
  ASCII label is, and it never looks inside a foreign string.
* Reading a property of `null` or `undefined` is a TypeError.
* An entry is the exported function an importer calls with any value. It is printed as
  `((p) => (input) => p($json(input)))(parse)`, where `$json`, printed once at the top of the module,
  gives `JSON.parse` of a string inside a `try`, and `undefined` for anything else or for text that
  doesn't parse. The model evaluates the parse function and holds it (`entryOf`); it doesn't call an
  entry, since only importers do, and what an entry promises is said by `ValOf` for every value
  `JSON.parse` returns. That `$json` gives `undefined` or such a value is the trusted step, measured.
* A module that exports a function named `then` can't be imported with `import()`, which takes the
  module for a promise and waits on it forever, so the model refuses one.
* A conditional `(t ? a : b)` evaluates its test, then one branch. A test is
  `typeof a === "string"`; `Number.isSafeInteger(a) && !Object.is(a, -0)`, which holds for a safe
  integer and not for `-0`; a shape test, which holds for a plain object whose own keys are exactly the
  given labels (`typeof`, `null`, `Array.isArray`, `Object.keys(a).length` and `Object.hasOwn`); or two
  tests joined by `&&`, the second evaluated only if the first holds. These rest on the built-ins named
  being the original ones.

A call runs a body, so evaluation takes fuel, and a body runs with one unit less than its call: fuel
bounds how deeply calls nest. `evalExpr_mono` and `runFrom_mono` prove that any other result stays the
same with more fuel, so a module that finishes at some fuel finishes the same way at every larger one.
V8 bounds nesting too, and the model leaves that out: its stack is finite, and a module whose calls
nest deeper than it allows throws a RangeError. On Node 22 with its default stack, a chain of emitted
functions each calling the one before runs 10,000 deep and throws at 11,000. The language has no
recursion and no nested calls, and we haven't found a way to nest calls deeper than about one level per
declaration, so getting there takes about 10,000 declarations.
-/

namespace LScript.JS

/-- A literal, a name, or a name followed by property reads. -/
inductive Atom where
  | num (n : Int)
  | str (s : String)
  | path (x : String) (labels : List String)      -- x, x.l, x.l.m, …
  deriving Repr, DecidableEq

/-- A test the emitted parse makes of a value. -/
inductive Test where
  | isStr (a : Atom)                              -- typeof a === "string"
  | isInt (a : Atom)                              -- Number.isSafeInteger(a) && !Object.is(a, -0)
  | isShape (a : Atom) (labels : List String)     -- a plain object whose own keys are exactly these
  | and (t u : Test)                              -- t && u
  deriving Repr, DecidableEq

inductive Expr where
  | atom (a : Atom)
  | obj (fields : List (String × Atom))           -- { l: a, … }
  | arrow (param : String) (body : Expr)          -- (param) => body
  | app (f : Expr) (arg : Expr)                   -- f(arg)
  | cond (t : Test) (a b : Expr)                  -- (t ? a : b)
  | entry (parse : Expr)                          -- an entry around its parse function
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
  | notInt                              -- a double that isn't a safe integer, nor -0
  | negZero                             -- -0
  | str (s : String)
  | bool (b : Bool)
  | null
  | undef                               -- undefined
  | arr (items : List Val)              -- an array
  | obj (fields : List (String × Val)) (frozen : Bool)  -- a plain object whose own fields are exactly these, each once
  | untracked                           -- a value the model doesn't track: see `readField`
  | clos (env : List (String × Val)) (param : String) (body : Expr)  -- an arrow function, and the names it sees
  | entryOf (parse : Val)               -- an entry, holding its parse function
  deriving Repr

/-- What an importer can be handed: numbers, strings, and frozen objects of those, never a function. -/
inductive Data : Val → Prop where
  | num {n} : Data (.num n)
  | str {s} : Data (.str s)
  | obj {fs} : (∀ l v, lookup fs l = some v → Data v) → Data (.obj fs true)

/-- What an importer can be handed: data, or an entry, which takes any value. -/
inductive Exportable : Val → Prop where
  | data {v} : Data v → Exportable v
  | entry {c} : Exportable (.entryOf c)

/-- A value V8 can call. -/
def callable : Val → Bool
  | .clos _ _ _ => true
  | .entryOf _ => true
  | _ => false

inductive Err where
  | syntax (msg : String)
  | reference (name : String)
  | unmodeled (msg : String)            -- V8 runs it, differently from what was written, or may
  | notCallable                         -- a TypeError: calling something that isn't a function
  | nullRead (label : String)           -- a TypeError: reading a property of null or undefined
  | outOfFuel                           -- the model's own limit, not an error in V8
  deriving Repr, DecidableEq

/-- `Number.MAX_SAFE_INTEGER`. -/
def maxSafe : Int := 9007199254740991

def isSafe (n : Int) : Bool := decide (-maxSafe ≤ n) && decide (n ≤ maxSafe)

/-- The values `JSON.parse` returns. -/
inductive IsJson : Val → Prop where
  | null : IsJson .null
  | bool {b} : IsJson (.bool b)
  | int {n} : isSafe n = true → IsJson (.num n)
  | negZero : IsJson .negZero
  | notInt : IsJson .notInt
  | str {s} : IsJson (.str s)
  | arr {vs} : (∀ v ∈ vs, IsJson v) → IsJson (.arr vs)
  | obj {fs} : (fs.map Prod.fst).Nodup → (∀ l v, lookup fs l = some v → IsJson v) → IsJson (.obj fs false)

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

/-- The reserved words, as a `Scope`, so that checking a name costs Lean's kernel the length of the
    name rather than a comparison with each reserved word. -/
def reserved : Scope Unit := reservedWords.foldl (fun s w => s.insert w ()) .empty

/-- A name a `const` can bind: the shape, and not reserved. -/
def validIdent (s : String) : Bool := identShape s && (reserved.find s).isNone

theorem validIdent_eq (s : String) : validIdent s = (identShape s && !reservedWords.contains s) := by
  simp only [validIdent, reserved, Scope.find_foldl, Scope.find_empty]
  cases reservedWords.contains s <;> rfl

/-- Globals the emitted code reads. A module binding one of these names would shadow it. -/
def emittedGlobals : List String := ["Object", "Array", "Number", "JSON"]

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
  | .null, l => .error (.nullRead l)
  | .undef, l => .error (.nullRead l)
  | _, _ => .ok .untracked

def readPath : Val → List String → Except Err Val
  | v, [] => .ok v
  | v, l :: ls =>
    match readField v l with
    | .ok w => readPath w ls
    | .error e => .error e

def evalAtom (env : List (String × Val)) : Atom → Except Err Val
  | .num n => .ok (if isSafe n then .num n else .notInt)
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

/-- `typeof v === "string"`. -/
def isStrVal : Val → Except Err Bool
  | .str _ => .ok true
  | .untracked => .error (.unmodeled "typeof of a value the model doesn't track")
  | _ => .ok false

/-- `Number.isSafeInteger(v) && !Object.is(v, -0)`. -/
def isIntVal : Val → Except Err Bool
  | .num n => .ok (isSafe n)
  | .untracked => .error (.unmodeled "testing a value the model doesn't track")
  | _ => .ok false

/-- `typeof v === "object" && v !== null && !Array.isArray(v) && Object.keys(v).length === n` and
    `Object.hasOwn(v, l)` for each label: a plain object whose own keys are exactly the labels. -/
def isShapeVal (ls : List String) : Val → Except Err Bool
  | .obj fs _ => .ok (fs.length == ls.length && ls.all fun l => (lookup fs l).isSome)
  | .untracked => .error (.unmodeled "testing a value the model doesn't track")
  | _ => .ok false

def evalTest (env : List (String × Val)) : Test → Except Err Bool
  | .isStr a => evalAtom env a >>= isStrVal
  | .isInt a => evalAtom env a >>= isIntVal
  | .isShape a ls => evalAtom env a >>= isShapeVal ls
  | .and t u =>
    match evalTest env t with
    | .ok true => evalTest env u
    | .ok false => .ok false
    | .error e => .error e

/-- The text of an atom parses as that atom. -/
def atomOk : Atom → Bool
  | .num _ => true
  | .str s => validStr s
  | .path x ls => validIdent x && ls.all identShape

def testOk : Test → Bool
  | .isStr a => atomOk a
  | .isInt a => atomOk a
  | .isShape a ls => atomOk a && ls.all validLabel
  | .and t u => testOk t && testOk u

/-- The text of an expression parses as that expression. -/
def staticOk : Expr → Bool
  | .atom a => atomOk a
  | .obj fs => (fs.map Prod.fst).all validLabel && fs.all (fun p => atomOk p.2)
  | .arrow x body => validIdent x && staticOk body
  | .app f a => staticOk f && staticOk a
  | .cond t a b => testOk t && staticOk a && staticOk b
  | .entry p => staticOk p

/-- Evaluate an expression with `n` units of fuel. A call's function, its argument and its body each
    get one unit less, so fuel bounds how deeply evaluation nests. -/
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
  | n + 1, env, .app f a =>
    match evalExpr n env f with
    | .error e => .error e
    | .ok fv =>
      match evalExpr n env a with
      | .error e => .error e
      | .ok w =>
        match fv with
        | .clos cenv x body => evalExpr n ((x, w) :: cenv) body
        | _ => .error .notCallable
  | n + 1, env, .cond t a b =>
    match evalTest env t with
    | .ok true => evalExpr n env a
    | .ok false => evalExpr n env b
    | .error e => .error e
  | n + 1, env, .entry p =>
    match evalExpr n env p with
    | .ok c => .ok (.entryOf c)
    | .error e => .error e

/-- Calling a function value with an argument, as an importer calls an entry's parse. -/
def applyVal (n : Nat) : Val → Val → Except Err Val
  | .clos cenv x body, w => evalExpr n ((x, w) :: cenv) body
  | _, _ => .error .notCallable

/-- Run the module from an environment of names already declared, with `n` units of fuel per line. -/
def runFrom (n : Nat) (env : List (String × Val)) : Program → Except Err (List (String × Val))
  | [] => .ok env
  | d :: ds =>
    if !validIdent d.name then .error (.syntax s!"{d.name} is not an identifier")
    else if emittedGlobals.contains d.name then .error (.unmodeled s!"{d.name} shadows a global the emitted code calls")
    else if (lookup env d.name).isSome then .error (.syntax s!"{d.name} is declared twice")
    else
      match evalExpr n env d.e with
      | .ok v =>
        if d.exported && d.name == "then" && callable v then .error (.unmodeled "an exported function named then: import() would wait on the module forever")
        else runFrom n ((d.name, v) :: env) ds
      | .error e => .error e

def run (n : Nat) (p : Program) : Except Err (List (String × Val)) := runFrom n [] p

/-- Strings joined from the right. `certify/check.sh` has Lean's kernel run the printer, and a string
    built by appending onto a growing left side, as `String.join` and `String.intercalate` do, costs the
    kernel time and memory quadratic in the length of the module. -/
def joinR : List String → String
  | [] => ""
  | s :: ss => s ++ joinR ss

/-- `joinR` with `sep` between the strings. -/
def sepR (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: ss => s ++ (sep ++ sepR sep ss)

def renderAtom : Atom → String
  | .num n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .path x ls => joinR (x :: ls.map (fun l => "." ++ l))

def renderTest : Test → String
  | .isStr a => "(typeof " ++ renderAtom a ++ " === \"string\")"
  | .isInt a => "(Number.isSafeInteger(" ++ renderAtom a ++ ") && !Object.is(" ++ renderAtom a ++ ", -0))"
  | .isShape a ls =>
    let x := renderAtom a
    "(typeof " ++ x ++ " === \"object\" && " ++ x ++ " !== null && !Array.isArray(" ++ x ++ ") && Object.keys(" ++ x ++
      ").length === " ++ toString ls.length ++ joinR (ls.map fun l => " && Object.hasOwn(" ++ x ++ ", \"" ++ l ++ "\")") ++ ")"
  | .and t u => "(" ++ renderTest t ++ " && " ++ renderTest u ++ ")"

def renderExpr : Expr → String
  | .atom a => renderAtom a
  | .obj [] => "Object.freeze({})"
  | .obj fs => "Object.freeze({ " ++ sepR ", " (fs.map fun (l, a) => l ++ ": " ++ renderAtom a) ++ " })"
  | .arrow x body => "(" ++ x ++ ") => " ++ renderExpr body
  | .app f a => (match f with
      | .arrow _ _ => "(" ++ renderExpr f ++ ")"
      | _ => renderExpr f) ++ "(" ++ renderExpr a ++ ")"
  | .cond t a b => "(" ++ renderTest t ++ " ? " ++ (match a with
      | .arrow _ _ => "(" ++ renderExpr a ++ ")"
      | _ => renderExpr a) ++ " : " ++ (match b with
      | .arrow _ _ => "(" ++ renderExpr b ++ ")"
      | _ => renderExpr b) ++ ")"
  | .entry p => "((p) => (input) => p($json(input)))(" ++ renderExpr p ++ ")"

def isEntry : Expr → Bool
  | .entry _ => true
  | _ => false

/-- `JSON.parse` of a string, and `undefined` for anything else or for text that doesn't parse: the
    entries' boundary, printed once at the top of a module that has any. -/
def jsonHelper : String :=
  "const $json = (s) => { if (typeof s !== \"string\") return void 0; try { return JSON.parse(s); } catch { return void 0; } };\n"

/-- The text of the module. -/
def render (p : Program) : String :=
  (if p.any (fun d => isEntry d.e) then jsonHelper else "") ++
    joinR (p.map fun d => s!"{if d.exported then "export " else ""}const {d.name} = {renderExpr d.e};\n")

/-! ## Fuel: any result other than running out stays the same with more fuel -/

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
    | cond t a b =>
      simp only [evalExpr] at h ⊢
      cases ht : evalTest env t with
      | error e => simpa [ht] using h
      | ok b' =>
        cases b' with
        | true => simp only [ht] at h ⊢; exact ih h hr m (by omega)
        | false => simp only [ht] at h ⊢; exact ih h hr m (by omega)
    | entry p =>
      simp only [evalExpr] at h ⊢
      cases hp : evalExpr n env p with
      | error e =>
        simp only [hp] at h
        rw [ih hp (by rw [h]; exact hr) m (by omega)]; exact h
      | ok c =>
        simp only [hp] at h
        rw [ih hp (by simp) m (by omega)]; exact h
    | app f a =>
      simp only [evalExpr] at h ⊢
      cases hf : evalExpr n env f with
      | error e =>
        simp only [hf] at h
        rw [ih hf (by rw [h]; exact hr) m (by omega)]; exact h
      | ok fv =>
        simp only [hf] at h
        rw [ih hf (by simp) m (by omega)]
        cases ha : evalExpr n env a with
        | error e =>
          simp only [ha] at h
          rw [ih ha (by rw [h]; exact hr) m (by omega)]; exact h
        | ok w =>
          simp only [ha] at h
          rw [ih ha (by simp) m (by omega)]
          cases fv
          all_goals (try simp only at h ⊢)
          case clos cenv x body => exact ih h hr m (by omega)
          all_goals exact h

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
            dsimp only
            split at h
            · rename_i hc; rw [if_pos hc]; exact h
            · rename_i hc; rw [if_neg hc]; exact ih h hr m hm
          · rename_i e he
            rw [evalExpr_mono n he (fun hx => hr (by rw [← h]; injection hx with hx; rw [hx])) m hm]
            exact h

theorem applyVal_mono {n c j r} (h : applyVal n c j = r) (hr : r ≠ .error .outOfFuel) (m : Nat) (hm : n ≤ m) :
    applyVal m c j = r := by
  cases c
  case clos cenv x body => simp only [applyVal] at h ⊢; exact evalExpr_mono n h hr m hm
  all_goals (simp only [applyVal] at h ⊢; exact h)

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
            split at h
            · cases h
            · apply ih h
              have hne : d.name ≠ x := fun e => by subst e; simp [hx] at hfresh
              simp [lookup, hne, hx]
          · cases h

theorem run_mono {n p r} (h : run n p = r) (hr : r ≠ .error .outOfFuel) : ∀ m, n ≤ m → run m p = r :=
  runFrom_mono p h hr

end LScript.JS
