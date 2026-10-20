/-!
# LScript: the syntax

A program is a list of declarations. Every binding is immutable, so there is no `const` and no
`let`: a value declaration is `name: Type = value`, and it compiles to a JavaScript `const`.

Slice 2 adds closed records: named product types whose values have exactly the declared fields. There
are no classes and no methods. A record is data, and an update is a new record.

    type User = { name: String, age: Int }
    ann: User = { name: "Ann", age: 42 }
    annName: String = ann.name
    bob: User = { ann with name: "Bob" }

Expressions are flat on purpose: a record's fields, and an update's new values, are literals or
names. Every intermediate value has a name, which keeps each proof a plain induction.

Slice 3 adds functions of one parameter, curried. A function type is `A -> B`, a function is
`(x) => body`, and a call is `f(a)` or `f(a)(b)`, with literals or names as arguments. A function's
body is any expression, so it can be another function. Functions stay inside the module: only data is
exported, and a record holds only data.

    inc: Int -> Int = (x) => x
    rename: String -> User -> User = (n) => (u) => { u with name: n }
    bob: User = rename("Bob")(ann)
-/

namespace LScript

/-- A type as written: `Int`, `String`, the name of a type declared earlier, or a function type. -/
inductive TyName where
  | int
  | str
  | named (name : String)
  | fn (param result : TyName)                               -- A -> B
  deriving Repr, DecidableEq

/-- What a type means once aliases are followed. A record is nominal: two records are the same type
    only if they are the same declaration. -/
inductive Ty where
  | int
  | str
  | record (name : String)
  | fn (param result : Ty)
  deriving Repr, DecidableEq

/-- A type whose values are data: anything but a function. -/
def isData : Ty → Bool
  | .fn _ _ => false
  | _ => true

/-- A literal or a name. -/
inductive Atom where
  | int (n : Int)
  | str (s : String)
  | var (name : String)
  deriving Repr, DecidableEq

inductive Expr where
  | atom (a : Atom)
  | path (x : String) (labels : List String)                 -- x.l₁.l₂…
  | record (fields : List (String × Atom))                   -- { l: a, … }
  | update (x : String) (fields : List (String × Atom))      -- { x with l: a, … }
  | lam (param : String) (body : Expr)                       -- (x) => body
  | app (f : String) (arg : Atom) (more : List Atom)         -- f(a)(b)…: at least one argument
  deriving Repr, DecidableEq

inductive Decl where
  | alias (name : String) (rhs : TyName)                     -- type Age = Int
  | record (name : String) (fields : List (String × TyName)) -- type User = { name: String, age: Int }
  | val (name : String) (ty : TyName) (e : Expr)             -- ann: User = { … }
  deriving Repr, DecidableEq

abbrev Program := List Decl

/-- The first binding of `k` in an association list. -/
def lookup {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (l, x) :: rest, k => if l = k then some x else lookup rest k

end LScript
