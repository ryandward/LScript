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
-/

namespace LScript

/-- A type as written: `Int`, `String`, or the name of a type declared earlier. -/
inductive TyName where
  | int
  | str
  | named (name : String)
  deriving Repr, DecidableEq

/-- What a type means once aliases are followed. A record is nominal: two records are the same type
    only if they are the same declaration. -/
inductive Ty where
  | int
  | str
  | record (name : String)
  deriving Repr, DecidableEq

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
