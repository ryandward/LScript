/-!
# LScript, slice 1: the syntax

A program is a list of declarations. Every binding is immutable, so there is no `const` and no
`let`: a value declaration is `name: Type = value`, and it compiles to a JavaScript `const`.

    type Age = Int
    myAge: Age = 10
    greeting: String = "hi"
    copy: Age = myAge
-/

namespace LScript

/-- A type as written: `Int`, `String`, or the name of an alias declared earlier. -/
inductive TyName where
  | int
  | str
  | alias (name : String)
  deriving Repr, DecidableEq

/-- What a type means once aliases are followed. -/
inductive Ty where
  | int
  | str
  deriving Repr, DecidableEq

inductive Expr where
  | int (n : Int)
  | str (s : String)
  | var (name : String)
  deriving Repr, DecidableEq

inductive Decl where
  | type (name : String) (rhs : TyName)            -- type Age = Int
  | val (name : String) (ty : TyName) (e : Expr)   -- myAge: Age = 10
  deriving Repr, DecidableEq

abbrev Program := List Decl

/-- The first binding of `k` in an association list. -/
def lookup {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (l, x) :: rest, k => if l = k then some x else lookup rest k

end LScript
