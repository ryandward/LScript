import LScript.JS

/-!
# The parser

Text to declarations. This is the one part of the compiler with no proof; `test/run.sh` runs it on
every test program.
-/

namespace LScript

inductive Tok where
  | kwType
  | ident (s : String)
  | int (n : Int)
  | str (s : String)
  | colon
  | eq
  deriving Repr, DecidableEq

partial def lex : List Char → Array Tok → Except String (Array Tok)
  | [], acc => .ok acc
  | c :: cs, acc =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then lex cs acc
    else if c == '/' && cs.head? == some '/' then lex (cs.dropWhile (· != '\n')) acc
    else if c == ':' then lex cs (acc.push .colon)
    else if c == '=' then lex cs (acc.push .eq)
    else if c == '"' then
      let body := cs.takeWhile (fun d => d != '"' && d != '\n')
      match cs.drop body.length with
      | '"' :: rest => lex rest (acc.push (.str (String.mk body)))
      | _ => .error "a string literal is not closed on its line"
    else if c.isDigit || (c == '-' && (cs.head?.map Char.isDigit).getD false) then
      let neg := c == '-'
      let from_ := if neg then cs else c :: cs
      let digits := from_.takeWhile Char.isDigit
      let n : Int := (String.mk digits).toNat!
      lex (from_.drop digits.length) (acc.push (.int (if neg then -n else n)))
    else if JS.isIdentStart c then
      let word := (c :: cs).takeWhile JS.isIdentRest
      let w := String.mk word
      lex ((c :: cs).drop word.length) (acc.push (if w == "type" then .kwType else .ident w))
    else .error s!"unexpected character {repr c}"

def tyNameOf (s : String) : TyName :=
  if s == "Int" then .int else if s == "String" then .str else .alias s

def parseDecls : List Tok → Array Decl → Except String (Array Decl)
  | [], acc => .ok acc
  | .kwType :: .ident a :: .eq :: .ident t :: rest, acc =>
    parseDecls rest (acc.push (.type a (tyNameOf t)))
  | .ident x :: .colon :: .ident t :: .eq :: .int n :: rest, acc =>
    parseDecls rest (acc.push (.val x (tyNameOf t) (.int n)))
  | .ident x :: .colon :: .ident t :: .eq :: .str s :: rest, acc =>
    parseDecls rest (acc.push (.val x (tyNameOf t) (.str s)))
  | .ident x :: .colon :: .ident t :: .eq :: .ident y :: rest, acc =>
    parseDecls rest (acc.push (.val x (tyNameOf t) (.var y)))
  | t :: _, _ => .error s!"expected `type Name = Type` or `name: Type = value`, at {repr t}"

def parse (src : String) : Except String Program := do
  let toks ← lex src.toList #[]
  let ds ← parseDecls toks.toList #[]
  pure ds.toList

end LScript
