import LScript.JS

/-!
# The parser

Text to declarations. This is the one part of the compiler with no proof; `test/run.sh` runs it on
every test program.

    decl  := "type" Name "=" Type | "type" Name "=" "{" (label ":" Type),* "}" | name ":" Type "=" expr
    expr  := atom | name ("." label)+ | "{" (label ":" atom),* "}" | "{" name "with" (label ":" atom),* "}"
    atom  := integer | string | name
-/

namespace LScript

inductive Tok where
  | kwType
  | kwWith
  | ident (s : String)
  | int (n : Int)
  | str (s : String)
  | colon
  | eq
  | lbrace
  | rbrace
  | comma
  | dot
  deriving Repr, DecidableEq

partial def lex : List Char → Array Tok → Except String (Array Tok)
  | [], acc => .ok acc
  | c :: cs, acc =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then lex cs acc
    else if c == '/' && cs.head? == some '/' then lex (cs.dropWhile (· != '\n')) acc
    else if c == ':' then lex cs (acc.push .colon)
    else if c == '=' then lex cs (acc.push .eq)
    else if c == '{' then lex cs (acc.push .lbrace)
    else if c == '}' then lex cs (acc.push .rbrace)
    else if c == ',' then lex cs (acc.push .comma)
    else if c == '.' then lex cs (acc.push .dot)
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
      let tok := if w == "type" then .kwType else if w == "with" then .kwWith else .ident w
      lex ((c :: cs).drop word.length) (acc.push tok)
    else .error s!"unexpected character {repr c}"

def tyNameOf (s : String) : TyName :=
  if s == "Int" then .int else if s == "String" then .str else .named s

abbrev P (α : Type) := List Tok → Except String (α × List Tok)

def atom : P Atom
  | .int n :: rest => .ok (.int n, rest)
  | .str s :: rest => .ok (.str s, rest)
  | .ident x :: rest => .ok (.var x, rest)
  | t :: _ => .error s!"expected a literal or a name, at {repr t}"
  | [] => .error "expected a literal or a name, at the end"

/-- `label: item, ...}` after the opening brace, through the closing one. -/
partial def fieldsOf {α : Type} (item : P α) : P (List (String × α))
  | .rbrace :: rest => .ok ([], rest)
  | .ident l :: .colon :: rest => do
    let (x, rest) ← item rest
    match rest with
    | .comma :: rest => do
      let (more, rest) ← fieldsOf item rest
      pure ((l, x) :: more, rest)
    | .rbrace :: rest => pure ([(l, x)], rest)
    | t :: _ => .error s!"expected , or }, at {repr t}"
    | [] => .error "expected , or }, at the end"
  | t :: _ => .error s!"expected label: ..., at {repr t}"
  | [] => .error "a { is not closed"

def tyItem : P TyName
  | .ident t :: rest => .ok (tyNameOf t, rest)
  | t :: _ => .error s!"expected a type, at {repr t}"
  | [] => .error "expected a type, at the end"

partial def labels : List Tok → List String × List Tok
  | .dot :: .ident l :: rest => let (ls, rest) := labels rest; (l :: ls, rest)
  | rest => ([], rest)

def expr : P Expr
  | .lbrace :: .ident x :: .kwWith :: rest => do
    let (fs, rest) ← fieldsOf atom rest
    pure (.update x fs, rest)
  | .lbrace :: rest => do
    let (fs, rest) ← fieldsOf atom rest
    pure (.record fs, rest)
  | .ident x :: rest =>
    let (ls, rest) := labels rest
    .ok (if ls.isEmpty then .atom (.var x) else .path x ls, rest)
  | toks => do
    let (a, rest) ← atom toks
    pure (.atom a, rest)

partial def decls : List Tok → Except String (List Decl)
  | [] => .ok []
  | .kwType :: .ident r :: .eq :: .lbrace :: rest => do
    let (fs, rest) ← fieldsOf tyItem rest
    pure (.record r fs :: (← decls rest))
  | .kwType :: .ident a :: .eq :: .ident t :: rest => do
    pure (.alias a (tyNameOf t) :: (← decls rest))
  | .ident x :: .colon :: .ident t :: .eq :: rest => do
    let (e, rest) ← expr rest
    pure (.val x (tyNameOf t) e :: (← decls rest))
  | t :: _ => .error s!"expected `type Name = ...` or `name: Type = value`, at {repr t}"

def parse (src : String) : Except String Program := do
  let toks ← lex src.toList #[]
  decls toks.toList

end LScript
