import LScript.JS

/-!
# The parser

Text to declarations. Every function here is total, so Lean's kernel can run the parser, which is what
lets `certify/check.sh` start from the source text itself. The lexer and the parser each take fuel, one
unit per character or token. Every step consumes at least one, so the fuel `parse` gives them should
always suffice; that is an argument, not yet a theorem. Running out returns an error, so it could only
reject a program, never accept one.

    decl  := "type" Name "=" Type | "type" Name "=" "{" (label ":" Type),* "}" | name ":" Type "=" expr
    expr  := atom | name ("." label)+ | "{" (label ":" atom),* "}" | "{" name "with" (label ":" atom),* "}"
    atom  := integer | string | name

`type` and `with` are keywords only where the grammar puts them, as TypeScript treats `type`: `type`
followed by a name at the start of a declaration, and `with` after `{ name`. Anywhere else they are
ordinary names, so `type: Int = 1`, `{ type: "click" }` and `type type = Int` all parse.
-/

namespace LScript

inductive Tok where
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

/-- A token as it is written, for messages. -/
def Tok.show : Tok → String
  | .ident s => s
  | .int n => toString n
  | .str s => "\"" ++ s ++ "\""
  | .colon => ":"
  | .eq => "="
  | .lbrace => "{"
  | .rbrace => "}"
  | .comma => ","
  | .dot => "."

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The number a run of decimal digits writes. -/
def digitsValue (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Text to tokens, in reverse in `acc` until the end. -/
def lex : Nat → List Char → List Tok → Except String (List Tok)
  | _, [], acc => .ok acc.reverse
  | 0, _ :: _, _ => .error "the lexer ran out of fuel"
  | n + 1, c :: cs, acc =>
    if isSpace c then lex n cs acc
    else if c == '/' && cs.head? == some '/' then lex n (cs.dropWhile (· != '\n')) acc
    else if c == ':' then lex n cs (.colon :: acc)
    else if c == '=' then lex n cs (.eq :: acc)
    else if c == '{' then lex n cs (.lbrace :: acc)
    else if c == '}' then lex n cs (.rbrace :: acc)
    else if c == ',' then lex n cs (.comma :: acc)
    else if c == '.' then lex n cs (.dot :: acc)
    else if c == '"' then
      let body := cs.takeWhile (fun d => d != '"' && d != '\n')
      match cs.drop body.length with
      | '"' :: rest => lex n rest (.str (String.mk body) :: acc)
      | _ => .error "a string literal is not closed on its line"
    else if c.isDigit || (c == '-' && (cs.head?.map Char.isDigit).getD false) then
      let neg := c == '-'
      let from_ := if neg then cs else c :: cs
      let digits := from_.takeWhile Char.isDigit
      let v : Int := digitsValue digits
      lex n (from_.drop digits.length) (.int (if neg then -v else v) :: acc)
    else if JS.isIdentStart c then
      let word := (c :: cs).takeWhile JS.isIdentRest
      lex n ((c :: cs).drop word.length) (.ident (String.mk word) :: acc)
    else .error s!"unexpected character {repr c}"

def tyNameOf (s : String) : TyName :=
  if s == "Int" then .int else if s == "String" then .str else .named s

abbrev P (α : Type) := List Tok → Except String (α × List Tok)

def atom : P Atom
  | .int n :: rest => .ok (.int n, rest)
  | .str s :: rest => .ok (.str s, rest)
  | .ident x :: rest => .ok (.var x, rest)
  | .lbrace :: _ => .error "a field's value is a literal or a name, so give the nested record its own declaration first"
  | t :: _ => .error s!"expected a literal or a name, at {t.show}"
  | [] => .error "expected a literal or a name, at the end"

/-- `label: item, ...}` after the opening brace, through the closing one. -/
def fieldList {α : Type} (item : P α) : Nat → P (List (String × α))
  | 0, _ => .error "the parser ran out of fuel"
  | _ + 1, .rbrace :: rest => .ok ([], rest)
  | n + 1, .ident l :: .colon :: rest => do
    let (x, rest) ← item rest
    match rest with
    | .dot :: _ => .error s!"a field's value is a literal or a name, so give the read in {l} its own declaration first"
    | .comma :: rest => do
      let (more, rest) ← fieldList item n rest
      pure ((l, x) :: more, rest)
    | .rbrace :: rest => pure ([(l, x)], rest)
    | t :: _ => .error s!"expected , or }, at {t.show}"
    | [] => .error "expected , or }, at the end"
  | _ + 1, t :: _ => .error s!"expected label: ..., at {t.show}"
  | _ + 1, [] => .error "a { is not closed"

def tyItem : P TyName
  | .ident t :: rest => .ok (tyNameOf t, rest)
  | t :: _ => .error s!"expected a type, at {t.show}"
  | [] => .error "expected a type, at the end"

def labels : List Tok → List String × List Tok
  | .dot :: .ident l :: rest => let (ls, rest) := labels rest; (l :: ls, rest)
  | rest => ([], rest)

def expr (fuel : Nat) : P Expr
  | .lbrace :: .ident x :: .ident "with" :: rest => do
    let (fs, rest) ← fieldList atom fuel rest
    pure (.update x fs, rest)
  | .lbrace :: rest => do
    let (fs, rest) ← fieldList atom fuel rest
    pure (.record fs, rest)
  | .ident x :: rest =>
    let (ls, rest) := labels rest
    .ok (if ls.isEmpty then .atom (.var x) else .path x ls, rest)
  | toks => do
    let (a, rest) ← atom toks
    pure (.atom a, rest)

def decls : Nat → List Tok → Except String (List Decl)
  | _, [] => .ok []
  | 0, _ :: _ => .error "the parser ran out of fuel"
  | n + 1, .ident "type" :: .ident r :: .eq :: .lbrace :: rest => do
    let (fs, rest) ← fieldList tyItem n rest
    pure (.record r fs :: (← decls n rest))
  | n + 1, .ident "type" :: .ident a :: .eq :: .ident t :: rest => do
    pure (.alias a (tyNameOf t) :: (← decls n rest))
  | n + 1, .ident x :: .colon :: .ident t :: .eq :: rest => do
    let (e, rest) ← expr n rest
    pure (.val x (tyNameOf t) e :: (← decls n rest))
  | _ + 1, t :: _ => .error s!"expected `type Name = ...` or `name: Type = value`, at {t.show}"

def parse (src : String) : Except String Program :=
  match lex (src.length + 1) src.toList [] >>= fun toks => decls (toks.length + 1) toks with
  | .ok p => .ok p
  | .error e => .error s!"{e} [parse]"

end LScript
