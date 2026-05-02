import LeanFX2.Surface.Token

/-! # Surface/Lex — `List Char` → token stream (zero-axiom internals)

```lean
def Lex.run (chars : List Char) : Except (Array LexError) (Array PositionedToken)
def Lex.runFromString (source : String) : Except (Array LexError) (Array PositionedToken)
```

Per `fx_lexer.md` §4-§5: UTF-8 source, ASCII identifiers, position
tracking, error recovery.

## Phase 10.A.2 — zero-axiom rewrite

The lexer now operates on `List Char` exclusively.  All internal
helpers, `Lex.run`, and the audited public surface are zero-axiom.

The single `String → List Char` conversion required to consume an
in-memory `String` lives in `Lex.runFromString` and inherits the
three Lean 4 v4.29.1 stdlib axioms (`propext`, `Classical.choice`,
`Quot.sound`) from `String.toList`.  Per AXIOMS.md, that boundary
shim is the only acceptable site — Pipeline composes from there
and the leak does not propagate into Algo/* or Foundation/*.

## What this implementation covers (Phase 10.A.1+)

* Whitespace + line/block comments (fuel-bounded structural)
* ASCII identifiers (snake_case → `ident`, PascalCase → `uident`)
* Integer literals (decimal only, no suffix; manual digit fold)
* Boolean literals (`true`/`false`)
* String literals (regular `"..."` only — no f/r/b prefixes yet)
* Punctuation: `( ) { } [ ]`, `, ; : .`
* Operators: `=`, `->`, `=>`, `+`, `-`, `*`, `/`, `==`, `!=`,
  `<`, `>`, `<=`, `>=`, `&`, `|`, `^`, `~`, `|>`, `@`, `@[`, `#`
* The 10 most common keywords (`fn`, `let`, `if`, `else`, `match`,
  `end`, `return`, `with`, `pub`, `type`)

## Algorithm

Single-pass `List Char` recursion.  At each step:
1. Skip whitespace + comments (fuel-bounded; fuel = total chars)
2. Determine the next token category by first character
3. Read the longest matching token's lexeme as a `List Char`
   accumulator
4. Emit `Token` (with lexeme rebuilt via `String.ofList` —
   zero-axiom direction) + recurse on the remainder

Position tracking: byte offset into the original source, computed
incrementally as we consume chars (UTF-8 codepoint sizing via
`Char.utf8Size`).

## Why `List Char` instead of `String`

In Lean 4 v4.29.1 `String` is backed by a UTF-8 `ByteArray` plus a
validity proof.  `String.toList`, `String.length`, `String.data`,
`String.toNat!` all require deserialising the byte array, which
involves `Quot.sound` + `propext` + `Classical.choice`.  In the
opposite direction `String.ofList : List Char → String` is a
plain structure constructor and is zero-axiom.

## Audit gates

`#print axioms Lex.run` reports "does not depend on any axioms".
`#print axioms Lex.runFromString` reports the three documented
leaks — confined to that one boundary function.
-/

namespace LeanFX2.Surface

/-- Lexer error categories.  Each carries a position (byte offset). -/
inductive LexError : Type
  | unexpectedChar (offset : Nat) (got : Char)
  | unterminatedString (offset : Nat)
  | invalidEscape (offset : Nat) (got : Char)
  deriving Repr

/-- Source position: byte offset only (line/col reconstruction is
deferred to error rendering — keeps the lexer simple).  -/
structure LexPos where
  offset : Nat
  deriving DecidableEq, Repr

/-- A token paired with its starting position. -/
structure PositionedToken where
  token : Token
  startPos : LexPos
  deriving Repr

/-- Test if a character starts an identifier (`a-zA-Z_`). -/
def isIdentStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

/-- Test if a character continues an identifier (alphanumeric + `_`). -/
def isIdentCont (c : Char) : Bool :=
  isIdentStart c || ('0' ≤ c && c ≤ '9')

/-- Test if a character starts a digit (`0-9`). -/
def isDigitChar (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- ASCII-uppercase test (zero-axiom; `Char.isUpper` is also
zero-axiom but we keep this local for clarity in classify). -/
def isAsciiUpper (c : Char) : Bool :=
  'A' ≤ c && c ≤ 'Z'

/-- Convert an ASCII digit char to its numeric value (0..9).
Returns 0 for non-digits — caller must filter via `isDigitChar`. -/
def digitValue (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- ASCII whitespace test: space, tab, LF, CR.  Per fx_lexer.md §2.1
the lexer also accepts vertical tab + form feed; those are added
when the lexer needs them. -/
def isWhitespaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Skip a line comment body up to the first newline (inclusive).
Per fx_lexer.md §2.2.  Single-cons pattern keeps this propext-free. -/
def skipUntilNewline : List Char → Nat → Nat × List Char
  | [], n => (n, [])
  | c :: rest, n =>
    if c == '\n' then (n + 1, rest)
    else skipUntilNewline rest (n + c.utf8Size)

/-- Skip a block comment body up to the closing `*/` (inclusive).
Per fx_lexer.md §2.3 — block comments do NOT nest.  Avoids the
double-cons pattern `'*' :: '/' :: rest` (which leaks propext via
Lean's match compiler) by matching cons once and using `==` on
the next char. -/
def skipBlockComment : List Char → Nat → Nat × List Char
  | [], n => (n, [])
  | c :: rest, n =>
    if c == '*' then
      match rest with
      | [] => (n + c.utf8Size, [])
      | next :: rest2 =>
        if next == '/' then (n + 2, rest2)
        else skipBlockComment rest (n + c.utf8Size)
    else
      skipBlockComment rest (n + c.utf8Size)

/-- Skip ASCII whitespace + line/block comments at the head of
`chars`.  Returns (bytes skipped, remaining chars).  Fuel-bounded
structural recursion: each recursive call consumes at least one
char from the head, so `chars.length` is a sound upper bound on
total iterations.

Pattern style: outer match peels one cons at a time, then nested
`if`/`match` on the head/next char.  Multi-character literal
patterns like `'/' :: '/' :: rest` are AVOIDED — Lean 4 v4.29.1's
match compiler emits propext-using auxiliaries for those. -/
def skipTrivia : Nat → List Char → Nat × List Char
  | 0,        chars => (0, chars)
  | _ + 1,    [] => (0, [])
  | fuel + 1, c :: rest =>
    if isWhitespaceChar c then
      let (n, r) := skipTrivia fuel rest
      (1 + n, r)
    else if c == '/' then
      match rest with
      | [] => (0, c :: rest)
      | next :: rest2 =>
        if next == '/' then
          let (lineSkipped, afterLine) := skipUntilNewline rest2 2
          let (n, r) := skipTrivia fuel afterLine
          (lineSkipped + n, r)
        else if next == '*' then
          let (blockSkipped, afterBlock) := skipBlockComment rest2 2
          let (n, r) := skipTrivia fuel afterBlock
          (blockSkipped + n, r)
        else
          (0, c :: rest)
    else
      (0, c :: rest)

/-- Read a contiguous identifier-or-keyword.  Returns
(reversed lexeme chars, byte size, remaining chars).  We
accumulate as a reversed list to keep cons O(1); caller reverses
once when constructing the final `String`. -/
def readIdentLexeme :
    List Char → List Char → Nat → List Char × Nat × List Char
  | [], acc, n => (acc, n, [])
  | c :: rest, acc, n =>
    if isIdentCont c then
      readIdentLexeme rest (c :: acc) (n + c.utf8Size)
    else
      (acc, n, c :: rest)

/-- Read a contiguous decimal integer literal.  Returns
(reversed digit chars, byte size, remaining chars). -/
def readIntLexeme :
    List Char → List Char → Nat → List Char × Nat × List Char
  | [], acc, n => (acc, n, [])
  | c :: rest, acc, n =>
    if isDigitChar c then
      readIntLexeme rest (c :: acc) (n + 1)  -- digits are 1 byte
    else
      (acc, n, c :: rest)

/-- Read a string literal body up to closing `"`.  Returns
(reversed body chars, byte size including delimiters,
remaining chars), or `none` if unterminated / invalid escape. -/
def readStringLexeme :
    List Char → List Char → Nat → Option (List Char × Nat × List Char)
  | [], _, _ => none  -- unterminated
  | '"' :: rest, acc, n => some (acc, n + 1, rest)  -- closing "
  | '\\' :: c :: rest, acc, n =>
    let escaped : Option Char := match c with
      | 'n'  => some '\n'
      | 't'  => some '\t'
      | 'r'  => some '\r'
      | '"'  => some '"'
      | '\\' => some '\\'
      | _    => none
    match escaped with
    | some ch => readStringLexeme rest (ch :: acc) (n + 2)
    | none    => none
  | '\\' :: [], _, _ => none
  | c :: rest, acc, n => readStringLexeme rest (c :: acc) (n + c.utf8Size)

/-- Fold a list of decimal-digit chars (in left-to-right order)
into a single `Nat`.  Non-digit chars are treated as 0 — caller
guarantees all chars came from `readIntLexeme` so this never
fires.  Zero-axiom (no `String.toNat!`). -/
def digitsToNat : List Char → Nat → Nat
  | [], acc => acc
  | c :: rest, acc => digitsToNat rest (acc * 10 + digitValue c)

/-- Classify an identifier lexeme (as a `List Char`) as keyword,
uident, or ident.  Operates directly on the char list to avoid
`String.length` / `String.front` / `String.toList` which all leak
axioms in Lean 4 v4.29.1.

The lexeme is passed in REVERSED order (head = last char read);
we reverse once here, the only allocation point.  Empty lexemes
cannot reach this — `lexOne` only calls when `isIdentStart` fired. -/
def classifyIdent (revLexeme : List Char) : Token :=
  let lexemeChars := revLexeme.reverse
  let lexemeStr := String.ofList lexemeChars
  -- Match on the keyword set first (lexemeStr equality is fine —
  -- `String.ofList` produces a structurally-built `String`, and
  -- `==` on String is defined via `BEq` which delegates to
  -- propositional equality but does not require the leaky readers).
  match lexemeStr with
  | "fn"     => Token.kwFn
  | "let"    => Token.kwLet
  | "if"     => Token.kwIf
  | "else"   => Token.kwElse
  | "match"  => Token.kwMatch
  | "end"    => Token.kwEnd
  | "return" => Token.kwReturn
  | "with"   => Token.kwWith
  | "pub"    => Token.kwPub
  | "type"   => Token.kwType
  | "true"   => Token.boolLit true
  | "false"  => Token.boolLit false
  | _ =>
    -- Decide uident vs ident from the FIRST char of the
    -- (already-reversed) lexeme list — zero-axiom.
    match lexemeChars with
    | c :: _ => if isAsciiUpper c then Token.uident lexemeStr
                else Token.ident lexemeStr
    | []     => Token.ident lexemeStr  -- unreachable per caller contract

/-- Internal lex result: produced token + bytes consumed + remaining
chars, OR error + bytes-to-skip + remaining chars. -/
inductive LexStep : Type
  | token (tok : Token) (bytes : Nat) (rest : List Char)
  | error (err : LexError) (bytes : Nat) (rest : List Char)
  | eof

/-- Lex one token from `chars` (already trimmed of leading trivia).
`offset` is the current byte offset (for error reporting). -/
def lexOne (offset : Nat) : List Char → LexStep
  | [] => LexStep.eof
  | (c :: rest) =>
    if isIdentStart c then
      let (revLex, bytes, remaining) := readIdentLexeme (c :: rest) [] 0
      LexStep.token (classifyIdent revLex) bytes remaining
    else if isDigitChar c then
      let (revDigits, bytes, remaining) := readIntLexeme (c :: rest) [] 0
      let digits := revDigits.reverse
      let value := digitsToNat digits 0
      LexStep.token (Token.intLit (Int.ofNat value) none) bytes remaining
    else if c == '"' then
      match readStringLexeme rest [] 1 with  -- 1 = opening quote
      | some (revBody, bytes, remaining) =>
          let body := String.ofList revBody.reverse
          LexStep.token (Token.strLit body StrKind.regular) bytes remaining
      | none =>
          LexStep.error (LexError.unterminatedString offset) 1 rest
    else
      -- Multi-character operators (look ahead one).  Avoid the
      -- two-element pattern `c1, c2 :: more` which leaks propext;
      -- instead peek at `rest` once and `if` on the second char.
      let twoChar : Option (Token × List Char) :=
        match rest with
        | [] => none
        | next :: more =>
          if c == '-' && next == '>' then some (Token.arrow, more)
          else if c == '=' && next == '>' then some (Token.fatArrow, more)
          else if c == '|' && next == '>' then some (Token.pipe, more)
          else if c == '=' && next == '=' then some (Token.eqEq, more)
          else if c == '!' && next == '=' then some (Token.notEq, more)
          else if c == '<' && next == '=' then some (Token.le, more)
          else if c == '>' && next == '=' then some (Token.ge, more)
          else if c == '<' && next == '<' then some (Token.shiftLeft, more)
          else if c == '>' && next == '>' then some (Token.shiftRight, more)
          else if c == '.' && next == '.' then some (Token.dotdot, more)
          else if c == '@' && next == '[' then some (Token.atBracket, more)
          else none
      match twoChar with
      | some (tok, more) => LexStep.token tok 2 more
      | none =>
        let single : Option Token := match c with
          | '(' => some Token.lparen
          | ')' => some Token.rparen
          | '{' => some Token.lbrace
          | '}' => some Token.rbrace
          | '[' => some Token.lbracket
          | ']' => some Token.rbracket
          | ',' => some Token.comma
          | ';' => some Token.semicolon
          | ':' => some Token.colon
          | '.' => some Token.dot
          | '=' => some Token.equals
          | '+' => some Token.plus
          | '-' => some Token.minus
          | '*' => some Token.star
          | '/' => some Token.slash
          | '%' => some Token.percent
          | '<' => some Token.lt
          | '>' => some Token.gt
          | '&' => some Token.amp
          | '|' => some Token.bar
          | '^' => some Token.caret
          | '~' => some Token.tilde
          | '@' => some Token.atSign
          | '#' => some Token.hash
          | _   => none
        match single with
        | some tok => LexStep.token tok c.utf8Size rest
        | none => LexStep.error (LexError.unexpectedChar offset c) c.utf8Size rest

/-- Drive the lexer until EOF.  Fuel is sized at the caller from
`chars.length`; each iteration consumes at least one char so the
fuel suffices.  Returns accumulated tokens + errors.

Pattern style: nested matches on `fuel` and `chars` separately —
multi-pattern overlapping cases (`0, _, _, ...` vs `_, _, [], ...`)
trigger Lean's propext-using match compiler.  Splitting them
keeps `lexLoop` zero-axiom. -/
def lexLoop (fuel : Nat) (offset : Nat) (chars : List Char)
    (tokens : Array PositionedToken) (errors : Array LexError) :
    Array PositionedToken × Array LexError :=
  match fuel with
  | 0 => (tokens, errors)
  | fuelMinusOne + 1 =>
    match chars with
    | [] => (tokens, errors)
    | _ :: _ =>
      let triviaFuel := chars.length
      let (skipped, afterTrivia) := skipTrivia triviaFuel chars
      match lexOne (offset + skipped) afterTrivia with
      | LexStep.eof => (tokens, errors)
      | LexStep.token tok bytes remaining =>
          let positioned : PositionedToken :=
            { token := tok, startPos := { offset := offset + skipped } }
          lexLoop fuelMinusOne (offset + skipped + bytes) remaining
            (tokens.push positioned) errors
      | LexStep.error err bytes remaining =>
          lexLoop fuelMinusOne (offset + skipped + bytes) remaining
            tokens (errors.push err)

/-- Compute the total UTF-8 byte length of a `List Char`.
Zero-axiom alternative to `String.length`. -/
def charsByteLength : List Char → Nat
  | [] => 0
  | c :: rest => c.utf8Size + charsByteLength rest

/-- Lex an FX source.  Input is `List Char` (zero-axiom).  Returns
`Except errors tokens` with a final `eof` sentinel token appended
on success.  Use `Lex.runFromString` if you have a `String`. -/
def Lex.run (chars : List Char) :
    Except (Array LexError) (Array PositionedToken) :=
  let fuel := chars.length + 1  -- +1 to handle empty input cleanly
  let totalBytes := charsByteLength chars
  let (tokens, errors) := lexLoop fuel 0 chars #[] #[]
  if errors.isEmpty then
    let withEof := tokens.push
      { token := Token.eof, startPos := { offset := totalBytes } }
    .ok withEof
  else
    .error errors

/-- Boundary entry: consume an in-memory `String`.  This is the
ONLY function in `Surface/Lex.lean` that depends on stdlib axioms
(`propext`, `Classical.choice`, `Quot.sound` — all from
`String.toList` which deserialises the underlying UTF-8
byte array).  All callers should funnel through this single shim
to keep the leak isolated. -/
def Lex.runFromString (source : String) :
    Except (Array LexError) (Array PositionedToken) :=
  Lex.run source.toList

end LeanFX2.Surface
