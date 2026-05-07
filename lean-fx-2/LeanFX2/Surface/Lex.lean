import LeanFX2.Surface.TokenSchema

/-! # Surface/Lex — `List Char` → token stream (zero-axiom internals)

```lean
def Lex.run (chars : List Char) : Except (Array LexError) (Array PositionedToken)
```

Per `fx_lexer.md` §4-§5: UTF-8 source, ASCII identifiers, position
tracking, error recovery.

## Phase 10.A.2 — zero-axiom rewrite

The lexer now operates on `List Char` exclusively.  All internal
helpers, `Lex.run`, and the audited public surface are zero-axiom.

The `String → List Char` conversion required to consume an in-memory
host `String` is intentionally not defined in this module.  It lives in
`Surface/HostLex.lean`, outside the production umbrella, because Lean 4
v4.29.1's `String.toList` inherits `propext`, `Classical.choice`, and
`Quot.sound`.  Keeping that boundary out of `Surface/Lex.lean` lets the
production `LeanFX2` import surface stay zero-axiom.

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
`#print axioms LeanFX2.Surface.HostLex.runFromString` reports the three
documented leaks — confined to that host-boundary module.
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
Per fx_lexer.md §2.2.  Single-cons pattern keeps this propext-free.

Uses uniform `c.utf8Size` accounting in BOTH branches (newline
itself is ASCII so `'\n'.utf8Size = 1`).  This uniform accounting
makes the byte-conservation proof
`Lex.skipUntilNewline_byteLength_invariant` propext-clean — the
proof needs only `Nat.add_assoc`, no Char-eq case analysis. -/
def skipUntilNewline : List Char → Nat → Nat × List Char
  | [], n => (n, [])
  | c :: rest, n =>
    if c == '\n' then (n + c.utf8Size, rest)
    else skipUntilNewline rest (n + c.utf8Size)

/-- Skip a block comment body up to the closing `*/` (inclusive).
Per fx_lexer.md §2.3 — block comments do NOT nest.

Uses 3-pattern flat enumeration (`[]`, `[c]`, `c :: next :: rest2`)
rather than nested `match rest with` — Lean 4 v4.29.1's match compiler
auto-reduces flat patterns at `show` sites without `simp` help, which
makes the byte-conservation proof propext-clean.

The single-element case collapses both star-and-non-star branches to
`(n + c.utf8Size, [])` (in both cases the original code returns the
same value: star branch hits inner `[]`, non-star tail-recurses on
`[]` which returns `(n + c.utf8Size, [])`).

Uses uniform `c.utf8Size + next.utf8Size` accounting at the closing
`*/` (both ASCII so `*.utf8Size = /.utf8Size = 1`, total 2). -/
def skipBlockComment : List Char → Nat → Nat × List Char
  | [], n => (n, [])
  | c :: [], n => (n + c.utf8Size, [])
  | c :: next :: rest2, n =>
    if c == '*' then
      if next == '/' then (n + c.utf8Size + next.utf8Size, rest2)
      else skipBlockComment (next :: rest2) (n + c.utf8Size)
    else
      skipBlockComment (next :: rest2) (n + c.utf8Size)

/-- Skip ASCII whitespace + line/block comments at the head of
`chars`.  Returns (bytes skipped, remaining chars).  Fuel-bounded
structural recursion: each recursive call consumes at least one
char from the head, so `chars.length` is a sound upper bound on
total iterations.

Pattern style: 4-pattern flat enumeration over (fuel, chars):
  `(0, _)`, `(_+1, [])`, `(_+1, [c])`, `(_+1, c :: next :: rest2)`.
The `[c]` (single-char) case collapses to terminal results since
neither `//` nor `/*` can match a single char.  The two-or-more
case dispatches via nested `if`/`if`/`if` rather than nested
`match` — Lean 4 v4.29.1's match compiler auto-reduces flat
patterns under `show` blocks but leaves nested-match-on-projection
scrutinees un-reduced, blocking propext-clean rewriting.

Uniform `c.utf8Size` accounting: whitespace branch charges
`c.utf8Size` instead of `1` (semantically identical for ASCII
whitespace, but eliminates `of_decide_eq_true` propext leak in
the byte-conservation proof).  Comment-prefix charges
`c.utf8Size + next.utf8Size` instead of `2`. -/
def skipTrivia : Nat → List Char → Nat × List Char
  | 0,        chars => (0, chars)
  | _ + 1,    [] => (0, [])
  | _ + 1, c :: [] =>
    if isWhitespaceChar c then (c.utf8Size, [])
    else (0, [c])
  | fuel + 1, c :: next :: rest2 =>
    if isWhitespaceChar c then
      let (n, r) := skipTrivia fuel (next :: rest2)
      (c.utf8Size + n, r)
    else if c == '/' then
      if next == '/' then
        let (lineSkipped, afterLine) :=
          skipUntilNewline rest2 (c.utf8Size + next.utf8Size)
        let (n, r) := skipTrivia fuel afterLine
        (lineSkipped + n, r)
      else if next == '*' then
        let (blockSkipped, afterBlock) :=
          skipBlockComment rest2 (c.utf8Size + next.utf8Size)
        let (n, r) := skipTrivia fuel afterBlock
        (blockSkipped + n, r)
      else
        (0, c :: next :: rest2)
    else
      (0, c :: next :: rest2)

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
(reversed digit chars, byte size, remaining chars).

Uses uniform `c.utf8Size` accounting (semantically identical to
`+ 1` since digits are ASCII, but eliminates the propext leak in
the byte-conservation proof). -/
def readIntLexeme :
    List Char → List Char → Nat → List Char × Nat × List Char
  | [], acc, n => (acc, n, [])
  | c :: rest, acc, n =>
    if isDigitChar c then
      readIntLexeme rest (c :: acc) (n + c.utf8Size)
    else
      (acc, n, c :: rest)

/-- Resolve an escape character following a `\\` in a string literal.
Maps `n`/`t`/`r`/`"`/`\\` to their unescaped form; everything else
returns `none` (signalling an invalid escape sequence). -/
def resolveEscapeChar : Char → Option Char
  | 'n'  => some '\n'
  | 't'  => some '\t'
  | 'r'  => some '\r'
  | '"'  => some '"'
  | '\\' => some '\\'
  | _    => none

/-- Read a string literal body up to closing `"`.  Returns
(reversed body chars, byte size including delimiters,
remaining chars), or `none` if unterminated / invalid escape.

Uses the same 3-pattern flat structure that skipBlockComment uses
(`[]`, `[c]`, `c :: c2 :: rest2`) to avoid the nested
`match rest with | [] => ... | c2 :: rest2 => ...` shape — Lean
4 v4.29.1's match compiler refuses to auto-reduce that nested
form for abstract scrutinees, blocking propext-clean rewriting
in the byte-conservation proof.

Single-char `[c]` case collapses both outcomes:
* `c == '"'`: closing quote, returns `some (acc, n + c.utf8Size, [])`.
* otherwise (incl. `c == '\\'` with no second char to escape, or
  any char without a closing quote in sight): returns `none`.

Two-or-more `c :: c2 :: rest2` case dispatches via three-way `if`:
* `c == '"'`: closing quote.
* `c == '\\'`: try `resolveEscapeChar c2`; valid escape recurses
  on `rest2` with byte count `n + c.utf8Size + c2.utf8Size`,
  invalid returns `none`.
* otherwise: normal char, tail-recurse on `c2 :: rest2` with
  `n + c.utf8Size`.

All forms use uniform abstract `Char.utf8Size` so the proof reduces
by `Nat.add_assoc` without literal-char unfolding. -/
def readStringLexeme :
    List Char → List Char → Nat → Option (List Char × Nat × List Char)
  | [], _, _ => none  -- unterminated
  | c :: [], acc, n =>
    if c == '"' then some (acc, n + c.utf8Size, [])
    else none
  | c :: c2 :: rest2, acc, n =>
    if c == '"' then
      some (acc, n + c.utf8Size, c2 :: rest2)
    else if c == '\\' then
      match resolveEscapeChar c2 with
      | some ch =>
        readStringLexeme rest2 (ch :: acc) (n + c.utf8Size + c2.utf8Size)
      | none => none
    else
      readStringLexeme (c2 :: rest2) (c :: acc) (n + c.utf8Size)

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

Keyword recognition delegates to `KeywordKind.fromCharsExact`
(in `Surface/TokenSchema.lean`) — that function is the single
source of truth for the 92-keyword catalog.  Adding a keyword
to the language requires updating ONE table (in TokenSchema);
the lexer picks it up automatically.

`true`/`false` are special-cased back into `boolLit` ctors after
keyword lookup — the spec lists them as keywords (`kwTrue`/
`kwFalse`) AND as boolean literals; the lexer chooses the
literal form for downstream parser convenience.

The lexeme is passed in REVERSED order (head = last char read);
we reverse once here, the only allocation point.  Empty lexemes
cannot reach this — `lexOne` only calls when `isIdentStart` fired. -/
def classifyIdent (revLexeme : List Char) : Token :=
  let lexemeChars := revLexeme.reverse
  let lexemeStr := String.ofList lexemeChars
  match KeywordKind.fromCharsExact lexemeChars with
  | some kind =>
    -- `true` / `false` are listed as keywords in fx_grammar.md §2.2
    -- AND as boolean literals in §2.3.  The lexer prefers the
    -- literal form so the parser sees a uniform `boolLit`.  Use
    -- `decide` on the DecidableEq KeywordKind to avoid a `match`
    -- on `Option KeywordKind` with partial-ctor patterns (which
    -- triggers Lean's propext-leaking match path).
    if decide (kind = KeywordKind.trueK) then Token.boolLit true
    else if decide (kind = KeywordKind.falseK) then Token.boolLit false
    else kind.toToken
  | none =>
    -- Not a keyword.  Decide uident vs ident from the FIRST char
    -- of the (already-reversed) lexeme list — zero-axiom.
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

/-! ### Branch helpers — extracted from `lexOne` for proof discipline

`lexOne` was originally one large if-cascade with two error-emitting
branches (string and punctuation).  Inline structure made
preservation proofs (`err.offset = offset`) require deep nested
`generalize`+`cases` maneuvers through Lean 4 v4.29.1's matcher.

Splitting into named helpers per-branch lets each helper own its
preservation lemma with a self-contained proof.  See L07 below. -/

/-- Two-character operator lookup.  Pure `Char × Char → Option Token`
— no list manipulation (refactored from earlier shape that threaded
`more` through unchanged, which forced `lexOpOrPunct` to use a
hardcoded `2` byte count instead of the abstract
`firstChar.utf8Size + secondChar.utf8Size` that composes with
`charsByteLength` for the byte-conservation proof). -/
def lexTwoCharOp (firstChar secondChar : Char) : Option Token :=
  if firstChar == '-' && secondChar == '>' then some Token.arrow
  else if firstChar == '=' && secondChar == '>' then some Token.fatArrow
  else if firstChar == '|' && secondChar == '>' then some Token.pipe
  else if firstChar == '=' && secondChar == '=' then some Token.eqEq
  else if firstChar == '!' && secondChar == '=' then some Token.notEq
  else if firstChar == '<' && secondChar == '=' then some Token.le
  else if firstChar == '>' && secondChar == '=' then some Token.ge
  else if firstChar == '<' && secondChar == '<' then some Token.shiftLeft
  else if firstChar == '>' && secondChar == '>' then some Token.shiftRight
  else if firstChar == '.' && secondChar == '.' then some Token.dotdot
  else if firstChar == '@' && secondChar == '[' then some Token.atBracket
  else none

/-- Two-character operator lookup with two-element list peek.
`none` for empty rest; otherwise consults `lexTwoCharOp`.  Carries
the `secondChar` through so byte accounting in `lexOpOrPunct` can
use `firstChar.utf8Size + secondChar.utf8Size` directly. -/
def lexTwoCharPeek (firstChar : Char) :
    List Char → Option (Token × Char × List Char)
  | [] => none
  | secondChar :: more =>
    match lexTwoCharOp firstChar secondChar with
    | some tok => some (tok, secondChar, more)
    | none => none

/-- Look up a single-character punctuation token.  Returns `none` if
`firstChar` is not in the punctuation set.  Pure `Char → Option`,
no offset. -/
def lexSingleCharPunct (firstChar : Char) : Option Token := match firstChar with
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

/-- Operator/punctuation branch: try two-char then single-char.
Returns either a token step or an `unexpectedChar` error step.
The `offset` parameter is forwarded into the error case ONLY. -/
def lexOpOrPunct (offset : Nat) (firstChar : Char) (restChars : List Char) :
    LexStep :=
  match lexTwoCharPeek firstChar restChars with
  | some (tok, secondChar, more) =>
    LexStep.token tok (firstChar.utf8Size + secondChar.utf8Size) more
  | none =>
    match lexSingleCharPunct firstChar with
    | some tok => LexStep.token tok firstChar.utf8Size restChars
    | none =>
        LexStep.error (LexError.unexpectedChar offset firstChar)
          firstChar.utf8Size restChars

/-- String branch: try `readStringLexeme`; emit `unterminatedString`
on failure.  Takes `firstChar` (always `'"'` at call sites in
`lexOne`) so byte accounting uses the abstract
`firstChar.utf8Size`, sidestepping the propext leak that
`eq_of_beq` would introduce when reducing `'"'.utf8Size = 1`.

The `offset` parameter is forwarded into the error case ONLY. -/
def lexStringBranch (offset : Nat) (firstChar : Char) (restChars : List Char) : LexStep :=
  match readStringLexeme restChars [] firstChar.utf8Size with
  | some (revBody, byteLen, remaining) =>
      LexStep.token
        (Token.strLit (String.ofList revBody.reverse) StrKind.regular)
        byteLen remaining
  | none =>
      LexStep.error (LexError.unterminatedString offset) firstChar.utf8Size
        restChars

/-- Identifier branch: read identifier lexeme, classify into Token.
Pure `Char → List Char → LexStep`, no offset needed (identifier
branch never emits errors).  Uses projection form to match
Lean's internal compilation of destructuring `let`. -/
def lexIdentBranch (firstChar : Char) (restChars : List Char) : LexStep :=
  let identResult := readIdentLexeme (firstChar :: restChars) [] 0
  LexStep.token (classifyIdent identResult.fst) identResult.snd.fst identResult.snd.snd

/-- Digit branch: read integer lexeme, build `Token.intLit`.
Pure `Char → List Char → LexStep`, no offset needed (digit
branch never emits errors).  Uses projection form. -/
def lexDigitBranch (firstChar : Char) (restChars : List Char) : LexStep :=
  let digitResult := readIntLexeme (firstChar :: restChars) [] 0
  LexStep.token
    (Token.intLit (Int.ofNat (digitsToNat digitResult.fst.reverse 0)) none)
    digitResult.snd.fst digitResult.snd.snd

/-- Lex one token from `chars` (already trimmed of leading trivia).
`offset` is the current byte offset (for error reporting).

Refactored: ALL four branches delegate to named helpers.  The if
cascade is the only structure here.  This factoring matches
`lexOne_error_offset_eq`'s proof structure exactly: each branch
either delegates to a non-error helper (no preservation needed)
or to a helper with a per-branch preservation lemma. -/
def lexOne (offset : Nat) : List Char → LexStep
  | [] => LexStep.eof
  | (firstChar :: restChars) =>
    if isIdentStart firstChar then
      lexIdentBranch firstChar restChars
    else if isDigitChar firstChar then
      lexDigitBranch firstChar restChars
    else if firstChar == '"' then
      lexStringBranch offset firstChar restChars
    else
      lexOpOrPunct offset firstChar restChars

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
on success.  Use `HostLex.runFromString` if you deliberately cross the
host `String` boundary. -/
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

end LeanFX2.Surface
