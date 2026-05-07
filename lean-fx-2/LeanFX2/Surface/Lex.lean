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

/-- Look up a two-character operator at `(firstChar, secondChar)`.
Returns `some (Token, restAfterTwo)` when matched, `none`
otherwise.  Pure `Char × Char × List Char → Option`, no offset. -/
def lexTwoCharOp (firstChar secondChar : Char) (more : List Char) :
    Option (Token × List Char) :=
  if firstChar == '-' && secondChar == '>' then some (Token.arrow, more)
  else if firstChar == '=' && secondChar == '>' then some (Token.fatArrow, more)
  else if firstChar == '|' && secondChar == '>' then some (Token.pipe, more)
  else if firstChar == '=' && secondChar == '=' then some (Token.eqEq, more)
  else if firstChar == '!' && secondChar == '=' then some (Token.notEq, more)
  else if firstChar == '<' && secondChar == '=' then some (Token.le, more)
  else if firstChar == '>' && secondChar == '=' then some (Token.ge, more)
  else if firstChar == '<' && secondChar == '<' then some (Token.shiftLeft, more)
  else if firstChar == '>' && secondChar == '>' then some (Token.shiftRight, more)
  else if firstChar == '.' && secondChar == '.' then some (Token.dotdot, more)
  else if firstChar == '@' && secondChar == '[' then some (Token.atBracket, more)
  else none

/-- Two-character operator lookup with two-element list peek.
`none` for empty rest; otherwise consults `lexTwoCharOp`. -/
def lexTwoCharPeek (firstChar : Char) : List Char → Option (Token × List Char)
  | [] => none
  | secondChar :: more => lexTwoCharOp firstChar secondChar more

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
  | some (tok, more) => LexStep.token tok 2 more
  | none =>
    match lexSingleCharPunct firstChar with
    | some tok => LexStep.token tok firstChar.utf8Size restChars
    | none =>
        LexStep.error (LexError.unexpectedChar offset firstChar)
          firstChar.utf8Size restChars

/-- String branch: try `readStringLexeme`; emit `unterminatedString`
on failure.  The `offset` parameter is forwarded into the error
case ONLY. -/
def lexStringBranch (offset : Nat) (restChars : List Char) : LexStep :=
  match readStringLexeme restChars [] 1 with
  | some (revBody, byteLen, remaining) =>
      LexStep.token
        (Token.strLit (String.ofList revBody.reverse) StrKind.regular)
        byteLen remaining
  | none =>
      LexStep.error (LexError.unterminatedString offset) 1 restChars

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
      lexStringBranch offset restChars
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

/-! ## Audit L03 — `Lex.run`'s success branch is EOF-terminated

The lemmas below establish that whenever `Lex.run` returns
`Except.ok tokens`, the underlying token list ends with a
`Token.eof` sentinel.  This is the load-bearing contract between
the lexer and downstream parser: the parser may rely on the
`eof` sentinel as an unconditional end-of-input marker.

Stated via `tokens.toList.getLast?` rather than `Array.back?` to
avoid Lean 4 v4.29.1's `Array.back?_push` / `Array.size_push`
simp lemmas, both of which transitively depend on `propext` and
would force the production `Surface.Lex` module out of zero-
axiom territory.  `Array.toList` is a structure projection
(`a.toList = a.toList`, `rfl`) and `List.getLast?` is built from
plain pattern matching, so the routes through them are clean.

All zero-axiom under `#print axioms`. -/

/-- Appending an element to a list via `List.concat` makes that
element the `getLast?` of the result.  Proved by structural
recursion; no `simp` lemmas (which leak `propext` via Lean's
match compiler when applied to `List.concat`'s `brecOn` body). -/
theorem List.concat_getLast?_eq {alpha : Type} :
    ∀ (initialList : List alpha) (lastElem : alpha),
      (initialList.concat lastElem).getLast? = some lastElem
  | [], _ => rfl
  | head :: rest, lastElem => by
    show (head :: rest.concat lastElem).getLast? = some lastElem
    match concatEq : rest.concat lastElem with
    | [] =>
        -- `rest.concat lastElem` is non-empty by case analysis on `rest`.
        have concatNonEmpty : rest.concat lastElem ≠ [] := by
          cases rest with
          | nil => intro hContra; cases hContra
          | cons _ _ => intro hContra; cases hContra
        exact absurd concatEq concatNonEmpty
    | nextHead :: nextTail =>
        show (head :: nextHead :: nextTail).getLast? = some lastElem
        have ihRecursive : (rest.concat lastElem).getLast? = some lastElem :=
          List.concat_getLast?_eq rest lastElem
        rw [concatEq] at ihRecursive
        exact ihRecursive

/-- Pushing an element onto an `Array` makes that element the
last entry of `toList`.  Direct corollary of
`List.concat_getLast?_eq` plus the definitional equation
`(arr.push x).toList = arr.toList.concat x` (which holds by
`rfl` since `Array.push` is defined as `⟨a.toList.concat v⟩`). -/
theorem Array.push_toList_getLast?_eq {alpha : Type}
    (arrInput : Array alpha) (lastElem : alpha) :
    (arrInput.push lastElem).toList.getLast? = some lastElem := by
  show (arrInput.toList.concat lastElem).getLast? = some lastElem
  exact List.concat_getLast?_eq arrInput.toList lastElem

/-- **Audit L03**: every successful `Lex.run` output ends with a
`Token.eof` sentinel.  Whenever `Lex.run chars` returns
`Except.ok tokens`, the last positioned token in `tokens.toList`
exists and carries `Token.eof` as its token field.

Proof outline:

1. Unfold `Lex.run` to expose its body — a `let-match-if` over
   `lexLoop`'s pair return.
2. Destructure the `lexLoop` pair into `(lexTokens, lexErrors)`
   via `match`; this reduces the wrapping `match` arm.
3. Rewrap the post-match expression at its actual type via a
   `have ... := runOk2` cast — this shrinks the goal to a plain
   `if-then-else`.
4. Branch on `lexErrors.isEmpty`:
   * `true`: `runOk` says `lexTokens.push eofPos = tokens`; supply
     the pushed `eofPos` as the existential witness, discharge
     the `getLast?` claim via `Array.push_toList_getLast?_eq`.
   * `false`: `runOk` becomes `Except.error _ = Except.ok _`;
     `cases` discharges the contradiction.

Zero-axiom under `#print axioms`. -/
theorem Lex.run_eof_terminated
    (chars : List Char) (tokens : Array PositionedToken)
    (runOk : Lex.run chars = Except.ok tokens) :
    ∃ eofPos : PositionedToken,
      tokens.toList.getLast? = some eofPos ∧ eofPos.token = Token.eof := by
  -- Step 1: unfold via an explicit `rfl` witness to keep the `match`
  -- visible after rewrite (plain `unfold` produces a `have`-binding
  -- form that blocks subsequent destructuring).
  have eqRun : Lex.run chars =
    (match lexLoop (chars.length + 1) 0 chars #[] #[] with
    | (lexTokens, lexErrors) =>
      if lexErrors.isEmpty = true then
        Except.ok (lexTokens.push
          ({ token := Token.eof,
             startPos := { offset := charsByteLength chars } } :
             PositionedToken))
      else Except.error lexErrors) := rfl
  rw [eqRun] at runOk
  -- Step 2: destructure the pair returned by lexLoop.
  match lexLoopEq : lexLoop (chars.length + 1) 0 chars #[] #[], runOk with
  | (lexTokens, lexErrors), runOkPair =>
    -- Step 3: reduce the wrapping `match (lexTokens, lexErrors) with ...`
    -- by ascription — both sides are definitionally equal.
    have runOkIf :
        (if lexErrors.isEmpty = true then
            Except.ok (lexTokens.push
              ({ token := Token.eof,
                 startPos := { offset := charsByteLength chars } } :
                 PositionedToken))
          else Except.error lexErrors)
        = Except.ok tokens := runOkPair
    -- Step 4: branch on the `if`.
    by_cases hErrorsEmpty : lexErrors.isEmpty = true
    · rw [if_pos hErrorsEmpty] at runOkIf
      let eofPos : PositionedToken :=
        { token := Token.eof, startPos := { offset := charsByteLength chars } }
      have tokensEq : lexTokens.push eofPos = tokens := by
        injection runOkIf
      refine ⟨eofPos, ?_, rfl⟩
      rw [← tokensEq]
      exact Array.push_toList_getLast?_eq _ eofPos
    · rw [if_neg hErrorsEmpty] at runOkIf
      cases runOkIf

/-! ## L02: classifyIdent reverses correctly (#1200)

`classifyIdent` consumes the lexeme in REVERSED order (last
char read = head of list) and reverses internally.  Composed
with `KeywordKind.toLexemeChars` (which yields the FORWARD
spelling), feeding `kind.toLexemeChars.reverse` into
`classifyIdent` recovers the keyword token.

Three cases: `trueK` and `falseK` decode to `Token.boolLit`
(per `classifyIdent`'s special-case for boolean literals);
every other keyword decodes to `kind.toToken`. -/

/-- L02 case A: `trueK`'s lexeme `['t','r','u','e']` reversed
through `classifyIdent` recovers the `boolLit true` token
(NOT `Token.kwTrue`, because `classifyIdent` prefers the
literal form for downstream parser convenience). -/
theorem Lex.classifyIdent_kwTrue :
    classifyIdent KeywordKind.trueK.toLexemeChars.reverse
      = Token.boolLit true := by
  decide

/-- L02 case B: `falseK`'s lexeme `['f','a','l','s','e']` reversed
through `classifyIdent` recovers the `boolLit false` token. -/
theorem Lex.classifyIdent_kwFalse :
    classifyIdent KeywordKind.falseK.toLexemeChars.reverse
      = Token.boolLit false := by
  decide

/-- L02 case C: every keyword OTHER than `trueK`/`falseK`
decodes through `classifyIdent` back to its canonical
`Token.toToken` form.  The reversal cancels and the
`fromCharsExact_toLexemeChars` round-trip recovers the
original `KeywordKind`; the two `decide` guards both
evaluate to `false` per the hypotheses. -/
theorem Lex.classifyIdent_keyword_toToken (kind : KeywordKind)
    (notTrue : kind ≠ KeywordKind.trueK)
    (notFalse : kind ≠ KeywordKind.falseK) :
    classifyIdent kind.toLexemeChars.reverse = kind.toToken := by
  cases kind <;> first
    | (exact absurd rfl notTrue)
    | (exact absurd rfl notFalse)
    | rfl

/-! ## L07: `LexError.offset` lies within source range (#1205)

Every `LexError` produced by `Lex.run chars` carries an offset
that fits within the source byte length.  This section ships a
mathematically bulletproof proof chain:

1. **Projection** — `LexError.offset` total, all 3 ctors.
2. **Per-step preservation** — `lexOne offset _ = LexStep.error err _ _`
   implies `err.offset = offset`.  Walks the full if/else cascade.
3. **Loop monotonicity** — `lexLoop` only ever pushes errors with
   offset bounded by `offset + skipped` at the call site, where
   `skipped` is the trivia bytes consumed.  Combined with the
   structural fact that `skipTrivia chars` returns `(skipped, _)`
   with `skipped ≤ charsByteLength chars`, the invariant gives
   `err.offset ≤ initialOffset + charsByteLength chars`.
3'. **Run bound** — `Lex.run chars = .error errs` implies every
   `err ∈ errs.toList` has `err.offset ≤ charsByteLength chars`
   (initial offset = 0).

All declarations zero-axiom under `#print axioms`. -/

/-- Unified projection: read the byte offset out of any `LexError`
constructor.  Total — every `LexError` carries an `offset`.  -/
def LexError.offset : LexError → Nat
  | LexError.unexpectedChar offsetVal _ => offsetVal
  | LexError.unterminatedString offsetVal => offsetVal
  | LexError.invalidEscape offsetVal _ => offsetVal

/-- Per-ctor projection for `unexpectedChar` — definitionally `rfl`.  -/
theorem LexError.offset_unexpectedChar (offsetVal : Nat) (gotChar : Char) :
    (LexError.unexpectedChar offsetVal gotChar).offset = offsetVal := rfl

/-- Per-ctor projection for `unterminatedString` — definitionally `rfl`.  -/
theorem LexError.offset_unterminatedString (offsetVal : Nat) :
    (LexError.unterminatedString offsetVal).offset = offsetVal := rfl

/-- Per-ctor projection for `invalidEscape` — definitionally `rfl`.  -/
theorem LexError.offset_invalidEscape (offsetVal : Nat) (gotChar : Char) :
    (LexError.invalidEscape offsetVal gotChar).offset = offsetVal := rfl

/-- **L07 totality**: `LexError.offset` is total — every `LexError`
case yields some `Nat` offset.  Witnessed by full `cases`
enumeration; the projection itself is structurally recursive,
so this lemma exists primarily as a smoke gate against future
ctor additions to `LexError` that forget an `offset` field.

Zero-axiom — pure pattern-match enumeration. -/
theorem LexError.offset_total (err : LexError) :
    ∃ offsetVal : Nat, err.offset = offsetVal := by
  cases err with
  | unexpectedChar offsetVal _ => exact ⟨offsetVal, rfl⟩
  | unterminatedString offsetVal => exact ⟨offsetVal, rfl⟩
  | invalidEscape offsetVal _ => exact ⟨offsetVal, rfl⟩

/-! ## L07 — per-helper + per-step preservation theorems (#1205)

The branch-helper refactor above (`lexStringBranch`,
`lexOpOrPunct`, `lexTwoCharPeek`, `lexSingleCharPunct`) lets each
preservation lemma decompose cleanly:

* `lexStringBranch_error_offset_eq` — when the string branch
  emits `LexStep.error err _ _`, `err.offset = offset`.
* `lexOpOrPunct_error_offset_eq` — when the op/punct branch
  emits `LexStep.error err _ _`, `err.offset = offset`.
* `lexOne_error_offset_eq` — composes the two helper lemmas
  with the identifier/digit/eof branches (which never emit).

All zero-axiom; verified at the end of this section under
`#assert_no_axioms`. -/

/-- **L07.1**: `lexStringBranch offset restChars = LexStep.error
err _ _` implies `err.offset = offset`.  The string branch only
emits `LexError.unterminatedString offset` when `readStringLexeme`
returns `none`. -/
theorem Lex.lexStringBranch_error_offset_eq (offset : Nat)
    (restChars : List Char)
    {err : LexError} {bytes : Nat} {restAfter : List Char}
    (stepEq : lexStringBranch offset restChars
              = LexStep.error err bytes restAfter) :
    err.offset = offset := by
  unfold lexStringBranch at stepEq
  generalize hReadStr : readStringLexeme restChars [] 1 = readResult at stepEq
  cases readResult with
  | none =>
    -- stepEq : LexStep.error (LexError.unterminatedString offset) 1 restChars
    --        = LexStep.error err bytes restAfter
    injection stepEq with errEq _ _
    rw [← errEq]; rfl
  | some _ =>
    -- stepEq : LexStep.token ... = LexStep.error err bytes restAfter
    cases stepEq

/-- **L07.2**: `lexOpOrPunct offset firstChar restChars =
LexStep.error err _ _` implies `err.offset = offset`.  The op/punct
branch only emits `LexError.unexpectedChar offset firstChar` when
both `lexTwoCharPeek` and `lexSingleCharPunct` return `none`. -/
theorem Lex.lexOpOrPunct_error_offset_eq (offset : Nat)
    (firstChar : Char) (restChars : List Char)
    {err : LexError} {bytes : Nat} {restAfter : List Char}
    (stepEq : lexOpOrPunct offset firstChar restChars
              = LexStep.error err bytes restAfter) :
    err.offset = offset := by
  unfold lexOpOrPunct at stepEq
  generalize hTwoChar :
      lexTwoCharPeek firstChar restChars = twoCharResult at stepEq
  cases twoCharResult with
  | some _ =>
    -- two-char branch returns LexStep.token, contradicts error hypothesis
    cases stepEq
  | none =>
    generalize hSingle :
        lexSingleCharPunct firstChar = singleResult at stepEq
    cases singleResult with
    | some _ =>
      cases stepEq
    | none =>
      injection stepEq with errEq _ _
      rw [← errEq]; rfl

/-- **L07.3a**: `lexIdentBranch` always returns `LexStep.token`,
never an error.  Pure structural fact — the function's body is
literally `LexStep.token (...) (...) (...)`. -/
theorem Lex.lexIdentBranch_no_error (firstChar : Char) (restChars : List Char)
    {err : LexError} {bytes : Nat} {restAfter : List Char}
    (stepEq : lexIdentBranch firstChar restChars
              = LexStep.error err bytes restAfter) :
    False := by
  unfold lexIdentBranch at stepEq
  cases stepEq

/-- **L07.3b**: `lexDigitBranch` always returns `LexStep.token`,
never an error. -/
theorem Lex.lexDigitBranch_no_error (firstChar : Char) (restChars : List Char)
    {err : LexError} {bytes : Nat} {restAfter : List Char}
    (stepEq : lexDigitBranch firstChar restChars
              = LexStep.error err bytes restAfter) :
    False := by
  unfold lexDigitBranch at stepEq
  cases stepEq

/-- **L07.3 — load-bearing per-step preservation**: every `LexError`
emitted by `lexOne offset _` has offset = the parameter `offset`.

Composes the four branch-helper preservation lemmas:

* `lexIdentBranch_no_error` — identifier branch never errors.
* `lexDigitBranch_no_error` — digit branch never errors.
* `lexStringBranch_error_offset_eq` — string branch's only error
  is `LexError.unterminatedString offset`.
* `lexOpOrPunct_error_offset_eq` — op/punct branch's only error
  is `LexError.unexpectedChar offset firstChar`.

Walks the if-cascade via `by_cases` on Decidable booleans, then
delegates to the appropriate helper lemma.  Zero-axiom — pure
composition. -/
theorem Lex.lexOne_error_offset_eq (offset : Nat) (chars : List Char)
    {err : LexError} {bytes : Nat} {restAfter : List Char}
    (stepEq : lexOne offset chars = LexStep.error err bytes restAfter) :
    err.offset = offset := by
  cases chars with
  | nil =>
    -- `lexOne offset [] = LexStep.eof`; `eof = error ...` impossible.
    cases stepEq
  | cons firstChar restChars =>
    by_cases hIdent : isIdentStart firstChar = true
    · -- Identifier branch.
      have stepEqUnfold :
          lexOne offset (firstChar :: restChars)
            = lexIdentBranch firstChar restChars := by
        show (if isIdentStart firstChar = true then _
              else if isDigitChar firstChar = true then _
              else if firstChar == '"' then _
              else lexOpOrPunct offset firstChar restChars) = _
        rw [if_pos hIdent]
      rw [stepEqUnfold] at stepEq
      exact absurd stepEq (fun stepEqEr =>
        Lex.lexIdentBranch_no_error firstChar restChars stepEqEr)
    · by_cases hDigit : isDigitChar firstChar = true
      · -- Digit branch.
        have stepEqUnfold :
            lexOne offset (firstChar :: restChars)
              = lexDigitBranch firstChar restChars := by
          show (if isIdentStart firstChar = true then _
                else if isDigitChar firstChar = true then _
                else if firstChar == '"' then _
                else lexOpOrPunct offset firstChar restChars) = _
          rw [if_neg hIdent, if_pos hDigit]
        rw [stepEqUnfold] at stepEq
        exact absurd stepEq (fun stepEqEr =>
          Lex.lexDigitBranch_no_error firstChar restChars stepEqEr)
      · by_cases hQuote : firstChar == '"'
        · -- String branch.
          have stepEqUnfold :
              lexOne offset (firstChar :: restChars)
                = lexStringBranch offset restChars := by
            show (if isIdentStart firstChar = true then _
                  else if isDigitChar firstChar = true then _
                  else if firstChar == '"' then _
                  else lexOpOrPunct offset firstChar restChars) = _
            rw [if_neg hIdent, if_neg hDigit, if_pos hQuote]
          rw [stepEqUnfold] at stepEq
          exact Lex.lexStringBranch_error_offset_eq offset restChars stepEq
        · -- Op/punct branch.
          have stepEqUnfold :
              lexOne offset (firstChar :: restChars)
                = lexOpOrPunct offset firstChar restChars := by
            show (if isIdentStart firstChar = true then _
                  else if isDigitChar firstChar = true then _
                  else if firstChar == '"' then _
                  else lexOpOrPunct offset firstChar restChars) = _
            rw [if_neg hIdent, if_neg hDigit, if_neg hQuote]
          rw [stepEqUnfold] at stepEq
          exact Lex.lexOpOrPunct_error_offset_eq offset firstChar restChars stepEq

/-! ## L07.4 — Byte-conservation invariants for trivia skippers

The `lexLoop` arithmetic invariant requires that `skipTrivia`
(and its helpers `skipUntilNewline` / `skipBlockComment`) conserve
bytes: the bytes counted as "skipped" plus the bytes remaining in
the output equal the bytes that came in (plus initial accumulator).

These are the foundation lemmas for the `Lex.run_error_offset_bounded`
runtime theorem. -/

/-- **L07.4a**: `skipUntilNewline` conserves bytes.

For `(skipBytes, restAfter) = skipUntilNewline chars n`, we have
`skipBytes + charsByteLength restAfter = n + charsByteLength chars`.

Proof: induction on `chars`.  Both branches of `if c == '\n'` use
`c.utf8Size` for byte accounting (uniform), so the proof needs
only structural recursion + `Nat.add_assoc`.  No `omega`, no
`decide`, no `of_decide_eq_true` — all propext-clean.

Zero-axiom under `#assert_no_axioms`. -/
theorem Lex.skipUntilNewline_byteLength_invariant :
    ∀ (chars : List Char) (n : Nat),
      let result := skipUntilNewline chars n
      result.fst + charsByteLength result.snd = n + charsByteLength chars
  | [], n => by
    show n + charsByteLength [] = n + charsByteLength []
    rfl
  | firstChar :: restChars, n => by
    show (skipUntilNewline (firstChar :: restChars) n).fst
        + charsByteLength (skipUntilNewline (firstChar :: restChars) n).snd
      = n + charsByteLength (firstChar :: restChars)
    by_cases hNewline : firstChar == '\n'
    · -- Newline branch: function returns (n + firstChar.utf8Size, restChars).
      have stepReduces :
          skipUntilNewline (firstChar :: restChars) n
            = (n + firstChar.utf8Size, restChars) := by
        show (if firstChar == '\n' then (n + firstChar.utf8Size, restChars)
              else skipUntilNewline restChars (n + firstChar.utf8Size))
            = (n + firstChar.utf8Size, restChars)
        rw [if_pos hNewline]
      rw [stepReduces]
      show (n + firstChar.utf8Size) + charsByteLength restChars
        = n + (firstChar.utf8Size + charsByteLength restChars)
      exact Nat.add_assoc n firstChar.utf8Size (charsByteLength restChars)
    · -- Non-newline branch: tail-recurses with n + firstChar.utf8Size.
      have stepReduces :
          skipUntilNewline (firstChar :: restChars) n
            = skipUntilNewline restChars (n + firstChar.utf8Size) := by
        show (if firstChar == '\n' then (n + firstChar.utf8Size, restChars)
              else skipUntilNewline restChars (n + firstChar.utf8Size))
            = skipUntilNewline restChars (n + firstChar.utf8Size)
        rw [if_neg hNewline]
      rw [stepReduces]
      have ihRecursive :
          (skipUntilNewline restChars (n + firstChar.utf8Size)).fst
          + charsByteLength (skipUntilNewline restChars
              (n + firstChar.utf8Size)).snd
            = (n + firstChar.utf8Size) + charsByteLength restChars :=
        Lex.skipUntilNewline_byteLength_invariant
          restChars (n + firstChar.utf8Size)
      rw [ihRecursive]
      show n + firstChar.utf8Size + charsByteLength restChars
        = n + (firstChar.utf8Size + charsByteLength restChars)
      exact Nat.add_assoc n firstChar.utf8Size (charsByteLength restChars)

/-! ## L07 follow-up — `skipBlockComment` + `skipTrivia` byte
conservation + `lexLoop_error_offset_bounded` + `Lex.run_error_offset_bounded`
(DEFERRED to next iteration)

`skipUntilNewline_byteLength_invariant` above is the simplest of the
three trivia byte-conservation lemmas.  `skipBlockComment` and
`skipTrivia` follow the same pattern but require deeper case
analysis.  Combined, they give the `lexLoop` arithmetic invariant
that closes L07's runtime bound. -/

end LeanFX2.Surface
