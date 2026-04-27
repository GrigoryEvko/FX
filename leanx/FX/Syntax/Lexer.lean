import FX.Syntax.Token
import FX.Util.Basic

/-!
# Lexer

Converts a UTF-8 source string into an `Array LocatedToken` plus
an array of diagnostics.  Implements `fx_lexer.md` §1–§10.

## What's in, what's out

**In** (Phase 1):
  * UTF-8 source with BOM stripping
  * ASCII-only in code; UTF-8 permitted only inside strings and
    comments
  * All 92 keywords, identifiers, backtick escapes
  * Whitespace, line and block comments (non-nesting),
    doc comments (`///` captured verbatim)
  * All single- and multi-character operators and delimiters
  * Integer literals in decimal, hex (`0x`), binary (`0b`),
    octal (`0o`) bases with underscore separators
  * Ternary literals (`0t10T`) with underscore separators
  * Decimal literals (`3.14`, `1.5e-3`, `1e10`) with underscore
    separators
  * Typed-integer (`u8..u1024`, `i8..i1024`, `usize`, `isize`),
    typed-decimal (`d32..d1024`), typed-float (`f32`, `f64`),
    and typed-ternary (`t6`, `t12`, `t24`, `t48`, `tsize`)
    suffixes scanned greedily and attached to the literal
  * Regular strings with full escape table: `\\ \" \n \t \r \0
    \b \f \v \xHH \uHHHH` and line continuation `\` + newline
  * Raw strings (`r"…"`) — no escape processing, single-quote form
  * Byte strings (`b"…"`) — byte-level escapes only, no `\u`
  * Format strings (`f"…"`) — raw capture only; expansion deferred
  * Three of the four transformer passes (ELSE IF, DOT disambig,
    trailing-comma strip) in `tokenize`

**Out** (deferred):
  * Variable-width unicode escape `\u{H+}` — Phase-2
  * F-string interpolation expansion (§8.4) — Phase-2
  * Hash-delimited raw strings (`r#"…"#`)
  * Triple-quoted string forms
  * Null-byte rejection in source
  * Full Zs category beyond U+00A0 and U+FEFF
  * U+2028 / U+2029 line separators

## Error codes (aligned with `fx_lexer.md` §9 recovery rules)

Every code used in the scanner below is enumerated here.  L005
and L009 are reserved — kept available so future additions do
not perturb the numbering.

  L001  unterminated backtick identifier
  L002  empty backtick identifier
  L003  unterminated block comment
  L004  unterminated raw / byte string literal
  L005  (reserved)
  L006  misplaced underscore in numeric literal
  L007  invalid suffix for numeric literal (e.g., `42foo`)
  L008  invalid hex / unicode escape in string
  L009  (reserved)
  L010  invalid simple escape sequence (e.g., `\q`)
  L011  unterminated regular / format string literal
  L012  empty numeric literal (base prefix without digits)
  L099  unexpected byte

## Scanner style

`partial def` recursion over a `LexState` record.  Every scanner
advances the cursor at least one byte per iteration so the loops
terminate even though Lean's termination checker cannot see that
`pos` increases monotonically across the many entry points.
-/

namespace FX.Syntax

open FX.Util

/-- Lexer-local state.  `bytes` is kept alongside `sourceText` so byte
    classifiers can run without re-encoding. -/
structure LexState where
  sourceText    : String
  bytes  : ByteArray
  pos    : Nat
  line   : Nat
  column : Nat

namespace LexState

/-- Build initial state.  Strips a leading UTF-8 BOM if present. -/
def init (sourceText : String) : LexState :=
  let bytes := sourceText.toUTF8
  let hasBom :=
    bytes.size ≥ 3
      ∧ bytes.get! 0 = 0xEF
      ∧ bytes.get! 1 = 0xBB
      ∧ bytes.get! 2 = 0xBF
  { sourceText := sourceText, bytes := bytes
  , pos := if hasBom then 3 else 0
  , line := 1, column := 0 }

/-- Current position as a `Position`. -/
def currentPosition (state : LexState) : Position :=
  { line := state.line, column := state.column, offset := state.pos }

def atEnd (state : LexState) : Bool :=
  state.pos ≥ state.bytes.size

/-- Peek at the byte at the cursor; returns 0 on EOF. -/
def peek (state : LexState) : UInt8 :=
  if state.pos < state.bytes.size then state.bytes.get! state.pos else 0

/-- Peek `offset` bytes ahead; returns 0 on EOF. -/
def peekAt (state : LexState) (offset : Nat) : UInt8 :=
  if state.pos + offset < state.bytes.size then state.bytes.get! (state.pos + offset) else 0

/-- Advance one byte, updating line/column on `\n`. -/
def advance (state : LexState) : LexState :=
  let byte := state.peek
  if byte = 0x0A then
    { state with pos := state.pos + 1, line := state.line + 1, column := 0 }
  else
    { state with pos := state.pos + 1, column := state.column + 1 }

/-- UTF-8 slice of `[start, stop)` as `String`. -/
def sliceText (state : LexState) (start stop : Nat) : String :=
  String.fromUTF8! (state.bytes.extract start stop)

end LexState

/-! ## Byte classifiers -/

@[inline] def isLower   (byte : UInt8) : Bool := byte ≥ 0x61 ∧ byte ≤ 0x7A
@[inline] def isUpper   (byte : UInt8) : Bool := byte ≥ 0x41 ∧ byte ≤ 0x5A
@[inline] def isDigit   (byte : UInt8) : Bool := byte ≥ 0x30 ∧ byte ≤ 0x39
@[inline] def isHex     (byte : UInt8) : Bool :=
  isDigit byte ∨ (byte ≥ 0x41 ∧ byte ≤ 0x46) ∨ (byte ≥ 0x61 ∧ byte ≤ 0x66)
@[inline] def isOct     (byte : UInt8) : Bool := byte ≥ 0x30 ∧ byte ≤ 0x37
@[inline] def isBin     (byte : UInt8) : Bool := byte = 0x30 ∨ byte = 0x31
@[inline] def isTern    (byte : UInt8) : Bool := byte = 0x30 ∨ byte = 0x31 ∨ byte = 0x54
@[inline] def isIdentStart (byte : UInt8) : Bool := isLower byte ∨ isUpper byte ∨ byte = 0x5F
@[inline] def isIdentCont  (byte : UInt8) : Bool := isIdentStart byte ∨ isDigit byte
@[inline] def isHSpace  (byte : UInt8) : Bool :=
  byte = 0x20 ∨ byte = 0x09 ∨ byte = 0x0B ∨ byte = 0x0C

/-- Map a hex digit byte to its numeric value (0..15).  Undefined for
    non-hex bytes; callers gate with `isHex`. -/
@[inline] def hexVal (byte : UInt8) : UInt8 :=
  if byte ≥ 0x30 ∧ byte ≤ 0x39 then byte - 0x30
  else if byte ≥ 0x41 ∧ byte ≤ 0x46 then byte - 0x41 + 10
  else if byte ≥ 0x61 ∧ byte ≤ 0x66 then byte - 0x61 + 10
  else 0

/-! ## Lexer output -/

structure LexOutput where
  tokens : Array LocatedToken := #[]
  errors : Array Error        := #[]
  deriving Repr

namespace LexOutput

def push (output : LexOutput) (token : LocatedToken) : LexOutput :=
  { output with tokens := output.tokens.push token }

def pushError (output : LexOutput) (error : Error) : LexOutput :=
  { output with errors := output.errors.push error }

def pushErrors (output : LexOutput) (errorList : Array Error) : LexOutput :=
  errorList.foldl (init := output) (fun outputSoFar errorToPush => outputSoFar.pushError errorToPush)

end LexOutput

/-- Build a diagnostic rooted at the current lex position. -/
def lexerError (state : LexState) (code msg : String) : Error :=
  { code := code, message := msg,
    source := some ("<lex>", state.line, state.column) }

/-! ## Whitespace and comment skipping -/

/-- Skip horizontal whitespace, newlines (LF/CR/CRLF), and the two
    recognized multi-byte Unicode whitespace code points (NBSP
    U+00A0 = 0xC2 0xA0, BOM-mid U+FEFF = 0xEF 0xBB 0xBF). -/
partial def skipHSpaceAndNewlines (state : LexState) : LexState :=
  if state.atEnd then state
  else
    let byte := state.peek
    if isHSpace byte then
      skipHSpaceAndNewlines state.advance
    else if byte = 0x0A then
      skipHSpaceAndNewlines state.advance
    else if byte = 0x0D then
      -- CR handled as newline; absorb the paired LF of CRLF.
      let afterCR :=
        { state with pos := state.pos + 1, line := state.line + 1, column := 0 }
      let afterCRLF :=
        if afterCR.pos < state.bytes.size ∧ state.bytes.get! afterCR.pos = 0x0A
        then { afterCR with pos := afterCR.pos + 1 }
        else afterCR
      skipHSpaceAndNewlines afterCRLF
    else if byte = 0xC2 ∧ state.peekAt 1 = 0xA0 then
      -- U+00A0 NO-BREAK SPACE
      skipHSpaceAndNewlines { state with pos := state.pos + 2, column := state.column + 2 }
    else if byte = 0xEF ∧ state.peekAt 1 = 0xBB ∧ state.peekAt 2 = 0xBF then
      -- U+FEFF ZERO WIDTH NO-BREAK SPACE (mid-file BOM)
      skipHSpaceAndNewlines { state with pos := state.pos + 3, column := state.column + 3 }
    else state

/-- Consume a line comment (past `//`) up to but not including the
    terminating newline. -/
partial def skipLineComment (state : LexState) : LexState :=
  if state.atEnd then state
  else if state.peek = 0x0A then state
  else skipLineComment state.advance

/-- Consume a block comment (past `/*`) up to and including `*/`.
    Returns `(newState, closed)` — `closed = false` on EOF.  Block
    comments do NOT nest per §2.3. -/
partial def skipBlockComment (state : LexState) : LexState × Bool :=
  if state.atEnd then (state, false)
  else if state.peek = 0x2A ∧ state.peekAt 1 = 0x2F then
    (state.advance.advance, true)
  else
    skipBlockComment state.advance

/-- Consume a `///` doc comment (past the slashes), returning the
    body as a string and the post-scan state.  The body excludes
    the terminating newline. -/
partial def scanDocComment (state : LexState) : LexState × String :=
  let startPosition := state.pos
  let rec go (cursor : LexState) : LexState :=
    if cursor.atEnd ∨ cursor.peek = 0x0A then cursor
    else go cursor.advance
  let stateAfter := go state
  let body := state.sliceText startPosition stateAfter.pos
  (stateAfter, body)

/-! ## Identifier and keyword scanning -/

/-- Scan an identifier starting at a byte satisfying
    `isIdentStart`.  Returns the post-scan state and the identifier
    slice. -/
partial def scanIdent (state : LexState) : LexState × String :=
  let startPosition := state.pos
  let rec go (cursor : LexState) : LexState :=
    if cursor.atEnd ∨ ¬ isIdentCont cursor.peek then cursor
    else go cursor.advance
  let stateAfter := go state
  let text := state.sliceText startPosition stateAfter.pos
  (stateAfter, text)

/-- Identifier-or-keyword scanner.  Emits one token and returns
    the post-scan state.  Precondition: `isIdentStart state.peek`. -/
def scanIdentOrKw (state : LexState) : LocatedToken × LexState :=
  let start := state.currentPosition
  let (stateAfter, text) := scanIdent state
  let stop := stateAfter.currentPosition
  let token :=
    match Keyword.ofString? text with
    | some keyword => Token.kw keyword
    | none =>
      if isUpper (text.toUTF8.get! 0)
      then Token.uident text
      else Token.ident text
  ({ token := token, span := { start := start, stop := stop } }, stateAfter)

/-! ## Backtick-escaped identifier (§3.3) -/

/-- Scan a backtick-escaped identifier starting at the opening
    backtick.  Returns the token, the post-scan state, and an
    optional error (unterminated or empty). -/
partial def scanBacktick (state : LexState)
    : LocatedToken × LexState × Option Error :=
  let start := state.currentPosition
  let afterOpen := state.advance    -- past opening `
  let contentStart := afterOpen.pos
  let rec go (cursor : LexState) : LexState :=
    if cursor.atEnd ∨ cursor.peek = 0x0A then cursor       -- unterminated
    else if cursor.peek = 0x60 then cursor                   -- closing backtick
    else go cursor.advance
  let afterContent := go afterOpen
  let text := state.sliceText contentStart afterContent.pos
  if afterContent.atEnd ∨ afterContent.peek = 0x0A then
    let error := lexerError state "L001" "unterminated backtick identifier"
    let stop := afterContent.currentPosition
    let token := if text.isEmpty then Token.ident "_" else
      if isUpper (text.toUTF8.get! 0)
      then Token.uident text else Token.ident text
    ({ token := token, span := { start := start, stop := stop } }, afterContent, some error)
  else
    let afterClose := afterContent.advance  -- past closing `
    let stop := afterClose.currentPosition
    let token :=
      if text.isEmpty then
        Token.ident "_"
      else if isUpper (text.toUTF8.get! 0) then
        Token.uident text
      else
        Token.ident text
    let errOpt := if text.isEmpty
      then some (lexerError state "L002" "empty backtick identifier")
      else none
    ({ token := token, span := { start := start, stop := stop } }, afterClose, errOpt)

/-! ## Numeric literals (§4)

The numeric scanner is structured around four phases:

  1. **Prefix/base detection** — `0x`, `0b`, `0o`, `0t`, or plain
     decimal.  Recognized prefixes must be followed by at least
     one valid digit; otherwise `L012`.
  2. **Digit run with underscore separators** — `_` is permitted
     between digits but not at the start of a run.
  3. **Optional decimal-point + exponent** — only for decimal-base
     literals.  Peek-after-dot: a `.` becomes a decimal point only
     if the byte after is a digit.  `42.field` remains `42` + `.`.
  4. **Optional type suffix** — scanned by attempting to consume
     an identifier-ish run of alphanumeric bytes and matching it
     against a fixed table.  If an identifier starts but is not
     a valid suffix, `L007` is emitted.
-/

/-- Scan a run of digits-or-underscores belonging to a single base.
    `pred` decides whether a byte is a valid base-`n` digit.  The
    first byte is assumed to be a valid digit.  Returns the post-scan
    state, the raw slice (underscores included), and the canonicalized
    digit string (underscores stripped). -/
partial def scanDigitRun (state : LexState) (isDigitOfBase : UInt8 → Bool)
    : LexState × String × String :=
  let startPosition := state.pos
  let rec go (cursor : LexState) (buffer : ByteArray) : LexState × ByteArray :=
    if cursor.atEnd then (cursor, buffer)
    else
      let byte := cursor.peek
      if isDigitOfBase byte then go cursor.advance (buffer.push byte)
      else if byte = 0x5F then  -- '_'
        go cursor.advance buffer
      else (cursor, buffer)
  let (stateAfter, buffer) := go state ByteArray.empty
  let rawText := state.sliceText startPosition stateAfter.pos
  let canonical := String.fromUTF8! buffer
  (stateAfter, rawText, canonical)

/-- Known integer suffixes, ordered so that longer matches win. -/
def intSuffixes : Array String := #[
  "usize", "isize",
  "u1024", "i1024", "u512", "i512", "u256", "i256",
  "u128", "i128", "u64", "i64", "u32", "i32",
  "u16", "i16", "u8", "i8" ]

/-- Known decimal suffixes (`dN`). -/
def decSuffixes : Array String := #[
  "d1024", "d512", "d256", "d128", "d96", "d64", "d32" ]

/-- Known float suffixes. -/
def floatSuffixes : Array String := #[ "f64", "f32" ]

/-- Known ternary suffixes. -/
def ternSuffixes : Array String := #[ "tsize", "t48", "t24", "t12", "t6" ]

/-- After scanning a numeric literal, attempt to consume an adjacent
    identifier-continuation run and match it against the allowed
    suffix set.  Identifier-looking bytes that do not match produce
    `L007` and are consumed so that `42foo` does not dribble into
    trailing ident tokens. -/
def scanSuffix (state : LexState) (allowed : Array String)
    : LexState × Option String × Option Error :=
  if state.atEnd ∨ ¬ isIdentStart state.peek then
    (state, none, none)
  else
    let (stateAfter, text) := scanIdent state
    if allowed.contains text then
      (stateAfter, some text, none)
    else
      let error := lexerError state "L007"
        s!"invalid suffix '{text}' for numeric literal"
      (stateAfter, none, some error)

/-- Scan a based-prefix integer (`0x…`, `0b…`, `0o…`).  Emits an
    empty-digit error if the prefix has no following digit. -/
def scanBasedInt
    (state : LexState) (start : Position) (base : IntBase)
    (isDigitOfBase : UInt8 → Bool) (label : String)
    : LocatedToken × LexState × Array Error :=
  let afterPrefix := state.advance.advance  -- past prefix
  let underscoreErrs : Array Error :=
    if afterPrefix.peek = 0x5F then
      #[lexerError afterPrefix "L006"
        s!"underscore not allowed immediately after '{label}'"]
    else #[]
  if afterPrefix.atEnd ∨ ¬ isDigitOfBase afterPrefix.peek then
    let errs := underscoreErrs.push
      (lexerError afterPrefix "L012"
        s!"{label} literal has no digits after '{label}'")
    let stop := afterPrefix.currentPosition
    (⟨.intLit "" base, ⟨start, stop⟩⟩, afterPrefix, errs)
  else
    let (afterDigits, _rawText, canonical) := scanDigitRun afterPrefix isDigitOfBase
    let (afterSuffix, suffixOpt, suffixErr) := scanSuffix afterDigits intSuffixes
    let errs := match suffixErr with
      | some error => underscoreErrs.push error
      | none       => underscoreErrs
    let stop := afterSuffix.currentPosition
    let token : Token := match suffixOpt with
      | some suffix => .typedInt canonical base suffix
      | none        => .intLit canonical base
    (⟨token, ⟨start, stop⟩⟩, afterSuffix, errs)

/-- Scan a `0t…` ternary literal with optional `tN` suffix. -/
def scanTernaryFull
    (state : LexState) (start : Position)
    : LocatedToken × LexState × Array Error :=
  let afterPrefix := state.advance.advance
  let underscoreErrs : Array Error :=
    if afterPrefix.peek = 0x5F then
      #[lexerError afterPrefix "L006"
        "underscore not allowed immediately after '0t'"]
    else #[]
  if afterPrefix.atEnd ∨ ¬ isTern afterPrefix.peek then
    let errs := underscoreErrs.push
      (lexerError afterPrefix "L012" "ternary literal has no digits after '0t'")
    let stop := afterPrefix.currentPosition
    (⟨.ternaryLit "", ⟨start, stop⟩⟩, afterPrefix, errs)
  else
    let (afterDigits, _rawText, canonical) := scanDigitRun afterPrefix isTern
    let (afterSuffix, suffixOpt, suffixErr) := scanSuffix afterDigits ternSuffixes
    let errs := match suffixErr with
      | some error => underscoreErrs.push error
      | none       => underscoreErrs
    let stop := afterSuffix.currentPosition
    let token : Token := match suffixOpt with
      | some suffix => .typedTernary canonical suffix
      | none        => .ternaryLit canonical
    (⟨token, ⟨start, stop⟩⟩, afterSuffix, errs)

/-- Try a decimal or float suffix after a dotted/exponent literal.
    `Sum.inl` = decimal suffix, `Sum.inr` = float suffix. -/
def scanDecFloatSuffix (state : LexState)
    : LexState × Option (Sum String String) × Option Error :=
  if state.atEnd ∨ ¬ isIdentStart state.peek then
    (state, none, none)
  else
    let (stateAfter, text) := scanIdent state
    if decSuffixes.contains text then
      (stateAfter, some (.inl text), none)
    else if floatSuffixes.contains text then
      (stateAfter, some (.inr text), none)
    else
      (stateAfter, none,
       some (lexerError state "L007"
         s!"invalid suffix '{text}' for decimal literal"))

/-- Scan an exponent tail starting at `e`/`E`.  Returns the post-scan
    state and the exponent-string (`"e+10"`, `"e-3"`, …).  On malformed
    exponent the state is returned unchanged and the exponent-string
    is empty; the caller then falls back to a plain int emit. -/
def scanExponent (state : LexState) : LexState × String :=
  let afterE := state.advance  -- past e/E
  let hasSign := afterE.peek = 0x2B ∨ afterE.peek = 0x2D
  let signChar : String :=
    if afterE.peek = 0x2B then "+"
    else if afterE.peek = 0x2D then "-"
    else ""
  let afterSign := if hasSign then afterE.advance else afterE
  if ¬ afterSign.atEnd ∧ isDigit afterSign.peek then
    let (afterDigits, _rawText, expDigits) := scanDigitRun afterSign isDigit
    (afterDigits, "e" ++ signChar ++ expDigits)
  else
    (state, "")

/-- Full numeric scanner entry point.  Handles decimal, hex, binary,
    octal, and ternary bases with underscore separators, decimal
    fractional/exponent forms, and all typed suffix families.  The
    caller has verified that `state.peek` is a decimal digit. -/
partial def scanNumber (state : LexState)
    : LocatedToken × LexState × Array Error :=
  let start := state.currentPosition
  let firstByte := state.peek
  let secondByte := state.peekAt 1
  if firstByte = 0x30 ∧ (secondByte = 0x78 ∨ secondByte = 0x58) then
    scanBasedInt state start .hex isHex "0x"
  else if firstByte = 0x30 ∧ (secondByte = 0x62 ∨ secondByte = 0x42) then
    scanBasedInt state start .bin isBin "0b"
  else if firstByte = 0x30 ∧ (secondByte = 0x6F ∨ secondByte = 0x4F) then
    scanBasedInt state start .oct isOct "0o"
  else if firstByte = 0x30 ∧ (secondByte = 0x74 ∨ secondByte = 0x54) then
    scanTernaryFull state start
  else
    -- Decimal base.  Digits, optional `.digits`, optional exponent,
    -- optional suffix.
    let (afterInt, _rawInt, intPart) := scanDigitRun state isDigit
    -- Only treat `.` as a decimal point when followed by a digit
    -- (§4.2).  `42.field` stays as INT + DOT.
    let dotDigit := afterInt.peek = 0x2E ∧ isDigit (afterInt.peekAt 1)
    let hasExp (cursor : LexState) : Bool := cursor.peek = 0x65 ∨ cursor.peek = 0x45
    if dotDigit then
      let afterDot := afterInt.advance
      let (afterFrac, _rawFrac, fracPart) := scanDigitRun afterDot isDigit
      let (afterExp, expStr) :=
        if hasExp afterFrac then scanExponent afterFrac else (afterFrac, "")
      let text := intPart ++ "." ++ fracPart ++ expStr
      let (afterSuffix, suffixOpt, suffixErr) := scanDecFloatSuffix afterExp
      let errs : Array Error := match suffixErr with
        | some error => #[error]
        | none       => #[]
      let stop := afterSuffix.currentPosition
      let token : Token := match suffixOpt with
        | some (.inl suffix) => .typedDecimal text suffix
        | some (.inr suffix) => .typedFloat   text suffix
        | none               => .decimalLit   text
      (⟨token, ⟨start, stop⟩⟩, afterSuffix, errs)
    else if hasExp afterInt then
      let (afterExp, expStr) := scanExponent afterInt
      if expStr.isEmpty then
        -- malformed: fall back to plain int, leave `e` for next scan
        let (afterSuffix, suffixOpt, suffixErr) := scanSuffix afterInt intSuffixes
        let errs : Array Error := match suffixErr with
          | some error => #[error]
          | none       => #[]
        let stop := afterSuffix.currentPosition
        let token : Token := match suffixOpt with
          | some suffix => .typedInt intPart .dec suffix
          | none        => .intLit intPart .dec
        (⟨token, ⟨start, stop⟩⟩, afterSuffix, errs)
      else
        let text := intPart ++ expStr
        let (afterSuffix, suffixOpt, suffixErr) := scanDecFloatSuffix afterExp
        let errs : Array Error := match suffixErr with
          | some error => #[error]
          | none       => #[]
        let stop := afterSuffix.currentPosition
        let token : Token := match suffixOpt with
          | some (.inl suffix) => .typedDecimal text suffix
          | some (.inr suffix) => .typedFloat   text suffix
          | none               => .decimalLit   text
        (⟨token, ⟨start, stop⟩⟩, afterSuffix, errs)
    else
      let (afterSuffix, suffixOpt, suffixErr) := scanSuffix afterInt intSuffixes
      let errs : Array Error := match suffixErr with
        | some error => #[error]
        | none       => #[]
      let stop := afterSuffix.currentPosition
      let token : Token := match suffixOpt with
        | some suffix => .typedInt intPart .dec suffix
        | none        => .intLit intPart .dec
      (⟨token, ⟨start, stop⟩⟩, afterSuffix, errs)

/-! ## String literals (§5) -/

/-- Decode a `\xHH` byte escape starting at the `\`.  Returns the
    decoded byte, the number of source bytes to advance, and an
    optional error. -/
def decodeHexEscape (state : LexState) : Option UInt8 × Nat × Option Error :=
  let hexHigh := state.peekAt 2
  let hexLow := state.peekAt 3
  if isHex hexHigh ∧ isHex hexLow then
    let byte : UInt8 := hexVal hexHigh * 16 + hexVal hexLow
    (some byte, 4, none)
  else
    (none, 2,
     some (lexerError state "L008"
       "invalid \\x escape: expected two hex digits"))

/-- Encode a Unicode code point into its UTF-8 byte sequence, or
    `none` on invalid code point (> U+10FFFF or in surrogate range).
    Works entirely in `Nat` to avoid UInt8/Nat instance mismatches. -/
def encodeUtf8 (codepoint : Nat) : Option ByteArray :=
  if codepoint > 0x10FFFF ∨ (codepoint ≥ 0xD800 ∧ codepoint ≤ 0xDFFF) then none
  else if codepoint < 0x80 then
    some (ByteArray.empty.push codepoint.toUInt8)
  else if codepoint < 0x800 then
    let byte1 : Nat := 0xC0 ||| (codepoint / 64)
    let byte2 : Nat := 0x80 ||| (codepoint % 64)
    some ((ByteArray.empty.push byte1.toUInt8).push byte2.toUInt8)
  else if codepoint < 0x10000 then
    let byte1 : Nat := 0xE0 ||| (codepoint / 4096)
    let byte2 : Nat := 0x80 ||| ((codepoint / 64) % 64)
    let byte3 : Nat := 0x80 ||| (codepoint % 64)
    some (((ByteArray.empty.push byte1.toUInt8).push byte2.toUInt8).push byte3.toUInt8)
  else
    let byte1 : Nat := 0xF0 ||| (codepoint / 262144)
    let byte2 : Nat := 0x80 ||| ((codepoint / 4096) % 64)
    let byte3 : Nat := 0x80 ||| ((codepoint / 64) % 64)
    let byte4 : Nat := 0x80 ||| (codepoint % 64)
    some ((((ByteArray.empty.push byte1.toUInt8).push byte2.toUInt8).push byte3.toUInt8).push byte4.toUInt8)

/-- Decode a `\uHHHH` 4-digit unicode escape starting at the `\`.
    Returns the encoded UTF-8 bytes (empty on failure), the advance
    count, and an optional error. -/
def decodeUnicode4Escape (state : LexState)
    : ByteArray × Nat × Option Error :=
  let hex1 := state.peekAt 2
  let hex2 := state.peekAt 3
  let hex3 := state.peekAt 4
  let hex4 := state.peekAt 5
  if isHex hex1 ∧ isHex hex2 ∧ isHex hex3 ∧ isHex hex4 then
    let codepoint : Nat :=
      (hexVal hex1).toNat * 0x1000 + (hexVal hex2).toNat * 0x100
      + (hexVal hex3).toNat * 0x10 + (hexVal hex4).toNat
    match encodeUtf8 codepoint with
    | some bytes => (bytes, 6, none)
    | none       =>
      (ByteArray.empty, 6,
       some (lexerError state "L008"
         s!"invalid unicode code point U+{codepoint} in \\u escape"))
  else
    (ByteArray.empty, 2,
     some (lexerError state "L008"
       "invalid \\u escape: expected four hex digits"))

/-- Process a single escape sequence in a **regular** string.
    Returns bytes-to-append, source advance-count, and optional error. -/
def decodeRegularEscape (state : LexState)
    : ByteArray × Nat × Option Error :=
  let escapeChar := state.peekAt 1
  match escapeChar with
  | 0x5C => (ByteArray.empty.push 0x5C, 2, none)          -- \\
  | 0x22 => (ByteArray.empty.push 0x22, 2, none)          -- \"
  | 0x6E => (ByteArray.empty.push 0x0A, 2, none)          -- \n
  | 0x74 => (ByteArray.empty.push 0x09, 2, none)          -- \t
  | 0x72 => (ByteArray.empty.push 0x0D, 2, none)          -- \r
  | 0x30 => (ByteArray.empty.push 0x00, 2, none)          -- \0
  | 0x62 => (ByteArray.empty.push 0x08, 2, none)          -- \b
  | 0x66 => (ByteArray.empty.push 0x0C, 2, none)          -- \f
  | 0x76 => (ByteArray.empty.push 0x0B, 2, none)          -- \v
  | 0x78 =>                                                -- \xHH
    let (byteOpt, advance, error) := decodeHexEscape state
    match byteOpt with
    | some byte => (ByteArray.empty.push byte, advance, error)
    | none      => (ByteArray.empty, advance, error)
  | 0x75 =>                                                -- \uHHHH
    decodeUnicode4Escape state
  | 0x0A => (ByteArray.empty, 2, none)                     -- \ + LF
  | 0x0D =>                                                -- \ + CR(LF)
    if state.peekAt 2 = 0x0A then (ByteArray.empty, 3, none)
    else (ByteArray.empty, 2, none)
  | _    =>
    let hexDigits := Nat.toDigits 16 escapeChar.toNat
    (ByteArray.empty.push 0x5C |>.push escapeChar, 2,
     some (lexerError state "L010"
       s!"invalid escape sequence '\\x{String.ofList hexDigits}'"))

/-- Process a single escape sequence in a **byte** string.  No `\u`. -/
def decodeByteEscape (state : LexState)
    : ByteArray × Nat × Option Error :=
  let escapeChar := state.peekAt 1
  match escapeChar with
  | 0x5C => (ByteArray.empty.push 0x5C, 2, none)
  | 0x22 => (ByteArray.empty.push 0x22, 2, none)
  | 0x6E => (ByteArray.empty.push 0x0A, 2, none)
  | 0x74 => (ByteArray.empty.push 0x09, 2, none)
  | 0x72 => (ByteArray.empty.push 0x0D, 2, none)
  | 0x30 => (ByteArray.empty.push 0x00, 2, none)
  | 0x62 => (ByteArray.empty.push 0x08, 2, none)
  | 0x66 => (ByteArray.empty.push 0x0C, 2, none)
  | 0x76 => (ByteArray.empty.push 0x0B, 2, none)
  | 0x78 =>
    let (byteOpt, advance, error) := decodeHexEscape state
    match byteOpt with
    | some byte => (ByteArray.empty.push byte, advance, error)
    | none      => (ByteArray.empty, advance, error)
  | 0x75 =>
    (ByteArray.empty, 2,
     some (lexerError state "L010"
       "\\u escape not allowed in byte string"))
  | _    =>
    let hexDigits := Nat.toDigits 16 escapeChar.toNat
    (ByteArray.empty.push 0x5C |>.push escapeChar, 2,
     some (lexerError state "L010"
       s!"invalid escape sequence '\\x{String.ofList hexDigits}'"))

/-- Advance a LexState by `count` bytes, tracking newlines correctly. -/
partial def advanceN (state : LexState) (count : Nat) : LexState :=
  if count = 0 then state else advanceN state.advance (count - 1)

/-- Scan a regular double-quoted string starting at the opening `"`.
    Returns the token, post-scan state, and collected errors. -/
partial def scanRegularString (state : LexState)
    : LocatedToken × LexState × Array Error :=
  let start := state.currentPosition
  let afterOpen := state.advance    -- past opening "
  let rec go (cursor : LexState) (accBytes : ByteArray) (errs : Array Error)
      : LexState × ByteArray × Array Error :=
    if cursor.atEnd then
      let error := lexerError cursor "L011" "unterminated string literal"
      (cursor, accBytes, errs.push error)
    else
      let byte := cursor.peek
      if byte = 0x22 then (cursor.advance, accBytes, errs)
      else if byte = 0x5C then
        let (escapeBytes, advanceCount, errOpt) := decodeRegularEscape cursor
        let accNext := accBytes ++ escapeBytes
        let errsNext := match errOpt with
          | some error => errs.push error
          | none       => errs
        go (advanceN cursor advanceCount) accNext errsNext
      else
        go cursor.advance (accBytes.push byte) errs
  let (afterString, bytes, errs) := go afterOpen ByteArray.empty #[]
  let text := String.fromUTF8! bytes
  let stop := afterString.currentPosition
  ({ token := .stringLit text
   , span := { start := start, stop := stop } }, afterString, errs)

/-- Scan an f-string (format string) starting at `f"`.  Per
    `fx_lexer.md` §5.3, the lexer captures the raw content without
    re-lexing interpolations; §8.4 handles expansion.  Backslash
    escapes of `"` and `\\` are honoured so `f"say \"hi\""` doesn't
    terminate at the escaped quote. -/
partial def scanFormatString (state : LexState)
    : LocatedToken × LexState × Array Error :=
  let start := state.currentPosition
  let afterOpen := state.advance.advance    -- past f"
  let contentStart := afterOpen.pos
  let rec go (cursor : LexState) (errs : Array Error)
      : LexState × Array Error :=
    if cursor.atEnd then
      let error := lexerError cursor "L011" "unterminated format string literal"
      (cursor, errs.push error)
    else
      let byte := cursor.peek
      if byte = 0x22 then (cursor, errs)
      else if byte = 0x5C then
        let afterSlash := if cursor.atEnd then cursor else cursor.advance
        go (if afterSlash.atEnd then afterSlash else afterSlash.advance) errs
      else
        go cursor.advance errs
  let (afterContent, errs) := go afterOpen #[]
  let text := state.sliceText contentStart afterContent.pos
  if afterContent.atEnd then
    let stop := afterContent.currentPosition
    ({ token := .fstringLit text
     , span := { start := start, stop := stop } }, afterContent, errs)
  else
    let afterClose := afterContent.advance  -- past closing "
    let stop := afterClose.currentPosition
    ({ token := .fstringLit text
     , span := { start := start, stop := stop } }, afterClose, errs)

/-- Scan a raw string starting at `r"`.  No escape processing; the
    string ends at the first `"`. -/
partial def scanRawString (state : LexState)
    : LocatedToken × LexState × Array Error :=
  let start := state.currentPosition
  let afterOpen := state.advance.advance    -- past r"
  let contentStart := afterOpen.pos
  let rec go (cursor : LexState) : LexState :=
    if cursor.atEnd ∨ cursor.peek = 0x22 then cursor
    else go cursor.advance
  let afterContent := go afterOpen
  let text := state.sliceText contentStart afterContent.pos
  if afterContent.atEnd then
    let error := lexerError afterContent "L004" "unterminated raw string literal"
    let stop := afterContent.currentPosition
    ({ token := .rstringLit text
     , span := { start := start, stop := stop } }, afterContent, #[error])
  else
    let afterClose := afterContent.advance
    let stop := afterClose.currentPosition
    ({ token := .rstringLit text
     , span := { start := start, stop := stop } }, afterClose, #[])

/-- Scan a byte string starting at `b"`.  Byte-level escapes only. -/
partial def scanByteString (state : LexState)
    : LocatedToken × LexState × Array Error :=
  let start := state.currentPosition
  let afterOpen := state.advance.advance    -- past b"
  let rec go (cursor : LexState) (accBytes : ByteArray) (errs : Array Error)
      : LexState × ByteArray × Array Error :=
    if cursor.atEnd then
      let error := lexerError cursor "L004" "unterminated byte string literal"
      (cursor, accBytes, errs.push error)
    else
      let byte := cursor.peek
      if byte = 0x22 then (cursor.advance, accBytes, errs)
      else if byte = 0x5C then
        let (escapeBytes, advanceCount, errOpt) := decodeByteEscape cursor
        let accNext := accBytes ++ escapeBytes
        let errsNext := match errOpt with
          | some error => errs.push error
          | none       => errs
        go (advanceN cursor advanceCount) accNext errsNext
      else
        go cursor.advance (accBytes.push byte) errs
  let (afterString, bytes, errs) := go afterOpen ByteArray.empty #[]
  -- Byte strings hold arbitrary bytes — `\xFF` may yield non-UTF-8
  -- content.  `String.fromUTF8!` would panic there.  We try the
  -- total decoder first; on failure we fall back to a lossy
  -- hex-escape rendering so the token still carries useful
  -- diagnostic text and the lexer never crashes.
  let asString : String :=
    match String.fromUTF8? bytes with
    | some decoded => decoded
    | none =>
      let hexOf (byte : UInt8) : String :=
        let highNibble := byte >>> 4
        let lowNibble := byte &&& 0x0F
        let digit (nibble : UInt8) : Char :=
          if nibble < 10 then Char.ofNat (0x30 + nibble.toNat)
          else              Char.ofNat (0x41 + (nibble.toNat - 10))
        s!"\\x{digit highNibble}{digit lowNibble}"
      bytes.foldl (init := "") (fun hexSoFar currentByte => hexSoFar ++ hexOf currentByte)
  let stop := afterString.currentPosition
  ({ token := .bstringLit asString
   , span := { start := start, stop := stop } }, afterString, errs)

/-! ## Operator and punctuation scanning -/

/-- Try to match a multi-character operator at the cursor.
    Returns the token and how many bytes to advance, or `none`. -/
def matchMultiOp (state : LexState) : Option (Token × Nat) :=
  let byte0 := state.peek
  let byte1 := state.peekAt 1
  let byte2 := state.peekAt 2
  let byte3 := state.peekAt 3
  if byte0 = 0x3C ∧ byte1 = 0x3D ∧ byte2 = 0x3D ∧ byte3 = 0x3E then
    some (.iff, 4)          -- <==>
  else if byte0 = 0x3D ∧ byte1 = 0x3D ∧ byte2 = 0x3E then
    some (.implies, 3)      -- ==>
  else if byte0 = 0x2E ∧ byte1 = 0x2E ∧ byte2 = 0x3D then
    some (.rangeIncl, 3)    -- ..=
  else if byte0 = 0x2E ∧ byte1 = 0x2E ∧ byte2 = 0x2E then
    some (.spread, 3)       -- ...
  else if byte0 = 0x3D ∧ byte1 = 0x3D then
    some (.eqEq, 2)
  else if byte0 = 0x21 ∧ byte1 = 0x3D then
    some (.neq, 2)
  else if byte0 = 0x3C ∧ byte1 = 0x3D then
    some (.leq, 2)
  else if byte0 = 0x3E ∧ byte1 = 0x3D then
    some (.geq, 2)
  else if byte0 = 0x3C ∧ byte1 = 0x3C then
    some (.lshift, 2)
  else if byte0 = 0x3E ∧ byte1 = 0x3E then
    some (.rshift, 2)
  else if byte0 = 0x2E ∧ byte1 = 0x2E then
    some (.range, 2)
  else if byte0 = 0x2D ∧ byte1 = 0x3E then
    some (.arrow, 2)
  else if byte0 = 0x3D ∧ byte1 = 0x3E then
    some (.fatArrow, 2)
  else if byte0 = 0x7C ∧ byte1 = 0x3E then
    some (.pipeRight, 2)
  else if byte0 = 0x40 ∧ byte1 = 0x5B then
    some (.atLbrack, 2)
  else
    none

/-- Match a single-character punctuator or operator. -/
def matchSingleOp (byte : UInt8) : Option Token :=
  match byte with
  | 0x2B => some .plus      | 0x2D => some .minus    | 0x2A => some .star
  | 0x2F => some .slash     | 0x25 => some .percent  | 0x3C => some .lt
  | 0x3E => some .gt        | 0x3D => some .equals   | 0x26 => some .amp
  | 0x7C => some .pipe      | 0x5E => some .caret    | 0x7E => some .tilde
  | 0x3A => some .colon     | 0x3B => some .semi     | 0x2C => some .comma
  | 0x2E => some .dot       | 0x23 => some .hash     | 0x40 => some .at
  | 0x28 => some .lparen    | 0x29 => some .rparen
  | 0x5B => some .lbrack    | 0x5D => some .rbrack
  | 0x7B => some .lbrace    | 0x7D => some .rbrace
  | _    => none

/-! ## Main dispatch -/

/-- Emit one EOF token at the current position. -/
def emitEof (state : LexState) (output : LexOutput) : LexOutput :=
  let position := state.currentPosition
  output.push { token := .eof, span := { start := position, stop := position } }

/-- Raw token emission loop.  Does NOT run the transformer passes. -/
partial def rawTokenize (state : LexState) (output : LexOutput) : LexOutput :=
  let state := skipHSpaceAndNewlines state
  if state.atEnd then
    emitEof state output
  else
    let byte0 := state.peek
    let byte1 := state.peekAt 1
    let byte2 := state.peekAt 2
    -- Comment forms first.
    if byte0 = 0x2F ∧ byte1 = 0x2F ∧ byte2 = 0x2F then
      -- /// doc comment
      let afterSlashes := state.advance.advance.advance
      let (afterDoc, body) := scanDocComment afterSlashes
      let start := state.currentPosition
      let stop := afterDoc.currentPosition
      let token : LocatedToken :=
        { token := .docComment body
        , span := { start := start, stop := stop } }
      rawTokenize afterDoc (output.push token)
    else if byte0 = 0x2F ∧ byte1 = 0x2F then
      rawTokenize (skipLineComment state.advance.advance) output
    else if byte0 = 0x2F ∧ byte1 = 0x2A then
      let (afterComment, closed) := skipBlockComment state.advance.advance
      let outputNext := if closed then output else
        output.pushError (lexerError state "L003" "unterminated block comment")
      rawTokenize afterComment outputNext
    -- String prefixes r" b" f" before the generic ident fallthrough.
    else if byte0 = 0x72 ∧ byte1 = 0x22 then
      let (token, stateAfter, errs) := scanRawString state
      rawTokenize stateAfter ((output.pushErrors errs).push token)
    else if byte0 = 0x62 ∧ byte1 = 0x22 then
      let (token, stateAfter, errs) := scanByteString state
      rawTokenize stateAfter ((output.pushErrors errs).push token)
    else if byte0 = 0x66 ∧ byte1 = 0x22 then
      let (token, stateAfter, errs) := scanFormatString state
      rawTokenize stateAfter ((output.pushErrors errs).push token)
    -- Identifier or keyword
    else if isIdentStart byte0 then
      let (token, stateAfter) := scanIdentOrKw state
      rawTokenize stateAfter (output.push token)
    -- Backtick-escaped identifier
    else if byte0 = 0x60 then
      let (token, stateAfter, errOpt) := scanBacktick state
      let outputNext := match errOpt with
        | some error => output.pushError error
        | none       => output
      rawTokenize stateAfter (outputNext.push token)
    -- Regular string
    else if byte0 = 0x22 then
      let (token, stateAfter, errs) := scanRegularString state
      rawTokenize stateAfter ((output.pushErrors errs).push token)
    -- Numeric literal (decimal, hex, binary, octal, ternary)
    else if isDigit byte0 then
      let (token, stateAfter, errs) := scanNumber state
      rawTokenize stateAfter ((output.pushErrors errs).push token)
    -- Multi-character operators
    else if let some (token, advanceCount) := matchMultiOp state then
      let start := state.currentPosition
      let stateAfter := advanceN state advanceCount
      let stop := stateAfter.currentPosition
      rawTokenize stateAfter
        (output.push { token := token, span := { start := start, stop := stop } })
    -- Single-character punctuator
    else if let some token := matchSingleOp byte0 then
      let start := state.currentPosition
      let stateAfter := state.advance
      let stop := stateAfter.currentPosition
      rawTokenize stateAfter
        (output.push { token := token, span := { start := start, stop := stop } })
    else
      let hexDigits := String.ofList (Nat.toDigits 16 byte0.toNat)
      let error := lexerError state "L099" s!"unexpected byte 0x{hexDigits}"
      rawTokenize state.advance (output.pushError error)

/-! ## Token transformer passes (§8.1–§8.3) -/

/-- Pass 8.1: replace every `else if` pair with a single `elif`. -/
partial def mergeElseIf (tokens : Array LocatedToken) : Array LocatedToken :=
  let rec go (index : Nat) (accumulator : Array LocatedToken) : Array LocatedToken :=
    if index < tokens.size then
      let current : LocatedToken := tokens[index]!
      match tokens[index + 1]? with
      | some (next : LocatedToken) =>
        match current.token, next.token with
        | Token.kw Keyword.elseKw, Token.kw Keyword.ifKw =>
          let merged : LocatedToken :=
            { token := Token.elif
            , span  := { start := current.span.start, stop := next.span.stop } }
          go (index + 2) (accumulator.push merged)
        | _, _ => go (index + 1) (accumulator.push current)
      | none => accumulator.push current
    else accumulator
  go 0 #[]

/-- Pass 8.2: `DOT → DOT_PROJ` except after `UIDENT`. -/
partial def disambiguateDot (tokens : Array LocatedToken) : Array LocatedToken :=
  let rec go (index : Nat) (prevToken : Option Token) (accumulator : Array LocatedToken)
      : Array LocatedToken :=
    if index < tokens.size then
      let current : LocatedToken := tokens[index]!
      let rewritten : Token :=
        match current.token with
        | Token.dot =>
          match prevToken with
          | some (Token.uident _) => current.token
          | _                     => Token.dotProj
        | _ => current.token
      go (index + 1) (some current.token) (accumulator.push { current with token := rewritten })
    else accumulator
  go 0 none #[]

/-- Pass 8.3: drop `COMMA` followed by a closing delimiter. -/
partial def stripTrailingCommas (tokens : Array LocatedToken) : Array LocatedToken :=
  let isClosing : Token → Bool
    | Token.rparen | Token.rbrack | Token.rbrace => true
    | _                                          => false
  let rec go (index : Nat) (accumulator : Array LocatedToken) : Array LocatedToken :=
    if index < tokens.size then
      let current : LocatedToken := tokens[index]!
      match tokens[index + 1]? with
      | some (next : LocatedToken) =>
        match current.token with
        | Token.comma =>
          if isClosing next.token
          then go (index + 1) accumulator
          else go (index + 1) (accumulator.push current)
        | _ => go (index + 1) (accumulator.push current)
      | none => accumulator.push current
    else accumulator
  go 0 #[]

/-! ## Top-level entry point -/

/-- Tokenize a UTF-8 source string into an `Array LocatedToken`
    plus diagnostics.  The transformer passes from §8 are applied
    in order: ELSE IF merge, DOT disambiguation, trailing-comma
    strip.  F-string expansion is deferred. -/
def tokenize (sourceText : String) : LexOutput :=
  let rawOutput := rawTokenize (LexState.init sourceText) {}
  let afterElseIf := mergeElseIf rawOutput.tokens
  let afterDotDisambig := disambiguateDot afterElseIf
  let afterCommaStrip := stripTrailingCommas afterDotDisambig
  { tokens := afterCommaStrip, errors := rawOutput.errors }

end FX.Syntax
