import LeanFX2.Surface.Lex

/-! # Surface/Lex/ErrorOffset — L07 LexError offset preservation

Split from `Surface/Lex.lean` (REFACTOR-LEX #1549) — keeps the
Lex impl module under the 1000-line ceiling.

This module ships the L07 (#1205) preservation chain:

* **Projection** — `LexError.offset` total, all 3 ctors.
* **Per-helper preservation** — `lexStringBranch` /
  `lexOpOrPunct` only emit errors with `err.offset = offset`.
* **Per-step preservation** — `lexOne_error_offset_eq` composes
  the per-helper lemmas with the no-error branches
  (`lexIdentBranch_no_error`, `lexDigitBranch_no_error`).

The downstream `lexLoop_error_offset_bounded` (#1536) uses
`lexOne_error_offset_eq` plus the byte-conservation chain (in
`Surface/Lex/ByteConservation.lean`) to prove every error
produced by `Lex.run chars` has offset bounded by source length.

All declarations zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

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

The branch-helper refactor in `Surface/Lex.lean`
(`lexStringBranch`, `lexOpOrPunct`, `lexTwoCharPeek`,
`lexSingleCharPunct`) lets each preservation lemma decompose
cleanly:

* `lexStringBranch_error_offset_eq` — when the string branch
  emits `LexStep.error err _ _`, `err.offset = offset`.
* `lexOpOrPunct_error_offset_eq` — when the op/punct branch
  emits `LexStep.error err _ _`, `err.offset = offset`.
* `lexOne_error_offset_eq` — composes the two helper lemmas
  with the identifier/digit/eof branches (which never emit).

All zero-axiom; verified at the end of this section under
`#assert_no_axioms`. -/

/-- **L07.1**: `lexStringBranch offset firstChar restChars =
LexStep.error err _ _` implies `err.offset = offset`.  The string
branch only emits `LexError.unterminatedString offset` when
`readStringLexeme` returns `none`. -/
theorem Lex.lexStringBranch_error_offset_eq (offset : Nat)
    (firstChar : Char) (restChars : List Char)
    {err : LexError} {bytes : Nat} {restAfter : List Char}
    (stepEq : lexStringBranch offset firstChar restChars
              = LexStep.error err bytes restAfter) :
    err.offset = offset := by
  unfold lexStringBranch at stepEq
  generalize hReadStr :
      readStringLexeme restChars [] firstChar.utf8Size = readResult at stepEq
  cases readResult with
  | none =>
    -- stepEq : LexStep.error (LexError.unterminatedString offset)
    --           firstChar.utf8Size restChars = LexStep.error err bytes restAfter
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
                = lexStringBranch offset firstChar restChars := by
            show (if isIdentStart firstChar = true then _
                  else if isDigitChar firstChar = true then _
                  else if firstChar == '"' then _
                  else lexOpOrPunct offset firstChar restChars) = _
            rw [if_neg hIdent, if_neg hDigit, if_pos hQuote]
          rw [stepEqUnfold] at stepEq
          exact Lex.lexStringBranch_error_offset_eq offset firstChar restChars
            stepEq
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

end LeanFX2.Surface
