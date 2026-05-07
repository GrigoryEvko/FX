import LeanFX2.Surface.Lex
import LeanFX2.Surface.Lex.ByteConservation
import LeanFX2.Surface.Lex.LoopBound

/-! # Surface/Lex/InvalidErrors — L06 no-silent-drop chain

Closes the L06 (#1204) preservation chain: every `lexOne` call
on non-empty input produces either a token or an error (never
`.eof`), every `lexLoop` iteration preserves earlier errors,
and `Lex.run` reports the loop's exact error array — never
silently dropping.

* L06.1 (#1542): `lexOne_cons_not_eof` — `lexOne offset (c :: rest)`
  never returns `LexStep.eof`.  Witnesses that no input character
  is silently consumed without producing a token-or-error step.

* L06.2 (#1543): `lexLoop_errors_initial_preserved` — every
  initial error in the input array survives to the output array.
  Loop is monotone in errors via membership preservation.

* L06.3 (#1544): `Lex.run_no_silent_drop` (closes L06 / #1204) —
  characterizes the `.ok / .error` boundary: success means the
  loop produced ZERO errors (never a `.ok` masking errors), and
  the reported error array on failure equals the loop's error
  array verbatim (no errors dropped between loop and run).

All declarations zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

/-! ## L06.1 — `lexOne` never silently consumes a non-empty input

The four branch helpers (`lexIdentBranch`, `lexDigitBranch`,
`lexStringBranch`, `lexOpOrPunct`) all return either
`LexStep.token _ _ _` or `LexStep.error _ _ _` — none returns
`LexStep.eof`.  Combined with the `lexOne` cascade structure
(`[]` returns `eof`, cons delegates to a helper), this gives:
non-empty input → not eof. -/

/-- `lexOpOrPunct` never returns `LexStep.eof`.  Cases enumerate
the three sub-arms: two-char op (token), single-char punct
(token), neither (error). -/
theorem Lex.lexOpOrPunct_not_eof
    (offset : Nat) (firstChar : Char) (restChars : List Char) :
    lexOpOrPunct offset firstChar restChars ≠ LexStep.eof := by
  unfold lexOpOrPunct
  intro hContra
  split at hContra
  case _ tok secondChar more eqInner => cases hContra
  case _ eqInner =>
    split at hContra
    case _ tok eqSingle => cases hContra
    case _ eqSingle => cases hContra

/-- `lexStringBranch` never returns `LexStep.eof`.  Cases:
`readStringLexeme` returns `some` (token branch) or `none`
(error branch with `LexError.unterminatedString`). -/
theorem Lex.lexStringBranch_not_eof
    (offset : Nat) (firstChar : Char) (restChars : List Char) :
    lexStringBranch offset firstChar restChars ≠ LexStep.eof := by
  unfold lexStringBranch
  intro hContra
  split at hContra
  case _ revBody byteLen remaining eqRead => cases hContra
  case _ eqRead => cases hContra

/-- `lexIdentBranch` never returns `LexStep.eof`.  Always returns
`LexStep.token` directly via `classifyIdent`. -/
theorem Lex.lexIdentBranch_not_eof
    (firstChar : Char) (restChars : List Char) :
    lexIdentBranch firstChar restChars ≠ LexStep.eof := by
  unfold lexIdentBranch
  intro hContra
  cases hContra

/-- `lexDigitBranch` never returns `LexStep.eof`.  Always returns
`LexStep.token` directly via `Token.intLit`. -/
theorem Lex.lexDigitBranch_not_eof
    (firstChar : Char) (restChars : List Char) :
    lexDigitBranch firstChar restChars ≠ LexStep.eof := by
  unfold lexDigitBranch
  intro hContra
  cases hContra

/-- **L06.1**: `lexOne offset (firstChar :: restChars)` never
returns `LexStep.eof`.  Witnesses that `lexOne` never silently
drops a non-empty input — every input character either becomes
part of a token or part of an error.  Composes the four branch
helpers' non-eof lemmas via the if/else cascade.  Proof
structure mirrors `lexOne_error_offset_eq` (rewrite to canonical
if-cascade, dispatch via `if_pos`/`if_neg`). -/
theorem Lex.lexOne_cons_not_eof
    (offset : Nat) (firstChar : Char) (restChars : List Char) :
    lexOne offset (firstChar :: restChars) ≠ LexStep.eof := by
  by_cases hIdent : isIdentStart firstChar = true
  · have stepEqUnfold :
        lexOne offset (firstChar :: restChars)
          = lexIdentBranch firstChar restChars := by
      show (if isIdentStart firstChar = true then _
            else if isDigitChar firstChar = true then _
            else if firstChar == '"' then _
            else lexOpOrPunct offset firstChar restChars) = _
      rw [if_pos hIdent]
    rw [stepEqUnfold]
    exact Lex.lexIdentBranch_not_eof firstChar restChars
  · by_cases hDigit : isDigitChar firstChar = true
    · have stepEqUnfold :
          lexOne offset (firstChar :: restChars)
            = lexDigitBranch firstChar restChars := by
        show (if isIdentStart firstChar = true then _
              else if isDigitChar firstChar = true then _
              else if firstChar == '"' then _
              else lexOpOrPunct offset firstChar restChars) = _
        rw [if_neg hIdent, if_pos hDigit]
      rw [stepEqUnfold]
      exact Lex.lexDigitBranch_not_eof firstChar restChars
    · by_cases hQuote : firstChar == '"'
      · have stepEqUnfold :
            lexOne offset (firstChar :: restChars)
              = lexStringBranch offset firstChar restChars := by
          show (if isIdentStart firstChar = true then _
                else if isDigitChar firstChar = true then _
                else if firstChar == '"' then _
                else lexOpOrPunct offset firstChar restChars) = _
          rw [if_neg hIdent, if_neg hDigit, if_pos hQuote]
        rw [stepEqUnfold]
        exact Lex.lexStringBranch_not_eof offset firstChar restChars
      · have stepEqUnfold :
            lexOne offset (firstChar :: restChars)
              = lexOpOrPunct offset firstChar restChars := by
          show (if isIdentStart firstChar = true then _
                else if isDigitChar firstChar = true then _
                else if firstChar == '"' then _
                else lexOpOrPunct offset firstChar restChars) = _
          rw [if_neg hIdent, if_neg hDigit, if_neg hQuote]
        rw [stepEqUnfold]
        exact Lex.lexOpOrPunct_not_eof offset firstChar restChars

/-! ## L06.2 — `lexLoop` preserves initial errors

`lexLoop` only ever appends to the error array (via
`errors.push err`) — never removes or mutates earlier entries.
We prove the per-element membership preservation: every error
in the initial array remains in the output array.  This avoids
`List.IsPrefix` (whose `prefix_refl` lemma's body uses
`List.append_nil` and may transitively pull in propext). -/

/-- **L06.2**: every initial error survives `lexLoop`.  Proof by
induction on `fuel`, case-split on `chars`, with the recursive
call's IH composed via `Lex.Array.push_toList_mem_decompose`'s
inverse direction (left-side membership preserved). -/
theorem Lex.lexLoop_errors_initial_preserved :
    ∀ (fuel : Nat) (offset : Nat) (chars : List Char)
      (tokens : Array PositionedToken) (errors : Array LexError)
      (priorErr : LexError),
      priorErr ∈ errors.toList →
      priorErr ∈ (lexLoop fuel offset chars tokens errors).snd.toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro offset chars tokens errors priorErr priorMember
    exact priorMember
  | succ fuelMinusOne ihFuel =>
    intro offset chars tokens errors priorErr priorMember
    cases chars with
    | nil =>
      exact priorMember
    | cons firstChar restChars =>
      rw [Lex.lexLoop_cons_unfold]
      generalize hSkipEq :
        skipTrivia (firstChar :: restChars).length (firstChar :: restChars)
          = trivia
      obtain ⟨skipped, afterTrivia⟩ := trivia
      dsimp only
      generalize hLexEq : lexOne (offset + skipped) afterTrivia = lexResult
      cases lexResult with
      | eof =>
        exact priorMember
      | token tokenSeen tokenBytes remainingChars =>
        exact ihFuel _ _ _ _ _ priorMember
      | error errEmitted errorBytes remainingChars =>
        -- Every prior error survives the push; structural recursion
        -- on the underlying list constructs membership directly.
        have priorMemberPush :
            priorErr ∈ (errors.push errEmitted).toList := by
          -- (arr.push x).toList = arr.toList.concat x = arr.toList ++ [x]
          -- (definitional via Array.push reducing to ⟨arr.data ++ [x]⟩)
          show priorErr ∈ errors.toList.concat errEmitted
          have helper : ∀ (listInput : List LexError),
              priorErr ∈ listInput → priorErr ∈ listInput.concat errEmitted := by
            intro listInput hMemInput
            induction listInput with
            | nil => cases hMemInput
            | cons headElem tailList ih =>
              cases hMemInput with
              | head _ => exact List.Mem.head _
              | tail _ hMemTail => exact List.Mem.tail _ (ih hMemTail)
          exact helper errors.toList priorMember
        exact ihFuel _ _ _ _ _ priorMemberPush

/-! ## L06.3 — `Lex.run` reports loop errors verbatim

`Lex.run chars` partitions on whether the loop's error array is
empty: empty → `.ok tokens` (with `Token.eof` appended), non-empty
→ `.error errs` with `errs = lexLoop's snd`.  No silent drop;
the reported error array is exactly the loop's error array. -/

/-- **L06.3**: `Lex.run chars = .error errs` implies the reported
error array is the loop's error array verbatim.  Closes L06
(#1204): every error produced during `lexLoop` reaches the user
unaltered.  Proof structure mirrors `Lex.run_eof_terminated`
(L03): unfold via the canonical `Lex.run` reduction, destructure
the loop's pair, then `if_pos`/`if_neg` to dispatch — avoids
`simp` (whose match-compiler treatment of the `if` leaks
`propext`). -/
theorem Lex.run_no_silent_drop
    (chars : List Char) (errs : Array LexError) :
    Lex.run chars = .error errs →
    errs = (lexLoop (chars.length + 1) 0 chars #[] #[]).snd := by
  intro hRun
  have eqRun : Lex.run chars =
      (match lexLoop (chars.length + 1) 0 chars #[] #[] with
      | (lexTokens, lexErrors) =>
        if lexErrors.isEmpty = true then
          Except.ok (lexTokens.push
            ({ token := Token.eof,
               startPos := { offset := charsByteLength chars } } :
               PositionedToken))
        else Except.error lexErrors) := rfl
  rw [eqRun] at hRun
  match lexLoopEq : lexLoop (chars.length + 1) 0 chars #[] #[], hRun with
  | (lexTokens, lexErrors), hRunPair =>
    have hRunIf :
        (if lexErrors.isEmpty = true then
            Except.ok (lexTokens.push
              ({ token := Token.eof,
                 startPos := { offset := charsByteLength chars } } :
                 PositionedToken))
          else Except.error lexErrors)
        = Except.error errs := hRunPair
    by_cases hErrorsEmpty : lexErrors.isEmpty = true
    · rw [if_pos hErrorsEmpty] at hRunIf
      cases hRunIf
    · rw [if_neg hErrorsEmpty] at hRunIf
      have errsEq : lexErrors = errs := by injection hRunIf
      exact errsEq.symm

/-- **L06.3 corollary**: `Lex.run chars = .ok tokens` implies the
loop's error array is empty.  Witnesses the no-silent-drop
contract from the success-side: `.ok` is returned only when
zero errors were produced during lexing. -/
theorem Lex.run_ok_implies_no_loop_errors
    (chars : List Char) (tokens : Array PositionedToken) :
    Lex.run chars = .ok tokens →
    (lexLoop (chars.length + 1) 0 chars #[] #[]).snd.isEmpty = true := by
  intro hRun
  have eqRun : Lex.run chars =
      (match lexLoop (chars.length + 1) 0 chars #[] #[] with
      | (lexTokens, lexErrors) =>
        if lexErrors.isEmpty = true then
          Except.ok (lexTokens.push
            ({ token := Token.eof,
               startPos := { offset := charsByteLength chars } } :
               PositionedToken))
        else Except.error lexErrors) := rfl
  rw [eqRun] at hRun
  match lexLoopEq : lexLoop (chars.length + 1) 0 chars #[] #[], hRun with
  | (lexTokens, lexErrors), hRunPair =>
    have hRunIf :
        (if lexErrors.isEmpty = true then
            Except.ok (lexTokens.push
              ({ token := Token.eof,
                 startPos := { offset := charsByteLength chars } } :
                 PositionedToken))
          else Except.error lexErrors)
        = Except.ok tokens := hRunPair
    by_cases hErrorsEmpty : lexErrors.isEmpty = true
    · exact hErrorsEmpty
    · rw [if_neg hErrorsEmpty] at hRunIf
      cases hRunIf

end LeanFX2.Surface
