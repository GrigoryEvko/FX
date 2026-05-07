import LeanFX2.Surface.Lex
import LeanFX2.Surface.Lex.ErrorOffset
import LeanFX2.Surface.Lex.ByteConservation

/-! # Surface/Lex/LoopBound — L07.5 lexLoop error-offset bound

Closes the L07 (#1205) preservation chain.  Every `LexError`
produced by `lexLoop fuel offset chars tokens errors` either:

* was already in the input `errors` array, OR
* has offset bounded by `offset + charsByteLength chars`.

Stated as a strengthened invariant: if every input error already
satisfies the bound, every output error does too.  The recursive
call's bound `(offset + trivia.fst + bytes) + charsByteLength remaining`
equals the parent's bound `offset + charsByteLength chars` by the
byte-conservation chain
`skipTrivia_byteLength_invariant` (L07.4d) ∘
`lexOne_byteLength_invariant` (L07.5.4), so the IH plugs in directly.

Combined with `lexOne_error_offset_eq` (L07.3) — every emitted
error has offset = the parameter offset — the bound on each new
error reduces to `offset + skipped ≤ offset + charsByteLength chars`,
witnessed by `skipTrivia_byteLength_invariant`.

Unblocks L07.6 `Lex.run_error_offset_bounded` (#1537), which
specializes to empty initial errors at offset 0.

Zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

namespace Lex

/-! ## Membership decomposition auxiliaries

Pure structural recursion over `List` / `Array.toList = List.concat`
projection.  Avoids `simp [List.mem_concat]` / similar stdlib lemmas
that leak `propext` via the match compiler. -/

/-- **Auxiliary**: membership in `initialList.concat lastElem` decomposes
into membership in `initialList` or equality with `lastElem`. -/
theorem List.mem_concat_decompose {alpha : Type} {targetElem : alpha} :
    ∀ (initialList : List alpha) (lastElem : alpha),
      targetElem ∈ initialList.concat lastElem →
        targetElem ∈ initialList ∨ targetElem = lastElem
  | [], lastElem, hMem => by
    cases hMem with
    | head _ => exact Or.inr rfl
    | tail _ hMemEmpty => cases hMemEmpty
  | head :: rest, lastElem, hMem => by
    cases hMem with
    | head _ => exact Or.inl (List.Mem.head rest)
    | tail _ hMemRecur =>
      cases List.mem_concat_decompose rest lastElem hMemRecur with
      | inl hMemRest => exact Or.inl (List.Mem.tail head hMemRest)
      | inr hEqLast => exact Or.inr hEqLast

/-- **Auxiliary**: `Array.push` membership decomposes through
`(arr.push x).toList = arr.toList.concat x` definitionally. -/
theorem Array.push_toList_mem_decompose {alpha : Type} {targetElem : alpha}
    (arrInput : Array alpha) (lastElem : alpha)
    (hMem : targetElem ∈ (arrInput.push lastElem).toList) :
    targetElem ∈ arrInput.toList ∨ targetElem = lastElem :=
  List.mem_concat_decompose arrInput.toList lastElem hMem

/-- **Auxiliary**: explicit unfold equation for `lexLoop` on a non-empty
`chars` argument with positive fuel.  By `rfl` after lexLoop's
refactor (#1536-prep) to use `let trivia := skipTrivia ...; trivia.fst`
projections instead of pattern-destructuring `let (skipped, afterTrivia) := ...`,
which produced an opaque match wrapper that blocked `generalize` /
`rw` on the body. -/
theorem lexLoop_cons_unfold
    (fuelMinusOne offset : Nat) (firstChar : Char) (restChars : List Char)
    (tokens : Array PositionedToken) (errors : Array LexError) :
    lexLoop (fuelMinusOne + 1) offset (firstChar :: restChars) tokens errors
      =
      (let trivia :=
        skipTrivia (firstChar :: restChars).length (firstChar :: restChars)
       match lexOne (offset + trivia.fst) trivia.snd with
       | LexStep.eof => (tokens, errors)
       | LexStep.token tokenSeen tokenBytes remainingChars =>
         lexLoop fuelMinusOne (offset + trivia.fst + tokenBytes) remainingChars
           (tokens.push
             { token := tokenSeen,
               startPos := { offset := offset + trivia.fst } })
           errors
       | LexStep.error errEmitted errorBytes remainingChars =>
         lexLoop fuelMinusOne (offset + trivia.fst + errorBytes) remainingChars
           tokens (errors.push errEmitted)) := rfl

end Lex

/-! ## L07.5: lexLoop error offset bound (#1536) -/

/-- **L07.5 (#1536) — load-bearing invariant**: lexLoop preserves
the error-offset bound across every fuel step.

Stated as a strengthened invariant so the recursive call's IH
matches without arithmetic re-derivation. -/
theorem Lex.lexLoop_error_offset_bounded :
    ∀ (fuel : Nat) (offset : Nat) (chars : List Char)
      (tokens : Array PositionedToken) (errors : Array LexError),
      (∀ pastErr ∈ errors.toList,
          pastErr.offset ≤ offset + charsByteLength chars) →
      ∀ resultErr ∈ (lexLoop fuel offset chars tokens errors).snd.toList,
        resultErr.offset ≤ offset + charsByteLength chars := by
  intro fuel
  induction fuel with
  | zero =>
    intro offset chars tokens errors errorsBounded resultErr resultMember
    exact errorsBounded resultErr resultMember
  | succ fuelMinusOne ihFuel =>
    intro offset chars tokens errors errorsBounded resultErr resultMember
    cases chars with
    | nil =>
      exact errorsBounded resultErr resultMember
    | cons firstChar restChars =>
      -- Step 1: unfold lexLoop's cons-arm body in `resultMember`.
      rw [Lex.lexLoop_cons_unfold] at resultMember
      -- Now resultMember references `skipTrivia ...` and `lexOne ...` directly.
      -- Step 2: generalize skipTrivia's result + grab byte-conservation.
      have hSkipBytesUngen :=
        Lex.skipTrivia_byteLength_invariant
          (firstChar :: restChars).length (firstChar :: restChars)
      generalize hSkipEq :
        skipTrivia (firstChar :: restChars).length (firstChar :: restChars)
          = trivia
        at resultMember hSkipBytesUngen
      obtain ⟨skipped, afterTrivia⟩ := trivia
      -- After `obtain`, `Prod.fst (skipped, afterTrivia)` and `Prod.snd
      -- (skipped, afterTrivia)` need definitional unfolding to reduce to
      -- `skipped` and `afterTrivia`.  `dsimp only` does this without
      -- triggering propext.
      dsimp only at resultMember hSkipBytesUngen
      have hSkipBytes :
          skipped + charsByteLength afterTrivia
            = charsByteLength (firstChar :: restChars) :=
        hSkipBytesUngen
      -- Step 3: case on lexOne result, get byte-conservation per case.
      have hLexOneBytesUngen :=
        Lex.lexOne_byteLength_invariant (offset + skipped) afterTrivia
      generalize hLexOneEq :
        lexOne (offset + skipped) afterTrivia = lexOneResult
        at resultMember hLexOneBytesUngen
      cases lexOneResult with
      | eof =>
        -- Body branch: `(tokens, errors)`.
        exact errorsBounded resultErr resultMember
      | token tokenSeen tokenBytes remainingChars =>
        have hLexOneBytes :
            tokenBytes + charsByteLength remainingChars
              = charsByteLength afterTrivia := hLexOneBytesUngen
        have hSumEq :
            offset + skipped + tokenBytes + charsByteLength remainingChars
              = offset + charsByteLength (firstChar :: restChars) := by
          rw [Nat.add_assoc offset skipped tokenBytes,
              Nat.add_assoc (offset) (skipped + tokenBytes)
                            (charsByteLength remainingChars),
              Nat.add_assoc skipped tokenBytes
                            (charsByteLength remainingChars),
              hLexOneBytes,
              hSkipBytes]
        have ihBoundedHyp :
            ∀ pastErr ∈ errors.toList,
              pastErr.offset
                ≤ (offset + skipped + tokenBytes)
                    + charsByteLength remainingChars := by
          intro pastErr pastMember
          rw [hSumEq]
          exact errorsBounded pastErr pastMember
        have ihResult := ihFuel
          (offset + skipped + tokenBytes)
          remainingChars
          (tokens.push
            { token := tokenSeen,
              startPos := { offset := offset + skipped } })
          errors
          ihBoundedHyp
          resultErr
          resultMember
        rw [hSumEq] at ihResult
        exact ihResult
      | error errEmitted errorBytes remainingChars =>
        have hLexOneBytes :
            errorBytes + charsByteLength remainingChars
              = charsByteLength afterTrivia := hLexOneBytesUngen
        have hErrOffsetEq : errEmitted.offset = offset + skipped :=
          Lex.lexOne_error_offset_eq (offset + skipped) afterTrivia hLexOneEq
        have hSumEq :
            offset + skipped + errorBytes + charsByteLength remainingChars
              = offset + charsByteLength (firstChar :: restChars) := by
          rw [Nat.add_assoc offset skipped errorBytes,
              Nat.add_assoc (offset) (skipped + errorBytes)
                            (charsByteLength remainingChars),
              Nat.add_assoc skipped errorBytes
                            (charsByteLength remainingChars),
              hLexOneBytes,
              hSkipBytes]
        have ihBoundedHyp :
            ∀ pastErr ∈ (errors.push errEmitted).toList,
              pastErr.offset
                ≤ (offset + skipped + errorBytes)
                    + charsByteLength remainingChars := by
          intro pastErr pastMember
          cases Lex.Array.push_toList_mem_decompose errors errEmitted pastMember
          with
          | inl hOldMember =>
            rw [hSumEq]
            exact errorsBounded pastErr hOldMember
          | inr hPastEqEmitted =>
            rw [hPastEqEmitted, hErrOffsetEq, hSumEq]
            have hSkipLe :
                skipped ≤ charsByteLength (firstChar :: restChars) := by
              rw [← hSkipBytes]
              exact Nat.le_add_right _ _
            exact Nat.add_le_add_left hSkipLe offset
        have ihResult := ihFuel
          (offset + skipped + errorBytes)
          remainingChars
          tokens
          (errors.push errEmitted)
          ihBoundedHyp
          resultErr
          resultMember
        rw [hSumEq] at ihResult
        exact ihResult

end LeanFX2.Surface
