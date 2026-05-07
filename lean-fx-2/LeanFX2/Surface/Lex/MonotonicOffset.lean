import LeanFX2.Surface.Lex
import LeanFX2.Surface.Lex.ByteConservation
import LeanFX2.Surface.Lex.LoopBound

/-! # Surface/Lex/MonotonicOffset — L04 monotonic offset chain

Closes the L04 (#1202) preservation chain: the `PositionedToken`
array produced by `Lex.run` has weakly-monotonically-increasing
`startPos.offset` across token indices.

* L04.1 (#1538): predicate `Array.isMonotonicByOffset` (this file)
* L04.2 (#1539): structural preservation under `Array.push`
* L04.3 (#1540): `lexLoop_preserves_monotonic_offsets` invariant
* L04.4 (#1541): `Lex.run_offsets_monotonic` (closes L04 / #1202)

This commit ships L04.1 (the predicate definition) plus L04.2's
push-preservation auxiliary.  The `lexLoop`-induction proof
(L04.3) and `Lex.run` specialization (L04.4) land in follow-ups
to keep each commit independently auditable.

## Why `List`-based (not `Array.size`-indexed)

Stdlib `Array.size_push` depends on `List.length_concat` which
depends on `propext`.  Any quantified-pairwise predicate over
`arr.size`-bounded indices ends up rewriting through that chain
and fails strict zero-axiom audits.  The project's existing
L07.5 pattern (e.g. `Array.push_toList_mem_decompose`) instead
operates on `arr.toList`, where `(arr.push x).toList =
arr.toList.concat x` reduces by `rfl`.  We follow the same
pattern: define monotonicity as an inductive `Prop` on `List
PositionedToken`, then bridge to arrays via `Array.toList`.

## Why weak (`≤`) instead of strict (`<`)

Strict monotonicity would require proving `bytes ≥ 1` at every
emitting branch of `lexOne`, which depends on
`Char.utf8Size_pos` from stdlib.  The stdlib proof uses
`iteInduction`/`decide` over `UInt32.le_iff_toNat_le`, both of
which risk leaking `propext` through Lean 4's match compiler in
strict zero-axiom builds.

Weak monotonicity (`≤`) reflects the structural property that
offsets never decrease.  For the L04 spec ("monotonically
increasing"), this is the load-bearing claim — strict can be
added incrementally once a propext-clean `utf8Size_pos`
substitute lands.

Zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

namespace Lex

/-- **L04.1 (#1538) — list monotonicity predicate**: a list of
`PositionedToken`s is *monotonic by offset* iff every adjacent
pair has non-decreasing `startPos.offset`.

The inductive structure makes the empty / singleton / cons cases
explicit, which lets the push-preservation proof (L04.2) recurse
structurally without invoking stdlib `Array.size`/`length_concat`
machinery (both depend on `propext`). -/
inductive List.IsMonotonicByOffset : List PositionedToken → Prop
  | empty : List.IsMonotonicByOffset []
  | single (token : PositionedToken) : List.IsMonotonicByOffset [token]
  | cons
      (token1 token2 : PositionedToken)
      (restTokens : List PositionedToken)
      (hOrder : token1.startPos.offset ≤ token2.startPos.offset)
      (hRest : List.IsMonotonicByOffset (token2 :: restTokens)) :
      List.IsMonotonicByOffset (token1 :: token2 :: restTokens)

/-- **L04.1 (#1538) — array projection**: a `PositionedToken`
array is monotonic by offset iff its `toList` projection is. -/
def Array.isMonotonicByOffset (tokenArr : Array PositionedToken) : Prop :=
  List.IsMonotonicByOffset tokenArr.toList

/-! ## L04.2 (#1539) — concat preservation

The structural induction over a `List PositionedToken`
classifies into three cases, mirroring the
`List.IsMonotonicByOffset` constructor structure:

* **empty**: `[].concat lastToken = [lastToken]`, which is
  `single`.

* **single**: `[firstToken].concat lastToken = [firstToken,
  lastToken]`.  Use `cons` with the order witness from
  `hAllBelow firstToken (List.Mem.head _)`.

* **cons of cons**: `(t1 :: t2 :: rest).concat lastToken =
  t1 :: t2 :: (rest.concat lastToken)`.  The outer `cons` carries
  forward `t1 ≤ t2` from the input invariant; the inner
  monotonicity comes from recursion on `t2 :: rest`.
-/

/-- **Auxiliary**: membership in a `List.cons` decomposes into
`= head` or `∈ tail`.  Pure structural pattern match; no stdlib
`List.mem_cons` (which leaks `propext` via match-compiler). -/
theorem List.mem_cons_decompose
    {alpha : Type} {targetElem headElem : alpha}
    {tailList : List alpha}
    (hMem : targetElem ∈ headElem :: tailList) :
    targetElem = headElem ∨ targetElem ∈ tailList := by
  cases hMem with
  | head _ => exact Or.inl rfl
  | tail _ hMemTail => exact Or.inr hMemTail

/-- **L04.2 (#1539) — concat preservation**: if `initialList`
is monotonic and every existing token's offset is bounded by
`lastToken.startPos.offset`, then `initialList.concat lastToken`
is also monotonic.

Pure structural recursion over `initialList`; no stdlib
`Array.size` / `List.length_concat` references. -/
theorem List.IsMonotonicByOffset.concat :
    ∀ (initialList : List PositionedToken) (lastToken : PositionedToken),
      List.IsMonotonicByOffset initialList →
      (∀ pastTok ∈ initialList,
          pastTok.startPos.offset ≤ lastToken.startPos.offset) →
      List.IsMonotonicByOffset (initialList.concat lastToken)
  | [], lastToken, _hMonotonic, _hAllBelow =>
    -- `[].concat lastToken` reduces to `[lastToken]` by definition.
    List.IsMonotonicByOffset.single lastToken
  | [firstToken], lastToken, _hMonotonic, hAllBelow =>
    -- `[firstToken].concat lastToken` reduces to `[firstToken, lastToken]`.
    List.IsMonotonicByOffset.cons firstToken lastToken []
      (hAllBelow firstToken (List.Mem.head []))
      (List.IsMonotonicByOffset.single lastToken)
  | firstToken :: secondToken :: restTokens, lastToken,
    hMonotonic, hAllBelow => by
    -- `(t1 :: t2 :: rest).concat lastToken` reduces to
    -- `t1 :: t2 :: (rest.concat lastToken)`.  Outer cons retains
    -- `t1 ≤ t2`; inner monotonicity by recursion on `t2 :: rest`.
    cases hMonotonic with
    | cons _ _ _ hOrder hRestMonotonic =>
      -- Build the recursive monotonicity at `(secondToken ::
      -- restTokens).concat lastToken`.  Definitionally equal to
      -- `secondToken :: restTokens.concat lastToken`.
      have hRecur :
          List.IsMonotonicByOffset
            ((secondToken :: restTokens).concat lastToken) :=
        List.IsMonotonicByOffset.concat
          (secondToken :: restTokens) lastToken hRestMonotonic
          (fun pastTok pastMember =>
            hAllBelow pastTok (List.Mem.tail firstToken pastMember))
      -- The inductive cons constructor reassembles outer pair.
      exact List.IsMonotonicByOffset.cons firstToken secondToken
        (restTokens.concat lastToken) hOrder hRecur

/-- **L04.2 (#1539) — array push preservation**: if `arrInput`
is monotonic by offset and every existing token's offset is
bounded by `newToken.startPos.offset`, then `arrInput.push
newToken` is also monotonic.

Bridge from list-level concat preservation via the `rfl`-equal
`(arr.push x).toList = arr.toList.concat x`. -/
theorem Array.isMonotonicByOffset_push
    (arrInput : Array PositionedToken) (newToken : PositionedToken)
    (hMonotonic : Array.isMonotonicByOffset arrInput)
    (hAllBelow :
      ∀ pastTok ∈ arrInput.toList,
        pastTok.startPos.offset ≤ newToken.startPos.offset) :
    Array.isMonotonicByOffset (arrInput.push newToken) :=
  -- `(arrInput.push newToken).toList = arrInput.toList.concat newToken`
  -- holds by `rfl`, so we can invoke the list-level theorem
  -- directly.  Definitional unfolding of `Array.isMonotonicByOffset`
  -- happens automatically.
  List.IsMonotonicByOffset.concat arrInput.toList newToken
    hMonotonic hAllBelow

end Lex

/-! ## L04.3 (#1540) — lexLoop preservation chain

Two strengthened invariants that together close the L04 spec:

* `Lex.lexLoop_token_offsets_bounded` — every loop-emitted token's
  offset stays within `offset + charsByteLength chars`.  Mirror of
  `Lex.lexLoop_error_offset_bounded` (L07.5) for tokens.

* `Lex.lexLoop_preserves_monotonic_offsets` — given monotonic
  input tokens whose offsets are bounded by the current `offset`,
  the loop's output tokens remain monotonic.

The two are stated as independent invariants because the
push-preservation step needs both: monotonic-up-to-now plus
bounded-by-newToken-offset (witnessed by the first invariant). -/

/-- **L04.3 (#1540) — token offset bound**: every token in
`(lexLoop fuel offset chars tokens errors).fst` has
`startPos.offset ≤ offset + charsByteLength chars`.

Mirror of `Lex.lexLoop_error_offset_bounded` for tokens.  Each
`LexStep.token` push lands at offset `offset + skipped`, which
is `≤ offset + charsByteLength chars` by
`skipTrivia_byteLength_invariant`. -/
theorem Lex.lexLoop_token_offsets_bounded :
    ∀ (fuel : Nat) (offset : Nat) (chars : List Char)
      (tokens : Array PositionedToken) (errors : Array LexError),
      (∀ pastTok ∈ tokens.toList,
          pastTok.startPos.offset ≤ offset + charsByteLength chars) →
      ∀ resultTok ∈ (lexLoop fuel offset chars tokens errors).fst.toList,
        resultTok.startPos.offset ≤ offset + charsByteLength chars := by
  intro fuel
  induction fuel with
  | zero =>
    intro offset chars tokens errors tokensBounded resultTok resultMember
    exact tokensBounded resultTok resultMember
  | succ fuelMinusOne ihFuel =>
    intro offset chars tokens errors tokensBounded resultTok resultMember
    cases chars with
    | nil =>
      exact tokensBounded resultTok resultMember
    | cons firstChar restChars =>
      rw [Lex.lexLoop_cons_unfold] at resultMember
      have hSkipBytesUngen :=
        Lex.skipTrivia_byteLength_invariant
          (firstChar :: restChars).length (firstChar :: restChars)
      generalize hSkipEq :
        skipTrivia (firstChar :: restChars).length (firstChar :: restChars)
          = trivia
        at resultMember hSkipBytesUngen
      obtain ⟨skipped, afterTrivia⟩ := trivia
      dsimp only at resultMember hSkipBytesUngen
      have hSkipBytes :
          skipped + charsByteLength afterTrivia
            = charsByteLength (firstChar :: restChars) :=
        hSkipBytesUngen
      have hLexOneBytesUngen :=
        Lex.lexOne_byteLength_invariant (offset + skipped) afterTrivia
      generalize hLexOneEq :
        lexOne (offset + skipped) afterTrivia = lexOneResult
        at resultMember hLexOneBytesUngen
      cases lexOneResult with
      | eof =>
        exact tokensBounded resultTok resultMember
      | token tokenSeen tokenBytes remainingChars =>
        have hLexOneBytes :
            tokenBytes + charsByteLength remainingChars
              = charsByteLength afterTrivia := hLexOneBytesUngen
        have hSumEq :
            offset + skipped + tokenBytes + charsByteLength remainingChars
              = offset + charsByteLength (firstChar :: restChars) := by
          rw [Nat.add_assoc offset skipped tokenBytes,
              Nat.add_assoc offset (skipped + tokenBytes)
                            (charsByteLength remainingChars),
              Nat.add_assoc skipped tokenBytes
                            (charsByteLength remainingChars),
              hLexOneBytes,
              hSkipBytes]
        have hSkipLe :
            skipped ≤ charsByteLength (firstChar :: restChars) := by
          rw [← hSkipBytes]
          exact Nat.le_add_right _ _
        have ihBoundedHyp :
            ∀ pastTok ∈ (tokens.push
                { token := tokenSeen,
                  startPos := { offset := offset + skipped } }).toList,
              pastTok.startPos.offset
                ≤ (offset + skipped + tokenBytes)
                    + charsByteLength remainingChars := by
          intro pastTok pastMember
          rw [hSumEq]
          cases Lex.Array.push_toList_mem_decompose tokens
                  { token := tokenSeen,
                    startPos := { offset := offset + skipped } }
                  pastMember with
          | inl hOldMember => exact tokensBounded pastTok hOldMember
          | inr hPastEqEmitted =>
            rw [hPastEqEmitted]
            exact Nat.add_le_add_left hSkipLe offset
        have ihResult := ihFuel
          (offset + skipped + tokenBytes)
          remainingChars
          (tokens.push
            { token := tokenSeen,
              startPos := { offset := offset + skipped } })
          errors
          ihBoundedHyp
          resultTok
          resultMember
        rw [hSumEq] at ihResult
        exact ihResult
      | error errEmitted errorBytes remainingChars =>
        have hLexOneBytes :
            errorBytes + charsByteLength remainingChars
              = charsByteLength afterTrivia := hLexOneBytesUngen
        have hSumEq :
            offset + skipped + errorBytes + charsByteLength remainingChars
              = offset + charsByteLength (firstChar :: restChars) := by
          rw [Nat.add_assoc offset skipped errorBytes,
              Nat.add_assoc offset (skipped + errorBytes)
                            (charsByteLength remainingChars),
              Nat.add_assoc skipped errorBytes
                            (charsByteLength remainingChars),
              hLexOneBytes,
              hSkipBytes]
        have ihBoundedHyp :
            ∀ pastTok ∈ tokens.toList,
              pastTok.startPos.offset
                ≤ (offset + skipped + errorBytes)
                    + charsByteLength remainingChars := by
          intro pastTok pastMember
          rw [hSumEq]
          exact tokensBounded pastTok pastMember
        have ihResult := ihFuel
          (offset + skipped + errorBytes)
          remainingChars
          tokens
          (errors.push errEmitted)
          ihBoundedHyp
          resultTok
          resultMember
        rw [hSumEq] at ihResult
        exact ihResult

/-- **L04.3 (#1540) — monotonicity preservation**: if the input
`tokens` array is monotonic by offset and every input token's
offset is `≤ offset`, then the loop's output token array remains
monotonic.

Structure mirrors `lexLoop_token_offsets_bounded`: induction on
fuel, case-split on `lexOne`.  At the `LexStep.token` push site,
`Lex.Array.isMonotonicByOffset_push` (L04.2) extends monotonicity
because every existing token's offset `≤ offset ≤ offset + skipped`
(the new token's offset). -/
theorem Lex.lexLoop_preserves_monotonic_offsets :
    ∀ (fuel : Nat) (offset : Nat) (chars : List Char)
      (tokens : Array PositionedToken) (errors : Array LexError),
      Lex.Array.isMonotonicByOffset tokens →
      (∀ pastTok ∈ tokens.toList, pastTok.startPos.offset ≤ offset) →
      Lex.Array.isMonotonicByOffset
        (lexLoop fuel offset chars tokens errors).fst := by
  intro fuel
  induction fuel with
  | zero =>
    intro offset chars tokens errors hMonotonic _hBounded
    exact hMonotonic
  | succ fuelMinusOne ihFuel =>
    intro offset chars tokens errors hMonotonic hBounded
    cases chars with
    | nil =>
      exact hMonotonic
    | cons firstChar restChars =>
      rw [Lex.lexLoop_cons_unfold]
      have hSkipBytesUngen :=
        Lex.skipTrivia_byteLength_invariant
          (firstChar :: restChars).length (firstChar :: restChars)
      generalize hSkipEq :
        skipTrivia (firstChar :: restChars).length (firstChar :: restChars)
          = trivia
        at hSkipBytesUngen ⊢
      obtain ⟨skipped, afterTrivia⟩ := trivia
      dsimp only at hSkipBytesUngen ⊢
      have hLexOneBytesUngen :=
        Lex.lexOne_byteLength_invariant (offset + skipped) afterTrivia
      generalize hLexOneEq :
        lexOne (offset + skipped) afterTrivia = lexOneResult
        at hLexOneBytesUngen ⊢
      cases lexOneResult with
      | eof =>
        exact hMonotonic
      | token tokenSeen tokenBytes remainingChars =>
        -- Push site: extend monotonicity to tokens.push newToken.
        have hPushMonotonic :
            Lex.Array.isMonotonicByOffset
              (tokens.push
                { token := tokenSeen,
                  startPos := { offset := offset + skipped } }) := by
          apply Lex.Array.isMonotonicByOffset_push tokens
            { token := tokenSeen,
              startPos := { offset := offset + skipped } }
            hMonotonic
          intro pastTok pastMember
          have hPastBound := hBounded pastTok pastMember
          exact Nat.le_trans hPastBound (Nat.le_add_right offset skipped)
        -- New bound for IH: every (tokens.push newToken) token's
        -- offset ≤ offset + skipped + tokenBytes (next loop offset).
        have hPushBounded :
            ∀ pastTok ∈ (tokens.push
                { token := tokenSeen,
                  startPos := { offset := offset + skipped } }).toList,
              pastTok.startPos.offset ≤ offset + skipped + tokenBytes := by
          intro pastTok pastMember
          cases Lex.Array.push_toList_mem_decompose tokens
                  { token := tokenSeen,
                    startPos := { offset := offset + skipped } }
                  pastMember with
          | inl hOldMember =>
            have hPastBound := hBounded pastTok hOldMember
            exact Nat.le_trans hPastBound
              (Nat.le_trans
                (Nat.le_add_right offset skipped)
                (Nat.le_add_right (offset + skipped) tokenBytes))
          | inr hEqNew =>
            rw [hEqNew]
            exact Nat.le_add_right (offset + skipped) tokenBytes
        exact ihFuel (offset + skipped + tokenBytes) remainingChars
          (tokens.push
            { token := tokenSeen,
              startPos := { offset := offset + skipped } })
          errors hPushMonotonic hPushBounded
      | error errEmitted errorBytes remainingChars =>
        -- Tokens unchanged; the bound widens because the next
        -- loop offset `offset + skipped + errorBytes ≥ offset`.
        have hWidenBounded :
            ∀ pastTok ∈ tokens.toList,
              pastTok.startPos.offset ≤ offset + skipped + errorBytes := by
          intro pastTok pastMember
          have hPastBound := hBounded pastTok pastMember
          exact Nat.le_trans hPastBound
            (Nat.le_trans
              (Nat.le_add_right offset skipped)
              (Nat.le_add_right (offset + skipped) errorBytes))
        exact ihFuel (offset + skipped + errorBytes) remainingChars
          tokens (errors.push errEmitted) hMonotonic hWidenBounded

/-! ## L04.4 (#1541) — Lex.run output monotonic, closes L04 (#1202) -/

/-- **L04.4 (#1541) — closes L04 (#1202)**: every successful
`Lex.run chars` produces an `Array PositionedToken` whose
`startPos.offset` values are weakly monotonically non-decreasing
across the array.

The proof:
1. Apply `Lex.lexLoop_preserves_monotonic_offsets` at the empty
   initial token array (trivially monotonic + bounded by 0).
2. Apply `Lex.lexLoop_token_offsets_bounded` to show every
   loop-produced token's offset `≤ charsByteLength chars`
   (the eof sentinel's offset).
3. Use `Lex.Array.isMonotonicByOffset_push` (L04.2) to extend
   monotonicity through the appended `Token.eof` sentinel. -/
theorem Lex.run_offsets_monotonic
    (chars : List Char) (tokens : Array PositionedToken)
    (hRun : Lex.run chars = .ok tokens) :
    Lex.Array.isMonotonicByOffset tokens := by
  rw [Lex.run_eq_loop_branch] at hRun
  generalize hLexEq :
      lexLoop (chars.length + 1) 0 chars #[] #[] = lexResult
    at hRun
  by_cases hEmpty : lexResult.snd.isEmpty
  · rw [if_pos hEmpty] at hRun
    have hTokensEq :
        lexResult.fst.push
            { token := Token.eof,
              startPos := { offset := charsByteLength chars } }
          = tokens := by
      cases hRun
      rfl
    -- Step 1: loop output is monotonic (L04.3 at empty initial).
    have hLoopMonotonic :
        Lex.Array.isMonotonicByOffset lexResult.fst := by
      have hInitMonotonic :
          Lex.Array.isMonotonicByOffset (#[] : Array PositionedToken) :=
        Lex.List.IsMonotonicByOffset.empty
      have hInitBounded :
          ∀ pastTok ∈ (#[] : Array PositionedToken).toList,
            pastTok.startPos.offset ≤ 0 := by
        intro _pastTok pastMember
        cases pastMember
      have hPreserved :=
        Lex.lexLoop_preserves_monotonic_offsets
          (chars.length + 1) 0 chars #[] #[]
          hInitMonotonic hInitBounded
      rw [hLexEq] at hPreserved
      exact hPreserved
    -- Step 2: every loop token's offset ≤ charsByteLength chars
    -- (L04.3 token bound at empty initial).
    have hLoopBounded :
        ∀ pastTok ∈ lexResult.fst.toList,
          pastTok.startPos.offset ≤ charsByteLength chars := by
      intro pastTok pastMember
      have hInitBounded :
          ∀ pastT ∈ (#[] : Array PositionedToken).toList,
            pastT.startPos.offset ≤ 0 + charsByteLength chars := by
        intro _pastT pastM
        cases pastM
      have hBoundedRes :=
        Lex.lexLoop_token_offsets_bounded
          (chars.length + 1) 0 chars #[] #[] hInitBounded
      rw [hLexEq] at hBoundedRes
      have hRes := hBoundedRes pastTok pastMember
      rw [Nat.zero_add] at hRes
      exact hRes
    -- Step 3: push eof preserves monotonicity (L04.2).
    have hPushMonotonic :
        Lex.Array.isMonotonicByOffset
          (lexResult.fst.push
            { token := Token.eof,
              startPos := { offset := charsByteLength chars } }) := by
      apply Lex.Array.isMonotonicByOffset_push lexResult.fst
        { token := Token.eof,
          startPos := { offset := charsByteLength chars } }
        hLoopMonotonic
      intro pastTok pastMember
      exact hLoopBounded pastTok pastMember
    rw [← hTokensEq]
    exact hPushMonotonic
  · rw [if_neg hEmpty] at hRun
    cases hRun

end LeanFX2.Surface
