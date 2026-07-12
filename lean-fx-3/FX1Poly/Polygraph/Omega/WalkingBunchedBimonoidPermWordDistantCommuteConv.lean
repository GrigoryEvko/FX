import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteGeneric
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordRunCommuteConv

/-! # Polygraph/Omega/WalkingBunchedBimonoidPermWordDistantCommuteConv — the `permWord`-level distant-commute
and the FIRST fold rung of the Cartier–Foata comb staircase, over the SHIPPED star scope (WP-PROP r22)

★ **THE r21 CENSUS RESIDUAL (clause 2 + the first rung of clause 3) IS DELIVERED.**  The r21 marker
`fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen` (`= false`, byte-intact cross-file)
named three open items after the fully generic additive-form distant-commute
(`bunchedBimonoidDistantCommuteGenericLetterConv`) landed:

  * (1) the ADJACENT braid atom — stays COMPUTE-walled (its width-4 triple-`vcomp` endpoint `rfl` exceeds even
    the 4M-heartbeat budget; a compute wall, NOT a soundness gap).  This round does NOT re-attempt it.
  * (2) the TRAILING-BOUNDARY reshape + the lift of the `vcomp`-form generic theorem to the `sigmaAt`-word /
    `permWord [..] w` fold — **DELIVERED here** (P1 + P2).
  * (3) the CONV folds (`swapCommutesRun*Conv` / `combInsertConv` / `combNormalizeFormConv` / `recCombConv`) —
    **the FIRST rung `swapCommutesRunAboveConv` is DELIVERED here** (P3); the `Below` twin, the comb-insertion
    fold, and the recursive comb staircase remain (r23+).

This is the printed-literature fact made kernel-checked.  The fold tower is **Cartier–Foata / Foata
normalization of a Mazurkiewicz trace** (Cartier–Foata 1969; Viennot, heaps of pieces; Krattenthaler, the
heaps ↔ Cartier–Foata monoid bijection).  Inside a single commutation class the canonical representative is
reached by **commutation (distant) moves alone** — the braid move is only ever needed to cross *between*
classes, so it is genuinely out of the fold's scope (Stembridge, *On the Fully Commutative Elements of Coxeter
Groups*, J. Alg. Combin. 5 (1996): a fully-commutative element = one whose reduced words are all related by
transpositions of adjacent COMMUTING generators).  The insertion fold's correctness is
"each drop is a run of independent adjacent swaps" (Maarand & Uustalu, *Certified Foata Normalization for
Generalized Traces*, NFM 2018 / ISSE 2019 — an Agda formalization; no Lean/Coq/Isabelle Cartier–Foata
normalization is known, so this kernel-checked Lean walker is first-of-kind).

**P1 — the trailing-boundary reshape (dim-1, essentially the shipped S4).**  For `sigmaAt`, the additive swap
generator `bunchedBimonoidAddSigmaGen = gen addSwap aaWord aaWord` has EQUAL source and target boundary
(`aaWord`), so `boundaryTarget (sigmaAt w k)` and `boundarySource (sigmaAt w k)` are the SAME tree definitionally.
Hence the shipped r15 `bunchedBimonoidSigmaAtBoundaryReshapeConv` (`aWordPow w ~ boundarySource (sigmaAt w k)`)
ALSO types at the `boundaryTarget` position.  The genuinely-new piece is the right-tail `id` bridge
`bunchedBimonoidVcompIdRightBridgedWithId` — the exact `idCongr`-keyed dual of the shipped
`vcompIdLeft_bridgedWithId` — assembled with a `StrictAxiomRel.vcompUnitRight` row into the trailing-id absorber
`bunchedBimonoidSigmaAtTrailingIdAbsorbConv` (`vcomp (sigmaAt w k) (id (aWordPow w)) ~ sigmaAt w k`).

**P2 — the `sigmaAt`-form generic distant-commute + the two-letter `permWord` lift.**  The r21 atom is in
additive-pad form; the fold consumer needs `(w, i, j)` form under a distance hypothesis.  The bridge sets
`leftPad = i`, `gap = j - i - 2`, `rightPad = w - j - 2` and transports the two whiskering exponents by
`congrArg (aWordPow ·)` along two propext-clean truncated-subtraction identities — A1 `i + (2 + (j-i-2)) = j`
(the r15 reshape-arith shape) and A2 `(j-i-2) + (2 + (w-j-2)) = w-i-2` (new, structural on `i`).  Yields
`bunchedBimonoidSigmaAtDistantCommuteConv : vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)`
for `i + 2 ≤ j` and `j + 2 ≤ w`, then the `permWord [i,j] w ~ permWord [j,i] w` lift by stripping both trailing
ids (P1) around the atom.

**P3 — the first fold rung `swapCommutesRunAboveConv`.**  Structural on the run length `count`, gated on the
distance `letter + count + 1 ≤ runTop` AND the width validity `runTop + 2 ≤ w`: the low letter commutes past a
whole descending run `descendingPositions runTop count` above it.  Base = the P1 absorbers (trailing via P1b,
leading via the shipped `vcompIdLeft_bridgedWithId` + S4); step = the associativity dance
`symm-vcompAssoc → vcompCongrLeft (P2 atom on the head pair) → vcompAssoc → vcompCongrRight (IH on the tail) →
symm-vcompAssoc`.  Matching `runTop` as a successor makes `runTop - 1` (the recursive run anchor) compute by
`rfl`, so no `Nat.pred`/`succ_pred` gymnastics arise.

The four star owners (`StarAssembly` / `RiffleAssembly` / `CollisionCanonForm` / `CoxeterUniqueness`) stay
`= false` byte-intact; `StrictAxioms.lean` + the shipped `bunchedBimonoidStarCongruenceScope` are untouched (only
the shipped `StrictAxiomRel.{vcompAssoc, vcompUnitLeft, vcompUnitRight, interchange}` rows are consumed through
`bunchedBimonoidStrictAxiomEmbedsIntoStarScope`).  No fabricated star flip.  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin). -/

namespace FX1Poly.Polygraph.Omega

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## P0 — the propext-clean truncated-subtraction backbone (the private A1 / A2 arithmetic)

`bunchedBimonoidReshapeArithConvFold` / `bunchedBimonoidCommuteHighEqConvFold` are `private` to the ConvFold
file, so the reshape arithmetic is re-derived here (identical clean structural recipe: `Nat.succ_sub_succ` /
`Nat.succ_add` / `Nat.zero_add` / `Nat.sub_zero` and the literal `n + 2 - 2 = n := rfl` closer — the truncation
lemmas `Nat.add_sub_cancel` / `Nat.sub_right_comm` / `omega` all pull `propext` and are avoided). -/

/-- `value - 2 + 2 = value` under `2 ≤ value` — the truncation base, full-enum on `value` so no partial-match
`propext` leak. -/
private theorem bunchedBimonoidPermWordSubTwoAddTwo : (value : Nat) → 2 ≤ value → value - 2 + 2 = value
  | 0, twoLe => absurd twoLe (by decide)
  | 1, twoLe => absurd twoLe (by decide)
  | _ + 2, _ => rfl

/-- `low + (high - low - 2) + 2 = high` under `low + 2 ≤ high` — the staircase identity, structural on `low`
(the r15 `commuteHighEq` recipe, re-derived because the original is `private`). -/
private theorem bunchedBimonoidPermWordCommuteHighEq :
    (low high : Nat) → low + 2 ≤ high → low + (high - low - 2) + 2 = high
  | 0, high, hLe => by
      rw [Nat.zero_add]
      exact bunchedBimonoidPermWordSubTwoAddTwo high hLe
  | _ + 1, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | low + 1, high + 1, hLe => by
      have inner : low + (high - low - 2) + 2 = high :=
        bunchedBimonoidPermWordCommuteHighEq low high (Nat.le_of_succ_le_succ hLe)
      rw [Nat.succ_sub_succ, Nat.succ_add, Nat.succ_add]
      exact congrArg Nat.succ inner

/-- `value + 2 - 2 = value` — the KEY clean closer (the literal `2` computes through `Nat.sub`, so `:= rfl`). -/
private theorem bunchedBimonoidPermWordAddTwoSubTwo (value : Nat) : value + 2 - 2 = value := rfl

/-- From `sum + 2 = total` conclude `sum = total - 2` — `sum` and `total` are independent, so `← h` rewrites
only the RHS `total` and the `+ 2 - 2` closer cancels.  Avoids `generalize ... at` entirely. -/
private theorem bunchedBimonoidPermWordSolveAddTwo {sum total : Nat} (h : sum + 2 = total) :
    sum = total - 2 := by
  rw [← h, bunchedBimonoidPermWordAddTwoSubTwo]

/-- **A1** — `lowPad + (2 + (highWidth - lowPad - 2)) = highWidth` under `lowPad + 2 ≤ highWidth`.  Exactly the
r15 `reshapeArith` shape (the shipped one is `private`): the first exponent identity the `sigmaAt`-form transport
needs. -/
private theorem bunchedBimonoidPermWordReshapeArithLow (lowPad highWidth : Nat)
    (inRange : lowPad + 2 ≤ highWidth) :
    lowPad + (2 + (highWidth - lowPad - 2)) = highWidth := by
  have staircase : lowPad + (highWidth - lowPad - 2) + 2 = highWidth :=
    bunchedBimonoidPermWordCommuteHighEq lowPad highWidth inRange
  rw [Nat.add_comm 2 (highWidth - lowPad - 2), ← Nat.add_assoc]
  exact staircase

/-- **A2** — `(midIndex - leftIndex - 2) + (2 + (highWidth - midIndex - 2)) = highWidth - leftIndex - 2` under
`leftIndex + 2 ≤ midIndex` and `midIndex + 2 ≤ highWidth`.  The NEW nested-subtraction identity: structural on
`leftIndex`, with `midIndex` / `highWidth` matched as successors (impossible zero cases discharged by
`Nat.not_succ_le_zero`) so the three `Nat.succ_sub_succ` redexes reduce in lockstep. -/
private theorem bunchedBimonoidPermWordGapReshapeArith :
    (leftIndex midIndex highWidth : Nat) → leftIndex + 2 ≤ midIndex → midIndex + 2 ≤ highWidth →
      (midIndex - leftIndex - 2) + (2 + (highWidth - midIndex - 2)) = highWidth - leftIndex - 2
  | 0, midIndex, highWidth, hij, hjw => by
      rw [Nat.sub_zero, Nat.sub_zero]
      have midDrop : midIndex - 2 + 2 = midIndex := bunchedBimonoidPermWordSubTwoAddTwo midIndex hij
      have highStair : midIndex + (highWidth - midIndex - 2) + 2 = highWidth :=
        bunchedBimonoidPermWordCommuteHighEq midIndex highWidth hjw
      rw [← Nat.add_assoc, midDrop]
      exact bunchedBimonoidPermWordSolveAddTwo highStair
  | _ + 1, 0, _, hij, _ => absurd hij (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, 0, _, hjw => absurd hjw (Nat.not_succ_le_zero _)
  | leftIndex + 1, midIndex + 1, highWidth + 1, hij, hjw => by
      rw [Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.succ_sub_succ]
      exact bunchedBimonoidPermWordGapReshapeArith leftIndex midIndex highWidth
        (Nat.le_of_succ_le_succ hij) (Nat.le_of_succ_le_succ hjw)

/-! ## P1 — the trailing-boundary reshape -/

/-- ★ **THE OMEGA-1 JAM STEP, RIGHT-TAIL DUAL.**  The `idCongr`-keyed dual of the shipped
`vcompIdLeft_bridgedWithId`: from a convertibility `targetCandidate ~ boundaryTarget cellA`, `idCongr` lifts it
to the identity `(dim+1)`-cells, `vcompCongrRight` places it under the vertical composite, and the supplied unit
row absorbs the TRAILING identity — yielding `vcomp cellA (id targetCandidate) ~ cellA`.  Generic in
`baseRel`. -/
theorem bunchedBimonoidVcompIdRightBridgedWithId {computad : OmegaComputad} {baseRel : CellRelOver computad}
    {dim : Nat} {targetCandidate : CellExpr computad dim} (cellA : CellExpr computad (dim + 1))
    (hconv : SaturatedConvOverWithId computad baseRel targetCandidate (boundaryTarget cellA))
    (unitRow : SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp cellA (CellExpr.id (boundaryTarget cellA))) cellA) :
    SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp cellA (CellExpr.id targetCandidate)) cellA :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight cellA (SaturatedConvOverWithId.idCongr hconv))
    unitRow

/-- ★★ **THE `sigmaAt` TRAILING-ID ABSORBER (P1, DELIVERED).**  Under `k + 2 ≤ w`,
`vcomp (sigmaAt w k) (id (aWordPow w)) ~ sigmaAt w k` over the star scope.  The `hconv` slot takes the r15 S4
`bunchedBimonoidSigmaAtBoundaryReshapeConv` DIRECTLY (no `symm`): S4 gives `aWordPow w ~ boundarySource (sigmaAt
w k)`, and `boundaryTarget (sigmaAt w k) = boundarySource (sigmaAt w k)` is definitional (the additive swap
generator has equal source/target boundary `aaWord`), so it also types at the `boundaryTarget` position.  The
`unitRow` slot is one `StrictAxiomRel.vcompUnitRight` row. -/
theorem bunchedBimonoidSigmaAtTrailingIdAbsorbConv (wordWidth positionK : Nat)
    (inRange : positionK + 2 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth positionK)
        (CellExpr.id (bunchedBimonoidAWordPow wordWidth)))
      (bunchedBimonoidSigmaAt wordWidth positionK) :=
  bunchedBimonoidVcompIdRightBridgedWithId (bunchedBimonoidSigmaAt wordWidth positionK)
    (bunchedBimonoidSigmaAtBoundaryReshapeConv wordWidth positionK inRange)
    (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
      (StrictAxiomRel.vcompUnitRight (bunchedBimonoidSigmaAt wordWidth positionK)))

/-! ## P2 — the `sigmaAt`-form generic distant-commute + the two-letter `permWord` lift -/

/-- ★★★ **THE `sigmaAt`-FORM GENERIC DISTANT-COMMUTE (P2, DELIVERED).**  For `i + 2 ≤ j` and `j + 2 ≤ w`,
`vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w i)` over the SHIPPED star scope — the
Coxeter commutation relation `s_i s_j = s_j s_i` for `|i - j| ≥ 2` at generic width.  The r21 additive-form atom
`bunchedBimonoidDistantCommuteGenericLetterConv` at pads `(i, j - i - 2, w - j - 2)` is transported to the
`sigmaAt`-word form by rewriting the two whiskering exponents along A1 and A2; `exact` then unfolds `sigmaAt`. -/
theorem bunchedBimonoidSigmaAtDistantCommuteConv (wordWidth leftIndex midIndex : Nat)
    (hij : leftIndex + 2 ≤ midIndex) (hjw : midIndex + 2 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth leftIndex) (bunchedBimonoidSigmaAt wordWidth midIndex))
      (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth midIndex) (bunchedBimonoidSigmaAt wordWidth leftIndex)) := by
  have atom := bunchedBimonoidDistantCommuteGenericLetterConv leftIndex (midIndex - leftIndex - 2)
    (wordWidth - midIndex - 2)
  rw [bunchedBimonoidPermWordReshapeArithLow leftIndex midIndex hij,
      bunchedBimonoidPermWordGapReshapeArith leftIndex midIndex wordWidth hij hjw] at atom
  exact atom

/-- ★★ **THE TWO-LETTER `permWord` DISTANT-COMMUTE (P2, DELIVERED).**  Under `i + 2 ≤ j` and `j + 2 ≤ w`,
`permWord [i, j] w ~ permWord [j, i] w` over the star scope.  The `permWord` fold carries an inner trailing
`id (aWordPow w)`; P1's absorber strips it on the right factor, the `sigmaAt`-form atom fires, and `symm` of the
absorber re-inserts it in the swapped order. -/
theorem bunchedBimonoidPermWordTwoLetterDistantCommuteConv (wordWidth leftIndex midIndex : Nat)
    (hij : leftIndex + 2 ≤ midIndex) (hjw : midIndex + 2 ≤ wordWidth) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord [leftIndex, midIndex] wordWidth)
      (bunchedBimonoidPermWord [midIndex, leftIndex] wordWidth) :=
  have hiw : leftIndex + 2 ≤ wordWidth :=
    Nat.le_trans hij (Nat.le_trans (Nat.le_add_right midIndex 2) hjw)
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth leftIndex)
      (bunchedBimonoidSigmaAtTrailingIdAbsorbConv wordWidth midIndex hjw))
    (SaturatedConvOverWithId.trans
      (bunchedBimonoidSigmaAtDistantCommuteConv wordWidth leftIndex midIndex hij hjw)
      (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth midIndex)
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidSigmaAtTrailingIdAbsorbConv wordWidth leftIndex hiw))))

/-! ## P3 — the first fold rung: `swapCommutesRunAboveConv` -/

/-- ★★★ **THE FIRST CONV FOLD RUNG (P3, DELIVERED) — a low letter commutes past a descending run above it.**
Structural on the run length `count`, gated on the distance `letter + count + 1 ≤ runTop` (the letter stays
`≥ 2` below every run generator, so every commutation is distant) AND the width validity `runTop + 2 ≤ w`.
Yields `vcomp (sigmaAt w letter) (permWord (descendingPositions runTop count) w) ~
vcomp (permWord (descendingPositions runTop count) w) (sigmaAt w letter)`.

Base (`count = 0`, the run is `id (aWordPow w)`): the P1 trailing absorber on the left, `symm` of the shipped
`vcompIdLeft_bridgedWithId` leading absorber on the right.  Step (`count + 1`, matching `runTop` as a successor
so `runTop - 1` computes to the recursive anchor): the associativity dance
`symm-vcompAssoc → vcompCongrLeft (P2 atom `letter`/`runTop`) → vcompAssoc → vcompCongrRight (IH) → symm-vcompAssoc`.
This is the Foata-normalization "each drop is a run of independent adjacent swaps" invariant (Maarand–Uustalu),
made kernel-checked.  The `Below` twin, `combInsertConv`, `combNormalizeFormConv`, `recCombConv`, and the Brauer
`combCanonicity` per-file clone remain (r23+). -/
theorem bunchedBimonoidSwapCommutesRunAboveConv (wordWidth letter : Nat) :
    (runTop count : Nat) → letter + count + 1 ≤ runTop → runTop + 2 ≤ wordWidth →
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth))
        (CellExpr.vcomp (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth)
          (bunchedBimonoidSigmaAt wordWidth letter))
  | runTop, 0, hLe, hW => by
      have hlw : letter + 2 ≤ wordWidth :=
        Nat.le_trans (Nat.succ_le_succ hLe) (Nat.le_trans (Nat.le_succ (runTop + 1)) hW)
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
            (CellExpr.id (bunchedBimonoidAWordPow wordWidth)))
          (CellExpr.vcomp (CellExpr.id (bunchedBimonoidAWordPow wordWidth))
            (bunchedBimonoidSigmaAt wordWidth letter))
      exact SaturatedConvOverWithId.trans
        (bunchedBimonoidSigmaAtTrailingIdAbsorbConv wordWidth letter hlw)
        (SaturatedConvOverWithId.symm
          (vcompIdLeft_bridgedWithId (bunchedBimonoidSigmaAt wordWidth letter)
            (bunchedBimonoidSigmaAtBoundaryReshapeConv wordWidth letter hlw)
            (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
              (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidSigmaAt wordWidth letter)))))
  | 0, count + 1, hLe, _ => absurd hLe (Nat.not_succ_le_zero _)
  | runTop + 1, count + 1, hLe, hW => by
      have topGap : letter + 2 ≤ runTop + 1 :=
        Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left 2 count) letter) hLe
      have ihGap : letter + count + 1 ≤ runTop := Nat.le_of_succ_le_succ hLe
      have ihWidth : runTop + 2 ≤ wordWidth :=
        Nat.le_trans (Nat.add_le_add_right (Nat.le_succ runTop) 2) hW
      show SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
          (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth letter)
            (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (runTop + 1))
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth)))
          (CellExpr.vcomp
            (CellExpr.vcomp (bunchedBimonoidSigmaAt wordWidth (runTop + 1))
              (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth))
            (bunchedBimonoidSigmaAt wordWidth letter))
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth letter)
            (bunchedBimonoidSigmaAt wordWidth (runTop + 1))
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth)))) ?_
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth)
          (bunchedBimonoidSigmaAtDistantCommuteConv wordWidth letter (runTop + 1) topGap hW)) ?_
      refine SaturatedConvOverWithId.trans
        (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
          (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth (runTop + 1))
            (bunchedBimonoidSigmaAt wordWidth letter)
            (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth))) ?_
      refine SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth (runTop + 1))
          (bunchedBimonoidSwapCommutesRunAboveConv wordWidth letter runTop count ihGap ihWidth)) ?_
      exact SaturatedConvOverWithId.symm (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
        (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth (runTop + 1))
          (bunchedBimonoidPermWord (bunchedBimonoidDescendingPositions runTop count) wordWidth)
          (bunchedBimonoidSigmaAt wordWidth letter)))

/-! ## Non-vacuity — matrix soundness pin + interpreter truth probes -/

/-- The distant pair `[0, 2]` / `[2, 0]` at width 4 shares its `4 x 4` permutation matrix (`rfl`) — the
soundness ceiling the P2 CONV lift is faithful to. -/
theorem bunchedBimonoidPermWordDistantCommuteFourZeroTwoMatrixShared :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 2] 4)
      = bunchedBimonoidEvalCell (bunchedBimonoidPermWord [2, 0] 4) := rfl

-- Distant pair COMMUTES (must print true); adjacent pair does NOT (must print false):
#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 2] 4)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [2, 0] 4)).entries) -- true
#eval decide ((bunchedBimonoidEvalCell (bunchedBimonoidPermWord [0, 1] 3)).entries
  = (bunchedBimonoidEvalCell (bunchedBimonoidPermWord [1, 0] 3)).entries) -- false

/-! ## The r22 honesty markers (new markers per literal delivery only; owners byte-intact) -/

/-- ★★★ **ESTABLISHED (P1) — the `sigmaAt` trailing-boundary reshape is DELIVERED.**  `= true` records
`bunchedBimonoidVcompIdRightBridgedWithId` (the right-tail dual of `vcompIdLeft_bridgedWithId`) and
`bunchedBimonoidSigmaAtTrailingIdAbsorbConv` (`vcomp (sigmaAt w k) (id (aWordPow w)) ~ sigmaAt w k`), reusing the
r15 S4 at the `boundaryTarget` position by the additive-swap equal-boundary defeq.  Closes clause (2) of the r21
census marker `fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen` (retire-name-only; that
marker stays `= false` byte-intact cross-file).  Zero-axiom. -/
def fxBunchedBimonoid_sigmaAtTrailingBoundaryReshapeShipped : Bool := true

/-- ★★★ **ESTABLISHED (P2) — the `sigmaAt`-form + `permWord` distant-commute is DELIVERED.**  `= true` records
`bunchedBimonoidSigmaAtDistantCommuteConv` (`vcomp (sigmaAt w i) (sigmaAt w j) ~ vcomp (sigmaAt w j) (sigmaAt w
i)` for `i + 2 ≤ j`, `j + 2 ≤ w`) and its `permWord [i,j] w ~ permWord [j,i] w` lift — the r21 additive atom
transported to word form along the A1 / A2 truncated-subtraction identities.  Matrix-sound (the `[0,2]`/`[2,0]`
pin) and interpreter-discriminated (distant true, adjacent false).  Zero-axiom. -/
def fxBunchedBimonoid_sigmaAtGenericDistantCommuteConvShipped : Bool := true

/-- ★★★ **ESTABLISHED (P3) — the first CONV fold rung `swapCommutesRunAboveConv` is DELIVERED.**  `= true`
records `bunchedBimonoidSwapCommutesRunAboveConv`: a low letter commutes past a descending run above it, the CONV
mirror of the r14 pure `bunchedBimonoidSwapCommutesRunAbove`, structural on the run length and assembled from the
P2 atom + the shipped `StrictAxiomRel.vcompAssoc` regrouping.  Closes the FIRST rung of clause (3) of the r21
census marker (retire-name-only).  Zero-axiom. -/
def fxBunchedBimonoid_swapCommutesRunAboveConvShipped : Bool := true

/-- ★ **THE `Below` TWIN + THE COMB FOLDS STAY OPEN — the honest r22 census, no fabricated flip.**  `= false`
records what this round does NOT reach: the symmetric `swapCommutesRunBelowConv` (gate `runTop + 2 ≤ letter`,
the reversed distance — the r23 head), the comb-insertion fold `combInsertConv`, the single-level
`combNormalizeFormConv`, the recursive comb staircase `recCombConv`, and the Brauer `combCanonicity` per-file
clone.  The ADJACENT braid atom stays COMPUTE-walled (unchanged).  The four star owners stay `= false`
byte-intact; `StrictAxioms.lean` + the shipped star scope are untouched.  No fabricated star flip. -/
def fxBunchedBimonoid_swapCommutesRunBelowAndCombFoldsStillOpen : Bool := false

end FX1Poly.Polygraph.Omega
