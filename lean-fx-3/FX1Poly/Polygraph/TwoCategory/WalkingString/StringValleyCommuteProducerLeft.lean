import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducer

/-! # WalkingString — Piece I COMMUTE producer, LEFT-of mirror at the three-generator seed (FC-3 r6, B2)

`StringValleyCommuteProducer` closed the COMMUTE producer for the RIGHT-of window offset (`cupLeft ≤ capLeft`).
The classifier's `disjointWindows` verdict is SYMMETRIC (`natWindowDistance` is `(a − b) + (b − a)`), so the same
verdict also covers the LEFT-of offset (`capLeft ≤ cupLeft`).  This file mirrors the right-of producer for that
direction, over the string signature, riding the shipped LEFT word factorization
`disjointWordWindowFactorDataLeft_of_disjointWordWindows` (keyed on the shared boundary WORD, signature-generic) —
a mechanical clone of `SpineValleyCommuteProducerLeft` with the WORD factorization in place of length rigidity:

  * ★ **`StringCommutePairDataLeft` / `stringCommutePairDataLeft_of_disjointWordWindows`** — the moved atoms (record
    updates), the three boundary-path coherences (pure `composePath_assoc`), the tag preservation, and the REVERSED
    flat `SpineAtomSwap (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)` (the constructor always seats
    the spatially-left atom — here the cap — at slot 0, so with the cup at slot 0 the swap fires backwards).
  * ★ **`stringDisjointWindowsLeft_directedOffset_ge_two`** — the sign/`windowGap`: with `capLeft ≤ cupLeft` the
    undirected distance collapses to `cupLeft − capLeft ≥ 2` (the OTHER `natWindowDistance` summand closes with
    `Nat.add_zero`).
  * ★ **`stringCommuteCellDescentStepLeft`** — the COMMUTE producer (left-of): same shape as
    `stringCommuteCellDescentStepRight` but `offsetLe : capLeft ≤ cupLeft`, assembling via
    `stringCellDescentResult_ofCommutePrefixSwapLeft` (the reversed-swap builder).

## What this does NOT close (gates stay `false`)

With both window directions closed, the COMMUTE half of the string oracle is complete.  The STRAIGHTEN arm and the
oracle wire-up are separate.  So `StringCellDescentStepOracle` stays UN-inhabited and
`fxString_hasAdjointTripleCompleteness` stays `false`.

Raw Lean 4 + Init; the factorization is the shipped LEFT word factorization Type-valued, the coherences are
`composePath_assoc`, the sign is truncated-subtraction `Nat` bookkeeping, the producer chains the generic
transposed `next` into the reversed-swap string COMMUTE builder.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Re-rolled `Nat` helpers (propext-free) -/

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free). -/
private theorem natAddSubCancelLeftStringCommuteLeft : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftStringCommuteLeft base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free). -/
private theorem natSubAddRightStringCommuteLeft : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightStringCommuteLeft base tail

/-- `a ≤ b → a - b = 0` (propext-free). -/
private theorem natSubEqZeroOfLeStringCommuteLeft {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller - larger = 0 := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq]
  exact natSubAddRightStringCommuteLeft smaller gap

/-- `a ≤ b → a + (b - a) = b` (propext-free). -/
private theorem natAddSubCancelStringCommuteLeft {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller + (larger - smaller) = larger := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq, natAddSubCancelLeftStringCommuteLeft smaller gap]

/-! ## The mirrored combined pair data: moved atoms, coherences, tags, and the reversed flat swap -/

/-- The left-of COMMUTE pair data bundle — Type-valued because the moved atoms are DATA feeding the transposed
`next`: the two moved atoms, their cup/cap tag preservation, the three boundary-path coherences, and the REVERSED
flat `SpineAtomSwap` (moved pair as source, original pair as target), all coherent for a single inert path.  The
three-generator twin of `CommutePairDataLeft`. -/
structure StringCommutePairDataLeft {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) : Type where
  /-- The moved cap (its right context re-threaded through the cup's consumed window). -/
  capMoved : SpineAtom adjointTripleModeSignature overallSource overallTarget
  /-- The moved cup (its left context re-threaded through the cap's produced window). -/
  cupMoved : SpineAtom adjointTripleModeSignature overallSource overallTarget
  /-- The moved cap keeps the cap tag. -/
  tagCapMoved : capMoved.isCupAtom = capAtom.isCupAtom
  /-- The moved cup keeps the cup tag. -/
  tagCupMoved : cupMoved.isCupAtom = cupAtom.isCupAtom
  /-- The moved cap re-anchors at the pair's source. -/
  coherenceMovedSource : atomFrameSource capMoved = atomFrameSource cupAtom
  /-- The moved atoms chain. -/
  coherenceMovedMid : atomFrameSource cupMoved = atomFrameTarget capMoved
  /-- The moved cup lands at the pair's target. -/
  coherenceMovedTarget : atomFrameTarget cupMoved = atomFrameTarget capAtom
  /-- The REVERSED flat transposition of the located pair (moved pair → original pair). -/
  swapStep : SpineAtomSwap adjointTripleModeSignature
    (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)

/-- ★ **The left-of COMMUTE pair data from the mirrored WORD factorization.**  From ONE inert-path word
factorization (`disjointWordWindowFactorDataLeft_of_disjointWordWindows`) it names the moved atoms (record updates),
proves the three boundary-path coherences (pure `composePath_assoc`), the tag preservation, and fires the REVERSED
flat `SpineAtomSwap` — all sharing the same inert path.  The three-generator twin of
`adjunctionCommutePairDataLeft_of_disjointWindows`, taking the shared word directly instead of a length. -/
def stringCommutePairDataLeft_of_disjointWordWindows
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (sharedWord :
      composePath cupAtom.leftContext (composePath cupAtom.generatorCod cupAtom.rightContext)
        = composePath capAtom.leftContext (composePath capAtom.generatorDom capAtom.rightContext))
    (windowGap : Nat)
    (windowsDisjoint :
      capAtom.leftContext.length + capAtom.generatorDom.length + windowGap
        = cupAtom.leftContext.length) :
    StringCommutePairDataLeft cupAtom capAtom rest := by
  obtain ⟨inertPath, leftFactor, rightFactor⟩ :=
    disjointWordWindowFactorDataLeft_of_disjointWordWindows cupAtom capAtom sharedWord windowGap
      windowsDisjoint
  refine ⟨{ capAtom with rightContext :=
              composePath (composePath inertPath cupAtom.generatorDom) cupAtom.rightContext },
          { cupAtom with leftContext :=
              composePath (composePath capAtom.leftContext capAtom.generatorCod) inertPath },
          rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show composePath capAtom.leftContext
        (composePath capAtom.generatorDom
          (composePath (composePath inertPath cupAtom.generatorDom) cupAtom.rightContext))
      = composePath cupAtom.leftContext
        (composePath cupAtom.generatorDom cupAtom.rightContext)
    rw [leftFactor,
        composePath_assoc inertPath cupAtom.generatorDom cupAtom.rightContext,
        composePath_assoc (composePath capAtom.leftContext capAtom.generatorDom) inertPath
          (composePath cupAtom.generatorDom cupAtom.rightContext),
        composePath_assoc capAtom.leftContext capAtom.generatorDom
          (composePath inertPath (composePath cupAtom.generatorDom cupAtom.rightContext))]
  · show composePath
        (composePath (composePath capAtom.leftContext capAtom.generatorCod) inertPath)
        (composePath cupAtom.generatorDom cupAtom.rightContext)
      = composePath capAtom.leftContext
        (composePath capAtom.generatorCod
          (composePath (composePath inertPath cupAtom.generatorDom) cupAtom.rightContext))
    rw [composePath_assoc inertPath cupAtom.generatorDom cupAtom.rightContext,
        composePath_assoc (composePath capAtom.leftContext capAtom.generatorCod) inertPath
          (composePath cupAtom.generatorDom cupAtom.rightContext),
        composePath_assoc capAtom.leftContext capAtom.generatorCod
          (composePath inertPath (composePath cupAtom.generatorDom cupAtom.rightContext))]
  · show composePath
        (composePath (composePath capAtom.leftContext capAtom.generatorCod) inertPath)
        (composePath cupAtom.generatorCod cupAtom.rightContext)
      = composePath capAtom.leftContext
        (composePath capAtom.generatorCod capAtom.rightContext)
    rw [rightFactor,
        composePath_assoc (composePath capAtom.leftContext capAtom.generatorCod) inertPath
          (composePath cupAtom.generatorCod cupAtom.rightContext),
        composePath_assoc capAtom.leftContext capAtom.generatorCod
          (composePath inertPath (composePath cupAtom.generatorCod cupAtom.rightContext))]
  · obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
      rightContextA⟩ := cupAtom
    obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
      rightContextB⟩ := capAtom
    dsimp only at leftFactor rightFactor ⊢
    rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorCodA rightContextA]
    exact SpineAtomSwap.swap generatorB generatorA leftContextB inertPath rightContextA rest

/-! ## The sign + `windowGap` derivation from the classifier verdict (mirrored) -/

/-- ★ **The `disjointWindows` verdict bounds the directed offset (mirrored).**  With `capLeft ≤ cupLeft` the
undirected `natWindowDistance ≥ 2` collapses to the directed `cupLeft − capLeft`, so `cupLeft − capLeft ≥ 2`.  The
mirror of `stringDisjointWindows_directedOffset_ge_two`: the OTHER `natWindowDistance` summand is closed by
`Nat.add_zero`. -/
theorem stringDisjointWindowsLeft_directedOffset_ge_two
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (offsetLe : capAtom.leftContext.length ≤ cupAtom.leftContext.length)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.disjointWindows) :
    2 ≤ cupAtom.leftContext.length - capAtom.leftContext.length := by
  have distanceGeTwo :
      2 ≤ natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length := by
    cases distanceCase :
        natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length with
    | zero =>
        rw [classifyAdjacentAtoms, classifyAdjacentCupCap, distanceCase] at verdict
        exact AdjacentCupCapKind.noConfusion verdict
    | succ predDistance =>
        cases predDistance with
        | zero =>
            rw [classifyAdjacentAtoms, classifyAdjacentCupCap, distanceCase] at verdict
            exact AdjacentCupCapKind.noConfusion verdict
        | succ prePredDistance =>
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le prePredDistance))
  have distanceEq :
      natWindowDistance cupAtom.leftContext.length capAtom.leftContext.length
        = cupAtom.leftContext.length - capAtom.leftContext.length := by
    dsimp only [natWindowDistance]
    rw [natSubEqZeroOfLeStringCommuteLeft offsetLe, Nat.add_zero]
  rw [distanceEq] at distanceGeTwo
  exact distanceGeTwo

/-! ## The COMMUTE producer (left-of window offset) -/

/-- ★ **The COMMUTE producer (left-of).**  From the located split, the cup/cap tags, and the `disjointWindows`
verdict with `capLeft ≤ cupLeft`, produce the `StringCellDescentResult cell`: derive the pair's boundary path
coherence from `cell`'s own realized chain, read it as the shared boundary WORD, derive the `windowGap` from the
verdict (a genuine cap's consumed window is width 2, so `windowGap := cupLeft − (capLeft + capDom.length)`), the pair
data (moved atoms + coherences + reversed flat swap) from `stringCommutePairDataLeft_of_disjointWordWindows`, the
generic transposed `next`, and assemble via `stringCellDescentResult_ofCommutePrefixSwapLeft`.  A
`StringCellDescentResult` producer, standalone. -/
def stringCommuteCellDescentStepLeft
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (offsetLe : capAtom.leftContext.length ≤ cupAtom.leftContext.length)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.disjointWindows) :
    StringCellDescentResult cell :=
  let sharedWord :
      composePath cupAtom.leftContext (composePath cupAtom.generatorCod cupAtom.rightContext)
        = composePath capAtom.leftContext (composePath capAtom.generatorDom capAtom.rightContext) :=
    framedChain_pairPathCoherence rest prefixCells
      (FramedSpineChain.castAtoms sourceSplit cell.cellChain)
  let offsetGeTwo : 2 ≤ cupAtom.leftContext.length - capAtom.leftContext.length :=
    stringDisjointWindowsLeft_directedOffset_ge_two cupAtom capAtom offsetLe verdict
  let combinedLe :
      capAtom.leftContext.length + capAtom.generatorDom.length ≤ cupAtom.leftContext.length := by
    rw [stringCapAtom_generatorDom_length_two capAtom isCapCap]
    have shifted := Nat.add_le_add_left offsetGeTwo capAtom.leftContext.length
    rw [natAddSubCancelStringCommuteLeft offsetLe] at shifted
    exact shifted
  let windowsDisjoint :
      capAtom.leftContext.length + capAtom.generatorDom.length
          + (cupAtom.leftContext.length
              - (capAtom.leftContext.length + capAtom.generatorDom.length))
        = cupAtom.leftContext.length :=
    natAddSubCancelStringCommuteLeft combinedLe
  let pairData := stringCommutePairDataLeft_of_disjointWordWindows cupAtom capAtom rest sharedWord
    (cupAtom.leftContext.length - (capAtom.leftContext.length + capAtom.generatorDom.length))
    windowsDisjoint
  stringCellDescentResult_ofCommutePrefixSwapLeft prefixCells rest isCupCup isCapCap
    (pairData.tagCapMoved.trans isCapCap) (pairData.tagCupMoved.trans isCupCup) sourceSplit
    (commuteNextCell_spine cell prefixCells rest pairData.coherenceMovedSource
      pairData.coherenceMovedMid pairData.coherenceMovedTarget sourceSplit)
    pairData.swapStep

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE producer half is CLOSED for BOTH window offsets at the three-generator seed.**
With the right-of `stringCommuteCellDescentStepRight` and this left-of `stringCommuteCellDescentStepLeft`, a located
cup·cap split with a `disjointWindows` verdict produces a `StringCellDescentResult cell` regardless of which atom's
window sits left — the symmetric classifier verdict feeds both, `Nat.le_total` on the two left-context widths
selects the direction.  The LEFT pair data rides the shipped LEFT word factorization
`disjointWordWindowFactorDataLeft_of_disjointWordWindows`, the reversed flat swap seats via
`stringCellDescentResult_ofCommutePrefixSwapLeft`.

  What this marker does NOT close: the STRAIGHTEN half of the oracle and the whole oracle wire-up.  So a total
  `StringCellDescentStepOracle` stays UN-inhabited and `fxString_hasAdjointTripleCompleteness` stays `false`.
  `= true`. -/
def fxString_hasStringValleyCommuteProducerLeft : Bool := true

end FX1Poly.Polygraph
