import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteProducer

/-! # mode-3 keystone — Piece I COMMUTE producer, LEFT-of mirror: the second window a gap LEFT of the first

`SpineValleyCommuteProducer` closed the COMMUTE producer for the RIGHT-of window offset
(`cupLeft ≤ capLeft`, the cup's produced window sits left of the cap's consumed window).  The classifier's
`disjointWindows` verdict is SYMMETRIC (`natWindowDistance` is `(a − b) + (b − a)`), so the same verdict also
covers the LEFT-of offset (`capLeft ≤ cupLeft`, the cap's window left of the cup's).  This file mirrors the
right-of producer for that direction, every declaration a mechanical clone of a shipped right-of decl with the
left arithmetic — the hard geometry (the mirrored Prop factorization
`adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows` and the mirrored flat swap
`adjunctionSpineAtomSwapLeft_of_disjointWindows`) is already shipped:

  * ★ **`DisjointWindowFactorDataLeft` / `adjunctionContextsFactorDataLeft_of_disjointWindows`** — the Type-valued
    mirror of the shipped Prop left factorization, keeping the inert path as DATA so the moved atoms (and hence
    brick 1's `next`) are usable in Type.  The cup's left context factors through the cap's consumed window then
    the inert zone; the cap's right context factors as the inert zone then the cup's produced window.
  * ★ **`CommutePairDataLeft` / `adjunctionCommutePairDataLeft_of_disjointWindows`** — the moved atoms (record
    updates), the three boundary-path coherences brick 1 consumes (pure `composePath_assoc`), the tag
    preservation, and the REVERSED flat `SpineAtomSwap (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)`
    (the constructor always seats the spatially-left atom — here the cap — at list position 0, so with the cup at
    position 0 the swap fires backwards).
  * ★ **`disjointWindowsLeft_directedOffset_ge_two`** — the sign/`windowGap`: with `capLeft ≤ cupLeft` the
    undirected distance collapses to `cupLeft − capLeft ≥ 2` (the mirror closes the OTHER `natWindowDistance`
    summand with `Nat.add_zero`).
  * ★ **`cellDescentResult_ofCommutePrefixSwapLeft`** — the COMMUTE builder from the REVERSED swap: lift the
    reversed flat swap to `SaturatedTwoCellConv next cell` (`commutePrefixSwapCellLift`), take `.symm`, feed
    `cellDescentResult_ofCommuteStep`.
  * ★ **`commuteCellDescentStepLeft`** — the COMMUTE producer (left-of): same shape as
    `commuteCellDescentStepRight` but `offsetLe : capLeft ≤ cupLeft`.  The other window direction of the COMMUTE
    dispatch, standalone.

## What this does NOT close (gates stay `false`)

With both window directions closed, the COMMUTE half of the oracle is complete.  The STRAIGHTEN half
(partner-collapse, coupled to Piece II) is NOT here.  So a total `CellDescentStepOracle` is still NOT inhabited:
`MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.

Raw Lean 4 + Init; the factorization is the shipped left rigidity derivation Type-valued, the coherences are
`composePath_assoc`, the sign is truncated-subtraction `Nat` bookkeeping, the producer chains brick 1 into the
reversed-swap COMMUTE builder.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## Re-rolled `Nat` helpers (the producer's copies are file-private) -/

/-- Left-cancellation for `Nat` addition, hand-rolled (core `Nat.add_left_cancel` is propext-tainted). -/
private theorem natAddLeftCancelLeft (base : Nat) :
    ∀ {leftValue rightValue : Nat},
      base + leftValue = base + rightValue → leftValue = rightValue := by
  induction base with
  | zero =>
      intro leftValue rightValue sumsEqual
      rw [Nat.zero_add, Nat.zero_add] at sumsEqual
      exact sumsEqual
  | succ basePred inductionHypothesis =>
      intro leftValue rightValue sumsEqual
      rw [Nat.succ_add, Nat.succ_add] at sumsEqual
      exact inductionHypothesis (Nat.succ.inj sumsEqual)

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free). -/
private theorem natAddSubCancelLeftCleanLeft : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftCleanLeft base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free). -/
private theorem natSubAddRightCleanLeft : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightCleanLeft base tail

/-- `a ≤ b → a - b = 0` (propext-free; core `Nat.sub_eq_zero_of_le` leaks propext). -/
private theorem natSubEqZeroOfLeCleanLeft {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller - larger = 0 := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq]
  exact natSubAddRightCleanLeft smaller gap

/-- `a ≤ b → a + (b - a) = b` (propext-free; core `Nat.add_sub_cancel'` leaks propext). -/
private theorem natAddSubCancelCleanLeft {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller + (larger - smaller) = larger := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq, natAddSubCancelLeftCleanLeft smaller gap]

/-! ## The mirrored disjoint-window factorization, Type-valued -/

/-- The left-of disjoint-window factorization data — Type-valued so the inert middle path is DATA the moved
atoms (and hence brick 1's `next`) depend on.  Here the SECOND atom (the cap) sits a gap LEFT of the first
(the cup): the cup's left context factors through the cap's consumed window then the inert zone, and the cap's
right context factors as the inert zone then the cup's produced window. -/
structure DisjointWindowFactorDataLeft {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget) : Type where
  /-- The inert middle zone separating the two windows. -/
  inertPath : ModalityPath adjunctionModeSignature.graph capAtom.rightMidMode cupAtom.leftMidMode
  /-- The cup's left context factors through the cap's consumed window then the inert zone. -/
  leftFactor : cupAtom.leftContext
    = composePath (composePath capAtom.leftContext capAtom.generatorDom) inertPath
  /-- The cap's right context factors as the inert zone then the cup's produced window. -/
  rightFactor : capAtom.rightContext
    = composePath inertPath (composePath cupAtom.generatorCod cupAtom.rightContext)

/-- ★ **The mirrored disjoint-window factorization, Type-valued.**  A constructive mirror of the shipped Prop
factorization `adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows`, keeping the inert path (the
`splitPathAt` prefix of the cup's left context) as DATA so the moved atoms it defines are usable in Type.  Every
pin lands by seed rigidity — parallel adjunction paths of equal length are equal. -/
def adjunctionContextsFactorDataLeft_of_disjointWindows
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (boundariesChain : capAtom.domBoundaryLength = cupAtom.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      capAtom.leftContext.length + capAtom.generatorDom.length + windowGap
        = cupAtom.leftContext.length) :
    DisjointWindowFactorDataLeft cupAtom capAtom := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := cupAtom
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := capAtom
  dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength] at boundariesChain
  dsimp only at windowsDisjoint ⊢
  rw [← windowsDisjoint] at boundariesChain
  rw [Nat.add_assoc (leftContextB.length + generatorDomB.length + windowGap)
        generatorCodA.length rightContextA.length,
      Nat.add_assoc (leftContextB.length + generatorDomB.length) windowGap
        (generatorCodA.length + rightContextA.length)] at boundariesChain
  have windowPlusGap := natAddLeftCancelLeft _ boundariesChain
  have splitInRange : leftContextB.length + generatorDomB.length ≤ leftContextA.length :=
    windowsDisjoint ▸ Nat.le_add_right (leftContextB.length + generatorDomB.length) windowGap
  obtain ⟨splitMiddle, windowPrefix, inertPath, splitComposes, prefixLengthMatches⟩ :=
    splitPathAt leftContextA (leftContextB.length + generatorDomB.length) splitInRange
  have composedLengths := congrArg ModalityPath.length splitComposes
  rw [ModalityPath.length_composePath, prefixLengthMatches, ← windowsDisjoint]
    at composedLengths
  have inertLength := natAddLeftCancelLeft _ composedLengths
  have prefixCandidateLength :
      (composePath leftContextB generatorDomB).length = windowPrefix.length := by
    rw [ModalityPath.length_composePath, prefixLengthMatches]
  cases adjunctionPathTargets_eq_of_length_eq (composePath leftContextB generatorDomB)
    windowPrefix prefixCandidateLength
  have windowPrefixEquation := adjunctionPath_eq_of_length_eq
    (composePath leftContextB generatorDomB) windowPrefix prefixCandidateLength
  have rightCandidateLength :
      (composePath inertPath (composePath generatorCodA rightContextA)).length
        = rightContextB.length := by
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength]
    exact windowPlusGap.symm
  have rightContextEquation := adjunctionPath_eq_of_length_eq
    (composePath inertPath (composePath generatorCodA rightContextA)) rightContextB
    rightCandidateLength
  refine ⟨inertPath, ?_, rightContextEquation.symm⟩
  exact splitComposes.symm.trans
    (congrArg (fun prefixPath => composePath prefixPath inertPath) windowPrefixEquation.symm)

/-! ## The combined pair data: moved atoms, coherences, tags, and the reversed flat swap -/

/-- The left-of COMMUTE pair data bundle — Type-valued because the moved atoms are DATA feeding brick 1's `next`:
the two moved atoms, their cup/cap tag preservation, the three boundary-path coherences brick 1 consumes, and the
REVERSED flat `SpineAtomSwap` (moved pair as source, original pair as target), all coherent for a single inert
path. -/
structure CommutePairDataLeft {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) : Type where
  /-- The moved cap (its right context re-threaded through the cup's consumed window). -/
  capMoved : SpineAtom adjunctionModeSignature overallSource overallTarget
  /-- The moved cup (its left context re-threaded through the cap's produced window). -/
  cupMoved : SpineAtom adjunctionModeSignature overallSource overallTarget
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
  swapStep : SpineAtomSwap adjunctionModeSignature
    (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)

/-- ★ **The left-of COMMUTE pair data from the mirrored factorization.**  From ONE inert-path factorization it
names the moved atoms (record updates of the originals), proves the three boundary-path coherences brick 1
consumes (pure `composePath_assoc` over the factorization equalities), the tag preservation, and fires the
REVERSED flat `SpineAtomSwap` — all sharing the same inert path so brick 1's `next` and the swap agree on the
moved atoms. -/
def adjunctionCommutePairDataLeft_of_disjointWindows
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (boundariesChain : capAtom.domBoundaryLength = cupAtom.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      capAtom.leftContext.length + capAtom.generatorDom.length + windowGap
        = cupAtom.leftContext.length) :
    CommutePairDataLeft cupAtom capAtom rest := by
  obtain ⟨inertPath, leftFactor, rightFactor⟩ :=
    adjunctionContextsFactorDataLeft_of_disjointWindows cupAtom capAtom boundariesChain
      windowGap windowsDisjoint
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

/-- ★ **The `disjointWindows` verdict bounds the directed offset (mirrored).**  A `disjointWindows`
classification means the undirected `natWindowDistance` is `≥ 2`; with `capLeft ≤ cupLeft` the truncated distance
collapses to the directed `cupLeft − capLeft`, so `cupLeft − capLeft ≥ 2`.  The mirror of
`disjointWindows_directedOffset_ge_two`: the SAME symmetric verdict feeds it, and the OTHER `natWindowDistance`
summand is closed by `Nat.add_zero`. -/
theorem disjointWindowsLeft_directedOffset_ge_two
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
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
    rw [natSubEqZeroOfLeCleanLeft offsetLe, Nat.add_zero]
  rw [distanceEq] at distanceGeTwo
  exact distanceGeTwo

/-! ## The COMMUTE builder from the reversed swap -/

/-- ★ **The COMMUTE `CellDescentResult` builder from the REVERSED flat swap.**  The left-of analogue of
`cellDescentResult_ofCommutePrefixSwap`: given a `next` cell whose spine is `cell`'s with the located cup·cap
pair transposed to a slot-preserving cap·cup, and the REVERSED flat located
`SpineAtomSwap (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)`, package a `CellDescentResult cell`.
The reversed swap lifts to `SaturatedTwoCellConv next cell` (`commutePrefixSwapCellLift` on the moved→original
swap); `.symm` flips it to `cell ≈ next`; `cellDescentResult_ofCommuteStep` discharges `disorderDrops`. -/
def cellDescentResult_ofCommutePrefixSwapLeft {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ capMoved :: cupMoved :: rest)
    (swapStep : SpineAtomSwap adjunctionModeSignature
      (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)) :
    CellDescentResult cell :=
  cellDescentResult_ofCommuteStep
    (SaturatedTwoCellConv.symm
      (commutePrefixSwapCellLift next cell prefixCells targetSplit sourceSplit swapStep))
    prefixCells rest isCupCup isCapCap isCapMoved isCupMoved sourceSplit targetSplit

/-! ## The COMMUTE producer (left-of window offset) -/

/-- ★ **The COMMUTE producer (left-of).**  From the located split, the cup/cap tags, and the `disjointWindows`
verdict with `capLeft ≤ cupLeft`, produce the `CellDescentResult cell`: derive the boundary chainedness from
`cell`'s own realized chain (`framedChain_pairPathCoherence`), the `windowGap` from the verdict (a genuine cap's
consumed window is width 2, so `windowGap := cupLeft − (capLeft + capDom.length)`), the pair data (moved atoms +
coherences + reversed flat swap) from `adjunctionCommutePairDataLeft_of_disjointWindows`, brick 1's transposed
`next`, and assemble via `cellDescentResult_ofCommutePrefixSwapLeft`.  The left-of window direction of the oracle
dispatch's COMMUTE case, standalone. -/
def commuteCellDescentStepLeft
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (offsetLe : capAtom.leftContext.length ≤ cupAtom.leftContext.length)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.disjointWindows) :
    CellDescentResult cell :=
  let pathCoherence : atomFrameTarget cupAtom = atomFrameSource capAtom :=
    framedChain_pairPathCoherence rest prefixCells
      (FramedSpineChain.castAtoms sourceSplit cell.cellChain)
  let boundariesChain : capAtom.domBoundaryLength = cupAtom.codBoundaryLength := by
    have lengthEq := congrArg ModalityPath.length pathCoherence
    dsimp only [atomFrameTarget, atomFrameSource] at lengthEq
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
        ModalityPath.length_composePath, ModalityPath.length_composePath] at lengthEq
    dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength]
    rw [Nat.add_assoc capAtom.leftContext.length, Nat.add_assoc cupAtom.leftContext.length]
    exact lengthEq.symm
  let offsetGeTwo : 2 ≤ cupAtom.leftContext.length - capAtom.leftContext.length :=
    disjointWindowsLeft_directedOffset_ge_two cupAtom capAtom offsetLe verdict
  let combinedLe :
      capAtom.leftContext.length + capAtom.generatorDom.length ≤ cupAtom.leftContext.length := by
    rw [capAtom_generatorDom_length_two capAtom isCapCap]
    have shifted := Nat.add_le_add_left offsetGeTwo capAtom.leftContext.length
    rw [natAddSubCancelCleanLeft offsetLe] at shifted
    exact shifted
  let windowsDisjoint :
      capAtom.leftContext.length + capAtom.generatorDom.length
          + (cupAtom.leftContext.length
              - (capAtom.leftContext.length + capAtom.generatorDom.length))
        = cupAtom.leftContext.length :=
    natAddSubCancelCleanLeft combinedLe
  let pairData := adjunctionCommutePairDataLeft_of_disjointWindows cupAtom capAtom rest boundariesChain
    (cupAtom.leftContext.length - (capAtom.leftContext.length + capAtom.generatorDom.length))
    windowsDisjoint
  cellDescentResult_ofCommutePrefixSwapLeft prefixCells rest isCupCup isCapCap
    (pairData.tagCapMoved.trans isCapCap) (pairData.tagCupMoved.trans isCupCup) sourceSplit
    (commuteNextCell_spine cell prefixCells rest pairData.coherenceMovedSource
      pairData.coherenceMovedMid pairData.coherenceMovedTarget sourceSplit)
    pairData.swapStep

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE producer half is CLOSED for BOTH window offsets.**  With the right-of
`commuteCellDescentStepRight` and this left-of `commuteCellDescentStepLeft`, a located cup·cap split with a
`disjointWindows` verdict produces a `CellDescentResult cell` regardless of which atom's window sits left — the
symmetric classifier verdict feeds both, `Nat.le_total` on the two left-context widths selects the direction.

  What this marker does NOT close: the STRAIGHTEN half of the oracle (partner-collapse, coupled to Piece II).  A
  total `CellDescentStepOracle` needs the STRAIGHTEN input, so it stays UN-inhabited:
  `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyCommuteProducerLeft : Bool := true

end FX1Poly.Polygraph
