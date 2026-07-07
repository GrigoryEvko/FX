import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteNext
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteLift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyClassifier
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations

/-! # mode-3 keystone — Piece I COMMUTE producer, brick 2+3: the flat swap from the classifier + the producer

Brick 1 (`SpineValleyCommuteNext`) shipped the transposed `next` GIVEN the three boundary-path coherences and
the flat `SpineAtomSwap`.  This file supplies both AT THE ADJUNCTION from the classifier's `disjointWindows`
verdict, and assembles the whole COMMUTE-case `CellDescentResult`:

  * ★ **`cupAtom_generatorCod_length_two` / `capAtom_generatorDom_length_two`** — the seed cup's target arity
    (`generatorCod.length = 2`) and cap's source arity (`generatorDom.length = 2`), read off the cup/cap tag via
    the shipped `adjunctionSpineAtom_isCupOrCap`.  These fix the `windowGap` factorization: for a genuine cup the
    produced window is width 2, so the classifier's ≥2 boundary is faithful.
  * ★ **`adjunctionCommutePairData_of_disjointWindows`** — the combined bundle: from ONE factorization
    (`adjunctionSpineAtom_contextsFactor_of_disjointWindows`) it names the moved atoms (record updates), proves
    the three boundary-path coherences (pure `composePath_assoc` over `leftFactor` / `rightFactor`), the tag
    preservation (`isCupAtom` reads only `generatorDom.length`, untouched by the context re-threading), and fires
    the flat `SpineAtomSwap` — all sharing the SAME inert path.
  * ★ **`disjointWindows_directedOffset_ge_two`** — the sign + `windowGap` derivation from the verdict: with
    `cupLeft ≤ capLeft` the undirected `natWindowDistance` collapses to `capLeft − cupLeft ≥ 2`, so
    `windowGap := capLeft − (cupLeft + cupCod.length)` gives `cupLeft + cupCod.length + windowGap = capLeft`
    directly (a genuine cup's `cupCod.length = 2`).  Clean `Nat` — hand-rolled `natAddSubCancelClean` /
    `natSubEqZeroOfLeClean` (core `Nat.add_sub_cancel'` / `Nat.sub_eq_zero_of_le` leak propext), no `omega`.
  * ★ **`commuteCellDescentStepRight`** — the COMMUTE producer (right-of): from the located split, the cup/cap
    tags, the boundary chainedness (derived from `cell`'s own chain, `framedChain_pairPathCoherence`), and the
    `disjointWindows` verdict with `cupLeft ≤ capLeft`, produce the `CellDescentResult cell` via
    `cellDescentResult_ofCommutePrefixSwap` fed brick 1's `next` and this brick's swap.  The COMMUTE case of the
    oracle dispatch, standalone.

## What this does NOT close (gates stay `false`)

This closes the COMMUTE producer for the right-of window offset (`cupLeft ≤ capLeft`).  The left-of mirror
(`adjunctionSpineAtomSwapLeft_of_disjointWindows`, moved→original orientation) and the STRAIGHTEN half
(partner-collapse, coupled to Piece II) are NOT here.  So a total `CellDescentStepOracle` is NOT inhabited:
`MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.

Raw Lean 4 + Init; the arity is `adjunctionSpineAtom_isCupOrCap` casing, the coherences are `composePath_assoc`
over the factorization, the sign is truncated-subtraction `Nat` bookkeeping, the producer chains brick 1 into
the COMMUTE builder.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The seed cup / cap generator arities from the tag -/

/-- A genuine cup atom has source arity `0` — its `generatorDom` is empty, read off the cup tag. -/
theorem cupAtom_generatorDom_length_zero
    {overallSource overallTarget : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : atom.isCupAtom = true) : atom.generatorDom.length = 0 := by
  cases lengthCase : atom.generatorDom.length with
  | zero => rfl
  | succ predLength =>
      dsimp only [SpineAtom.isCupAtom] at isCup
      rw [lengthCase] at isCup
      exact Bool.noConfusion isCup

/-- ★ A genuine cup atom has target arity `2` — the unit creates `left · right`.  Read off the cup tag: the
disjunction `adjunctionSpineAtom_isCupOrCap` has its cap branch (`generatorDom.length = 2`) excluded by the cup's
empty source. -/
theorem cupAtom_generatorCod_length_two
    {overallSource overallTarget : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : atom.isCupAtom = true) : atom.generatorCod.length = 2 := by
  have domZero := cupAtom_generatorDom_length_zero atom isCup
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupBranch => exact cupBranch.2
  | inr capBranch =>
      rw [domZero] at capBranch
      exact Nat.noConfusion capBranch.1

/-- ★ A genuine cap atom has source arity `2` — the counit consumes `right · left`.  Read off the cap tag: the
cup branch (`generatorDom.length = 0`) is excluded by the cap tag. -/
theorem capAtom_generatorDom_length_two
    {overallSource overallTarget : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCap : atom.isCupAtom = false) : atom.generatorDom.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupBranch =>
      dsimp only [SpineAtom.isCupAtom] at isCap
      rw [cupBranch.1] at isCap
      exact Bool.noConfusion isCap
  | inr capBranch => exact capBranch.1

/-! ## The disjoint-window factorization, Type-valued (the inert path as DATA) -/

/-- Left-cancellation for `Nat` addition, hand-rolled (core `Nat.add_left_cancel` is propext-tainted). -/
private theorem natAddLeftCancel (base : Nat) :
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

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free; core `Nat.add_sub_cancel_left`
leaks propext). -/
private theorem natAddSubCancelLeftClean : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftClean base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free). -/
private theorem natSubAddRightClean : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightClean base tail

/-- `a ≤ b → a - b = 0` (propext-free; core `Nat.sub_eq_zero_of_le` leaks propext). -/
private theorem natSubEqZeroOfLeClean {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller - larger = 0 := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq]
  exact natSubAddRightClean smaller gap

/-- `a ≤ b → a + (b - a) = b` (propext-free; core `Nat.add_sub_cancel'` leaks propext). -/
private theorem natAddSubCancelClean {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller + (larger - smaller) = larger := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq, natAddSubCancelLeftClean smaller gap]

/-- The disjoint-window factorization data — Type-valued so the inert middle path is DATA the moved atoms
(and hence brick 1's `next`) depend on: the inert path plus the two context decompositions. -/
structure DisjointWindowFactorData {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget) : Type where
  /-- The inert middle zone separating the two windows. -/
  inertPath : ModalityPath adjunctionModeSignature.graph cupAtom.rightMidMode capAtom.leftMidMode
  /-- The cap's left context factors through the cup's produced window then the inert zone. -/
  leftFactor : capAtom.leftContext
    = composePath (composePath cupAtom.leftContext cupAtom.generatorCod) inertPath
  /-- The cup's right context factors as the inert zone then the cap's consumed window. -/
  rightFactor : cupAtom.rightContext
    = composePath inertPath (composePath capAtom.generatorDom capAtom.rightContext)

/-- ★ **The disjoint-window factorization, Type-valued.**  A constructive mirror of the shipped Prop factorization
`adjunctionSpineAtom_contextsFactor_of_disjointWindows`, keeping the inert path (the `splitPathAt` prefix of the
cup's right context) as DATA so the moved atoms it defines are usable in Type.  Every pin lands by seed rigidity —
parallel adjunction paths of equal length are equal. -/
def adjunctionContextsFactorData_of_disjointWindows
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (boundariesChain : capAtom.domBoundaryLength = cupAtom.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      cupAtom.leftContext.length + cupAtom.generatorCod.length + windowGap
        = capAtom.leftContext.length) :
    DisjointWindowFactorData cupAtom capAtom := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := cupAtom
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := capAtom
  dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength] at boundariesChain
  dsimp only at windowsDisjoint
  rw [← windowsDisjoint] at boundariesChain
  rw [Nat.add_assoc (leftContextA.length + generatorCodA.length + windowGap)
        generatorDomB.length rightContextB.length,
      Nat.add_assoc (leftContextA.length + generatorCodA.length) windowGap
        (generatorDomB.length + rightContextB.length)] at boundariesChain
  have gapPlusWindow := natAddLeftCancel _ boundariesChain
  have gapInRange : windowGap ≤ rightContextA.length :=
    gapPlusWindow ▸ Nat.le_add_right windowGap (generatorDomB.length + rightContextB.length)
  obtain ⟨inertMiddle, inertPrefix, inertSuffix, inertComposes, inertLength⟩ :=
    splitPathAt rightContextA windowGap gapInRange
  have inertSuffixLength : inertSuffix.length
      = generatorDomB.length + rightContextB.length := by
    have composedLengths := congrArg ModalityPath.length inertComposes
    rw [ModalityPath.length_composePath, inertLength, ← gapPlusWindow] at composedLengths
    exact natAddLeftCancel windowGap composedLengths
  have domInRange : generatorDomB.length ≤ inertSuffix.length :=
    inertSuffixLength.symm ▸ Nat.le_add_right generatorDomB.length rightContextB.length
  obtain ⟨genMiddle, genPrefix, genSuffix, genComposes, genLength⟩ :=
    splitPathAt inertSuffix generatorDomB.length domInRange
  have leftCandidateLength :
      (composePath (composePath leftContextA generatorCodA) inertPrefix).length
        = leftContextB.length := by
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength]
    exact windowsDisjoint
  cases adjunctionPathTargets_eq_of_length_eq
    (composePath (composePath leftContextA generatorCodA) inertPrefix) leftContextB
    leftCandidateLength
  have leftContextEquation := adjunctionPath_eq_of_length_eq
    (composePath (composePath leftContextA generatorCodA) inertPrefix) leftContextB
    leftCandidateLength
  cases adjunctionPathTargets_eq_of_length_eq genPrefix generatorDomB genLength
  have genPrefixEquation := adjunctionPath_eq_of_length_eq genPrefix generatorDomB genLength
  have genSuffixLength : genSuffix.length = rightContextB.length := by
    have composedLengths := congrArg ModalityPath.length genComposes
    rw [ModalityPath.length_composePath, genLength, inertSuffixLength] at composedLengths
    exact natAddLeftCancel generatorDomB.length composedLengths
  have genSuffixEquation := adjunctionPath_eq_of_length_eq genSuffix rightContextB
    genSuffixLength
  refine ⟨inertPrefix, leftContextEquation.symm, ?_⟩
  rw [← inertComposes, ← genComposes, genPrefixEquation, genSuffixEquation]

/-! ## The combined pair data: moved atoms, coherences, tags, and the flat swap -/

/-- The COMMUTE pair data bundle — Type-valued because the moved atoms are DATA feeding brick 1's `next`: the two
moved atoms, their cup/cap tag preservation, the three boundary-path coherences brick 1 consumes, and the flat
`SpineAtomSwap`, all coherent for a single inert path. -/
structure CommutePairData {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) : Type where
  /-- The moved cap (its left context re-threaded through the cup's produced window). -/
  capMoved : SpineAtom adjunctionModeSignature overallSource overallTarget
  /-- The moved cup (its right context re-threaded through the cap's consumed window). -/
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
  /-- The flat transposition of the located pair. -/
  swapStep : SpineAtomSwap adjunctionModeSignature
    (cupAtom :: capAtom :: rest) (capMoved :: cupMoved :: rest)

/-- ★ **The COMMUTE pair data from the disjoint-window factorization.**  From ONE inert-path factorization it
names the moved atoms (record updates of the originals), proves the three boundary-path coherences brick 1
consumes (pure `composePath_assoc` over the factorization equalities), the tag preservation, and fires the flat
`SpineAtomSwap` — all sharing the same inert path so brick 1's `next` and the swap agree on the moved atoms. -/
def adjunctionCommutePairData_of_disjointWindows
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (boundariesChain : capAtom.domBoundaryLength = cupAtom.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      cupAtom.leftContext.length + cupAtom.generatorCod.length + windowGap
        = capAtom.leftContext.length) :
    CommutePairData cupAtom capAtom rest := by
  obtain ⟨inertPath, leftFactor, rightFactor⟩ :=
    adjunctionContextsFactorData_of_disjointWindows cupAtom capAtom boundariesChain
      windowGap windowsDisjoint
  refine ⟨{ capAtom with leftContext :=
              composePath (composePath cupAtom.leftContext cupAtom.generatorDom) inertPath },
          { cupAtom with rightContext :=
              composePath (composePath inertPath capAtom.generatorCod) capAtom.rightContext },
          rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show composePath
        (composePath (composePath cupAtom.leftContext cupAtom.generatorDom) inertPath)
        (composePath capAtom.generatorDom capAtom.rightContext)
      = composePath cupAtom.leftContext
        (composePath cupAtom.generatorDom cupAtom.rightContext)
    rw [rightFactor,
        composePath_assoc (composePath cupAtom.leftContext cupAtom.generatorDom) inertPath
          (composePath capAtom.generatorDom capAtom.rightContext),
        composePath_assoc cupAtom.leftContext cupAtom.generatorDom
          (composePath inertPath (composePath capAtom.generatorDom capAtom.rightContext))]
  · show composePath cupAtom.leftContext
        (composePath cupAtom.generatorDom
          (composePath (composePath inertPath capAtom.generatorCod) capAtom.rightContext))
      = composePath
        (composePath (composePath cupAtom.leftContext cupAtom.generatorDom) inertPath)
        (composePath capAtom.generatorCod capAtom.rightContext)
    rw [composePath_assoc inertPath capAtom.generatorCod capAtom.rightContext,
        composePath_assoc (composePath cupAtom.leftContext cupAtom.generatorDom) inertPath
          (composePath capAtom.generatorCod capAtom.rightContext),
        composePath_assoc cupAtom.leftContext cupAtom.generatorDom
          (composePath inertPath (composePath capAtom.generatorCod capAtom.rightContext))]
  · show composePath cupAtom.leftContext
        (composePath cupAtom.generatorCod
          (composePath (composePath inertPath capAtom.generatorCod) capAtom.rightContext))
      = composePath capAtom.leftContext
        (composePath capAtom.generatorCod capAtom.rightContext)
    rw [leftFactor, composePath_assoc inertPath capAtom.generatorCod capAtom.rightContext,
        composePath_assoc (composePath cupAtom.leftContext cupAtom.generatorCod) inertPath
          (composePath capAtom.generatorCod capAtom.rightContext),
        composePath_assoc cupAtom.leftContext cupAtom.generatorCod
          (composePath inertPath (composePath capAtom.generatorCod capAtom.rightContext))]
  · obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
      rightContextA⟩ := cupAtom
    obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
      rightContextB⟩ := capAtom
    dsimp only at leftFactor rightFactor ⊢
    rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorDomB rightContextB]
    exact SpineAtomSwap.swap generatorA generatorB leftContextA inertPath rightContextB rest

/-! ## The sign + `windowGap` derivation from the classifier verdict -/

/-- ★ **The `disjointWindows` verdict bounds the directed offset.**  A `disjointWindows` classification means the
undirected `natWindowDistance` is `≥ 2`; with `cupLeft ≤ capLeft` the truncated distance collapses to the
directed `capLeft − cupLeft`, so `capLeft − cupLeft ≥ 2`.  This is the arithmetic that a genuine cup's width-2
window needs to slide clear of the cap. -/
theorem disjointWindows_directedOffset_ge_two
    {overallSource overallTarget : AdjunctionMode}
    (cupAtom capAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (offsetLe : cupAtom.leftContext.length ≤ capAtom.leftContext.length)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.disjointWindows) :
    2 ≤ capAtom.leftContext.length - cupAtom.leftContext.length := by
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
        = capAtom.leftContext.length - cupAtom.leftContext.length := by
    dsimp only [natWindowDistance]
    rw [natSubEqZeroOfLeClean offsetLe, Nat.zero_add]
  rw [distanceEq] at distanceGeTwo
  exact distanceGeTwo

/-! ## The COMMUTE producer (right-of window offset) -/

/-- ★ **The COMMUTE producer (right-of).**  From the located split, the cup/cap tags, and the `disjointWindows`
verdict with `cupLeft ≤ capLeft`, produce the `CellDescentResult cell`: derive the boundary chainedness from
`cell`'s own realized chain (`framedChain_pairPathCoherence`), the `windowGap` from the verdict (a genuine cup's
window is width 2, so `windowGap := capLeft − (cupLeft + cupCod.length)`), the pair data (moved atoms + coherences + flat
swap) from `adjunctionCommutePairData_of_disjointWindows`, brick 1's transposed `next`, and assemble via
`cellDescentResult_ofCommutePrefixSwap`.  This is the COMMUTE case of the oracle dispatch, standalone. -/
def commuteCellDescentStepRight
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (offsetLe : cupAtom.leftContext.length ≤ capAtom.leftContext.length)
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
  let offsetGeTwo : 2 ≤ capAtom.leftContext.length - cupAtom.leftContext.length :=
    disjointWindows_directedOffset_ge_two cupAtom capAtom offsetLe verdict
  let combinedLe :
      cupAtom.leftContext.length + cupAtom.generatorCod.length ≤ capAtom.leftContext.length := by
    rw [cupAtom_generatorCod_length_two cupAtom isCupCup]
    have shifted := Nat.add_le_add_left offsetGeTwo cupAtom.leftContext.length
    rw [natAddSubCancelClean offsetLe] at shifted
    exact shifted
  let windowsDisjoint :
      cupAtom.leftContext.length + cupAtom.generatorCod.length
          + (capAtom.leftContext.length
              - (cupAtom.leftContext.length + cupAtom.generatorCod.length))
        = capAtom.leftContext.length :=
    natAddSubCancelClean combinedLe
  let pairData := adjunctionCommutePairData_of_disjointWindows cupAtom capAtom rest boundariesChain
    (capAtom.leftContext.length - (cupAtom.leftContext.length + cupAtom.generatorCod.length))
    windowsDisjoint
  cellDescentResult_ofCommutePrefixSwap prefixCells rest isCupCup isCapCap
    (pairData.tagCapMoved.trans isCapCap) (pairData.tagCupMoved.trans isCupCup) sourceSplit
    (commuteNextCell_spine cell prefixCells rest pairData.coherenceMovedSource
      pairData.coherenceMovedMid pairData.coherenceMovedTarget sourceSplit)
    pairData.swapStep

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE producer half is CLOSED for the right-of window offset.**  From a located
cup·cap split, the cup/cap tags, and the `disjointWindows` verdict with `cupLeft ≤ capLeft`,
`commuteCellDescentStepRight` produces the `CellDescentResult cell` — the COMMUTE case of the oracle's per-step
dispatch.  It assembles: the boundary chainedness derived from `cell`'s own realized chain
(`framedChain_pairPathCoherence`), the `windowGap`/sign from the verdict
(`disjointWindows_directedOffset_ge_two`, a genuine cup's window being width 2), the pair data — moved atoms,
three boundary-path coherences, tag preservation, and the flat `SpineAtomSwap` — all sharing one inert path
(`adjunctionCommutePairData_of_disjointWindows`), brick 1's transposed `next` (`commuteNextCell` /
`commuteNextCell_spine`), and the COMMUTE builder `cellDescentResult_ofCommutePrefixSwap`.

  What this marker does NOT close: the left-of window mirror (`adjunctionSpineAtomSwapLeft_of_disjointWindows`,
  the moved→original orientation), and — crucially — the STRAIGHTEN half of the oracle (partner-collapse, coupled
  to Piece II).  A total `CellDescentStepOracle` needs BOTH halves plus Piece II, so it stays UN-inhabited:
  `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyCommuteProducer : Bool := true

end FX1Poly.Polygraph
