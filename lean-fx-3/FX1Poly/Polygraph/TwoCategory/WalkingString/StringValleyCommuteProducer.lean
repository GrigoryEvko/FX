import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteLift
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCommuteWordFactorData
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteNext

/-! # WalkingString — Piece I COMMUTE producer (RIGHT-of window offset) at the three-generator seed (FC-3 r6, B2)

The COMMUTE branch of the walking adjunction (`SpineValleyCommuteProducer`) reconstructs the disjoint-window
factorization from a boundary LENGTH by SEED RIGIDITY (parallel adjunction paths of equal length are equal); at the
walking adjoint triple that rigidity is FALSE, so the string producer instead uses the WORD-valued factorization
`disjointWordWindowFactorData_of_disjointWordWindows` (keyed on the shared BOUNDARY WORD, signature-generic).  The
producer is thereby CLEANER than the adjunction: the pair's inter-atom coherence `atomFrameTarget cupAtom =
atomFrameSource capAtom` (from `cell`'s own realized chain) IS the shared word DIRECTLY — no length degradation, no
rigidity reconstruction.

  * ★ **`stringCupAtom_generatorDom_length_zero` / `stringCupAtom_generatorCod_length_two` /
    `stringCapAtom_generatorDom_length_two`** — the seed cup's / cap's generator arities read off the four-generator
    classification `adjointTripleSpineAtom_isCupOrCap` (cup: `0 ⇒ 2`, cap: `2 ⇒ 0`).  These fix the `windowGap`
    factorization for a genuine string cup/cap.
  * ★ **`stringDisjointWindows_directedOffset_ge_two`** — the `disjointWindows` verdict bounds the directed offset:
    with `cupLeft ≤ capLeft` the undirected `natWindowDistance ≥ 2` collapses to `capLeft − cupLeft ≥ 2`.
  * ★ **`StringCommutePairData` / `stringCommutePairData_of_disjointWordWindows`** — the moved atoms (record
    updates), the three boundary-path coherences the transposed `next` consumes (pure `composePath_assoc` over the
    word factorization), the tag preservation, and the flat `SpineAtomSwap`, all sharing one inert path.
  * ★ **`stringCommuteCellDescentStepRight`** — the COMMUTE producer (right-of): derive the pair's boundary path
    coherence from `cell`'s own realized chain (the generic `framedChain_pairPathCoherence`), read it as the shared
    word, derive `windowGap` from the verdict, build the pair data, the transposed `next` (the generic
    `commuteNextCell`), and assemble via `stringCellDescentResult_ofCommutePrefixSwap`.  A `StringCellDescentResult`
    producer, standalone.

## What this does NOT close (gates stay `false`)

This closes the COMMUTE producer for the right-of window offset (`cupLeft ≤ capLeft`).  The left-of mirror is the
sibling file; the STRAIGHTEN arm and the oracle wire-up are separate.  So `StringCellDescentStepOracle` stays
UN-inhabited and `fxString_hasAdjointTripleCompleteness` stays `false`.

Raw Lean 4 + Init; the arity is `adjointTripleSpineAtom_isCupOrCap` casing, the coherences are `composePath_assoc`
over the word factorization, the sign is truncated-subtraction `Nat` bookkeeping (hand-rolled propext-free),
the producer chains the generic transposed `next` into the string COMMUTE builder.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Re-rolled `Nat` helpers (propext-free) -/

/-- Left-cancellation of a subtracted addend: `a + b - a = b` (propext-free; core `Nat.add_sub_cancel_left`
leaks propext). -/
private theorem natAddSubCancelLeftStringCommute : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natAddSubCancelLeftStringCommute base value

/-- Subtracting a self-plus-tail is zero: `a - (a + k) = 0` (propext-free). -/
private theorem natSubAddRightStringCommute : (base tail : Nat) → base - (base + tail) = 0
  | 0, tail => by rw [Nat.zero_add, Nat.zero_sub]
  | base + 1, tail => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact natSubAddRightStringCommute base tail

/-- `a ≤ b → a - b = 0` (propext-free; core `Nat.sub_eq_zero_of_le` leaks propext). -/
private theorem natSubEqZeroOfLeStringCommute {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller - larger = 0 := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq]
  exact natSubAddRightStringCommute smaller gap

/-- `a ≤ b → a + (b - a) = b` (propext-free; core `Nat.add_sub_cancel'` leaks propext). -/
private theorem natAddSubCancelStringCommute {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller + (larger - smaller) = larger := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest isLe
  rw [← gapEq, natAddSubCancelLeftStringCommute smaller gap]

/-! ## The seed cup / cap generator arities from the tag -/

/-- A genuine string cup atom has source arity `0` — its `generatorDom` is empty, read off the cup tag. -/
theorem stringCupAtom_generatorDom_length_zero
    {overallSource overallTarget : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : atom.isCupAtom = true) : atom.generatorDom.length = 0 := by
  cases lengthCase : atom.generatorDom.length with
  | zero => rfl
  | succ predLength =>
      dsimp only [SpineAtom.isCupAtom] at isCup
      rw [lengthCase] at isCup
      exact Bool.noConfusion isCup

/-- ★ A genuine string cup atom has target arity `2` — a unit creates a length-2 word.  Read off the cup tag: the
four-generator classification `adjointTripleSpineAtom_isCupOrCap` has its cap branch excluded by the cup's empty
source. -/
theorem stringCupAtom_generatorCod_length_two
    {overallSource overallTarget : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : atom.isCupAtom = true) : atom.generatorCod.length = 2 := by
  have domZero := stringCupAtom_generatorDom_length_zero atom isCup
  cases adjointTripleSpineAtom_isCupOrCap atom with
  | inl cupBranch => exact cupBranch.2
  | inr capBranch =>
      rw [domZero] at capBranch
      exact Nat.noConfusion capBranch.1

/-- ★ A genuine string cap atom has source arity `2` — a counit consumes a length-2 word.  Read off the cap tag:
the cup branch (`generatorDom.length = 0`) is excluded by the cap tag. -/
theorem stringCapAtom_generatorDom_length_two
    {overallSource overallTarget : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCap : atom.isCupAtom = false) : atom.generatorDom.length = 2 := by
  cases adjointTripleSpineAtom_isCupOrCap atom with
  | inl cupBranch =>
      dsimp only [SpineAtom.isCupAtom] at isCap
      rw [cupBranch.1] at isCap
      exact Bool.noConfusion isCap
  | inr capBranch => exact capBranch.1

/-! ## The sign + `windowGap` derivation from the classifier verdict -/

/-- ★ **The `disjointWindows` verdict bounds the directed offset.**  A `disjointWindows` classification means the
undirected `natWindowDistance` is `≥ 2`; with `cupLeft ≤ capLeft` the truncated distance collapses to the directed
`capLeft − cupLeft`, so `capLeft − cupLeft ≥ 2`.  The string twin of `disjointWindows_directedOffset_ge_two`;
the classifier is signature-generic so only the `Nat` bookkeeping is re-rolled. -/
theorem stringDisjointWindows_directedOffset_ge_two
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
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
    rw [natSubEqZeroOfLeStringCommute offsetLe, Nat.zero_add]
  rw [distanceEq] at distanceGeTwo
  exact distanceGeTwo

/-! ## The combined pair data: moved atoms, coherences, tags, and the flat swap -/

/-- The RIGHT-of COMMUTE pair data bundle — Type-valued because the moved atoms are DATA feeding the transposed
`next`: the two moved atoms, their cup/cap tag preservation, the three boundary-path coherences, and the flat
`SpineAtomSwap`, all coherent for a single inert path.  The three-generator twin of `CommutePairData`. -/
structure StringCommutePairData {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) : Type where
  /-- The moved cap (its left context re-threaded through the cup's produced window). -/
  capMoved : SpineAtom adjointTripleModeSignature overallSource overallTarget
  /-- The moved cup (its right context re-threaded through the cap's consumed window). -/
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
  /-- The flat transposition of the located pair. -/
  swapStep : SpineAtomSwap adjointTripleModeSignature
    (cupAtom :: capAtom :: rest) (capMoved :: cupMoved :: rest)

/-- ★ **The RIGHT-of COMMUTE pair data from the WORD factorization.**  From ONE inert-path word factorization
(`disjointWordWindowFactorData_of_disjointWordWindows`, keyed on the shared boundary WORD — signature-generic, so it
runs at the walking adjoint triple where length-rigidity is FALSE) it names the moved atoms (record updates of the
originals), proves the three boundary-path coherences (pure `composePath_assoc` over the factorization equalities),
the tag preservation, and fires the flat `SpineAtomSwap` — all sharing the same inert path.  The three-generator
twin of `adjunctionCommutePairData_of_disjointWindows`, taking the shared word directly instead of a length. -/
def stringCommutePairData_of_disjointWordWindows
    {overallSource overallTarget : AdjointTripleMode}
    (cupAtom capAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (sharedWord :
      composePath cupAtom.leftContext (composePath cupAtom.generatorCod cupAtom.rightContext)
        = composePath capAtom.leftContext (composePath capAtom.generatorDom capAtom.rightContext))
    (windowGap : Nat)
    (windowsDisjoint :
      cupAtom.leftContext.length + cupAtom.generatorCod.length + windowGap
        = capAtom.leftContext.length) :
    StringCommutePairData cupAtom capAtom rest := by
  obtain ⟨inertPath, leftFactor, rightFactor⟩ :=
    disjointWordWindowFactorData_of_disjointWordWindows cupAtom capAtom sharedWord windowGap
      windowsDisjoint
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

/-! ## The COMMUTE producer (right-of window offset) -/

/-- ★ **The COMMUTE producer (right-of).**  From the located split, the cup/cap tags, and the `disjointWindows`
verdict with `cupLeft ≤ capLeft`, produce the `StringCellDescentResult cell`: derive the pair's boundary path
coherence from `cell`'s own realized chain (`framedChain_pairPathCoherence`), read it as the shared boundary WORD,
derive the `windowGap` from the verdict (a genuine cup's window is width 2, so `windowGap := capLeft − (cupLeft +
cupCod.length)`), the pair data from `stringCommutePairData_of_disjointWordWindows`, the transposed `next` (the
generic `commuteNextCell`), and assemble via `stringCellDescentResult_ofCommutePrefixSwap`.  A `StringCellDescentResult`
producer, standalone. -/
def stringCommuteCellDescentStepRight
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (offsetLe : cupAtom.leftContext.length ≤ capAtom.leftContext.length)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.disjointWindows) :
    StringCellDescentResult cell :=
  let sharedWord :
      composePath cupAtom.leftContext (composePath cupAtom.generatorCod cupAtom.rightContext)
        = composePath capAtom.leftContext (composePath capAtom.generatorDom capAtom.rightContext) :=
    framedChain_pairPathCoherence rest prefixCells
      (FramedSpineChain.castAtoms sourceSplit cell.cellChain)
  let offsetGeTwo : 2 ≤ capAtom.leftContext.length - cupAtom.leftContext.length :=
    stringDisjointWindows_directedOffset_ge_two cupAtom capAtom offsetLe verdict
  let combinedLe :
      cupAtom.leftContext.length + cupAtom.generatorCod.length ≤ capAtom.leftContext.length := by
    rw [stringCupAtom_generatorCod_length_two cupAtom isCupCup]
    have shifted := Nat.add_le_add_left offsetGeTwo cupAtom.leftContext.length
    rw [natAddSubCancelStringCommute offsetLe] at shifted
    exact shifted
  let windowsDisjoint :
      cupAtom.leftContext.length + cupAtom.generatorCod.length
          + (capAtom.leftContext.length
              - (cupAtom.leftContext.length + cupAtom.generatorCod.length))
        = capAtom.leftContext.length :=
    natAddSubCancelStringCommute combinedLe
  let pairData := stringCommutePairData_of_disjointWordWindows cupAtom capAtom rest sharedWord
    (capAtom.leftContext.length - (cupAtom.leftContext.length + cupAtom.generatorCod.length))
    windowsDisjoint
  stringCellDescentResult_ofCommutePrefixSwap prefixCells rest isCupCup isCapCap
    (pairData.tagCapMoved.trans isCapCap) (pairData.tagCupMoved.trans isCupCup) sourceSplit
    (commuteNextCell_spine cell prefixCells rest pairData.coherenceMovedSource
      pairData.coherenceMovedMid pairData.coherenceMovedTarget sourceSplit)
    pairData.swapStep

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE producer half is CLOSED for the right-of window offset at the three-generator
seed.**  From a located cup·cap split, the cup/cap tags, and the `disjointWindows` verdict with `cupLeft ≤ capLeft`,
`stringCommuteCellDescentStepRight` produces the `StringCellDescentResult cell`.  It assembles: the pair's boundary
path coherence from `cell`'s own realized chain (`framedChain_pairPathCoherence`), read DIRECTLY as the shared
boundary WORD (no length degradation — the string producer is cleaner than the length-rigid adjunction); the
`windowGap`/sign from the verdict (`stringDisjointWindows_directedOffset_ge_two`, the cup's window being width 2 via
`stringCupAtom_generatorCod_length_two`); the pair data — moved atoms, three boundary-path coherences, tag
preservation, and the flat `SpineAtomSwap` — all sharing one inert path
(`stringCommutePairData_of_disjointWordWindows` over the WORD factorization), the generic transposed `next`, and the
string COMMUTE builder `stringCellDescentResult_ofCommutePrefixSwap`.

  What this marker does NOT close: the left-of window mirror (the sibling file), the STRAIGHTEN half, and the whole
  oracle wire-up.  So `StringCellDescentStepOracle` stays UN-inhabited and `fxString_hasAdjointTripleCompleteness`
  stays `false`.  `= true`. -/
def fxString_hasStringValleyCommuteProducer : Bool := true

end FX1Poly.Polygraph
