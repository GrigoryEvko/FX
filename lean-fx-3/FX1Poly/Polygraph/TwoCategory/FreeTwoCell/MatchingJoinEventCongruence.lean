import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # mode-3 keystone — fresh-shift equivariance of the join-event trace

The sigma witness's `componentComm`/`loopsEq` now reduce to relating the two transposed Godement
orders' EVENT TRACES (`MatchingJoinEvents` reified them; `MatchingJoinEventExchange` proved the
block swap).  The missing leg is the cross-order correspondence: each block's trace in one order
is the `freshShiftAbove`-rename of its trace in the other.  This file proves that congruence:

  * ★ `runMatchingCell_joinEvents_freshShift` — under the cup/cap discipline, two runs of the SAME
    cell — each at its OWN left accumulator, with arbitrary right accumulators, from states whose
    window reads are `freshShiftAbove`-related and whose counters run `delta` apart — emit traces
    related by the pointwise pair-rename.  A cup's events are its two fresh legs (counters `delta`
    apart, both at-or-above the threshold), a cap's events are its two window reads (related by the
    window hypothesis) — so the trace is a function of the window evolution the shipped
    two-position window congruence (`runMatchingCell_windowWireView_freshShift`) already relates;
    the cell induction mirrors it, invoking it for the intermediate state relations.
  * Spine plumbing: `RawTwoCellExpr.spineDiff_append` (the difference-list normalizes to an
    append), `spineJoinEvents_append` (the trace splits over atom-list concatenation), and
    `spineJoinEvents_vcompSplit` (a vertical composite's trace is its factors' traces
    concatenated at the intermediate state).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## List plumbing (hand-rolled; core append/map lemmas leak propext) -/

private theorem listAppendNil {Element : Type} :
    (list : List Element) → list ++ [] = list
  | [] => rfl
  | head :: rest => congrArg (head :: ·) (listAppendNil rest)

private theorem listAppendAssoc {Element : Type} :
    (first : List Element) → (second : List Element) → (third : List Element) →
    (first ++ second) ++ third = first ++ (second ++ third)
  | [], _, _ => rfl
  | head :: firstRest, second, third =>
      congrArg (head :: ·) (listAppendAssoc firstRest second third)

private theorem listMapAppend {Element ResultElement : Type} (mapped : Element → ResultElement) :
    (first : List Element) → (second : List Element) →
    (first ++ second).map mapped = first.map mapped ++ second.map mapped
  | [], _ => rfl
  | head :: firstRest, second =>
      congrArg (mapped head :: ·) (listMapAppend mapped firstRest second)

/-! ## Nat monotonicity/cancellation helpers (hand-rolled; core `Nat.add_right_cancel` leaks propext) -/

private theorem natAddLeMonoRight : (added : Nat) → {leftSide rightSide : Nat} →
    leftSide ≤ rightSide → leftSide + added ≤ rightSide + added
  | 0, _, _, sidesLe => sidesLe
  | added + 1, _, _, sidesLe => Nat.succ_le_succ (natAddLeMonoRight added sidesLe)

private theorem natAddLeCancelRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natAddLeCancelRight cancelled (Nat.le_of_succ_le_succ sumsLe)

private theorem natAddLeMonoLeft (added : Nat) {leftSide rightSide : Nat}
    (sidesLe : leftSide ≤ rightSide) : added + leftSide ≤ added + rightSide := by
  rw [Nat.add_comm added leftSide, Nat.add_comm added rightSide]
  exact natAddLeMonoRight added sidesLe

private theorem natAddLtMonoLeft (added : Nat) {leftSide rightSide : Nat}
    (sidesLt : leftSide < rightSide) : added + leftSide < added + rightSide := by
  show added + leftSide + 1 ≤ added + rightSide
  rw [Nat.add_assoc added leftSide 1]
  exact natAddLeMonoLeft added sidesLt

/-! ## Spine plumbing: the difference list as an append -/

/-- The spine difference-list normalizes to an append: flattening onto `rest` is flattening onto
`[]` followed by appending `rest`.  Structural cell induction; the `gen`/`id`/whisker arms are
definitional, the `vcomp` arm re-associates. -/
theorem RawTwoCellExpr.spineDiff_append {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    cell.spineDiff leftAccumulator rightAccumulator rest
      = cell.spineDiff leftAccumulator rightAccumulator [] ++ rest
  | _, _, _, _, _, _, .gen _, _ => rfl
  | _, _, _, _, _, _, .id _, _ => rfl
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest => by
      show cellAlpha.spineDiff leftAccumulator rightAccumulator
            (cellBeta.spineDiff leftAccumulator rightAccumulator rest)
          = cellAlpha.spineDiff leftAccumulator rightAccumulator
              (cellBeta.spineDiff leftAccumulator rightAccumulator []) ++ rest
      rw [RawTwoCellExpr.spineDiff_append leftAccumulator rightAccumulator cellAlpha
          (cellBeta.spineDiff leftAccumulator rightAccumulator rest),
        RawTwoCellExpr.spineDiff_append leftAccumulator rightAccumulator cellBeta rest,
        RawTwoCellExpr.spineDiff_append leftAccumulator rightAccumulator cellAlpha
          (cellBeta.spineDiff leftAccumulator rightAccumulator []),
        listAppendAssoc]
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, rest =>
      RawTwoCellExpr.spineDiff_append (composePath leftAccumulator oneCell) rightAccumulator
        body rest
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, rest =>
      RawTwoCellExpr.spineDiff_append leftAccumulator (composePath oneCell rightAccumulator)
        body rest

/-- The join-event trace splits over atom-list concatenation (the second block traced from the
first block's output state). -/
theorem spineJoinEvents_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atomsOne atomsTwo : List (SpineAtom signature sourceMode targetMode)) →
    (state : WireState) →
    spineJoinEvents (atomsOne ++ atomsTwo) state
      = spineJoinEvents atomsOne state
        ++ spineJoinEvents atomsTwo (processSpine state atomsOne)
  | [], _, _ => rfl
  | atom :: restAtoms, atomsTwo, state => by
      show stepAtomJoinEvents state atom
            ++ spineJoinEvents (restAtoms ++ atomsTwo) (stepAtom state atom)
          = (stepAtomJoinEvents state atom
              ++ spineJoinEvents restAtoms (stepAtom state atom))
            ++ spineJoinEvents atomsTwo (processSpine (stepAtom state atom) restAtoms)
      rw [spineJoinEvents_append restAtoms atomsTwo (stepAtom state atom), listAppendAssoc]

/-- A vertical composite's trace is its factors' traces concatenated, the second factor traced
from the first factor's output run. -/
theorem spineJoinEvents_vcompSplit {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph localSource localTarget}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    spineJoinEvents
        ((RawTwoCellExpr.vcomp cellAlpha cellBeta).spineDiff leftAcc rightAcc []) state
      = spineJoinEvents (cellAlpha.spineDiff leftAcc rightAcc []) state
        ++ spineJoinEvents (cellBeta.spineDiff leftAcc rightAcc [])
            (runMatchingCell state leftAcc rightAcc cellAlpha) := by
  show spineJoinEvents (cellAlpha.spineDiff leftAcc rightAcc
        (cellBeta.spineDiff leftAcc rightAcc [])) state = _
  rw [RawTwoCellExpr.spineDiff_append leftAcc rightAcc cellAlpha
      (cellBeta.spineDiff leftAcc rightAcc [])]
  exact spineJoinEvents_append (cellAlpha.spineDiff leftAcc rightAcc [])
    (cellBeta.spineDiff leftAcc rightAcc []) state

/-! ## The per-atom event equivariance -/

/-- ★ **One cup/cap atom's join events are equivariant under the fresh shift.**  Two atoms with the
same generator arities, each firing at its OWN position, on counter-shifted states with
`freshShiftAbove`-related input-window reads: a cup emits its two fresh legs (counters `delta`
apart, both at-or-above the threshold), a cap emits its two window reads (offsets `0` and `1` of
the window hypothesis).  Unlike the wire-window layer, the cap DOES consume the input window here
— its events are the reads themselves. -/
theorem stepAtomPair_joinEvents_freshShift {signature : ModeSignature}
    {sourceModeS targetModeS sourceModeT targetModeT : signature.graph.Mode}
    (threshold delta : Nat) (stateS stateT : WireState)
    (atomS : SpineAtom signature sourceModeS targetModeS)
    (atomT : SpineAtom signature sourceModeT targetModeT)
    (domEq : atomT.generatorDom.length = atomS.generatorDom.length)
    (codEq : atomT.generatorCod.length = atomS.generatorCod.length)
    (arity : AtomHasCupOrCapArity atomS)
    (freshShifted : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh)
    (windowMap : ∀ innerOffset, innerOffset < atomS.generatorDom.length →
      natListGetAt stateT.openWires (atomT.leftContext.length + innerOffset)
        = freshShiftAbove threshold delta
            (natListGetAt stateS.openWires (atomS.leftContext.length + innerOffset))) :
    stepAtomJoinEvents stateT atomT
      = (stepAtomJoinEvents stateS atomS).map
          (fun event => (freshShiftAbove threshold delta event.1,
            freshShiftAbove threshold delta event.2)) := by
  cases arity with
  | inl cupArity =>
      rw [stepAtomJoinEvents_ofCupArity stateT atomT (domEq.trans cupArity.1)
          (codEq.trans cupArity.2),
        stepAtomJoinEvents_ofCupArity stateS atomS cupArity.1 cupArity.2]
      show [(stateT.nextFresh, stateT.nextFresh + 1)]
          = [(freshShiftAbove threshold delta stateS.nextFresh,
              freshShiftAbove threshold delta (stateS.nextFresh + 1))]
      rw [freshShiftAbove_ofLe threshold delta stateS.nextFresh thresholdLe,
        freshShiftAbove_ofLe threshold delta (stateS.nextFresh + 1)
          (Nat.le_succ_of_le thresholdLe),
        freshShifted, Nat.add_right_comm stateS.nextFresh 1 delta]
  | inr capArity =>
      have windowBoundZero : 0 < atomS.generatorDom.length := by
        rw [capArity.1]
        exact Nat.le_succ 1
      have windowBoundOne : 1 < atomS.generatorDom.length := by
        rw [capArity.1]
        exact Nat.le_refl 2
      have readZero : natListGetAt stateT.openWires atomT.leftContext.length
          = freshShiftAbove threshold delta
              (natListGetAt stateS.openWires atomS.leftContext.length) :=
        windowMap 0 windowBoundZero
      have readOne := windowMap 1 windowBoundOne
      rw [stepAtomJoinEvents_ofCapArity stateT atomT (domEq.trans capArity.1)
          (codEq.trans capArity.2),
        stepAtomJoinEvents_ofCapArity stateS atomS capArity.1 capArity.2]
      show [(natListGetAt stateT.openWires atomT.leftContext.length,
            natListGetAt stateT.openWires (atomT.leftContext.length + 1))]
          = [(freshShiftAbove threshold delta
                (natListGetAt stateS.openWires atomS.leftContext.length),
              freshShiftAbove threshold delta
                (natListGetAt stateS.openWires (atomS.leftContext.length + 1)))]
      rw [readZero, readOne]

/-! ## The block layer: trace equivariance of a whole cell's fold -/

/-- ★ **A whole block's join-event trace is equivariant under the fresh shift** — the cross-order
trace correspondence of the sigma witness.  Under the cup/cap discipline, two runs of the SAME
cell, each at its OWN left accumulator over the same local boundary, with arbitrary (even
different) right accumulators, from states whose window reads are `freshShiftAbove`-related and
whose counters run `delta` apart, emit traces related by the pointwise pair-rename.  Structural
cell induction mirroring the shipped two-position window congruence and INVOKING it for the
intermediate state relations: a generator is the atom-pair lemma, an identity's trace is empty, a
vertical composite splits its trace at the intermediate run (`spineJoinEvents_vcompSplit`) with
the middle window relation supplied by `runMatchingCell_windowWireView_freshShift` (middle ranges
from the banked suffix count equation), and the two whiskerings re-anchor the hypotheses exactly
as the window congruence does — the trace conclusion needs no zone split. -/
theorem runMatchingCell_joinEvents_freshShift {signature : ModeSignature}
    {overallSourceS overallSourceT overallTargetS overallTargetT : signature.graph.Mode}
    (threshold delta : Nat) :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccS : ModalityPath signature.graph overallSourceS localSource) →
    (leftAccT : ModalityPath signature.graph overallSourceT localSource) →
    (rightAccS : ModalityPath signature.graph localTarget overallTargetS) →
    (rightAccT : ModalityPath signature.graph localTarget overallTargetT) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (stateS stateT : WireState) →
    CellHasCupCapGenerators cell →
    (∀ innerOffset, innerOffset < localDom.length →
      natListGetAt stateT.openWires (leftAccT.length + innerOffset)
        = freshShiftAbove threshold delta
            (natListGetAt stateS.openWires (leftAccS.length + innerOffset))) →
    stateT.nextFresh = stateS.nextFresh + delta →
    threshold ≤ stateS.nextFresh →
    leftAccS.length + localDom.length ≤ stateS.openWires.length →
    leftAccT.length + localDom.length ≤ stateT.openWires.length →
    spineJoinEvents (cell.spineDiff leftAccT rightAccT []) stateT
      = (spineJoinEvents (cell.spineDiff leftAccS rightAccS []) stateS).map
          (fun event => (freshShiftAbove threshold delta event.1,
            freshShiftAbove threshold delta event.2))
  | _, _, leftAccS, leftAccT, rightAccS, rightAccT, _, _, .gen generator, stateS, stateT,
      cupCap, windowMap, freshShifted, thresholdLe, _, _ => by
      show stepAtomJoinEvents stateT ⟨_, _, leftAccT, _, _, generator, rightAccT⟩ ++ []
          = ((stepAtomJoinEvents stateS ⟨_, _, leftAccS, _, _, generator, rightAccS⟩
              ++ []).map
              (fun event : Nat × Nat => (freshShiftAbove threshold delta event.1,
                freshShiftAbove threshold delta event.2)))
      rw [listAppendNil, listAppendNil]
      exact stepAtomPair_joinEvents_freshShift threshold delta stateS stateT
        ⟨_, _, leftAccS, _, _, generator, rightAccS⟩
        ⟨_, _, leftAccT, _, _, generator, rightAccT⟩
        rfl rfl cupCap freshShifted thresholdLe windowMap
  | _, _, _, _, _, _, _, _, .id _, _, _, _, _, _, _, _, _ => rfl
  | _, _, leftAccS, leftAccT, rightAccS, rightAccT, _, _,
      @RawTwoCellExpr.vcomp _ _ _ oneCellF oneCellG oneCellH cellAlpha cellBeta,
      stateS, stateT, cupCap, windowMap, freshShifted, thresholdLe,
      windowInRangeS, windowInRangeT => by
      have alphaCongruence := runMatchingCell_windowWireView_freshShift threshold delta leftAccS
        leftAccT rightAccS rightAccT cellAlpha stateS stateT cupCap.1 windowMap freshShifted
        thresholdLe windowInRangeS windowInRangeT
      have alphaCountS := (runMatchingCell_openWiresSuffix_invariant leftAccS rightAccS cellAlpha
        stateS cupCap.1 windowInRangeS).2
      have alphaCountT := (runMatchingCell_openWiresSuffix_invariant leftAccT rightAccT cellAlpha
        stateT cupCap.1 windowInRangeT).2
      have middleRangeS : leftAccS.length + oneCellG.length
          ≤ (runMatchingCell stateS leftAccS rightAccS cellAlpha).openWires.length := by
        have padded : leftAccS.length + oneCellG.length + oneCellF.length
            ≤ (runMatchingCell stateS leftAccS rightAccS cellAlpha).openWires.length
              + oneCellF.length := by
          rw [Nat.add_right_comm leftAccS.length oneCellG.length oneCellF.length, alphaCountS]
          exact natAddLeMonoRight oneCellG.length windowInRangeS
        exact natAddLeCancelRight oneCellF.length padded
      have middleRangeT : leftAccT.length + oneCellG.length
          ≤ (runMatchingCell stateT leftAccT rightAccT cellAlpha).openWires.length := by
        have padded : leftAccT.length + oneCellG.length + oneCellF.length
            ≤ (runMatchingCell stateT leftAccT rightAccT cellAlpha).openWires.length
              + oneCellF.length := by
          rw [Nat.add_right_comm leftAccT.length oneCellG.length oneCellF.length, alphaCountT]
          exact natAddLeMonoRight oneCellG.length windowInRangeT
        exact natAddLeCancelRight oneCellF.length padded
      have alphaEvents := runMatchingCell_joinEvents_freshShift threshold delta leftAccS
        leftAccT rightAccS rightAccT cellAlpha stateS stateT cupCap.1 windowMap freshShifted
        thresholdLe windowInRangeS windowInRangeT
      have betaEvents := runMatchingCell_joinEvents_freshShift threshold delta leftAccS
        leftAccT rightAccS rightAccT cellBeta
        (runMatchingCell stateS leftAccS rightAccS cellAlpha)
        (runMatchingCell stateT leftAccT rightAccT cellAlpha) cupCap.2 alphaCongruence.1
        alphaCongruence.2
        (Nat.le_trans thresholdLe
          (runMatchingCell_nextFresh_le stateS leftAccS rightAccS cellAlpha))
        middleRangeS middleRangeT
      rw [spineJoinEvents_vcompSplit stateT leftAccT rightAccT cellAlpha cellBeta,
        spineJoinEvents_vcompSplit stateS leftAccS rightAccS cellAlpha cellBeta,
        alphaEvents, betaEvents,
        listMapAppend (fun event : Nat × Nat => (freshShiftAbove threshold delta event.1,
          freshShiftAbove threshold delta event.2))
          (spineJoinEvents (cellAlpha.spineDiff leftAccS rightAccS []) stateS)
          (spineJoinEvents (cellBeta.spineDiff leftAccS rightAccS [])
            (runMatchingCell stateS leftAccS rightAccS cellAlpha))]
  | _, _, leftAccS, leftAccT, rightAccS, rightAccT, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body,
      stateS, stateT, cupCap, windowMap, freshShifted, thresholdLe,
      windowInRangeS, windowInRangeT => by
      rw [composePath_length oneCell oneCellG] at windowInRangeS windowInRangeT
      have bodyWindowMap : ∀ innerOffset, innerOffset < oneCellG.length →
          natListGetAt stateT.openWires ((composePath leftAccT oneCell).length + innerOffset)
            = freshShiftAbove threshold delta
                (natListGetAt stateS.openWires
                  ((composePath leftAccS oneCell).length + innerOffset)) := by
        intro innerOffset offsetInRange
        have outerRead := windowMap (oneCell.length + innerOffset) (by
          rw [composePath_length oneCell oneCellG]
          exact natAddLtMonoLeft oneCell.length offsetInRange)
        rw [← Nat.add_assoc leftAccT.length oneCell.length innerOffset,
          ← Nat.add_assoc leftAccS.length oneCell.length innerOffset,
          ← composePath_length leftAccT oneCell,
          ← composePath_length leftAccS oneCell] at outerRead
        exact outerRead
      have bodyRangeS : (composePath leftAccS oneCell).length + oneCellG.length
          ≤ stateS.openWires.length := by
        rw [composePath_length leftAccS oneCell,
          Nat.add_assoc leftAccS.length oneCell.length oneCellG.length]
        exact windowInRangeS
      have bodyRangeT : (composePath leftAccT oneCell).length + oneCellG.length
          ≤ stateT.openWires.length := by
        rw [composePath_length leftAccT oneCell,
          Nat.add_assoc leftAccT.length oneCell.length oneCellG.length]
        exact windowInRangeT
      exact runMatchingCell_joinEvents_freshShift threshold delta
        (composePath leftAccS oneCell) (composePath leftAccT oneCell) rightAccS rightAccT body
        stateS stateT cupCap bodyWindowMap freshShifted thresholdLe bodyRangeS bodyRangeT
  | _, _, leftAccS, leftAccT, rightAccS, rightAccT, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body,
      stateS, stateT, cupCap, windowMap, freshShifted, thresholdLe,
      windowInRangeS, windowInRangeT => by
      rw [composePath_length oneCellF oneCell] at windowInRangeS windowInRangeT
      have bodyRangeS : leftAccS.length + oneCellF.length ≤ stateS.openWires.length := by
        rw [← Nat.add_assoc leftAccS.length oneCellF.length oneCell.length] at windowInRangeS
        exact Nat.le_trans
          (Nat.le_add_right (leftAccS.length + oneCellF.length) oneCell.length) windowInRangeS
      have bodyRangeT : leftAccT.length + oneCellF.length ≤ stateT.openWires.length := by
        rw [← Nat.add_assoc leftAccT.length oneCellF.length oneCell.length] at windowInRangeT
        exact Nat.le_trans
          (Nat.le_add_right (leftAccT.length + oneCellF.length) oneCell.length) windowInRangeT
      have bodyWindowMap : ∀ innerOffset, innerOffset < oneCellF.length →
          natListGetAt stateT.openWires (leftAccT.length + innerOffset)
            = freshShiftAbove threshold delta
                (natListGetAt stateS.openWires (leftAccS.length + innerOffset)) :=
        fun innerOffset offsetInRange =>
          windowMap innerOffset (by
            rw [composePath_length oneCellF oneCell]
            exact Nat.lt_of_lt_of_le offsetInRange
              (Nat.le_add_right oneCellF.length oneCell.length))
      exact runMatchingCell_joinEvents_freshShift threshold delta leftAccS leftAccT
        (composePath oneCell rightAccS) (composePath oneCell rightAccT) body stateS stateT
        cupCap bodyWindowMap freshShifted thresholdLe bodyRangeS bodyRangeT

/-! ## Honesty marker -/

/-- **Honesty marker — the fresh-shift equivariance of the JOIN-EVENT TRACE is PROVED, at two
positions.**  Under the cup/cap discipline, two runs of the same cell — each at its own left
accumulator, arbitrary right accumulators — from window-related, counter-shifted states emit
traces related by the pointwise `freshShiftAbove` pair-rename
(`stepAtomPair_joinEvents_freshShift`, `runMatchingCell_joinEvents_freshShift`), riding the
shipped window congruence for every intermediate state relation.  Together with the trace
reification/faithfulness (`MatchingJoinEvents`) and the block exchange
(`MatchingJoinEventExchange`), the sigma witness's `componentComm`/`loopsEq` reduce to pure
assembly: relate each order's links/loops to its trace, rename one order's trace by the rotation
(this congruence composed with the per-zone rotation/shift agreement lemmas), and transpose the
blocks (the exchange).  NOT yet covered: that final assembly and the `MatchingComponentSim`
bundling itself.  `= true`. -/
def fxMode_hasMatchingJoinEventFreshShiftCongruence : Bool := true

end FX1Poly.Polygraph
