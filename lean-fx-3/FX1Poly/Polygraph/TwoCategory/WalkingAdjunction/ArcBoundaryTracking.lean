import FX1Poly.Polygraph.Computad.AdjunctionSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations

/-! # WalkingAdjunction/ArcBoundaryTracking — the arc fold's open-wire count tracks the boundary

The arc-fold twin of `stepAtom_openWires_tracksBoundary`: one cup/cap arc step moves the
open-wire count from the atom's dom boundary to its cod boundary.  Combined with
`SpineBoundaryChained` this threads `openWires.length = boundaryLength` through a whole chained
run — which is what turns the peel's chainedness hypothesis into the dispatcher's window-fit
premise for free (the window is a prefix of the boundary sum).  The walking-adjunction seed
discharges the arity hypothesis wholesale: its only generators are the unit (a cup) and the
counit (a cap).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Cancelling a common right summand — hand-rolled because `Nat.add_right_cancel` pulls
`propext` through its simp-lemma proof. -/
theorem natSumRightCancel : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEqual => sumsEqual
  | cancelled + 1, _, _, sumsEqual => natSumRightCancel cancelled (Nat.succ.inj sumsEqual)

/-- ★ **One cup/cap arc step tracks the boundary**: entering at the atom's dom boundary, the
open-wire count exits at its cod boundary.  A cup inserts two wires (`natListInsertAt_length`),
a cap removes two (`natListRemoveTwoAt_length`, in range because the dom boundary bounds the
window from above).  The generic-box arm is excluded by the arity hypothesis — its placeholder
wire bookkeeping does not track boundaries. -/
theorem stepArcAtom_openWires_tracksBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength) :
    (stepArcAtom state atom).openWires.length = atom.codBoundaryLength := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases arity with
  | inl cupArity =>
      obtain ⟨domZero, codTwo⟩ := cupArity
      rw [domZero] at entryShape
      dsimp only [stepArcAtom]
      rw [domZero, codTwo]
      show (natListInsertAt state.openWires atom.leftContext.length
            [state.nextFresh, state.nextFresh + 1]).length
          = atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
      rw [natListInsertAt_length state.openWires atom.leftContext.length
          [state.nextFresh, state.nextFresh + 1],
        entryShape, codTwo]
      exact Nat.add_right_comm atom.leftContext.length atom.rightContext.length 2
  | inr capArity =>
      obtain ⟨domTwo, codZero⟩ := capArity
      rw [domTwo] at entryShape
      have windowFits : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      have removeShift := natListRemoveTwoAt_length state.openWires
        atom.leftContext.length windowFits
      dsimp only [stepArcAtom]
      rw [domTwo, codZero]
      show (natListRemoveTwoAt state.openWires atom.leftContext.length).length
          = atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
      rw [codZero]
      have paddedGoal : (natListRemoveTwoAt state.openWires atom.leftContext.length).length + 2
          = atom.leftContext.length + atom.rightContext.length + 2 := by
        rw [removeShift, entryShape,
          Nat.add_right_comm atom.leftContext.length 2 atom.rightContext.length]
      exact natSumRightCancel 2 paddedGoal

/-- ★ **Every walking-adjunction atom is a cup or a cap** — the seed's only generators are the
unit (`0 ⇒ 2`) and the counit (`2 ⇒ 0`), so the arity hypothesis of the boundary-tracking and
window-suffix kit discharges wholesale at the adjunction signature.  Delegates to the
canonical peel-foundations disjunction, which IS `AtomHasCupOrCapArity` unfolded. -/
theorem adjunctionSpineAtom_hasCupOrCapArity
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode) :
    AtomHasCupOrCapArity atom :=
  adjunctionSpineAtom_isCupOrCap atom

end FX1Poly.Polygraph
