import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPositionalShiftSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcComponentShiftStep — the component leg steps with the arc fold

Wires the head-cancellation component invariant (`ArcComponentShiftCorr`) to the actual
cup/cap steps over `ArcWireState`.  Each step's links are TWO nested joins whose arguments on
the shifted side are `sigma`-images of the base side's — the fresh legs and event nodes through
the positional simulation's counter correspondence, the cap's consumed wires through `openMap`
with the in-range read (`natListGetAt_map_inRange`; the cap therefore carries the in-range
window premise, discharged from boundary tracking at the per-atom dispatch).  Each join then
preserves the invariant by `arcComponentShiftCorr_correspondingJoin`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **A cup step preserves the component-leg invariant.**  Both runs join their two fresh legs
then the event node onto the left leg; the shifted arguments are the `sigma`-images of the base
ones through the counter correspondence, so the invariant survives two corresponding joins. -/
theorem arcComponentShiftCorr_stepCupArc (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (legLeft legRight : Nat)
    (baseState shiftedState : ArcWireState) (position : Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (posSim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState)
    (baseForest : isUnionFindForest baseState.links)
    (shiftedForest : isUnionFindForest shiftedState.links)
    (corr : ArcComponentShiftCorr sigma legLeft legRight
      baseState.links shiftedState.links) :
    ArcComponentShiftCorr sigma legLeft legRight
      (stepCupArc baseState position).links (stepCupArc shiftedState position).links := by
  have shiftLegZero : sigma baseState.nextFresh = shiftedState.nextFresh :=
    (sigmaShiftsAboveThreshold baseState.nextFresh posSim.nfFloor).trans posSim.nfShift.symm
  have shiftLegOne : sigma (baseState.nextFresh + 1) = shiftedState.nextFresh + 1 :=
    (sigmaShiftsAboveThreshold (baseState.nextFresh + 1)
        (Nat.le_trans posSim.nfFloor (Nat.le_add_right baseState.nextFresh 1))).trans
      ((Nat.add_right_comm baseState.nextFresh 1 delta).trans
        (congrArg (· + 1) posSim.nfShift.symm))
  have shiftLegTwo : sigma (baseState.nextFresh + 2) = shiftedState.nextFresh + 2 :=
    (sigmaShiftsAboveThreshold (baseState.nextFresh + 2)
        (Nat.le_trans posSim.nfFloor (Nat.le_add_right baseState.nextFresh 2))).trans
      ((Nat.add_right_comm baseState.nextFresh 2 delta).trans
        (congrArg (· + 2) posSim.nfShift.symm))
  have afterLegs := arcComponentShiftCorr_correspondingJoin sigma legLeft legRight
    baseState.links shiftedState.links baseForest shiftedForest corr
    baseState.nextFresh (baseState.nextFresh + 1)
  have afterEvent := arcComponentShiftCorr_correspondingJoin sigma legLeft legRight
    (unionFindJoin baseState.links baseState.nextFresh (baseState.nextFresh + 1))
    (unionFindJoin shiftedState.links (sigma baseState.nextFresh)
      (sigma (baseState.nextFresh + 1)))
    (isUnionFindForest_unionFindJoin baseState.links baseState.nextFresh
      (baseState.nextFresh + 1) baseForest)
    (isUnionFindForest_unionFindJoin shiftedState.links (sigma baseState.nextFresh)
      (sigma (baseState.nextFresh + 1)) shiftedForest)
    afterLegs (baseState.nextFresh + 2) baseState.nextFresh
  show ArcComponentShiftCorr sigma legLeft legRight
    (unionFindJoin
      (unionFindJoin baseState.links baseState.nextFresh (baseState.nextFresh + 1))
      (baseState.nextFresh + 2) baseState.nextFresh)
    (unionFindJoin
      (unionFindJoin shiftedState.links shiftedState.nextFresh (shiftedState.nextFresh + 1))
      (shiftedState.nextFresh + 2) shiftedState.nextFresh)
  rw [← shiftLegTwo, ← shiftLegOne, ← shiftLegZero]
  exact afterEvent

/-- **A cap step preserves the component-leg invariant** — GIVEN the fire window sits inside
the base boundary, so both consumed-wire reads land in range and correspond under `openMap`.
Both runs join the two consumed wires then the event node onto the left wire. -/
theorem arcComponentShiftCorr_stepCapArc (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (legLeft legRight : Nat)
    (baseState shiftedState : ArcWireState) (position : Nat)
    (windowInRange : position + 2 ≤ baseState.openWires.length)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (posSim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState)
    (baseForest : isUnionFindForest baseState.links)
    (shiftedForest : isUnionFindForest shiftedState.links)
    (corr : ArcComponentShiftCorr sigma legLeft legRight
      baseState.links shiftedState.links) :
    ArcComponentShiftCorr sigma legLeft legRight
      (stepCapArc baseState position).links (stepCapArc shiftedState position).links := by
  have shiftEvent : sigma baseState.nextFresh = shiftedState.nextFresh :=
    (sigmaShiftsAboveThreshold baseState.nextFresh posSim.nfFloor).trans posSim.nfShift.symm
  have leftWireReads : natListGetAt shiftedState.openWires position
      = sigma (natListGetAt baseState.openWires position) := by
    rw [posSim.openMap]
    exact natListGetAt_map_inRange sigma baseState.openWires position
      (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self position)) windowInRange)
  have rightWireReads : natListGetAt shiftedState.openWires (position + 1)
      = sigma (natListGetAt baseState.openWires (position + 1)) := by
    rw [posSim.openMap]
    exact natListGetAt_map_inRange sigma baseState.openWires (position + 1)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowInRange)
  have afterWires := arcComponentShiftCorr_correspondingJoin sigma legLeft legRight
    baseState.links shiftedState.links baseForest shiftedForest corr
    (natListGetAt baseState.openWires position)
    (natListGetAt baseState.openWires (position + 1))
  have afterEvent := arcComponentShiftCorr_correspondingJoin sigma legLeft legRight
    (unionFindJoin baseState.links (natListGetAt baseState.openWires position)
      (natListGetAt baseState.openWires (position + 1)))
    (unionFindJoin shiftedState.links (sigma (natListGetAt baseState.openWires position))
      (sigma (natListGetAt baseState.openWires (position + 1))))
    (isUnionFindForest_unionFindJoin baseState.links
      (natListGetAt baseState.openWires position)
      (natListGetAt baseState.openWires (position + 1)) baseForest)
    (isUnionFindForest_unionFindJoin shiftedState.links
      (sigma (natListGetAt baseState.openWires position))
      (sigma (natListGetAt baseState.openWires (position + 1))) shiftedForest)
    afterWires baseState.nextFresh (natListGetAt baseState.openWires position)
  show ArcComponentShiftCorr sigma legLeft legRight
    (unionFindJoin
      (unionFindJoin baseState.links (natListGetAt baseState.openWires position)
        (natListGetAt baseState.openWires (position + 1)))
      baseState.nextFresh (natListGetAt baseState.openWires position))
    (unionFindJoin
      (unionFindJoin shiftedState.links (natListGetAt shiftedState.openWires position)
        (natListGetAt shiftedState.openWires (position + 1)))
      shiftedState.nextFresh (natListGetAt shiftedState.openWires position))
  rw [leftWireReads, rightWireReads, ← shiftEvent]
  exact afterEvent

/-- **One boundary-tracked cup/cap atom preserves the component-leg invariant.**  The arity
disjunction picks the branch; the cap's window bound comes from the tracking premise. -/
theorem arcComponentShiftCorr_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (legLeft legRight : Nat)
    (baseState shiftedState : ArcWireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (tracksEntry : baseState.openWires.length = atom.domBoundaryLength)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (posSim : ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState)
    (baseForest : isUnionFindForest baseState.links)
    (shiftedForest : isUnionFindForest shiftedState.links)
    (corr : ArcComponentShiftCorr sigma legLeft legRight
      baseState.links shiftedState.links) :
    ArcComponentShiftCorr sigma legLeft legRight
      (stepArcAtom baseState atom).links (stepArcAtom shiftedState atom).links := by
  have entryShape : baseState.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases arity with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc baseState atom cupArity.1 cupArity.2,
        stepArcAtom_eq_stepCupArc shiftedState atom cupArity.1 cupArity.2]
      exact arcComponentShiftCorr_stepCupArc sigma delta threshold
        headCupEvents headCapEvents legLeft legRight baseState shiftedState
        atom.leftContext.length sigmaShiftsAboveThreshold posSim
        baseForest shiftedForest corr
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have windowInRange : atom.leftContext.length + 2 ≤ baseState.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc baseState atom hasCapDomArity hasCapCodArity,
        stepArcAtom_eq_stepCapArc shiftedState atom hasCapDomArity hasCapCodArity]
      exact arcComponentShiftCorr_stepCapArc sigma delta threshold
        headCupEvents headCapEvents legLeft legRight baseState shiftedState
        atom.leftContext.length windowInRange sigmaShiftsAboveThreshold posSim
        baseForest shiftedForest corr

/-! ## Honesty marker -/

/-- **Honesty marker — the component leg STEPS with the arc fold (peel campaign H, rung 2b).**
Cup and cap steps preserve `ArcComponentShiftCorr` (two corresponding joins each; the cap's
consumed-wire reads correspond through `openMap` in range), and the boundary-tracked per-atom
dispatch picks the branch.  What this marker does NOT claim: the whole-spine FOLD (threading
the positional sim, both forests, tracking, and chainedness together), the seed instantiation,
and the extract correspondence.  `= true`. -/
def fxMode_hasArcComponentShiftStep : Bool := true

end FX1Poly.Polygraph
