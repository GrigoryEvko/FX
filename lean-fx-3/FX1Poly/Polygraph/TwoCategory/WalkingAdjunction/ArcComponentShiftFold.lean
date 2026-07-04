import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftStep

/-! # ArcComponentShiftFold — the component leg folds over every chained adjunction spine

The whole-spine fold for the head-cancellation component invariant: a boundary-chained
walking-adjunction spine, fired from any pair of states related by the positional shift
simulation and the component-leg correspondence (both links forests), keeps the correspondence
at every step and hence at the fold's output.  Five invariants thread alongside through their
per-step lemmas — the positional simulation (`arcPositionalShiftSim_stepArcAtom`), both
forests (`isUnionFindForest_stepArcAtom_ofCupOrCap`), boundary tracking
(`stepArcAtom_openWires_tracksBoundary`), and chainedness (`spineBoundaryChained_tail`) —
while the correspondence itself steps by `arcComponentShiftCorr_stepArcAtom`.

The final positional simulation is NOT re-exported here: it is separately available from
`arcPositionalShiftSim_processArcSpine`, which needs none of the threading.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The component-leg correspondence folds over every boundary-chained walking-adjunction
spine.**  Chainedness feeds the boundary tracking that discharges each cap step's in-range
window; the positional simulation and both forests re-derive themselves per step. -/
theorem arcComponentShiftCorr_processArcSpine
    {overallSource overallTarget : adjunctionGraph.Mode}
    (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (legLeft legRight : Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta) :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (baseState shiftedState : ArcWireState) → (boundaryLength : Nat) →
    baseState.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState →
    isUnionFindForest baseState.links →
    isUnionFindForest shiftedState.links →
    ArcComponentShiftCorr sigma legLeft legRight baseState.links shiftedState.links →
    ArcComponentShiftCorr sigma legLeft legRight
      (processArcSpine baseState atoms).links (processArcSpine shiftedState atoms).links
  | [], _, _, _, _, _, _, _, _, corr => corr
  | headAtom :: restAtoms, baseState, shiftedState, _, tracks, chained, posSim,
      baseForest, shiftedForest, corr => by
    obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
    have tracksEntry : baseState.openWires.length = headAtom.domBoundaryLength :=
      tracks.trans headFires.symm
    have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
    show ArcComponentShiftCorr sigma legLeft legRight
      (processArcSpine (stepArcAtom baseState headAtom) restAtoms).links
      (processArcSpine (stepArcAtom shiftedState headAtom) restAtoms).links
    exact arcComponentShiftCorr_processArcSpine sigma delta threshold
      headCupEvents headCapEvents legLeft legRight sigmaShiftsAboveThreshold restAtoms
      (stepArcAtom baseState headAtom) (stepArcAtom shiftedState headAtom)
      headAtom.codBoundaryLength
      (stepArcAtom_openWires_tracksBoundary baseState headAtom headArity tracksEntry)
      tailChained
      (arcPositionalShiftSim_stepArcAtom sigma delta threshold headCupEvents headCapEvents
        baseState shiftedState headAtom headArity sigmaShiftsAboveThreshold posSim)
      (isUnionFindForest_stepArcAtom_ofCupOrCap baseState headAtom headArity baseForest)
      (isUnionFindForest_stepArcAtom_ofCupOrCap shiftedState headAtom headArity
        shiftedForest)
      (arcComponentShiftCorr_stepArcAtom sigma delta threshold headCupEvents headCapEvents
        legLeft legRight baseState shiftedState headAtom headArity tracksEntry
        sigmaShiftsAboveThreshold posSim baseForest shiftedForest corr)

/-! ## Honesty marker -/

/-- **Honesty marker — the component leg FOLDS with the whole chained spine (peel campaign H,
rung 2c).**  `arcComponentShiftCorr_processArcSpine`: the correspondence survives every
boundary-chained walking-adjunction spine, with the positional simulation, both forests,
boundary tracking, and chainedness threaded per step.  What this marker does NOT claim: the
concrete seed instantiation (the piecewise head reindex and the seed correspondence at the
head pair's initial states) and the extract correspondence the cancellation consumes.
`= true`. -/
def fxMode_hasArcComponentShiftFold : Bool := true

end FX1Poly.Polygraph
