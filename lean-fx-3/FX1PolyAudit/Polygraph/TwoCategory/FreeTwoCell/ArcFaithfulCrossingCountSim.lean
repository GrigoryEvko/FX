import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCrossingCountSim

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCrossingCountSim — zero-axiom gate

Per-declaration zero-axiom gate for the faithful crossing count-simulation arm: the crossing reduction
`stepArcAtomFaithful_eq_stepCrossArc_of_crossArity`, the third-arm step-stability `arcStepSimCount_stepCrossArc`
(the corrected `2 -> 2` crossing preserves the LIVE `ArcStepSimCount` invariant in window, `openMap` via
`natListSwapTwoAt_map` and every other field the input `sim`'s own), the faithful engine's per-atom dispatcher
`arcStepSimCountFaithful_step`, the extract consequences (`extractArc_eq_of_arcStepSimCount`,
`sameArcPartition_stepCrossArc_of_arcStepSimCount`, `extractArc_stepCrossArc_eq_of_arcStepSimCount`), the concrete
non-vacuity witness, and the honesty marker + pins.

The file flips ONLY its own marker `fxMode_hasArcFaithfulCrossingCountSim := true`; the permanent keystone pins
`fxMode_hasArcPeelGeneralSignature`, `fxMode_hasArcGodementSamePartitionFreshProof` and
`fxMode_hasArcGodementSwapRenameableProof2` stay `false` (re-asserted by `rfl`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the crossing reduction + the third-arm count-simulation step + the per-atom dispatcher
#assert_no_axioms FX1Poly.Polygraph.stepArcAtomFaithful_eq_stepCrossArc_of_crossArity
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_stepCrossArc
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCountFaithful_step

-- the extract consequences
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_arcStepSimCount
#assert_no_axioms FX1Poly.Polygraph.sameArcPartition_stepCrossArc_of_arcStepSimCount
#assert_no_axioms FX1Poly.Polygraph.extractArc_stepCrossArc_eq_of_arcStepSimCount

-- the non-vacuity witness
#assert_no_axioms FX1Poly.Polygraph.crossingCountSimProbeState
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_nonvacuous

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulCrossingCountSim
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_swapRenameableProof2_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_eq_stepCrossArc_of_crossArity
#print axioms FX1Poly.Polygraph.arcStepSimCount_stepCrossArc
#print axioms FX1Poly.Polygraph.arcStepSimCountFaithful_step
#print axioms FX1Poly.Polygraph.extractArc_eq_of_arcStepSimCount
#print axioms FX1Poly.Polygraph.sameArcPartition_stepCrossArc_of_arcStepSimCount
#print axioms FX1Poly.Polygraph.extractArc_stepCrossArc_eq_of_arcStepSimCount
#print axioms FX1Poly.Polygraph.crossingCountSimProbeState
#print axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_nonvacuous
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulCrossingCountSim
#print axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulCrossingCountSim_swapRenameableProof2_stays_false

end FX1PolyAudit
