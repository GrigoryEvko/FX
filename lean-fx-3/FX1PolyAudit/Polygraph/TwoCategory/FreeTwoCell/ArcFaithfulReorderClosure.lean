import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderClosure — zero-axiom gate

Per-declaration zero-axiom gate for the FAITHFUL reorder closure and its extract invariance (r19 keystone):
the equivalence relation `FaithfulReorderEquiv`, the six smart constructors (`faithfulReorder_of{CrossCross,
CupCross,CrossCup,CapCross,CrossCap,CupCup}`), THE CLOSURE THEOREM `extractArc_eq_of_faithfulReorderEquiv`,
the two per-arm single-step extract corollaries, the non-vacuity MIXED reorder witness + closure firing +
refl-failure probe + the genuine literal node, and the honesty marker + the three permanent pins.

The file flips ONLY its own marker `fxMode_hasArcFaithfulReorderExtractInvariance := true`; the permanent
keystone pins `fxMode_hasArcPeelGeneralSignature`, `fxMode_hasArcGodementSamePartitionFreshProof` and
`fxMode_hasArcGodementSwapRenameableProof2` stay `false` (re-asserted by `rfl`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- K2a — the reorder equivalence relation
#assert_no_axioms FX1Poly.Polygraph.FaithfulReorderEquiv

-- K2b — the six smart constructors
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCross
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCupCross
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCup
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCapCross
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCap
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCupCup

-- K2c — THE CLOSURE THEOREM
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulReorderEquiv

-- K2b (explicit) — the per-arm single-step extract corollaries
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_ofCrossCrossReorderStep
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_ofCupCupReorderStep

-- non-vacuity — the genuine literal node, the MIXED witness, the closure firing, the refl-failure probe
#assert_no_axioms FX1Poly.Polygraph.literalCrossReorder_witness
#assert_no_axioms FX1Poly.Polygraph.mixedReorderWitness
#assert_no_axioms FX1Poly.Polygraph.mixedReorder_extractEq
#assert_no_axioms FX1Poly.Polygraph.mixedReorder_statesDiffer

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulReorderExtractInvariance
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_swapRenameableProof2_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.FaithfulReorderEquiv
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCross
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCupCross
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCup
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCapCross
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCap
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCupCup
#print axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulReorderEquiv
#print axioms FX1Poly.Polygraph.extractArc_eq_ofCrossCrossReorderStep
#print axioms FX1Poly.Polygraph.extractArc_eq_ofCupCupReorderStep
#print axioms FX1Poly.Polygraph.literalCrossReorder_witness
#print axioms FX1Poly.Polygraph.mixedReorderWitness
#print axioms FX1Poly.Polygraph.mixedReorder_extractEq
#print axioms FX1Poly.Polygraph.mixedReorder_statesDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulReorderExtractInvariance
#print axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_swapRenameableProof2_stays_false

end FX1PolyAudit
