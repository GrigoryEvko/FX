import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderCapCapClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderCapCapClosure — zero-axiom gate

Per-declaration zero-axiom gate for the CAP x CAP faithful reorder sibling closure (r20): the port
`arcFaithfulCapCapSuffixExtractCommute`, the sibling relation `FaithfulReorderEquivWithCapCap`
(`ofR19` / `ofCapCapSwap` / `symm` / `trans`), the cap-cap smart constructor, the embedding
`reorderWithCapCap_of_faithfulReorder`, THE EXTENDED CLOSURE THEOREM
`extractArc_eq_of_faithfulReorderEquivWithCapCap`, the four-partition-family fires + refl-failure probes + the
MIXED witness, and the honesty marker + the three permanent pins.

The file flips ONLY its own NEW marker `fxMode_hasArcFaithfulReorderCapCapExtractInvariance := true`; the
r19 marker `fxMode_hasArcFaithfulReorderExtractInvariance` is untouched, and the permanent keystone pins
`fxMode_hasArcPeelGeneralSignature`, `fxMode_hasArcGodementSamePartitionFreshProof` and
`fxMode_hasArcGodementSwapRenameableProof2` stay `false` (re-asserted by `rfl`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the port
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCapCapSuffixExtractCommute

-- the sibling relation + smart constructor + embedding
#assert_no_axioms FX1Poly.Polygraph.FaithfulReorderEquivWithCapCap
#assert_no_axioms FX1Poly.Polygraph.faithfulReorder_ofCapCap
#assert_no_axioms FX1Poly.Polygraph.reorderWithCapCap_of_faithfulReorder

-- THE EXTENDED CLOSURE THEOREM
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulReorderEquivWithCapCap

-- non-vacuity — all four partition-swap families + the MIXED witness + refl-failure probes
#assert_no_axioms FX1Poly.Polygraph.capCapReorder_witness
#assert_no_axioms FX1Poly.Polygraph.capCapReorder_extractEq
#assert_no_axioms FX1Poly.Polygraph.capCapReorder_statesDiffer
#assert_no_axioms FX1Poly.Polygraph.cupCupReorder_extractEq
#assert_no_axioms FX1Poly.Polygraph.cupCupReorder_statesDiffer
#assert_no_axioms FX1Poly.Polygraph.cupCapSuffixExtractCommute
#assert_no_axioms FX1Poly.Polygraph.cupCapSuffix_statesDiffer
#assert_no_axioms FX1Poly.Polygraph.capCupSuffixExtractCommute
#assert_no_axioms FX1Poly.Polygraph.capCupSuffix_statesDiffer
#assert_no_axioms FX1Poly.Polygraph.mixedCapCapReorderWitness
#assert_no_axioms FX1Poly.Polygraph.mixedCapCapReorder_extractEq
#assert_no_axioms FX1Poly.Polygraph.mixedCapCapReorder_statesDiffer

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulReorderCapCapExtractInvariance
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_swapRenameableProof2_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.arcFaithfulCapCapSuffixExtractCommute
#print axioms FX1Poly.Polygraph.FaithfulReorderEquivWithCapCap
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCapCap
#print axioms FX1Poly.Polygraph.reorderWithCapCap_of_faithfulReorder
#print axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulReorderEquivWithCapCap
#print axioms FX1Poly.Polygraph.capCapReorder_witness
#print axioms FX1Poly.Polygraph.capCapReorder_extractEq
#print axioms FX1Poly.Polygraph.capCapReorder_statesDiffer
#print axioms FX1Poly.Polygraph.cupCupReorder_extractEq
#print axioms FX1Poly.Polygraph.cupCupReorder_statesDiffer
#print axioms FX1Poly.Polygraph.cupCapSuffixExtractCommute
#print axioms FX1Poly.Polygraph.cupCapSuffix_statesDiffer
#print axioms FX1Poly.Polygraph.capCupSuffixExtractCommute
#print axioms FX1Poly.Polygraph.capCupSuffix_statesDiffer
#print axioms FX1Poly.Polygraph.mixedCapCapReorderWitness
#print axioms FX1Poly.Polygraph.mixedCapCapReorder_extractEq
#print axioms FX1Poly.Polygraph.mixedCapCapReorder_statesDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulReorderCapCapExtractInvariance
#print axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_swapRenameableProof2_stays_false

end FX1PolyAudit
