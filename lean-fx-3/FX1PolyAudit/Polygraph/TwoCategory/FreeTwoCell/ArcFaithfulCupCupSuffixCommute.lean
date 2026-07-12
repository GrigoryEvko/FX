import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCupCupSuffixCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCupCupSuffixCommute — zero-axiom gate

Per-declaration zero-axiom gate for the spine-level cup-cup extract corollary over the FAITHFUL engine:
the partition-level crossing step `arcPartitionSim_stepCrossArc` (the corrected `2 -> 2` crossing preserves
`ArcPartitionSim` in window, `openMap` via `natListSwapTwoAt_map` and every other field the input `sim`'s
own), the faithful per-atom dispatcher `arcPartitionSim_stepArcAtomFaithful`, the running-state admissibility
predicate `SpineAdmissibleFaithful`, THE SUFFIX FOLD `arcPartitionSim_processArcSpineFaithful`, the
unconditional faithful event-length accounting (`stepArcAtomFaithful_cupEventNodes_length` / `_cap...` and
their folds), the assembly `extractArc_eq_rest_faithful_of_swapCorePackage`, THE DELIVERY
`arcFaithfulCupCupSuffixExtractCommute`, the concrete non-vacuity + refl-failure probe, and the honesty
marker + pins.

The file flips ONLY its own marker `fxMode_hasArcFaithfulCupCupSuffixCommute := true`; the permanent
keystone pins `fxMode_hasArcPeelGeneralSignature`, `fxMode_hasArcGodementSamePartitionFreshProof` and
`fxMode_hasArcGodementSwapRenameableProof2` stay `false` (re-asserted by `rfl`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- K1.a/K1.b — the partition-level crossing step + the faithful per-atom dispatcher
#assert_no_axioms FX1Poly.Polygraph.arcPartitionSim_stepCrossArc
#assert_no_axioms FX1Poly.Polygraph.arcPartitionSim_stepArcAtomFaithful

-- the running-state admissibility predicate + THE SUFFIX FOLD
#assert_no_axioms FX1Poly.Polygraph.SpineAdmissibleFaithful
#assert_no_axioms FX1Poly.Polygraph.arcPartitionSim_processArcSpineFaithful

-- K1.d — the faithful event-length accounting (per-step + folds)
#assert_no_axioms FX1Poly.Polygraph.stepArcAtomFaithful_cupEventNodes_length
#assert_no_axioms FX1Poly.Polygraph.stepArcAtomFaithful_capEventNodes_length
#assert_no_axioms FX1Poly.Polygraph.processArcSpineFaithful_cupEventNodes_length
#assert_no_axioms FX1Poly.Polygraph.processArcSpineFaithful_capEventNodes_length

-- K1.e — the assembly + the cup-cup delivery
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_rest_faithful_of_swapCorePackage
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixExtractCommute

-- non-vacuity + refl-failure probe
#assert_no_axioms FX1Poly.Polygraph.cupCupSuffixProbeSeed
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_nonvacuous
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_statesDiffer

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulCupCupSuffixCommute
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_swapRenameableProof2_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.arcPartitionSim_stepCrossArc
#print axioms FX1Poly.Polygraph.arcPartitionSim_stepArcAtomFaithful
#print axioms FX1Poly.Polygraph.SpineAdmissibleFaithful
#print axioms FX1Poly.Polygraph.arcPartitionSim_processArcSpineFaithful
#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_cupEventNodes_length
#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_capEventNodes_length
#print axioms FX1Poly.Polygraph.processArcSpineFaithful_cupEventNodes_length
#print axioms FX1Poly.Polygraph.processArcSpineFaithful_capEventNodes_length
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_faithful_of_swapCorePackage
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixExtractCommute
#print axioms FX1Poly.Polygraph.cupCupSuffixProbeSeed
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_nonvacuous
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_statesDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulCupCupSuffixCommute
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_swapRenameableProof2_stays_false

end FX1PolyAudit
