import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify06

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Type.Level.LevelExprSimplify` (part 6 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.or_eq_false_imp_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.or_eq_false_imp_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.scaledPointEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.occursAsVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_scaledPointEnvironment_of_not_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_eq_left_of_right_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_eq_right_of_left_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.beq_false_of_ble_succ

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.allVariablesAtLeast_imp_not_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.offsetOf

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_scaledPointEnvironment_of_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.beq_self

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_cons_self

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_cons_of_beq_false

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_eq_none_of_allVariablesAtLeast

#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_antisymm

#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_succ_le_of_ble_false

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_pointwise_tail

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_ext

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_eq_none_of_not_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_eq_some_offsetOf_of_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denote_scaledPointEnvironment_of_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denote_scaledPointEnvironment_of_not_occurs

#assert_no_axioms FX1Poly.Universe.LevelExpr.add_left_cancel

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_of_denote_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalForm_unique

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_isStrictlySortedByVariable

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_baseConstant_eq_denote_zeroEnvironment

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv_iff_fullCanonicalize_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_idempotentDedup

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_leftUnitLzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_rightUnitLzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_commutativeMax

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_associativeMax

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_succDominatesVar

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_succAbsorbsBareVar

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_constantCollapse

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_succZeroDominates

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_nestedDedupReorder

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_threeVariableSort

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_constVarCommute

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_notDenoteEquiv_distinctVars

#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_notDenoteEquiv_varVsSucc

#assert_no_axioms FX1Poly.Universe.LevelExpr.predicativeSmokeCorpus

#assert_no_axioms FX1Poly.Universe.LevelExpr.predicativeSmokeCorpus_count

#assert_no_axioms FX1Poly.Universe.LevelExpr.predicativeSmokeCorpus_behavior

end FX1PolyAudit
