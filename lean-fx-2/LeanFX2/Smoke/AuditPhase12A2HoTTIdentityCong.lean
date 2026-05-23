import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.Observational

-- ι rule: J on refl reduces to baseCase (identity-type computation rule)
#print axioms LeanFX2.Step.idJ_refl
#print axioms LeanFX2.Conv.idJ_refl_baseCase

#print axioms LeanFX2.StepStar.idJ_baseCase_lift_isClosedTy_general
#print axioms LeanFX2.StepStar.idJ_baseCase_lift_isClosedTy
#print axioms LeanFX2.Conv.idJ_baseCase_cong_isClosedTy
#print axioms LeanFX2.StepStar.idJ_baseCase_lift_unit
#print axioms LeanFX2.StepStar.idJ_baseCase_lift_bool
#print axioms LeanFX2.StepStar.idJ_baseCase_lift_nat
#print axioms LeanFX2.Conv.idJ_baseCase_cong_unit
#print axioms LeanFX2.Conv.idJ_baseCase_cong_bool
#print axioms LeanFX2.Conv.idJ_baseCase_cong_nat

-- Observational-equality eliminator family (HoTT/Observational.lean)
#print axioms LeanFX2.OEq.refl
#print axioms LeanFX2.OEq.sym
#print axioms LeanFX2.OEq.trans
#print axioms LeanFX2.OEq.cong
#print axioms LeanFX2.OEq.cong2
#print axioms LeanFX2.OEq.transport
#print axioms LeanFX2.OEq.subst
#print axioms LeanFX2.OEqDecomposeProd.to_components
#print axioms LeanFX2.OEqDecomposeProd.from_components
#print axioms LeanFX2.OEqDecomposeSum.inl_components
#print axioms LeanFX2.OEqDecomposeSum.inr_components
#print axioms LeanFX2.OEqDecomposeSum.inl_inr_impossible
#print axioms LeanFX2.OEqDecomposePiSetWise.to_pointwise
#print axioms LeanFX2.OEqUIP.uip_set
#print axioms LeanFX2.OEqType.to_equiv
