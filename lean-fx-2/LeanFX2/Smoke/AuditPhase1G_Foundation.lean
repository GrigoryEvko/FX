import LeanFX2.Foundation.Subst

/-! Phase 1.G.1 zero-axiom audit — identity + weaken-subst foundation lemmas. -/

-- Raw side
#print axioms LeanFX2.RawTermSubst.identity_lift_pointwise
#print axioms LeanFX2.RawTerm.subst_identity
#print axioms LeanFX2.RawTermSubst.weaken_then_singleton_pointwise
#print axioms LeanFX2.RawTerm.weaken_subst_singleton
#print axioms LeanFX2.RawTermSubst.weaken_lift_subst_pointwise
#print axioms LeanFX2.RawTerm.weaken_subst_commute

-- Ty side
#print axioms LeanFX2.Subst.identity_lift_forTy_pointwise
#print axioms LeanFX2.Subst.identity_lift_forRaw_pointwise
#print axioms LeanFX2.Ty.subst_identity
#print axioms LeanFX2.Subst.weaken_then_singleton_forTy_pointwise
#print axioms LeanFX2.Subst.weaken_then_singleton_forRaw_pointwise
#print axioms LeanFX2.Ty.weaken_subst_singleton
#print axioms LeanFX2.Subst.weaken_lift_forTy_pointwise
#print axioms LeanFX2.Subst.weaken_lift_forRaw_pointwise
#print axioms LeanFX2.Ty.weaken_subst_commute
