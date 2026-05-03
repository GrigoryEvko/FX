import LeanFX2.Reduction.CumulSubstCompat

/-! # AuditCumulSubstCompat — zero-axiom audit

`#print axioms` over every shipped Allais helper in
`Reduction/CumulSubstCompat.lean`.  All must report
"does not depend on any axioms" under strict policy.
-/

-- Allais paired-env predicate + combinators (4)
#print axioms LeanFX2.TermSubstHet.PointwiseCompat
#print axioms LeanFX2.TermSubstHet.PointwiseCompat.refl
#print axioms LeanFX2.TermSubstHet.PointwiseCompat.sym
#print axioms LeanFX2.TermSubstHet.PointwiseCompat.trans

-- Allais closed-payload arms (8)
#print axioms LeanFX2.ConvCumul.subst_compatible_unit_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_boolTrue_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_boolFalse_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_natZero_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_universeCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_listNil_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_optionNone_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_refl_allais

-- Allais var arm (1)
#print axioms LeanFX2.ConvCumul.subst_compatible_var_allais

-- Allais single-subterm cong arms (8)
#print axioms LeanFX2.ConvCumul.subst_compatible_natSucc_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_optionSome_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_eitherInl_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_eitherInr_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_modIntro_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_modElim_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_subsume_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_fst_allais

-- Allais multi-subterm cong arms (4)
#print axioms LeanFX2.ConvCumul.subst_compatible_app_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_listCons_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_idJ_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_boolElim_allais

-- Allais cumul-promotion arm (1)
#print axioms LeanFX2.ConvCumul.subst_compatible_cumulUp_allais
