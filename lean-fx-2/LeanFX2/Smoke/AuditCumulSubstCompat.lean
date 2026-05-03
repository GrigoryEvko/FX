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

-- BHKM cast-elim primitives (3)
#print axioms LeanFX2.ConvCumul.cast_eq_left_benton
#print axioms LeanFX2.ConvCumul.cast_eq_right_benton
#print axioms LeanFX2.ConvCumul.cast_eq_both_benton

-- Allais cast-aware single-subterm arm (1)
#print axioms LeanFX2.ConvCumul.subst_compatible_snd_allais

-- Allais multi-subterm cong arms (6: 4 cast-free + 2 cast-aware)
#print axioms LeanFX2.ConvCumul.subst_compatible_app_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_listCons_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_idJ_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_boolElim_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_appPi_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_pair_allais

-- Allais cumul-promotion arm (1)
#print axioms LeanFX2.ConvCumul.subst_compatible_cumulUp_allais

-- Benton rename per-Term-ctor helpers (Step A — 22 ctors, 5 eliminator gap)
-- Closed-payload arms (10)
#print axioms LeanFX2.ConvCumul.rename_compatible_unit_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_boolTrue_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_boolFalse_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_natZero_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_var_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_universeCode_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_listNil_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_optionNone_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_refl_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_cumulUp_benton

-- Single-subterm cong arms (9)
#print axioms LeanFX2.ConvCumul.rename_compatible_natSucc_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_optionSome_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_eitherInl_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_eitherInr_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_modIntro_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_modElim_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_subsume_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_fst_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_snd_benton

-- Multi-subterm cong arms (5)
#print axioms LeanFX2.ConvCumul.rename_compatible_app_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_appPi_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_pair_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_listCons_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_idJ_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_boolElim_benton

-- Binder cong arms (2)
#print axioms LeanFX2.ConvCumul.rename_compatible_lam_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_lamPi_benton
