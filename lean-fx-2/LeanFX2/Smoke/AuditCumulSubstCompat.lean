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
-- `rename_compatible_boolElim_benton` deferred during codex's
-- dependent-eliminator refactor of `Term.boolElim`; see
-- `Reduction/CumulBenton.lean` for context.

-- Binder cong arms (2)
#print axioms LeanFX2.ConvCumul.rename_compatible_lam_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_lamPi_benton

-- Allais binder arms (lam + lamPi)
#print axioms LeanFX2.ConvCumul.subst_compatible_lam_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_lamPi_allais

-- Allais eliminator arms (5 — kernel-gap closed via natElimCong / natRecCong /
-- listElimCong / optionMatchCong / eitherMatchCong added to ConvCumul)
#print axioms LeanFX2.ConvCumul.subst_compatible_natElim_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_natRec_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_listElim_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_optionMatch_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_eitherMatch_allais

-- Benton eliminator rename arms (5)
#print axioms LeanFX2.ConvCumul.rename_compatible_natElim_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_natRec_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_listElim_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_optionMatch_benton
#print axioms LeanFX2.ConvCumul.rename_compatible_eitherMatch_benton

-- Pattern 3 (Allais paired-env) Homo-typed compat + lift (5)
#print axioms LeanFX2.TermSubstHet.PointwiseCompatHomo.refl
#print axioms LeanFX2.TermSubstHet.PointwiseCompatHomo.sym
#print axioms LeanFX2.TermSubstHet.PointwiseCompatHomo.trans
#print axioms LeanFX2.TermSubstHet.PointwiseCompatHomo.toPointwiseCompat
#print axioms LeanFX2.TermSubstHet.PointwiseCompatHomo.lift

-- Pattern 3 fundamental lemma — Term-induction with per-arm dispatch (1)
#print axioms LeanFX2.Term.subst_compatible_pointwise_allais

-- Pattern 3 fundamental headline — Allais sim at identity simulation (1)
#print axioms LeanFX2.ConvCumul.subst_compatible_paired_allais

-- BHKM cast-elim independent (1)
#print axioms LeanFX2.ConvCumul.cast_eq_indep_benton

-- Pattern 3 FULL HEADLINE at homogeneous level (1)
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_paired_allais

-- CUMUL-1.7 entry point — unified ConvCumul.subst_compatible (1)
#print axioms LeanFX2.ConvCumul.subst_compatible
