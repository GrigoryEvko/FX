import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationFormerCorpus

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationFormerCorpus

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationFormerCorpus`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- One closed strong-normalization witness per raw former family, plus two nested compositional witnesses
-- (closures compose with correct de Bruijn scope threading through the under-binder slots).  Each exercises
-- one Step.from_<former> congruence injection on a concrete cell.
#assert_no_axioms FX1Poly.Core.smoke_lam_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_pathLam_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_diffLambda_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_natSucc_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_optionSome_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_eitherInl_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_eitherInr_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_refl_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_modIntro_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_pair_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_listCons_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_glueIntro_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_arrowCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_productCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_sumCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_eitherCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_equivCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_piTyCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_sigmaTyCode_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_polyFunctor_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_nestedLamNatSucc_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_nestedPiSigma_isStronglyNormalizing

-- Modal core + universe-mode bridge family (congruence-only operators): one closed SN witness per
-- operator, so a regression in any single congruence closure fails its own gated witness.
#assert_no_axioms FX1Poly.Core.smoke_modElim_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_subsume_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_liftInnerToOuter_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_lowerOuterToInner_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.smoke_modElimLiftInnerToOuter_isStronglyNormalizing

end FX1PolyAudit
