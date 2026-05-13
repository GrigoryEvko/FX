import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.VarShape

Tait reducibility — variable-shape strong-normalization gates.

Covers the `of_progress_closure` family + the var-shape SN
lemmas for every eliminator (`app_var`, `fst_var`, `snd_var`,
`boolElim_var`, `natElim_var`, `natRec_var`, `listElim_var`,
`optionMatch_var`, `eitherMatch_var`, `pathApp_var`,
`equivApp_var`, `idJ_var`, `oeqJ_var`, `idStrictRec_var`,
`modElim_var`, `glueElim_var`, `hcomp_var`, `transp_var`,
`refineElim_var`, `recordProj_var`, `codataDest_var`) and the
matching `Reducible.X_of_varShape` headlines for piTy/id/oeq/idStrict.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms RawTerm.modIntro_inner_isStronglyNormalizing
#print axioms RawTerm.isStronglyNormalizing.of_progress_closure
#print axioms Term.isStronglyNormalizing.of_raw_progress_closure
#print axioms RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
#print axioms Term.isStronglyNormalizing_of_neutral_progress_closure
#print axioms RawTerm.var_isStronglyNormalizing
#print axioms RawTerm.app_var_isStronglyNormalizing
#print axioms RawTerm.fst_var_isStronglyNormalizing
#print axioms RawTerm.snd_var_isStronglyNormalizing
#print axioms RawTerm.boolElim_var_isStronglyNormalizing
#print axioms RawTerm.natElim_var_isStronglyNormalizing
#print axioms RawTerm.natRec_var_isStronglyNormalizing
#print axioms RawTerm.listElim_var_isStronglyNormalizing
#print axioms RawTerm.optionMatch_var_isStronglyNormalizing
#print axioms RawTerm.eitherMatch_var_isStronglyNormalizing
#print axioms RawTerm.pathApp_var_isStronglyNormalizing
#print axioms RawTerm.equivApp_var_isStronglyNormalizing
#print axioms RawTerm.idJ_var_isStronglyNormalizing
#print axioms RawTerm.oeqJ_var_isStronglyNormalizing
#print axioms RawTerm.oeqJ_isStronglyNormalizing
#print axioms RawTerm.idJ_isStronglyNormalizing
#print axioms RawTerm.idStrictRec_var_isStronglyNormalizing
#print axioms RawTerm.idStrictRec_isStronglyNormalizing
#print axioms RawTerm.modElim_var_isStronglyNormalizing
#print axioms RawTerm.glueElim_var_isStronglyNormalizing
#print axioms RawTerm.hcomp_var_isStronglyNormalizing
#print axioms RawTerm.transp_var_isStronglyNormalizing
#print axioms Reducible.piTy_of_varShape
#print axioms Reducible.id_of_varShape
#print axioms Reducible.oeq_of_varShape
#print axioms Reducible.idStrict_of_varShape
#print axioms RawTerm.refineElim_var_isStronglyNormalizing
#print axioms RawTerm.recordProj_var_isStronglyNormalizing
#print axioms RawTerm.codataDest_var_isStronglyNormalizing

end LeanFX2.Smoke
