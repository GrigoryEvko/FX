import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.Weakening

Tait reducibility — RC weakening + renaming-stable infrastructure.

Covers `Reducible.weaken_*` for every closed-leaf and compound
arm, `IsRenamingStableReducible` + `IsRenamingStableReducibleSubst`,
the cast/HEq glue lemmas, the `pathApp`/`transp`/`hcomp` SN gates,
and the auxiliary `RawTerm.*_isStronglyNormalizing_aux` lemmas for
app/pair/optionSome/eitherInl/eitherInr/recordIntro/listCons.

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms Reducible.weaken_unit
#print axioms Reducible.weaken_bool
#print axioms Reducible.weaken_nat
#print axioms Reducible.weaken_empty
#print axioms Reducible.weaken_interval
#print axioms Reducible.weaken_universe
#print axioms Reducible.weaken_tyVar
#print axioms Reducible.weaken_session
#print axioms Reducible.weaken_effect
#print axioms Reducible.weaken_modal
#print axioms Reducible.weaken_sigmaTy
#print axioms Reducible.weaken_glue
#print axioms Reducible.weaken_refine
#print axioms Reducible.weaken_record
#print axioms Reducible.weaken_codata
#print axioms RawTerm.app_lam_isStronglyNormalizing
#print axioms RawTerm.pathApp_pathLam_isStronglyNormalizing
#print axioms Term.pathApp_pathLam_isStronglyNormalizing
#print axioms RawTerm.transp_pathLam_weaken_isStronglyNormalizing
#print axioms Term.transp_pathLam_weaken_isStronglyNormalizing
#print axioms RawTerm.transp_isStronglyNormalizing
#print axioms Term.transp_isStronglyNormalizing
#print axioms RawTerm.hcomp_isStronglyNormalizing
#print axioms Term.hcomp_isStronglyNormalizing
#print axioms RawTerm.app_function_isStronglyNormalizing_aux
#print axioms RawTerm.app_function_isStronglyNormalizing
#print axioms RawTerm.app_argument_isStronglyNormalizing_aux
#print axioms RawTerm.app_argument_isStronglyNormalizing
#print axioms RawTerm.pair_first_isStronglyNormalizing_aux
#print axioms RawTerm.pair_first_isStronglyNormalizing
#print axioms RawTerm.pair_second_isStronglyNormalizing_aux
#print axioms RawTerm.pair_second_isStronglyNormalizing
#print axioms RawTerm.optionSome_value_isStronglyNormalizing_aux
#print axioms RawTerm.optionSome_value_isStronglyNormalizing
#print axioms RawTerm.eitherInl_value_isStronglyNormalizing_aux
#print axioms RawTerm.eitherInl_value_isStronglyNormalizing
#print axioms RawTerm.eitherInr_value_isStronglyNormalizing_aux
#print axioms RawTerm.eitherInr_value_isStronglyNormalizing
#print axioms RawTerm.recordIntro_field_isStronglyNormalizing_aux
#print axioms RawTerm.recordIntro_field_isStronglyNormalizing
#print axioms RawTerm.listCons_head_isStronglyNormalizing_aux
#print axioms RawTerm.listCons_head_isStronglyNormalizing
#print axioms RawTerm.listCons_tail_isStronglyNormalizing_aux
#print axioms RawTerm.listCons_tail_isStronglyNormalizing

end LeanFX2.Smoke
