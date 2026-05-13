import LeanFX2.Reducibility

/-! # LeanFX2.Smoke.AuditReducibility.Base

Tait reducibility — base predicates and closed-leaf arms.

Covers `RawStep.parProgress`, `RawTerm.isStronglyNormalizing`,
`Term.isStronglyNormalizing`, the `Reducible` def itself,
closed-leaf arms (`unit`/`bool`/`nat`/`empty`/`interval`/
`universe`/`tyVar`/`session`/`effect`/`modal`),
`ReducibleSubst`, and the nullary-introducer fundamental cases
(`var`, `unit`, `boolTrue`, `boolFalse`, `natZero` and their
_stable variants).

## Root status

Layer S smoke audit log.  Pre-merge gating. -/

namespace LeanFX2.Smoke

open LeanFX2

#print axioms RawStep.parProgress
#print axioms RawTerm.isStronglyNormalizing
#print axioms Term.isStronglyNormalizing
#print axioms Reducible
#print axioms Reducible.isStronglyNormalizing
#print axioms Reducible.unit_of_isStronglyNormalizing
#print axioms Reducible.bool_of_isStronglyNormalizing
#print axioms Reducible.nat_of_isStronglyNormalizing
#print axioms Reducible.empty_of_isStronglyNormalizing
#print axioms Reducible.interval_of_isStronglyNormalizing
#print axioms Reducible.universe_of_isStronglyNormalizing
#print axioms Reducible.tyVar_of_isStronglyNormalizing
#print axioms Reducible.session_of_isStronglyNormalizing
#print axioms Reducible.effect_of_isStronglyNormalizing
#print axioms Reducible.modal_of_isStronglyNormalizing
#print axioms ReducibleSubst
#print axioms Reducible.fundamental_var
#print axioms RawTerm.unit_isStronglyNormalizing
#print axioms RawTerm.boolTrue_isStronglyNormalizing
#print axioms RawTerm.boolFalse_isStronglyNormalizing
#print axioms RawTerm.natZero_isStronglyNormalizing
#print axioms Reducible.fundamental_unit
#print axioms Reducible.fundamental_boolTrue
#print axioms Reducible.fundamental_boolFalse
#print axioms Reducible.fundamental_natZero
#print axioms Reducible.fundamental_unit_stable
#print axioms Reducible.fundamental_boolTrue_stable
#print axioms Reducible.fundamental_boolFalse_stable
#print axioms Reducible.fundamental_natZero_stable
#print axioms RawTerm.lam_isStronglyNormalizing
#print axioms Term.lam_isStronglyNormalizing
#print axioms Term.lamPi_isStronglyNormalizing
#print axioms RawTerm.isStronglyNormalizing.step_preserves
#print axioms RawTerm.isStronglyNormalizing_weaken
#print axioms Term.isStronglyNormalizing_weaken
#print axioms Reducible.weaken_isStronglyNormalizing
#print axioms IsRenamingStableReducible
#print axioms IsRenamingStableReducible.weaken
#print axioms IsRenamingStableReducible.of_varShape
#print axioms IsRenamingStableReducible.of_unitShape
#print axioms IsRenamingStableReducible.of_boolTrueShape
#print axioms IsRenamingStableReducible.of_boolFalseShape
#print axioms IsRenamingStableReducible.of_natZeroShape
#print axioms TermRenaming.dropWeaken
#print axioms TermRenaming.compose
#print axioms Term.rename_type_eq_symm_cast_HEq
#print axioms Term.rename_type_eq_cast_HEq
#print axioms Term.type_eq_symm_cast_HEq
#print axioms Term.rename_raw_type_eq_symm_cast_HEq
#print axioms Term.raw_type_eq_symm_cast_HEq
#print axioms IsRenamingStableReducibleSubst
#print axioms IsRenamingStableReducibleSubst.weaken_position

end LeanFX2.Smoke
