import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.Subst0RenameCommute

/-! # AuditTerm.StrengthT8 — strength-T8 subst/rename fusion gates.

Per-declaration zero-axiom gates for the strength-T8 chain:

* the typed-Term rename functoriality substrate (`Term.rename_rename`,
  `Term.rename_pointwise_HEq`, `Term.rename_weaken_commute`, the lifted
  rename-compose helpers, the rename targetCtx cast);
* the typed-Term subst substrate (`Term.subst_pointwise_HEq`,
  `Term.subst_targetCtx_cast_HEq`, the lift/targetCtx entry HEq bridges
  and the effect-signature pointwise lemma the binder arms consume);
* the ScR engine `Term.subst_rename_commute` (78-arm) + its three binder arms
  + support lifts + the renameOutput-lift binder entry lemma;
* the RcS engine `Term.rename_subst_commute` (78-arm) + its three binder arms
  + support lifts + the precomposeRenaming-lift binder entry lemma;
* the T8 headline `Term.subst0_rename_commute` (#1964) + its singleton bridges.

`Subst0RenameCommute` transitively imports the ScR engine (`SubstRenameCommute`),
the RcS engine (`RenameSubstCommute`), and the substrate, so this single gate file
brings the whole strength-T8 graph into the `LeanFX2Audit` import closure. -/

namespace LeanFX2.Tools

-- Substrate: typed-Term rename functoriality + pointwise bridge.
#assert_no_axioms LeanFX2.RawTerm.rename_compose_lift
#assert_no_axioms LeanFX2.Ty.rename_compose_lift
#assert_no_axioms LeanFX2.Term.rename_rename
#assert_no_axioms LeanFX2.Term.rename_targetCtx_cast_HEq
#assert_no_axioms LeanFX2.Term.rename_pointwise_HEq
#assert_no_axioms LeanFX2.Term.rename_weaken_commute

-- Substrate: typed-Term subst pointwise + targetCtx-cast bridges (the
-- heterogeneous-congruence substrate the ScR/RcS binder arms consume).
#assert_no_axioms LeanFX2.TermSubst.lift_pointwise_HEq
#assert_no_axioms LeanFX2.TermSubst.targetCtx_cast_entry_HEq
#assert_no_axioms LeanFX2.Term.subst_targetCtx_cast_HEq
#assert_no_axioms LeanFX2.Effects.OperationSignature.map_subst_pointwise
#assert_no_axioms LeanFX2.Term.effectPerform_HEq_congr_subst
#assert_no_axioms LeanFX2.Term.subst_pointwise_HEq

-- ScR binder entry lemma + binder arms + 78-arm engine.
#assert_no_axioms LeanFX2.TermSubst.lift_renameOutput_entry_HEq
#assert_no_axioms LeanFX2.TermSubst.renameOutput_lift_entry_HEq
#assert_no_axioms LeanFX2.Ty.subst_rename_commute_lift
#assert_no_axioms LeanFX2.RawTerm.subst_rename_commute_lift
#assert_no_axioms LeanFX2.Effects.OperationSignature.map_subst_rename_commute
#assert_no_axioms LeanFX2.Term.subst_rename_commute_lamPi
#assert_no_axioms LeanFX2.Term.subst_rename_commute_lam
#assert_no_axioms LeanFX2.Term.subst_rename_commute_pathLam
#assert_no_axioms LeanFX2.Term.subst_rename_commute

-- RcS binder entry lemmas + binder arms + 78-arm engine.
#assert_no_axioms LeanFX2.TermSubst.lift_precompose_entry_HEq
#assert_no_axioms LeanFX2.TermSubst.precomposeRenaming_lift_entry_HEq
#assert_no_axioms LeanFX2.Ty.rename_subst_commute_lift
#assert_no_axioms LeanFX2.RawTerm.rename_subst_commute_lift
#assert_no_axioms LeanFX2.Effects.OperationSignature.map_rename_subst_commute
#assert_no_axioms LeanFX2.Term.rename_subst_commute_lamPi
#assert_no_axioms LeanFX2.Term.rename_subst_commute_lam
#assert_no_axioms LeanFX2.Term.rename_subst_commute_pathLam
#assert_no_axioms LeanFX2.Term.rename_subst_commute

-- T8 headline + singleton bridges.
#assert_no_axioms LeanFX2.Term.singleton_renameOutput_lift_entry_HEq
#assert_no_axioms LeanFX2.Term.singleton_renameOutput_precompose_entry_HEq
#assert_no_axioms LeanFX2.Term.subst0_rename_commute

end LeanFX2.Tools
