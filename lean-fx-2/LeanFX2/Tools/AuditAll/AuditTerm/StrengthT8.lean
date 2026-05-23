import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.Subst0RenameCommute

/-! # AuditTerm.StrengthT8 — strength-T8 subst/rename fusion gates.

Per-declaration zero-axiom gates for the strength-T8 chain:

* the typed-Term rename functoriality substrate (`Term.rename_rename`,
  `Term.rename_pointwise_HEq`, `Term.rename_weaken_commute`, the lifted
  rename-compose helpers, the rename targetCtx cast);
* the ScR engine `Term.subst_rename_commute` (78-arm) + its three binder arms
  + the renameOutput-lift binder entry lemma;
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

-- ScR binder entry lemma + binder arms + 78-arm engine.
#assert_no_axioms LeanFX2.TermSubst.lift_renameOutput_entry_HEq
#assert_no_axioms LeanFX2.TermSubst.renameOutput_lift_entry_HEq
#assert_no_axioms LeanFX2.Term.subst_rename_commute_lamPi
#assert_no_axioms LeanFX2.Term.subst_rename_commute_lam
#assert_no_axioms LeanFX2.Term.subst_rename_commute_pathLam
#assert_no_axioms LeanFX2.Term.subst_rename_commute

-- T8 headline + singleton bridges.
#assert_no_axioms LeanFX2.Term.singleton_renameOutput_lift_entry_HEq
#assert_no_axioms LeanFX2.Term.singleton_renameOutput_precompose_entry_HEq
#assert_no_axioms LeanFX2.Term.subst0_rename_commute

end LeanFX2.Tools
