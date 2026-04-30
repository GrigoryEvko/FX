import LeanFX.Syntax.Term
import LeanFX.Syntax.Identity
import LeanFX.Syntax.DependentJ
import LeanFX.Tools.DependencyAudit

/-! # Axiom regression gate.

This module is intentionally small: importing it runs a curated
zero-axiom audit over the public kernel theorems that future work is
most likely to depend on.  If any target gains a lean-fx-scope axiom
dependency, elaboration fails and therefore `lake build` fails.
-/

namespace LeanFX.Tools.AuditAll

open Lean
open Lean.Elab.Command
open LeanFX.Tools.DependencyAudit

/-- Render an axiom-name list for an audit failure. -/
def formatAxiomNameList (axiomNames : Array Name) : String :=
  String.join (axiomNames.toList.map toString |>.intersperse ", ")

/-- Assert that a named constant has zero lean-fx-scope axiom
dependencies.  Stdlib plumbing is intentionally excluded here: the
project policy audits the lean-fx layer separately from Lean's TCB. -/
elab "#assert_no_axioms" targetSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  if !environment.contains targetName then
    throwError s!"unknown constant in axiom audit: {targetName}"
  let dependencyStats := computeStats environment targetName (includeStdlib := false)
  if dependencyStats.axioms == 0 then
    logInfo s!"axiom audit ok: {targetName}"
  else
    throwError
      s!"axiom audit failed for {targetName}: " ++
      s!"{dependencyStats.axioms} axiom(s): " ++
      formatAxiomNameList dependencyStats.axiomNames

#assert_no_axioms LeanFX.Syntax.Ty.subst_id
#assert_no_axioms LeanFX.Syntax.Ty.subst_compose
#assert_no_axioms LeanFX.Syntax.Term.subst_id
#assert_no_axioms LeanFX.Syntax.Term.subst_compose
#assert_no_axioms LeanFX.Syntax.Term.rename_id
#assert_no_axioms LeanFX.Syntax.Term.rename_compose_HEq
#assert_no_axioms LeanFX.Syntax.Step.rename_compatible
#assert_no_axioms LeanFX.Syntax.Step.subst_compatible
#assert_no_axioms LeanFX.Syntax.Step.par.rename_compatible
#assert_no_axioms LeanFX.Syntax.Step.par.subst_compatible
#assert_no_axioms LeanFX.Syntax.StepStar.rename_compatible
#assert_no_axioms LeanFX.Syntax.StepStar.subst_compatible
#assert_no_axioms LeanFX.Syntax.Conv.rename_compatible
#assert_no_axioms LeanFX.Syntax.Conv.subst_compatible
#assert_no_axioms LeanFX.Syntax.Step.par.toStar
#assert_no_axioms LeanFX.Syntax.IdProof.transport
#assert_no_axioms LeanFX.Syntax.OptionalRenaming.unweaken_rightInverse
#assert_no_axioms LeanFX.Syntax.OptionalRenaming.lift_rightInverse
#assert_no_axioms LeanFX.Syntax.OptionalRenaming.lift_isRenamingSquare
#assert_no_axioms LeanFX.Syntax.OptionalRenaming.weaken_lift_isRenamingSquare
#assert_no_axioms LeanFX.Syntax.RawTerm.optRename
#assert_no_axioms LeanFX.Syntax.RawTerm.optRename_congr
#assert_no_axioms LeanFX.Syntax.RawTerm.optRename_identity
#assert_no_axioms LeanFX.Syntax.RawTerm.rename_optRename
#assert_no_axioms LeanFX.Syntax.RawTerm.rename_optRename_commute
#assert_no_axioms LeanFX.Syntax.RawTerm.weaken_optRename_lift
#assert_no_axioms LeanFX.Syntax.RawTermSubst.lift_optionalRenamingSquare
#assert_no_axioms LeanFX.Syntax.RawTermSubst.dropNewest_optionalRenamingSquare
#assert_no_axioms LeanFX.Syntax.RawTerm.subst_optRename_commute
#assert_no_axioms LeanFX.Syntax.RawTerm.dropNewest_optRename_commute
#assert_no_axioms LeanFX.Syntax.Subst.lift_optionalRenamingSquare
#assert_no_axioms LeanFX.Syntax.Subst.singleton_optionalRenamingSquare
#assert_no_axioms LeanFX.Syntax.Ty.subst_optRename_commute
#assert_no_axioms LeanFX.Syntax.Ty.subst0_optRename_success
#assert_no_axioms LeanFX.Syntax.RawTerm.strengthen_weaken
#assert_no_axioms LeanFX.Syntax.RawTerm.optRename_sound
#assert_no_axioms LeanFX.Syntax.RawTerm.strengthen_sound
#assert_no_axioms LeanFX.Syntax.RawTerm.strengthen_eq_some_iff_weaken
#assert_no_axioms LeanFX.Syntax.Ty.optRename
#assert_no_axioms LeanFX.Syntax.Ty.optRename_congr
#assert_no_axioms LeanFX.Syntax.Ty.optRename_identity
#assert_no_axioms LeanFX.Syntax.Ty.rename_optRename
#assert_no_axioms LeanFX.Syntax.Ty.rename_optRename_commute
#assert_no_axioms LeanFX.Syntax.Ty.weaken_optRename_lift
#assert_no_axioms LeanFX.Syntax.Ty.arrow_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.piTy_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.sigmaTy_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.list_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.option_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.either_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.id_optRename_success
#assert_no_axioms LeanFX.Syntax.Ty.strengthen_weaken
#assert_no_axioms LeanFX.Syntax.Ty.optRename_sound
#assert_no_axioms LeanFX.Syntax.Ty.strengthen_sound
#assert_no_axioms LeanFX.Syntax.Ty.strengthen_eq_some_iff_weaken
#assert_no_axioms LeanFX.Syntax.StrengthenedTerm.original_eq_of_strengthen
#assert_no_axioms LeanFX.Syntax.StrengthenedTerm.termAs
#assert_no_axioms LeanFX.Syntax.OptionalRenamedTerm.renamed_eq_of_optRename
#assert_no_axioms LeanFX.Syntax.OptionalRenamedTerm.termAs
#assert_no_axioms LeanFX.Syntax.OptionalRenamedTerm.toStrengthened
#assert_no_axioms LeanFX.Syntax.TermOptionalRenaming.identity
#assert_no_axioms LeanFX.Syntax.TermOptionalRenaming.unweaken
#assert_no_axioms LeanFX.Syntax.TermOptionalRenaming.lift
#assert_no_axioms LeanFX.Syntax.Option.bindSome
#assert_no_axioms LeanFX.Syntax.Term.optRename
#assert_no_axioms LeanFX.Syntax.Term.strengthen
#assert_no_axioms LeanFX.Syntax.Ty.arrow_weaken_strengthen
#assert_no_axioms LeanFX.Syntax.Term.isNewestVar
#assert_no_axioms LeanFX.Syntax.Term.cd_idJ_redex_aligned
#assert_no_axioms LeanFX.Syntax.Term.cd_idJ_redex
#assert_no_axioms LeanFX.Syntax.Term.cd
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates
#assert_no_axioms LeanFX.Syntax.RawTermSubst.singleton
#assert_no_axioms LeanFX.Syntax.RawTerm.subst0
#assert_no_axioms LeanFX.Syntax.RawStep.par
#assert_no_axioms LeanFX.Syntax.RawStep.par.lam_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.pair_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.refl_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.boolTrue_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.boolFalse_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.natZero_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.natSucc_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.listNil_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.listCons_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.optionNone_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.optionSome_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.eitherInl_inv
#assert_no_axioms LeanFX.Syntax.RawStep.par.eitherInr_inv
#assert_no_axioms LeanFX.Syntax.RawTerm.cd
#assert_no_axioms LeanFX.Syntax.RawStep.par.cd_dominates
#assert_no_axioms LeanFX.Syntax.RawTerm.subst0_rename_commute
#assert_no_axioms LeanFX.Syntax.RawStep.par.rename
#assert_no_axioms LeanFX.Syntax.RawTermSubst.par_lift
#assert_no_axioms LeanFX.Syntax.RawTerm.subst_par_pointwise
#assert_no_axioms LeanFX.Syntax.RawTerm.weaken_subst_singleton
#assert_no_axioms LeanFX.Syntax.RawTerm.subst0_subst_commute
#assert_no_axioms LeanFX.Syntax.RawStep.par.subst_par
#assert_no_axioms LeanFX.Syntax.RawStep.par.subst0_par
#assert_no_axioms LeanFX.Syntax.RawStep.par.cd_lemma
#assert_no_axioms LeanFX.Syntax.RawStep.par.diamond
#assert_no_axioms LeanFX.Syntax.RawStep.parStar
#assert_no_axioms LeanFX.Syntax.RawStep.par.toStar
#assert_no_axioms LeanFX.Syntax.RawStep.parStar.snoc
#assert_no_axioms LeanFX.Syntax.RawStep.parStar.append
#assert_no_axioms LeanFX.Syntax.RawStep.par.strip
#assert_no_axioms LeanFX.Syntax.RawStep.parStar.confluence
#assert_no_axioms LeanFX.Syntax.Term.toRaw_cast
#assert_no_axioms LeanFX.Syntax.Term.toRaw_rename
#assert_no_axioms LeanFX.Syntax.TermSubst.RawConsistent
#assert_no_axioms LeanFX.Syntax.TermSubst.lift_RawConsistent
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst0_of_consistent
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton
#assert_no_axioms LeanFX.Syntax.Term.subst0_term
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton_RawConsistent
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst0_term
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst0_term_raw
#assert_no_axioms LeanFX.Syntax.Subst.termSingleton
#assert_no_axioms LeanFX.Syntax.Subst.precompose_weaken_termSingleton_equiv_identity
#assert_no_axioms LeanFX.Syntax.Subst.singleton_equiv_termSingleton_unit
#assert_no_axioms LeanFX.Syntax.Ty.weaken_subst_termSingleton
#assert_no_axioms LeanFX.Syntax.Subst.termSingleton_renameAfter_equiv_precompose
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton_renameAfter_pointwise
#assert_no_axioms LeanFX.Syntax.Term.rename_subst0_term_HEq
#assert_no_axioms LeanFX.Syntax.TermSubst.par_lift
#assert_no_axioms LeanFX.Syntax.Term.subst_par_pointwise
#assert_no_axioms LeanFX.Syntax.TermSubst.singleton_par_pointwise
#assert_no_axioms LeanFX.Syntax.Step.parStar
#assert_no_axioms LeanFX.Syntax.Step.par.toParStar
#assert_no_axioms LeanFX.Syntax.Step.parStar.snoc
#assert_no_axioms LeanFX.Syntax.Step.parStar.append
#assert_no_axioms LeanFX.Syntax.Step.parStar.subst_compatible
#assert_no_axioms LeanFX.Syntax.Term.subst0_parStar_argument
#assert_no_axioms LeanFX.Syntax.Term.subst0_parStar_body
#assert_no_axioms LeanFX.Syntax.Step.parStar.subst0_parStar

end LeanFX.Tools.AuditAll
