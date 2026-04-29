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
#assert_no_axioms LeanFX.Syntax.Ty.strengthen_weaken
#assert_no_axioms LeanFX.Syntax.Ty.optRename_sound
#assert_no_axioms LeanFX.Syntax.Ty.strengthen_sound
#assert_no_axioms LeanFX.Syntax.Ty.strengthen_eq_some_iff_weaken
#assert_no_axioms LeanFX.Syntax.StrengthenedTerm.original_eq_of_strengthen
#assert_no_axioms LeanFX.Syntax.StrengthenedTerm.termAs
#assert_no_axioms LeanFX.Syntax.OptionalRenamedTerm.renamed_eq_of_optRename
#assert_no_axioms LeanFX.Syntax.OptionalRenamedTerm.termAs
#assert_no_axioms LeanFX.Syntax.TermOptionalRenaming.unweaken
#assert_no_axioms LeanFX.Syntax.TermOptionalRenaming.lift

end LeanFX.Tools.AuditAll
