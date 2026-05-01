import LeanFX.Syntax.Term
import LeanFX.Syntax.Identity
import LeanFX.Syntax.DependentJ
import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.CdLemmaStar
import LeanFX.Syntax.Reduction.CdLemmaStarWithBi
import LeanFX.Syntax.Reduction.Diamond
import LeanFX.Syntax.Reduction.CdParMono
import LeanFX.Syntax.Reduction.Confluence
import LeanFX.Syntax.Reduction.ParInversion
import LeanFX.Frontend.Surface
import LeanFX.Frontend.Token
import LeanFX.Syntax.Inductive
import LeanFX.Mode.Collision
import LeanFX.Mode.Modality
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

/-- Assert that a named constant has zero axiom dependencies.
Includes Lean core: propext, Quot.sound, Classical.choice all count.
Project policy is strict zero — any axiom in the dependency tree
fails the gate.  Constructive proofs only. -/
elab "#assert_no_axioms" targetSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  if !environment.contains targetName then
    throwError s!"unknown constant in axiom audit: {targetName}"
  let dependencyStats := computeStats environment targetName (includeStdlib := true)
  if dependencyStats.axioms == 0 then
    logInfo s!"axiom audit ok: {targetName}"
  else
    throwError
      s!"axiom audit failed for {targetName}: " ++
      s!"{dependencyStats.axioms} axiom(s): " ++
      formatAxiomNameList dependencyStats.axiomNames

#assert_no_axioms LeanFX.Syntax.Ty.universeCumul
#assert_no_axioms LeanFX.Syntax.Ty.liftLevel
#assert_no_axioms LeanFX.Syntax.Ty.levelMax
#assert_no_axioms LeanFX.Syntax.Ty.level_le_max_left
#assert_no_axioms LeanFX.Syntax.Ty.level_le_max_right
#assert_no_axioms LeanFX.Syntax.Ty.piTyLevel
#assert_no_axioms LeanFX.Syntax.Ty.sigmaTyLevel
#assert_no_axioms LeanFX.Syntax.Ty.rename_universeCumul
#assert_no_axioms LeanFX.Syntax.Ty.subst_id
#assert_no_axioms LeanFX.Syntax.Ty.subst_compose
#assert_no_axioms LeanFX.Syntax.Term.subst
#assert_no_axioms LeanFX.Syntax.Term.subst_id
#assert_no_axioms LeanFX.Syntax.Term.subst_compose
#assert_no_axioms LeanFX.Syntax.Term.rename
#assert_no_axioms LeanFX.Syntax.Term.rename_id
#assert_no_axioms LeanFX.Syntax.Term.rename_compose_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst_id_HEq
#assert_no_axioms LeanFX.Syntax.Term.rename_id_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst_compose_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst_HEq_pointwise
#assert_no_axioms LeanFX.Syntax.Term.rename_HEq_pointwise
#assert_no_axioms LeanFX.Syntax.Term.castRight_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst_weaken_commute_HEq
#assert_no_axioms LeanFX.Syntax.Term.rename_weaken_commute_HEq
#assert_no_axioms LeanFX.Syntax.Term.rename_subst_commute_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst_rename_commute_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst_weaken_singleton_HEq
#assert_no_axioms LeanFX.Syntax.Term.subst0_subst_HEq
#assert_no_axioms LeanFX.Syntax.Term.rename_subst0_HEq
#assert_no_axioms LeanFX.Syntax.Step.castBoth
#assert_no_axioms LeanFX.Syntax.Step.castSource
#assert_no_axioms LeanFX.Syntax.Step.castTarget
#assert_no_axioms LeanFX.Syntax.Step.rename_compatible
#assert_no_axioms LeanFX.Syntax.Step.subst_compatible
#assert_no_axioms LeanFX.Syntax.Step.par.castBoth
#assert_no_axioms LeanFX.Syntax.Step.par.castSource
#assert_no_axioms LeanFX.Syntax.Step.par.castTarget
#assert_no_axioms LeanFX.Syntax.Step.par.rename_compatible
#assert_no_axioms LeanFX.Syntax.Step.par.subst_compatible
#assert_no_axioms LeanFX.Syntax.StepStar.rename_compatible
#assert_no_axioms LeanFX.Syntax.StepStar.subst_compatible
#assert_no_axioms LeanFX.Syntax.Conv.rename_compatible
#assert_no_axioms LeanFX.Syntax.Conv.subst_compatible
#assert_no_axioms LeanFX.Syntax.Conv.app_cong_left
#assert_no_axioms LeanFX.Syntax.Conv.app_cong_right
#assert_no_axioms LeanFX.Syntax.Conv.app_cong
#assert_no_axioms LeanFX.Syntax.Conv.lam_cong
#assert_no_axioms LeanFX.Syntax.Conv.lamPi_cong
#assert_no_axioms LeanFX.Syntax.Conv.appPi_cong_left
#assert_no_axioms LeanFX.Syntax.Conv.appPi_cong_right
#assert_no_axioms LeanFX.Syntax.Conv.appPi_cong
#assert_no_axioms LeanFX.Syntax.Conv.pair_cong_first
#assert_no_axioms LeanFX.Syntax.Conv.pair_cong_second
#assert_no_axioms LeanFX.Syntax.Conv.pair_cong
#assert_no_axioms LeanFX.Syntax.Conv.fst_cong
#assert_no_axioms LeanFX.Syntax.Conv.snd_cong
#assert_no_axioms LeanFX.Syntax.Conv.boolElim_cong
#assert_no_axioms LeanFX.Syntax.Conv.natElim_cong
#assert_no_axioms LeanFX.Syntax.Conv.natRec_cong
#assert_no_axioms LeanFX.Syntax.Conv.listElim_cong
#assert_no_axioms LeanFX.Syntax.Conv.optionMatch_cong
#assert_no_axioms LeanFX.Syntax.Conv.eitherMatch_cong
#assert_no_axioms LeanFX.Syntax.Conv.idJ_cong
#assert_no_axioms LeanFX.Syntax.Term.eta_arrow_eq
#assert_no_axioms LeanFX.Syntax.Term.eta_sigma_eq
#assert_no_axioms LeanFX.Syntax.instDecidableEqRawTerm
#assert_no_axioms LeanFX.Syntax.instDecidableEqTy
#assert_no_axioms LeanFX.Mode.instDecidableEqModality
#assert_no_axioms LeanFX.Syntax.Step.par.toStar
#assert_no_axioms LeanFX.Syntax.StepStar.toConv
#assert_no_axioms LeanFX.Syntax.StepStar.append
#assert_no_axioms LeanFX.Syntax.StepStar.mapStep
#assert_no_axioms LeanFX.Syntax.Conv.mapStep
#assert_no_axioms LeanFX.Syntax.IdProof.refl
#assert_no_axioms LeanFX.Syntax.IdProof.symm
#assert_no_axioms LeanFX.Syntax.IdProof.trans
#assert_no_axioms LeanFX.Syntax.IdProof.cong
#assert_no_axioms LeanFX.Syntax.IdProof.cong_app
#assert_no_axioms LeanFX.Syntax.IdProof.subst
#assert_no_axioms LeanFX.Syntax.IdProof.rename
#assert_no_axioms LeanFX.Syntax.IdProof.toEq
#assert_no_axioms LeanFX.Syntax.IdProof.ofEq
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

-- W8.7 Term.cd typed-cascade infrastructure (zero-axiom).
-- Layer 1: Generic typed extractors keyed by `Term.toRaw` shape
-- (TermExtraction.lean).  Each `_general` form takes a HEq witness
-- and returns the typed payload of the matched constructor; the
-- match is at universal index per Rule 3, propext-free.
#assert_no_axioms LeanFX.Syntax.Term.body_of_lam_general
#assert_no_axioms LeanFX.Syntax.Term.body_of_lamPi_general
#assert_no_axioms LeanFX.Syntax.Term.firstVal_of_pair_general
#assert_no_axioms LeanFX.Syntax.Term.secondVal_of_pair_general
#assert_no_axioms LeanFX.Syntax.Term.predecessor_of_natSucc_general
#assert_no_axioms LeanFX.Syntax.Term.head_of_listCons_general
#assert_no_axioms LeanFX.Syntax.Term.tail_of_listCons_general
#assert_no_axioms LeanFX.Syntax.Term.value_of_optionSome_general
#assert_no_axioms LeanFX.Syntax.Term.value_of_eitherInl_general
#assert_no_axioms LeanFX.Syntax.Term.value_of_eitherInr_general

-- Layer 2: Typed-inversion equations (eq_<ctor>_of_toRaw_<ctor>).
-- Each base form discharges `Term.toRaw t = RawTerm.<ctor> ...` →
-- `t = Term.<ctor> ...`; the `_general` form is the universal-
-- index variant used by `Term.cd_<head>_redex` helpers.
#assert_no_axioms LeanFX.Syntax.Term.eq_lam_of_toRaw_lam_general
#assert_no_axioms LeanFX.Syntax.Term.eq_lam_of_toRaw_lam
#assert_no_axioms LeanFX.Syntax.Term.eq_lamPi_of_toRaw_lam_general
#assert_no_axioms LeanFX.Syntax.Term.eq_lamPi_of_toRaw_lam
#assert_no_axioms LeanFX.Syntax.Term.eq_pair_of_toRaw_pair_general
#assert_no_axioms LeanFX.Syntax.Term.eq_pair_of_toRaw_pair
#assert_no_axioms LeanFX.Syntax.Term.eq_boolTrue_of_toRaw_boolTrue_general
#assert_no_axioms LeanFX.Syntax.Term.eq_boolTrue_of_toRaw_boolTrue
#assert_no_axioms LeanFX.Syntax.Term.eq_boolFalse_of_toRaw_boolFalse_general
#assert_no_axioms LeanFX.Syntax.Term.eq_boolFalse_of_toRaw_boolFalse
#assert_no_axioms LeanFX.Syntax.Term.eq_natZero_of_toRaw_natZero_general
#assert_no_axioms LeanFX.Syntax.Term.eq_natZero_of_toRaw_natZero
#assert_no_axioms LeanFX.Syntax.Term.eq_natSucc_of_toRaw_natSucc_general
#assert_no_axioms LeanFX.Syntax.Term.eq_natSucc_of_toRaw_natSucc
#assert_no_axioms LeanFX.Syntax.Term.eq_listNil_of_toRaw_listNil_general
#assert_no_axioms LeanFX.Syntax.Term.eq_listNil_of_toRaw_listNil
#assert_no_axioms LeanFX.Syntax.Term.eq_listCons_of_toRaw_listCons_general
#assert_no_axioms LeanFX.Syntax.Term.eq_listCons_of_toRaw_listCons
#assert_no_axioms LeanFX.Syntax.Term.eq_optionNone_of_toRaw_optionNone_general
#assert_no_axioms LeanFX.Syntax.Term.eq_optionNone_of_toRaw_optionNone
#assert_no_axioms LeanFX.Syntax.Term.eq_optionSome_of_toRaw_optionSome_general
#assert_no_axioms LeanFX.Syntax.Term.eq_optionSome_of_toRaw_optionSome
#assert_no_axioms LeanFX.Syntax.Term.eq_eitherInl_of_toRaw_eitherInl_general
#assert_no_axioms LeanFX.Syntax.Term.eq_eitherInl_of_toRaw_eitherInl
#assert_no_axioms LeanFX.Syntax.Term.eq_eitherInr_of_toRaw_eitherInr_general
#assert_no_axioms LeanFX.Syntax.Term.eq_eitherInr_of_toRaw_eitherInr

-- Layer 3: Per-redex `cd_<head>_redex` helpers in
-- CompleteDevelopmentRedex.lean.  Each peels the `Term.toRaw`
-- shape of the developed function/scrutinee and either fires
-- the redex contractum (β/ι) or rebuilds the constructor.
#assert_no_axioms LeanFX.Syntax.Term.cd_app_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_appPi_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_fst_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_snd_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_boolElim_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_natElim_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_natRec_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_listElim_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_optionMatch_redex
#assert_no_axioms LeanFX.Syntax.Term.cd_eitherMatch_redex

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
#assert_no_axioms LeanFX.Syntax.Term.toRaw
#assert_no_axioms LeanFX.Syntax.Term.toRaw_cast
#assert_no_axioms LeanFX.Syntax.Term.toRaw_rename
#assert_no_axioms LeanFX.Syntax.TermSubst.RawConsistent
#assert_no_axioms LeanFX.Syntax.TermSubst.lift_RawConsistent
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst0_of_consistent
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton
#assert_no_axioms LeanFX.Syntax.Term.subst0
#assert_no_axioms LeanFX.Syntax.Term.subst0_term
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton_RawConsistent
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst0_term
#assert_no_axioms LeanFX.Syntax.Term.toRaw_subst0_term_raw
#assert_no_axioms LeanFX.Syntax.Subst.termSingleton
#assert_no_axioms LeanFX.Syntax.Subst.precompose_weaken_termSingleton_equiv_identity
#assert_no_axioms LeanFX.Syntax.Subst.singleton_equiv_termSingleton_unit
#assert_no_axioms LeanFX.Syntax.Ty.subst_singleton_eq_termSingleton_unit
#assert_no_axioms LeanFX.Syntax.Ty.subst0_eq_termSingleton_unit
#assert_no_axioms LeanFX.Syntax.Ty.weaken_subst_termSingleton
#assert_no_axioms LeanFX.Syntax.Subst.termSingleton_renameAfter_equiv_precompose
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton_renameAfter_pointwise
#assert_no_axioms LeanFX.Syntax.Subst.termSingleton_compose_equiv_lift_compose_termSingleton
#assert_no_axioms LeanFX.Syntax.TermSubst.precompose_weaken_termSingleton_pointwise
#assert_no_axioms LeanFX.Syntax.Term.subst_weaken_termSingleton_HEq
#assert_no_axioms LeanFX.Syntax.TermSubst.termSingleton_compose_pointwise
#assert_no_axioms LeanFX.Syntax.Term.subst0_term_subst_HEq
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
#assert_no_axioms LeanFX.Syntax.Step.parStar.lam_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.lamPi_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.app_cong_function
#assert_no_axioms LeanFX.Syntax.Step.parStar.app_cong_argument
#assert_no_axioms LeanFX.Syntax.Step.parStar.app_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.appPi_cong_function
#assert_no_axioms LeanFX.Syntax.Step.parStar.appPi_cong_argument
#assert_no_axioms LeanFX.Syntax.Step.parStar.appPi_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.pair_cong_first
#assert_no_axioms LeanFX.Syntax.Step.parStar.pair_cong_second
#assert_no_axioms LeanFX.Syntax.Step.parStar.pair_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.fst_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.snd_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolElim_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolElim_cong_then
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolElim_cong_else
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolElim_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.natSucc_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.natElim_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStar.natElim_cong_zero
#assert_no_axioms LeanFX.Syntax.Step.parStar.natElim_cong_succ
#assert_no_axioms LeanFX.Syntax.Step.parStar.natElim_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.natRec_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStar.natRec_cong_zero
#assert_no_axioms LeanFX.Syntax.Step.parStar.natRec_cong_succ
#assert_no_axioms LeanFX.Syntax.Step.parStar.natRec_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.listCons_cong_head
#assert_no_axioms LeanFX.Syntax.Step.parStar.listCons_cong_tail
#assert_no_axioms LeanFX.Syntax.Step.parStar.listCons_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.listElim_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStar.listElim_cong_nil
#assert_no_axioms LeanFX.Syntax.Step.parStar.listElim_cong_cons
#assert_no_axioms LeanFX.Syntax.Step.parStar.listElim_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionSome_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionMatch_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionMatch_cong_none
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionMatch_cong_some
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionMatch_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherInl_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherInr_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherMatch_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherMatch_cong_left
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherMatch_cong_right
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherMatch_cong
#assert_no_axioms LeanFX.Syntax.Step.parStar.idJ_cong_base
#assert_no_axioms LeanFX.Syntax.Step.parStar.idJ_cong_witness
#assert_no_axioms LeanFX.Syntax.Step.parStar.idJ_cong
#assert_no_axioms LeanFX.Syntax.Step.par.isBi
#assert_no_axioms LeanFX.Syntax.Step.parStar.castBoth
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_refl_only_smoke
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_refl_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_lam_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_lamPi_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_pair_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_natSucc_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_listCons_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_optionSome_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_eitherInl_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_eitherInr_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_app_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_appPi_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_fst_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_snd_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_boolElim_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_natElim_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_natRec_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_listElim_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_optionMatch_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_eitherMatch_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_idJ_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaApp_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaAppPi_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaFstPair_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaSndPair_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaBoolElimTrue_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaBoolElimFalse_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatElimZero_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatElimSucc_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatRecZero_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatRecSucc_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaListElimNil_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaListElimCons_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaOptionMatchNone_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaOptionMatchSome_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaEitherMatchInl_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaEitherMatchInr_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaIdJRefl_case

-- Dependent-J motive scaffold (forward-looking design, see #875).
#assert_no_axioms LeanFX.Syntax.DependentJMotive
#assert_no_axioms LeanFX.Syntax.DependentJ.baseCaseType
#assert_no_axioms LeanFX.Syntax.DependentJ.resultType
#assert_no_axioms LeanFX.Syntax.DependentJ.Input
#assert_no_axioms LeanFX.Syntax.DependentJ.Input.resultType

-- Identity-fragment foundations (constructors + Ty.id formation).
#assert_no_axioms LeanFX.Syntax.Term.refl
#assert_no_axioms LeanFX.Syntax.Term.idJ
#assert_no_axioms LeanFX.Syntax.Ty.id

-- Strengthen (option-returning inverse of weaken).
#assert_no_axioms LeanFX.Syntax.Ty.strengthen

-- Core inductive substrate.  Gating the inductives directly catches
-- any future refactor that introduces an axiom into the type theory
-- without requiring per-constructor sweeps.
#assert_no_axioms LeanFX.Syntax.Term
#assert_no_axioms LeanFX.Syntax.Ty
#assert_no_axioms LeanFX.Syntax.Ctx
#assert_no_axioms LeanFX.Syntax.RawTerm

-- Reduction relations: typed and raw layers, single-step and
-- transitive-closure flavours.  Each is an inductive carrying the
-- reduction-step taxonomy; gating them protects against any new
-- ctor that would silently smuggle an axiom in via target-type subst.
#assert_no_axioms LeanFX.Syntax.Step
#assert_no_axioms LeanFX.Syntax.Step.par
#assert_no_axioms LeanFX.Syntax.Step.parStar
#assert_no_axioms LeanFX.Syntax.Step.par.isBi
#assert_no_axioms LeanFX.Syntax.StepStar
#assert_no_axioms LeanFX.Syntax.Conv
#assert_no_axioms LeanFX.Syntax.RawStep.par
#assert_no_axioms LeanFX.Syntax.RawStep.parStar

-- Substitution / renaming carriers.  Structure types holding the
-- joint Ty + RawTerm substitution functions (`Subst`) and the term-
-- level analogues (`TermSubst`, `TermRenaming`).  Plus the bare
-- raw-only carriers (`RawTermSubst`, `Renaming`).
#assert_no_axioms LeanFX.Syntax.Subst
#assert_no_axioms LeanFX.Syntax.RawTermSubst
#assert_no_axioms LeanFX.Syntax.Renaming
#assert_no_axioms LeanFX.Syntax.TermSubst
#assert_no_axioms LeanFX.Syntax.TermRenaming
#assert_no_axioms LeanFX.Syntax.LengthList
#assert_no_axioms LeanFX.Mode.Mode

-- Modality + Context-lock equivalence.  Modality is the 1-cell
-- between modes; LockEquiv is the propositional context-lock
-- relation (kept relational, not Eq, to dodge propext from
-- dependent matching on the Modality family).  IdProof is the
-- propositional id-fragment witness.  StandardList / StandardNat
-- are the universe-polymorphic standard data types used by
-- LengthList and friends.  InductiveArgumentShape gates the
-- shape predicate used in Inductive.lean's argument analysis.
#assert_no_axioms LeanFX.Mode.Modality
#assert_no_axioms LeanFX.Mode.FxCollisionAtom
#assert_no_axioms LeanFX.Syntax.Ctx.LockEquiv
#assert_no_axioms LeanFX.Syntax.IdProof
#assert_no_axioms LeanFX.Syntax.StandardList
#assert_no_axioms LeanFX.Syntax.StandardNat
#assert_no_axioms LeanFX.Syntax.InductiveArgumentShape
#assert_no_axioms LeanFX.Frontend.MatchArmList
#assert_no_axioms LeanFX.Frontend.PatternList

-- Frontend (Surface AST + Token AST).  These mirror the kernel's
-- intrinsic indexing discipline and must stay axiom-free for the
-- elaborator/lexer roadmap (#896, #897, #905, #906).
#assert_no_axioms LeanFX.Frontend.Surface
#assert_no_axioms LeanFX.Frontend.ParamData
#assert_no_axioms LeanFX.Frontend.ParamList
#assert_no_axioms LeanFX.Frontend.Pattern
#assert_no_axioms LeanFX.Frontend.MatchArm
#assert_no_axioms LeanFX.Frontend.NameSpan
#assert_no_axioms LeanFX.Frontend.BindingPrefix
#assert_no_axioms LeanFX.Frontend.ModalAnnotation
#assert_no_axioms LeanFX.Frontend.Token
#assert_no_axioms LeanFX.Frontend.Keyword
#assert_no_axioms LeanFX.Frontend.ContextualKeyword
#assert_no_axioms LeanFX.Frontend.IdentifierKind
#assert_no_axioms LeanFX.Frontend.NumericKind
#assert_no_axioms LeanFX.Frontend.StringKind
#assert_no_axioms LeanFX.Frontend.Operator
#assert_no_axioms LeanFX.Frontend.Punctuation
#assert_no_axioms LeanFX.Frontend.CommentKind
#assert_no_axioms LeanFX.Frontend.SourcePos
#assert_no_axioms LeanFX.Frontend.TokenSpan

/-! ## Wave 9-B1 typed source-inversion lemmas (post-W6.1).

Block at zero axioms via HEq-generalized induction + `Term.toRaw`
projection refutation.  See `LeanFX/Syntax/Reduction/ParInversion.lean`
for the strategy. -/

#assert_no_axioms LeanFX.Syntax.Step.par.boolTrue_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.boolTrue_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolTrue_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolTrue_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.boolFalse_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.boolFalse_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolFalse_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.boolFalse_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.natZero_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.natZero_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.natZero_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.natZero_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.listNil_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.listNil_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.listNil_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.listNil_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.optionNone_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.optionNone_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionNone_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionNone_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.refl_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.refl_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.refl_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.refl_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.natSucc_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.natSucc_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.natSucc_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.listCons_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.listCons_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.listCons_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.optionSome_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.optionSome_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.optionSome_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.eitherInl_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.eitherInl_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherInl_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.eitherInr_source_inv_general
#assert_no_axioms LeanFX.Syntax.Step.par.eitherInr_source_inv
#assert_no_axioms LeanFX.Syntax.Step.parStar.eitherInr_source_inv

/-! ## Wave 9-B1 Deep βι case helpers (post-W6.1).

These use the typed source-inversions above to collapse `Term.cd` of
elimination forms whose scrutinees parallel-reduce to head normal
forms. -/

#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaBoolElimTrueDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaBoolElimFalseDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatElimZeroDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatRecZeroDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaListElimNilDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaOptionMatchNoneDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaIdJReflDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatElimSuccDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaNatRecSuccDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaListElimConsDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaOptionMatchSomeDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaEitherMatchInlDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_iotaEitherMatchInrDeep_case

/-! ## Wave 9-B1.6: chain-level isBi predicate.

`Step.parStar.isBi` is the chain-level analog of `Step.par.isBi`:
a chain is βι iff every step in it is βι.  Required for the
4 dep β Deep cases (betaAppDeep, betaAppPiDeep, betaFstPairDeep,
betaSndPairDeep) of `cd_lemma_star`, which need lam/pair target
inversions under chain-isBi gating to discharge η-blocked cases. -/

#assert_no_axioms LeanFX.Syntax.Step.par.toParStar_isBi

/-! ## Wave 9-B1.7: single-step lam/pair target inversions under isBi.

The breakthrough: `induction stepBi` (rather than `induction parStep`)
automatically OMITS etaArrow / etaSigma constructors because
`Step.par.isBi` has no such ctors.  This sidesteps the dep-elim
wall on `cases (h : Step.par.isBi (Step.par.etaArrow _))`.

Both single-step and chain (parStar) versions land at zero axioms.
The chain version was unblocked by inducting on `chainBi` directly
(NOT on `chain`); chainBi's ctor pattern gives the right shape for
the chain in each case, and the body is universally quantified
inside the goal so the IH can be re-instantiated at each chain
link with the intermediate body produced by single-step inversion. -/

#assert_no_axioms LeanFX.Syntax.Step.par.lam_target_inv_isBi_general
#assert_no_axioms LeanFX.Syntax.Step.par.lam_target_inv_isBi
#assert_no_axioms LeanFX.Syntax.Step.par.pair_target_inv_isBi_general
#assert_no_axioms LeanFX.Syntax.Step.par.pair_target_inv_isBi
#assert_no_axioms LeanFX.Syntax.Step.parStar.lam_target_inv_isBi_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.lam_target_inv_isBi
#assert_no_axioms LeanFX.Syntax.Step.parStar.pair_target_inv_isBi_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.pair_target_inv_isBi
#assert_no_axioms LeanFX.Syntax.Step.par.lamPi_target_inv_isBi_general
#assert_no_axioms LeanFX.Syntax.Step.par.lamPi_target_inv_isBi
#assert_no_axioms LeanFX.Syntax.Step.parStar.lamPi_target_inv_isBi_general
#assert_no_axioms LeanFX.Syntax.Step.parStar.lamPi_target_inv_isBi

/-! ## Wave 9-B1.5 dep β Deep case helpers.

The four dep β Deep cases of `cd_lemma_star` were previously gated
on either Wave 6 β-surgery or the Wave 9 Term refactor.  W9.B1.7
unblocked them via the chain inversions above.  Each case applies
`Step.parStar.{lam,lamPi,pair}_target_inv_isBi` to the IH chain
and discharges via `subst0_parStar` (β cases) or direct projection
(Σ cases). -/

#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaAppDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaAppPiDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaFstPairDeep_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_betaSndPairDeep_case

#assert_no_axioms LeanFX.Syntax.Step.par.isBi.cast_target_eq

/-! ## #1137: cd_dominates_isBi — every cd_dominates step is βι.

Single inductive predicate `Step.parWithBi` packages Step.par
with its isBi proof; helpers + main theorem produce both at once.
Closes #1137 and unblocks W8.x (cd_lemma → diamond → Church-Rosser
→ canonical_form, blocking #883/884/885/886). -/

#assert_no_axioms LeanFX.Syntax.Step.parWithBi
#assert_no_axioms LeanFX.Syntax.Step.parWithBi.toStep
#assert_no_axioms LeanFX.Syntax.Step.parWithBi.toIsBi
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_idJ_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_app_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_appPi_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_fst_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_snd_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_boolElim_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_natElim_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_natRec_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_listElim_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_optionMatch_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_eitherMatch_pair
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_with_isBi
#assert_no_axioms LeanFX.Syntax.Step.par.cd_dominates_isBi

/-! ## Wave 8.1: paired parStarWithBi infrastructure.

`Step.parStarWithBi` bundles a `Step.parStar` chain with the
isBi witness on every link.  The paired-predicate trick (per
the project's feedback memory) sidesteps the opacity of
tactic-mode theorems by constructing fresh witnesses at each
case.  Used to discharge `cd_lemma_star_with_bi` (the typed
complete-development aggregator) and its plain projections. -/

#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.toParStar
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.toIsBi
#assert_no_axioms LeanFX.Syntax.Step.par.isBi.toParStarWithBi

/-! ## W8.1b: paired core ops (snoc, append, cast). -/

#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.snoc
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.append
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.castBoth

/-! ## W8.1c: paired cong rules — binders, app/appPi, pair/fst/snd,
idJ. -/

#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.lam_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.lamPi_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.app_cong_function
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.app_cong_argument
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.app_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.appPi_cong_function
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.appPi_cong_argument
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.appPi_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.pair_cong_first
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.pair_cong_second
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.pair_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.fst_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.snd_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.idJ_cong_base
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.idJ_cong_witness
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.idJ_cong

/-! ## W8.1d: paired cong rules — eliminators + cell ctors. -/

#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.boolElim_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.boolElim_cong_then
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.boolElim_cong_else
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.boolElim_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natSucc_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natElim_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natElim_cong_zero
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natElim_cong_succ
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natElim_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natRec_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natRec_cong_zero
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natRec_cong_succ
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natRec_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listCons_cong_head
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listCons_cong_tail
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listCons_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listElim_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listElim_cong_nil
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listElim_cong_cons
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listElim_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.optionSome_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.optionMatch_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.optionMatch_cong_none
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.optionMatch_cong_some
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.optionMatch_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherInl_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherInr_cong
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherMatch_cong_scrutinee
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherMatch_cong_left
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherMatch_cong_right
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherMatch_cong

/-! ## W8.1: isBi cast helpers. -/

#assert_no_axioms LeanFX.Syntax.Step.par.isBi.castBoth
#assert_no_axioms LeanFX.Syntax.Step.par.isBi.castTarget
#assert_no_axioms LeanFX.Syntax.Step.par.isBi.castSource

/-! ## W8.1f: paired target inversions (lam, lamPi, pair). -/

#assert_no_axioms LeanFX.Syntax.Step.par.lam_target_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.par.lam_target_inv_with_bi
#assert_no_axioms LeanFX.Syntax.Step.par.lamPi_target_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.par.lamPi_target_inv_with_bi
#assert_no_axioms LeanFX.Syntax.Step.par.pair_target_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.par.pair_target_inv_with_bi
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.lam_target_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.lam_target_inv
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.lamPi_target_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.lamPi_target_inv
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.pair_target_inv_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.pair_target_inv

/-! ## W8.1g: paired source inversions (deep ι cell ctors). -/

#assert_no_axioms LeanFX.Syntax.Step.par.natSucc_source_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.natSucc_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.listCons_source_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.listCons_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.optionSome_source_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.optionSome_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.eitherInl_source_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherInl_source_inv
#assert_no_axioms LeanFX.Syntax.Step.par.eitherInr_source_inv_with_bi_general
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.eitherInr_source_inv

/-! ## W8.1: parWithBi singleton + cast helpers + compatibility. -/

#assert_no_axioms LeanFX.Syntax.Step.parWithBi.castBoth
#assert_no_axioms LeanFX.Syntax.Step.parWithBi.castTarget
#assert_no_axioms LeanFX.Syntax.Step.parWithBi.castSource
#assert_no_axioms LeanFX.Syntax.Step.parWithBi.rename_compatible
#assert_no_axioms LeanFX.Syntax.Step.parWithBi.subst_compatible
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.subst_compatible

/-! ## W8.1e: paired β-workhorse — subst0_parStar arg & body. -/

#assert_no_axioms LeanFX.Syntax.Term.subst0_parStarWithBi_body
#assert_no_axioms LeanFX.Syntax.TermSubst.parWithBi_lift
#assert_no_axioms LeanFX.Syntax.Term.subst_parWithBi_pointwise
#assert_no_axioms LeanFX.Syntax.TermSubst.singleton_parWithBi_pointwise
#assert_no_axioms LeanFX.Syntax.Term.subst0_parStarWithBi_argument
#assert_no_axioms LeanFX.Syntax.Step.parStarWithBi.subst0_parStarWithBi

/-! ## W8.1g: typed complete-development aggregator + projections.

`cd_lemma_star_with_bi` is the paired aggregator — induction on
the isBi witness over 54 cases produces both the chain and the
chain-isBi witness simultaneously.  `cd_lemma_star` and
`cd_lemma_star_isBi` are one-line projections that close
**#883** (typed cd-lemma) and unblock #884/#885/#886
(diamond → confluence → canonical-form). -/

#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_with_bi
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star
#assert_no_axioms LeanFX.Syntax.Step.par.cd_lemma_star_isBi

/-! ## W8.2: typed diamond property.

`Term.cd source` is the universal common reduct of every
βι-witnessed parallel step from `source`.  Both legs are
`cd_lemma_star` applied to the input βι-witness — closes
**#884** (W8.2 typed diamond). -/

#assert_no_axioms LeanFX.Syntax.Step.par.diamond
#assert_no_axioms LeanFX.Syntax.Step.par.diamond_isBi

/-! ## W8.3a: iterated complete development.

`Term.cdIter` iterates `Term.cd` `count` times.  Pure structural
recursion; `cdIter_zero`, `cdIter_succ`, and `cdIter_one` are
defining `rfl`s.  All four constructions are zero-axiom; this
file provides the join-point definition for the W8.3 confluence
proof. -/

#assert_no_axioms LeanFX.Syntax.Term.cdIter
#assert_no_axioms LeanFX.Syntax.Term.cdIter_zero
#assert_no_axioms LeanFX.Syntax.Term.cdIter_succ
#assert_no_axioms LeanFX.Syntax.Term.cdIter_one

/-! ## W8.3b: cd_monotone trivial cong cases (10).

Cases of the cd-monotonicity workhorse where `Term.cd` performs
no contraction.  Each helper takes parStarWithBi IH(s) on cd's
of the recursive premises and lifts through the matching
`parStarWithBi.<C>_cong` rule.  Zero-axiom across all 10. -/

#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_refl_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_lam_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_lamPi_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_pair_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_natSucc_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_listCons_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_optionSome_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_eitherInl_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_eitherInr_case

/-! ## W8.3c: cd_monotone eliminator-cong cases.

When the elaborator's complete development contracts a redex
(e.g., `cd (Term.app (Term.lam body) arg) = body.subst0 (cd arg)`)
the case helper has to handle four IH configurations:
both fire / source-only / target-only / neither.  Each helper
splits on source-side and target-side cd-redex helper, with the
case-D fallback (neither fires) closed by `<C>_cong`. -/

#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_app_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_appPi_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_fst_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_snd_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_boolElim_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_natElim_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_natRec_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_listElim_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_optionMatch_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_eitherMatch_case
#assert_no_axioms LeanFX.Syntax.Step.par.cd_monotone_idJ_case

end LeanFX.Tools.AuditAll
