import Lean
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Reduction.RawParInversion

/-! # Tools/Tactics/RawInversion

Raw parallel-reduction inversion shorthands.

The raw confluence and SN files frequently end branches by applying one
constructor-specific `RawStep.par.<ctor>_inv` or canonical-head
`RawStep.parStar.<ctor>_inv` lemma.  These tactics are thin wrappers around
those theorem names; they deliberately do not destruct the returned witnesses
or perform search beyond the explicit whitelist.
-/

namespace LeanFX2.Tools.Tactics

/-! ## Single-step raw parallel inversion -/

syntax "fx_raw_par_inv " term : tactic
macro_rules
  | `(tactic| fx_raw_par_inv $parallelStep) =>
      `(tactic|
        first
          | exact LeanFX2.RawStep.par.unit_inv $parallelStep
          | exact LeanFX2.RawStep.par.boolTrue_inv $parallelStep
          | exact LeanFX2.RawStep.par.boolFalse_inv $parallelStep
          | exact LeanFX2.RawStep.par.natZero_inv $parallelStep
          | exact LeanFX2.RawStep.par.listNil_inv $parallelStep
          | exact LeanFX2.RawStep.par.optionNone_inv $parallelStep
          | exact LeanFX2.RawStep.par.var_inv $parallelStep
          | exact LeanFX2.RawStep.par.universeCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.lam_inv $parallelStep
          | exact LeanFX2.RawStep.par.pair_inv $parallelStep
          | exact LeanFX2.RawStep.par.refl_inv $parallelStep
          | exact LeanFX2.RawStep.par.natSucc_inv $parallelStep
          | exact LeanFX2.RawStep.par.listCons_inv $parallelStep
          | exact LeanFX2.RawStep.par.optionSome_inv $parallelStep
          | exact LeanFX2.RawStep.par.eitherInl_inv $parallelStep
          | exact LeanFX2.RawStep.par.eitherInr_inv $parallelStep
          | exact LeanFX2.RawStep.par.app_inv $parallelStep
          | exact LeanFX2.RawStep.par.fst_inv $parallelStep
          | exact LeanFX2.RawStep.par.snd_inv $parallelStep
          | exact LeanFX2.RawStep.par.boolElim_inv $parallelStep
          | exact LeanFX2.RawStep.par.natElim_inv $parallelStep
          | exact LeanFX2.RawStep.par.natRec_inv $parallelStep
          | exact LeanFX2.RawStep.par.listElim_inv $parallelStep
          | exact LeanFX2.RawStep.par.optionMatch_inv $parallelStep
          | exact LeanFX2.RawStep.par.eitherMatch_inv $parallelStep
          | exact LeanFX2.RawStep.par.idJ_inv $parallelStep
          | exact LeanFX2.RawStep.par.modIntro_inv $parallelStep
          | exact LeanFX2.RawStep.par.modElim_inv $parallelStep
          | exact LeanFX2.RawStep.par.subsume_inv $parallelStep
          | exact LeanFX2.RawStep.par.recordIntro_inv $parallelStep
          | exact LeanFX2.RawStep.par.recordProj_inv $parallelStep
          | exact LeanFX2.RawStep.par.codataUnfold_inv $parallelStep
          | exact LeanFX2.RawStep.par.codataDest_inv $parallelStep
          | exact LeanFX2.RawStep.par.sessionSend_inv $parallelStep
          | exact LeanFX2.RawStep.par.sessionRecv_inv $parallelStep
          | exact LeanFX2.RawStep.par.effectPerform_inv $parallelStep
          | exact LeanFX2.RawStep.par.interval0_inv $parallelStep
          | exact LeanFX2.RawStep.par.interval1_inv $parallelStep
          | exact LeanFX2.RawStep.par.intervalOpp_inv $parallelStep
          | exact LeanFX2.RawStep.par.intervalMeet_inv $parallelStep
          | exact LeanFX2.RawStep.par.intervalJoin_inv $parallelStep
          | exact LeanFX2.RawStep.par.pathLam_inv $parallelStep
          | exact LeanFX2.RawStep.par.pathApp_inv $parallelStep
          | exact LeanFX2.RawStep.par.glueIntro_inv $parallelStep
          | exact LeanFX2.RawStep.par.glueElim_inv $parallelStep
          | exact LeanFX2.RawStep.par.transp_inv $parallelStep
          | exact LeanFX2.RawStep.par.hcomp_inv $parallelStep
          | exact LeanFX2.RawStep.par.oeqRefl_inv $parallelStep
          | exact LeanFX2.RawStep.par.oeqJ_inv $parallelStep
          | exact LeanFX2.RawStep.par.oeqFunext_inv $parallelStep
          | exact LeanFX2.RawStep.par.idStrictRefl_inv $parallelStep
          | exact LeanFX2.RawStep.par.idStrictRec_inv $parallelStep
          | exact LeanFX2.RawStep.par.equivIntro_inv $parallelStep
          | exact LeanFX2.RawStep.par.equivApp_inv $parallelStep
          | exact LeanFX2.RawStep.par.uaToEquiv_inv $parallelStep
          | exact LeanFX2.RawStep.par.arrowCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.piTyCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.sigmaTyCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.productCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.sumCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.listCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.optionCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.eitherCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.idCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.equivCode_inv $parallelStep
          | exact LeanFX2.RawStep.par.equivApply_inv $parallelStep)

syntax "fx_raw_par_unit_inv " term : tactic
syntax "fx_raw_par_boolTrue_inv " term : tactic
syntax "fx_raw_par_boolFalse_inv " term : tactic
syntax "fx_raw_par_natZero_inv " term : tactic
syntax "fx_raw_par_var_inv " term : tactic
syntax "fx_raw_par_app_inv " term : tactic
syntax "fx_raw_par_lam_inv " term : tactic
syntax "fx_raw_par_pair_inv " term : tactic

macro_rules
  | `(tactic| fx_raw_par_unit_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.unit_inv $parallelStep)
  | `(tactic| fx_raw_par_boolTrue_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.boolTrue_inv $parallelStep)
  | `(tactic| fx_raw_par_boolFalse_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.boolFalse_inv $parallelStep)
  | `(tactic| fx_raw_par_natZero_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.natZero_inv $parallelStep)
  | `(tactic| fx_raw_par_var_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.var_inv $parallelStep)
  | `(tactic| fx_raw_par_app_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.app_inv $parallelStep)
  | `(tactic| fx_raw_par_lam_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.lam_inv $parallelStep)
  | `(tactic| fx_raw_par_pair_inv $parallelStep) =>
      `(tactic| exact LeanFX2.RawStep.par.pair_inv $parallelStep)

/-! ## Canonical-head raw parStar inversion -/

syntax "fx_raw_parstar_canonical_inv " term : tactic
macro_rules
  | `(tactic| fx_raw_parstar_canonical_inv $chainProof) =>
      `(tactic|
        first
          | exact LeanFX2.RawStep.parStar.unit_inv $chainProof
          | exact LeanFX2.RawStep.parStar.boolTrue_inv $chainProof
          | exact LeanFX2.RawStep.parStar.boolFalse_inv $chainProof
          | exact LeanFX2.RawStep.parStar.natZero_inv $chainProof
          | exact LeanFX2.RawStep.parStar.listNil_inv $chainProof
          | exact LeanFX2.RawStep.parStar.optionNone_inv $chainProof
          | exact LeanFX2.RawStep.parStar.var_inv $chainProof
          | exact LeanFX2.RawStep.parStar.universeCode_inv $chainProof
          | exact LeanFX2.RawStep.parStar.natSucc_inv $chainProof)

syntax "fx_raw_parstar_unit_inv " term : tactic
syntax "fx_raw_parstar_boolTrue_inv " term : tactic
syntax "fx_raw_parstar_boolFalse_inv " term : tactic
syntax "fx_raw_parstar_natZero_inv " term : tactic
syntax "fx_raw_parstar_var_inv " term : tactic
syntax "fx_raw_parstar_universeCode_inv " term : tactic

macro_rules
  | `(tactic| fx_raw_parstar_unit_inv $chainProof) =>
      `(tactic| exact LeanFX2.RawStep.parStar.unit_inv $chainProof)
  | `(tactic| fx_raw_parstar_boolTrue_inv $chainProof) =>
      `(tactic| exact LeanFX2.RawStep.parStar.boolTrue_inv $chainProof)
  | `(tactic| fx_raw_parstar_boolFalse_inv $chainProof) =>
      `(tactic| exact LeanFX2.RawStep.parStar.boolFalse_inv $chainProof)
  | `(tactic| fx_raw_parstar_natZero_inv $chainProof) =>
      `(tactic| exact LeanFX2.RawStep.parStar.natZero_inv $chainProof)
  | `(tactic| fx_raw_parstar_var_inv $chainProof) =>
      `(tactic| exact LeanFX2.RawStep.parStar.var_inv $chainProof)
  | `(tactic| fx_raw_parstar_universeCode_inv $chainProof) =>
      `(tactic| exact LeanFX2.RawStep.parStar.universeCode_inv $chainProof)

end LeanFX2.Tools.Tactics
