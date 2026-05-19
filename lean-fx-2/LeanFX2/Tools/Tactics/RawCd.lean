import LeanFX2.Confluence.RawCdRename.Main

/-! # Tools/Tactics/RawCd

Complete-development proof shorthands.

The `RawCdRename` cascade repeatedly unfolds `RawTerm.cd`, rewrites one
constructor-specific `cd*Case_rename` theorem, then discharges the remaining
shape by the local induction hypotheses.  These tactics expose only that
curated rewrite surface; they do not install global simp rules and they do not
search across the confluence library.
-/

namespace LeanFX2.Tools.Tactics

/-! ## Local cd unfolding -/

macro "fx_simp_raw_cd" : tactic =>
  `(tactic| simp only [LeanFX2.RawTerm.cd])

syntax "fx_simp_raw_cd" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_simp_raw_cd $location) =>
      `(tactic| simp only [LeanFX2.RawTerm.cd] $location)

/-! ## Complete-development rename rewrites -/

macro "fx_rw_raw_cd_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cd_rename])

syntax "fx_rw_raw_cd_rename" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| fx_rw_raw_cd_rename $location) =>
      `(tactic| rw [LeanFX2.RawTerm.cd_rename] $location)

/-! ## Redex-case rename rewrites -/

macro "fx_rw_cd_app_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdAppCase_rename])

macro "fx_rw_cd_path_app_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdPathAppCase_rename])

macro "fx_rw_cd_glue_elim_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdGlueElimCase_rename])

macro "fx_rw_cd_mod_elim_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdModElimCase_rename])

macro "fx_rw_cd_refine_elim_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdRefineElimCase_rename])

macro "fx_rw_cd_record_proj_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdRecordProjCase_rename])

macro "fx_rw_cd_codata_dest_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdCodataDestCase_rename])

macro "fx_rw_cd_fst_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdFstCase_rename])

macro "fx_rw_cd_snd_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdSndCase_rename])

macro "fx_rw_cd_bool_elim_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdBoolElimCase_rename])

macro "fx_rw_cd_nat_elim_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdNatElimCase_rename])

macro "fx_rw_cd_nat_rec_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdNatRecCase_rename])

macro "fx_rw_cd_list_elim_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdListElimCase_rename])

macro "fx_rw_cd_option_match_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdOptionMatchCase_rename])

macro "fx_rw_cd_either_match_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdEitherMatchCase_rename])

macro "fx_rw_cd_id_j_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdIdJCase_rename])

macro "fx_rw_cd_id_strict_rec_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdIdStrictRecCase_rename])

macro "fx_rw_cd_id_to_equiv_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdIdToEquivCase_rename])

macro "fx_rw_cd_ua_to_equiv_apply_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdUaToEquivApplyCase_rename])

macro "fx_rw_cd_equiv_apply_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdEquivApplyCase_rename])

macro "fx_rw_cd_transp_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdTranspCase_rename])

macro "fx_rw_cd_transp_pi_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdTranspPiCase_rename])

macro "fx_rw_cd_hcomp_case_rename" : tactic =>
  `(tactic| rw [LeanFX2.RawTerm.cdHcompCase_rename])

end LeanFX2.Tools.Tactics
