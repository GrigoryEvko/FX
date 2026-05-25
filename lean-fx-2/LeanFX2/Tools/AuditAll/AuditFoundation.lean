import LeanFX2.Tools.DependencyAudit
import LeanFX2.Foundation.Universe
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRename.UnweakenSubstCommute
import LeanFX2.Foundation.RawPartialRename.UnweakenSubstDispatch
import LeanFX2.Foundation.RawPartialRename.Swap01
import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer
import LeanFX2.Foundation.RawPartialRename.IsSomeInversion
import LeanFX2.Foundation.TyStrengthen
import LeanFX2.Foundation.TyStrengthenInversion
import LeanFX2.Foundation.TyRenameInjective
import LeanFX2.Foundation._deprecated_polygraph.Wellfounded
import LeanFX2.Foundation._deprecated_polygraph.DecEq
import LeanFX2.Foundation._deprecated_polygraph.FreeCategory
import LeanFX2.Reduction.RawParWeakenInv.Foundation

namespace LeanFX2.Tools

/-! ## AuditFoundation — foundation `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.PartialRawRenaming
#assert_no_axioms LeanFX2.PartialRawRenaming.lift
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest_weaken
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_dropNewest_weaken_lift
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_subst_compat
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest_subst_lift_compat
#assert_no_axioms LeanFX2.RawTerm.partialRename?_subst_compat
#assert_no_axioms LeanFX2.RawTerm.unweaken?_subst_lift_commute
#assert_no_axioms LeanFX2.RawTerm.unweaken?_subst_lift_dispatch_some
#assert_no_axioms LeanFX2.RawTerm.unweaken?_subst_lift_dispatch_none
#assert_no_axioms LeanFX2.UniverseLevel.toNat_not_injective
#assert_no_axioms LeanFX2.RawRenaming.swap01
#assert_no_axioms LeanFX2.RawRenaming.swap01_involution
#assert_no_axioms LeanFX2.RawRenaming.swap01_lift_lift_commute
#assert_no_axioms LeanFX2.RawTerm.swap01_rename_lift_lift_commute
#assert_no_axioms LeanFX2.RawTerm.swap01_subst_lift_lift_commute
#assert_no_axioms LeanFX2.RawTerm.transpPiBetaContractum
#assert_no_axioms LeanFX2.RawTerm.transpPiBetaContractum_rename
#assert_no_axioms LeanFX2.RawTerm.transpPiBetaContractum_subst
#assert_no_axioms LeanFX2.RawTerm.matchTranspPiBetaShape?
#assert_no_axioms LeanFX2.RawTerm.matchTranspPiBetaShape?_imp_piTyCode_weaken
#assert_no_axioms LeanFX2.RawTerm.matchTranspPiBetaShape?_rename
#assert_no_axioms LeanFX2.RawTerm.matchTranspPiBetaShape?_subst_some
#assert_no_axioms LeanFX2.RawTerm.matchTranspPiBetaShape?_piTyCode_weaken
#assert_no_axioms LeanFX2.RawTerm.partialRename?
#assert_no_axioms LeanFX2.RawTerm.unweaken?
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?
#assert_no_axioms LeanFX2.RawTerm.partialStrengthen?
#assert_no_axioms LeanFX2.RawTerm.partialStrengthen?_eq_partialRename?
#assert_no_axioms LeanFX2.RawTerm.partialStrengthen?_imp_rename
#assert_no_axioms LeanFX2.RawTerm.partialStrengthen?_rename_some
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_weaken_map
#assert_no_axioms LeanFX2.RawTerm.partialStrengthen?_weaken_lift
#assert_no_axioms LeanFX2.RawTerm.strengthen?
#assert_no_axioms LeanFX2.RawTerm.usesNewestSlot?
#assert_no_axioms LeanFX2.RawTerm.strengthen?_weaken
#assert_no_axioms LeanFX2.RawTerm.strengthen?_imp_weaken
#assert_no_axioms LeanFX2.RawTerm.not_usesNewestSlot?_imp_weaken
#assert_no_axioms LeanFX2.RawTerm.weaken_not_usesNewestSlot?
#assert_no_axioms LeanFX2.Ty.partialStrengthen?
#assert_no_axioms LeanFX2.Ty.strengthen?
#assert_no_axioms LeanFX2.Ty.usesNewestSlot?
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_rename_some
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_rename_compat
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_weaken_lift
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_imp_rename
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_subst0_of_success
#assert_no_axioms LeanFX2.Ty.strengthen?_weaken
#assert_no_axioms LeanFX2.Ty.strengthen?_imp_weaken
#assert_no_axioms LeanFX2.Ty.not_usesNewestSlot?_imp_weaken
#assert_no_axioms LeanFX2.Ty.rename_injective_under_injective_renaming
#assert_no_axioms LeanFX2.RawTerm.unweaken?_newest_var_none
#assert_no_axioms LeanFX2.RawTerm.unweaken?_weaken_var
#assert_no_axioms LeanFX2.RawTerm.partialRename?_lift_preserves_binder_var
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_rename_some
#assert_no_axioms LeanFX2.RawTerm.partialRename?_rename_some
#assert_no_axioms LeanFX2.RawTerm.unweaken?_weaken
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken
#assert_no_axioms LeanFX2.RawTerm.unweaken?_pathLam_binder_var
#assert_no_axioms LeanFX2.RawTerm.unweaken?_pathLam_dropped_outer_var_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_interval_var_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken_var
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_binder_var
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_interval_escape_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_unit_none
#assert_no_axioms LeanFX2.RawTerm.cdModElimCase
#assert_no_axioms LeanFX2.RawTerm.cdCodataDestCase

#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.ParallelPair
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.atomVertex
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.arrowSource
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.arrowTarget
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.cellSource
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.cellTarget
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.cellIdx
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.dimensionMeasure
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.cellSource_dimensionMeasure_lt
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.cellTarget_dimensionMeasure_lt
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.arrowSource_dimensionMeasure_lt
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.arrowTarget_dimensionMeasure_lt

#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell.atom_unique_at_dim0
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell.arrow_unique_at_dim1
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.PolyCell.cell_decompose_at_dimSucc
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.decEqAtDim0
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.decEqAtDim1
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.decEqAtDimSucc
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.polyCellDecEqAt
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.decEqPolyCell

#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.length
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.length_identity_eq_zero
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.length_cons_eq_succ_length_tail
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.append
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.append_identity_left
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.append_cons_unfold
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.append_identity_right
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.length_append_eq_sum_of_lengths
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.composeTwoCells
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.composeTwoCells_length_eq_two

#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.length
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.length_identity_eq_zero
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.length_cons_eq_succ_length_tail
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.append
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.append_identity_left
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.append_cons_unfold
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.append_identity_right
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.length_append_eq_sum_of_lengths
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.composeTwoArrows
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.composeTwoArrows_length_eq_two

#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.VerticalChain.append_assoc
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.HorizontalChain.append_assoc

#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeOneCategory.compose_assoc
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeOneCategory.identity_left
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeOneCategory.identity_right
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeOneCategory.fromGenerator
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeOneCategory.fromGenerator_length_eq_one
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeTwoCategoryAt.compose_assoc
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeTwoCategoryAt.identity_left
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeTwoCategoryAt.identity_right
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeTwoCategoryAt.fromGenerator
#assert_no_axioms LeanFX2.Foundation._deprecated_polygraph.FreeTwoCategoryAt.fromGenerator_length_eq_one

/-! ### RawRenaming weaken/lift injectivity (RawStep.par.weaken_inv prereq)

`RawRenaming.weaken_injective` and `RawRenaming.lift_injective` are
the foundational injectivity facts that `weaken_inv` (the Phase G
headline already gated) depends on transitively.  Propext-clean by
direct structural reasoning on `Fin` (per `feedback_lean_fin_cases_axiom.md`
— direct `⟨0, _⟩` / `⟨k+1, h⟩` matches instead of `Fin.cases`). -/

#assert_no_axioms LeanFX2.RawRenaming.weaken_injective
#assert_no_axioms LeanFX2.RawRenaming.lift_injective

/-! ### Ty per-ctor `partialStrengthen?_<ctor>_isSome` inversion lemmas

18 zero-axiom inversion lemmas decomposing
`((Ty.<ctor> args).partialStrengthen? back).isSome = true` into
per-sub-field `.isSome = true` facts.  Foundational for the eventual
universal typed-strengthening driver (Block B
`Step.par.preserves_rename_image`, #2022).  See
`Foundation/TyStrengthenInversion.lean`. -/

#assert_no_axioms LeanFX2.Ty.partialStrengthen?_arrow_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_piTy_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_sigmaTy_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_listType_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_optionType_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_eitherType_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_refine_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_codata_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_equiv_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_modal_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_record_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_session_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_effect_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_glue_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_id_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_path_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_oeq_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_idStrict_isSome

/-! ### RawTerm per-ctor `partialRename?_<ctor>_isSome` inversion

Zero-axiom inversion lemmas decomposing
`((RawTerm.<ctor> args).partialRename? back).isSome = true` into
per-sub-field `.isSome = true` facts.  Raw-side siblings of the
Ty inversion lemmas above; current coverage includes the original
pilot (lam, app, pair, fst, snd, listCons — binder + binary +
single-child shapes) and the single-child non-binder expansion
batch (natSucc, optionSome, eitherInl, eitherInr, refl, modIntro,
modElim, subsume, intervalOpp, glueElim).  Recipe is mechanically
identical for the remaining ctors and uses definitional tactics
only (`dsimp only` unfold + nested `match` + `cases` on impossible
`none` arms).  See `Foundation/RawPartialRename/IsSomeInversion.lean`. -/

#assert_no_axioms LeanFX2.RawTerm.partialRename?_lam_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_app_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_pair_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_fst_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_snd_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_listCons_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_natSucc_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_optionSome_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_eitherInl_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_eitherInr_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_refl_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_modIntro_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_modElim_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_subsume_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_intervalOpp_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_glueElim_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_idJ_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_intervalMeet_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_intervalJoin_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_pathApp_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_glueIntro_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_transp_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_boolElim_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_natElim_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_natRec_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_listElim_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_optionMatch_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_eitherMatch_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_oeqRefl_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_oeqFunext_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_idStrictRefl_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_refineElim_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_recordIntro_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_recordProj_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_codataDest_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_sessionRecv_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_listCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_optionCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_cumulUpMarker_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_uaToEquiv_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_idToEquiv_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_hcomp_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_oeqJ_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_idStrictRec_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_equivIntro_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_equivApp_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_refineIntro_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_codataUnfold_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_sessionSend_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_effectPerform_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_arrowCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_productCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_sumCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_eitherCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_equivCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_equivApply_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_pathCompose_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_oeqTrans_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_equivCompose_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_pathLam_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_piTyCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_sigmaTyCode_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_transpFill_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_idCode_isSome

-- Closed-atomic unconditional inversion lemmas (Foundation/RawPartialRename/
-- IsSomeInversion.lean tail).  Each ctor's `partialRename?` arm returns
-- `some <self>` unconditionally, so `.isSome = true` is a `rfl` proof.  These
-- gates lock the zero-axiom contract on the 9 closed-atomic inversion siblings
-- consumed by the eventual T5 universal driver for #2022 unblock-B.t5.par.
#assert_no_axioms LeanFX2.RawTerm.partialRename?_unit_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_boolTrue_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_boolFalse_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_natZero_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_listNil_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_optionNone_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_interval0_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_interval1_isSome
#assert_no_axioms LeanFX2.RawTerm.partialRename?_universeCode_isSome

-- Closed-atomic Ty unconditional inversion lemmas (Foundation/
-- TyStrengthenInversion.lean tail).  Each closed-atomic Ty ctor's
-- `partialStrengthen?` arm returns `some <self>` unconditionally
-- (matching the RawTerm closed-atomic family above); the
-- `.isSome = true` witness reduces to `rfl`.  These gates lock the
-- zero-axiom contract on the 6 Ty-side inversion siblings consumed
-- by the eventual T5 universal driver for #2022 unblock-B.t5.par
-- when the Term-side recursion hits a closed-atomic Ty arm.
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_unit_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_bool_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_nat_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_empty_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_interval_isSome
#assert_no_axioms LeanFX2.Ty.partialStrengthen?_universe_isSome

end LeanFX2.Tools
