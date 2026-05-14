import LeanFX2.Reduction.RawParInversion
import LeanFX2.Confluence.RawParStarCong

/-! Phase 6.B inversion-lemma zero-axiom audit.

These 16 inversion lemmas use `cases` on a single-Nat-indexed Prop
inductive (RawStep.par).  Per `feedback_lean_match_arity_axioms.md`,
single-Nat-indexed inductives don't trigger propext+Quot.sound on
`cases` — but verify per-lemma anyway. -/

#print axioms LeanFX2.RawStep.par.lam_inv
#print axioms LeanFX2.RawStep.par.pair_inv
#print axioms LeanFX2.RawStep.par.refl_inv
#print axioms LeanFX2.RawStep.par.unit_inv
#print axioms LeanFX2.RawStep.par.boolTrue_inv
#print axioms LeanFX2.RawStep.par.boolFalse_inv
#print axioms LeanFX2.RawStep.par.natZero_inv
#print axioms LeanFX2.RawStep.par.natSucc_inv
#print axioms LeanFX2.RawStep.par.listNil_inv
#print axioms LeanFX2.RawStep.par.listCons_inv
#print axioms LeanFX2.RawStep.par.optionNone_inv
#print axioms LeanFX2.RawStep.par.optionSome_inv
#print axioms LeanFX2.RawStep.par.eitherInl_inv
#print axioms LeanFX2.RawStep.par.eitherInr_inv
#print axioms LeanFX2.RawStep.par.modIntro_inv
#print axioms LeanFX2.RawStep.par.modElim_inv
#print axioms LeanFX2.RawStep.par.subsume_inv

/-! ## Phase 3 (#1590 TYPED-SR-TERM-CONSTRUCTION) — multi-step canonical inversions

`RawStep.parStar.<head>_inv` lifts the single-step inversions
through chain induction.  Each is a one-line specialization of the
generic `canonical_inv_helper` private lemma.  Used by
`Conv.canonicalForm_<head>` corollaries to constrain target raw form
when source has a canonical-head raw projection. -/

#print axioms LeanFX2.RawStep.parStar.unit_inv
#print axioms LeanFX2.RawStep.parStar.boolTrue_inv
#print axioms LeanFX2.RawStep.parStar.boolFalse_inv
#print axioms LeanFX2.RawStep.parStar.natZero_inv
#print axioms LeanFX2.RawStep.parStar.listNil_inv
#print axioms LeanFX2.RawStep.parStar.optionNone_inv
#print axioms LeanFX2.RawStep.parStar.var_inv
#print axioms LeanFX2.RawStep.parStar.universeCode_inv
#print axioms LeanFX2.RawStep.parStar.natSucc_inv

/-! ## Coverage extension — remaining `RawStep.par.<ctor>_inv` audit pins

Per the post-M04 stabilization roadmap chores §1.3:
extend audit-pin coverage to ALL `RawStep.par.<ctor>_inv` lemmas
shipped under `LeanFX2/Reduction/RawParInversion/` and
`LeanFX2/Reduction/RawParWeakenInv/`.

Pure documentation — every inversion below was already shipped and
gated under `#assert_no_axioms` via the `#audit_namespace LeanFX2`
sweep in `Tools/AuditAll/`.  Adding the per-decl `#print axioms`
lines here makes coverage explicit to reviewers and ensures
regression visibility when a new inversion is added.

Grouped by source sub-module. -/

/-! ### `RawParInversion/AtomicCtors.lean` — var (other atomic ctors
covered in Phase 1 above). -/

#print axioms LeanFX2.RawStep.par.var_inv

/-! ### `RawParInversion/TypeCodes.lean` — type-code ctors. -/

#print axioms LeanFX2.RawStep.par.arrowCode_inv
#print axioms LeanFX2.RawStep.par.piTyCode_inv
#print axioms LeanFX2.RawStep.par.sigmaTyCode_inv
#print axioms LeanFX2.RawStep.par.productCode_inv
#print axioms LeanFX2.RawStep.par.sumCode_inv
#print axioms LeanFX2.RawStep.par.listCode_inv
#print axioms LeanFX2.RawStep.par.optionCode_inv
#print axioms LeanFX2.RawStep.par.eitherCode_inv
#print axioms LeanFX2.RawStep.par.idCode_inv
#print axioms LeanFX2.RawStep.par.equivCode_inv
#print axioms LeanFX2.RawStep.par.equivApply_inv
#print axioms LeanFX2.RawStep.par.universeCode_inv

/-! ### `RawParInversion/RedexParents.lean` — elimination heads. -/

#print axioms LeanFX2.RawStep.par.app_inv
#print axioms LeanFX2.RawStep.par.fst_inv
#print axioms LeanFX2.RawStep.par.snd_inv
#print axioms LeanFX2.RawStep.par.boolElim_inv
#print axioms LeanFX2.RawStep.par.natElim_inv
#print axioms LeanFX2.RawStep.par.natRec_inv
#print axioms LeanFX2.RawStep.par.listElim_inv
#print axioms LeanFX2.RawStep.par.optionMatch_inv
#print axioms LeanFX2.RawStep.par.eitherMatch_inv
#print axioms LeanFX2.RawStep.par.idJ_inv

/-! ### `RawParInversion/CubicalAndIdentity.lean` — cubical + identity ctors. -/

#print axioms LeanFX2.RawStep.par.intervalOpp_inv
#print axioms LeanFX2.RawStep.par.intervalMeet_inv
#print axioms LeanFX2.RawStep.par.intervalJoin_inv
#print axioms LeanFX2.RawStep.par.pathLam_inv
#print axioms LeanFX2.RawStep.par.uaToEquiv_inv
#print axioms LeanFX2.RawStep.par.pathCompose_inv
#print axioms LeanFX2.RawStep.par.idToEquiv_inv
#print axioms LeanFX2.RawStep.par.oeqTrans_inv
#print axioms LeanFX2.RawStep.par.equivCompose_inv
#print axioms LeanFX2.RawStep.par.pathApp_inv
#print axioms LeanFX2.RawStep.par.glueIntro_inv
#print axioms LeanFX2.RawStep.par.glueElim_inv
#print axioms LeanFX2.RawStep.par.transp_inv
#print axioms LeanFX2.RawStep.par.hcomp_inv
#print axioms LeanFX2.RawStep.par.oeqRefl_inv
#print axioms LeanFX2.RawStep.par.oeqJ_inv
#print axioms LeanFX2.RawStep.par.oeqFunext_inv
#print axioms LeanFX2.RawStep.par.idStrictRefl_inv
#print axioms LeanFX2.RawStep.par.idStrictRec_inv
#print axioms LeanFX2.RawStep.par.equivIntro_inv
#print axioms LeanFX2.RawStep.par.equivApp_inv

/-! ### `RawParInversion/ModalAndAdvanced.lean` — cumul/refine/record/
codata/session/effect (other modal ctors covered in Phase 1 above). -/

#print axioms LeanFX2.RawStep.par.cumulUpMarker_inv
#print axioms LeanFX2.RawStep.par.refineIntro_inv
#print axioms LeanFX2.RawStep.par.refineElim_inv
#print axioms LeanFX2.RawStep.par.recordIntro_inv
#print axioms LeanFX2.RawStep.par.recordProj_inv
#print axioms LeanFX2.RawStep.par.codataUnfold_inv
#print axioms LeanFX2.RawStep.par.codataDest_inv
#print axioms LeanFX2.RawStep.par.sessionSend_inv
#print axioms LeanFX2.RawStep.par.sessionRecv_inv
#print axioms LeanFX2.RawStep.par.effectPerform_inv

/-! ### `RawParWeakenInv/Weaken.lean` — weakening inversion. -/

#print axioms LeanFX2.RawStep.par.weaken_inv
