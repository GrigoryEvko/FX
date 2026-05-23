import LeanFX2.Confluence.PreEtaStarInversion
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Confluence.ParStarBridge
import LeanFX2.Reduction.RawParWeakenInv.ParStar

/-! # Smoke/AuditParStarChainInversion

Reviewer-facing `#print axioms` gate for the
`LeanFX2.RawStep.parStar.*` per-constructor chain-inversion
family — the chain (reflexive-transitive closure) version of
`RawStep.par.*_inv`.

Each `_inv` lemma proves: if `RawStep.parStar source target`
holds and `source` has a particular constructor head, then
`target` also has that constructor head with each child related
by `parStar` to the corresponding source child.  Propext-clean
via toRaw-shape match (per
`feedback_lean_zero_axiom_match.md`) lifted across the
reflexive-transitive closure.

The 64 per-ctor entries below mirror
`Tools/AuditAll/AuditReduction.lean:655-720` (the cluster
between the `par.*_inv` smoke and the rename-injectivity Phase G
infrastructure section), plus 13 ancillary chain lemmas from
lines 748-764 covering:

* `rename_compatible` / `weaken_compatible` — chain analog of
  the single-step compatibility theorems;
* `target_in_{rename,weaken}_image[_of_source_eq]` — chain
  versions of the renaming/weakening image-membership lemmas
  consumed by `Step.parStar.invertRaw` (#2024);
* `weaken_inv` / `weaken_inv_of_source_eq` — chain analog of
  the Phase G weaken-inversion headline;
* `subst_compatible_same` / `subst0_compatible_same` —
  chain-level subst-compat needed by the bridge layer;
* `subst_par` / `subst0_par` — chain subst-Step.par mixers.

Each `#print axioms` line below must report "does not depend on
any axioms" — strict Layer K gate per `lean-fx-2/CLAUDE.md`. -/

namespace LeanFX2.Smoke.AuditParStarChainInversion

-- Closed-atomic ctors (no IH children, vacuous inversion).
#print axioms LeanFX2.RawStep.parStar.interval0_inv
#print axioms LeanFX2.RawStep.parStar.interval1_inv
#print axioms LeanFX2.RawStep.parStar.listNil_inv
#print axioms LeanFX2.RawStep.parStar.optionNone_inv

-- Single-IH ctors (nat / option / either / interval-opp / mod).
#print axioms LeanFX2.RawStep.parStar.natSucc_inv
#print axioms LeanFX2.RawStep.parStar.optionSome_inv
#print axioms LeanFX2.RawStep.parStar.eitherInl_inv
#print axioms LeanFX2.RawStep.parStar.eitherInr_inv
#print axioms LeanFX2.RawStep.parStar.intervalOpp_inv
#print axioms LeanFX2.RawStep.parStar.modIntro_inv
#print axioms LeanFX2.RawStep.parStar.modElim_inv
#print axioms LeanFX2.RawStep.parStar.subsume_inv
#print axioms LeanFX2.RawStep.parStar.cumulUpMarker_inv

-- Binary-IH ctors (app / pair / fst / snd / list-cons / interval-binops).
#print axioms LeanFX2.RawStep.parStar.app_inv
#print axioms LeanFX2.RawStep.parStar.pair_inv
#print axioms LeanFX2.RawStep.parStar.fst_inv
#print axioms LeanFX2.RawStep.parStar.snd_inv
#print axioms LeanFX2.RawStep.parStar.listCons_inv
#print axioms LeanFX2.RawStep.parStar.intervalMeet_inv
#print axioms LeanFX2.RawStep.parStar.intervalJoin_inv

-- Binder ctors (lam / pathLam).
#print axioms LeanFX2.RawStep.parStar.lam_inv
#print axioms LeanFX2.RawStep.parStar.pathLam_inv

-- ι-eliminators (boolElim / natElim / natRec / listElim / optionMatch /
-- eitherMatch).
#print axioms LeanFX2.RawStep.parStar.boolElim_inv
#print axioms LeanFX2.RawStep.parStar.natElim_inv
#print axioms LeanFX2.RawStep.parStar.natRec_inv
#print axioms LeanFX2.RawStep.parStar.listElim_inv
#print axioms LeanFX2.RawStep.parStar.optionMatch_inv
#print axioms LeanFX2.RawStep.parStar.eitherMatch_inv

-- HoTT family (refl / idJ / refine / record / codata / session / effect).
#print axioms LeanFX2.RawStep.parStar.refl_inv
#print axioms LeanFX2.RawStep.parStar.idJ_inv
#print axioms LeanFX2.RawStep.parStar.refineIntro_inv
#print axioms LeanFX2.RawStep.parStar.refineElim_inv
#print axioms LeanFX2.RawStep.parStar.recordIntro_inv
#print axioms LeanFX2.RawStep.parStar.recordProj_inv
#print axioms LeanFX2.RawStep.parStar.codataUnfold_inv
#print axioms LeanFX2.RawStep.parStar.codataDest_inv
#print axioms LeanFX2.RawStep.parStar.sessionSend_inv
#print axioms LeanFX2.RawStep.parStar.sessionRecv_inv
#print axioms LeanFX2.RawStep.parStar.effectPerform_inv

-- Observational + strict equality (oeq / idStrict / equiv).
#print axioms LeanFX2.RawStep.parStar.oeqRefl_inv
#print axioms LeanFX2.RawStep.parStar.oeqFunext_inv
#print axioms LeanFX2.RawStep.parStar.oeqJ_inv
#print axioms LeanFX2.RawStep.parStar.oeqTrans_inv
#print axioms LeanFX2.RawStep.parStar.idStrictRefl_inv
#print axioms LeanFX2.RawStep.parStar.idStrictRec_inv
#print axioms LeanFX2.RawStep.parStar.equivIntro_inv
#print axioms LeanFX2.RawStep.parStar.equivApp_inv
#print axioms LeanFX2.RawStep.parStar.equivApply_inv
#print axioms LeanFX2.RawStep.parStar.equivCompose_inv
#print axioms LeanFX2.RawStep.parStar.idToEquiv_inv
#print axioms LeanFX2.RawStep.parStar.uaToEquiv_inv

-- Cubical (glue / transp / hcomp / pathApp / pathCompose / transpFill).
#print axioms LeanFX2.RawStep.parStar.glueIntro_inv
#print axioms LeanFX2.RawStep.parStar.glueElim_inv
#print axioms LeanFX2.RawStep.parStar.transp_inv
#print axioms LeanFX2.RawStep.parStar.transpFill_inv
#print axioms LeanFX2.RawStep.parStar.hcomp_inv
#print axioms LeanFX2.RawStep.parStar.pathApp_inv
#print axioms LeanFX2.RawStep.parStar.pathCompose_inv

-- Type-code ctors (list / option / arrow / piTy / sigmaTy / product /
-- sum / either / equiv / id).
#print axioms LeanFX2.RawStep.parStar.listCode_inv
#print axioms LeanFX2.RawStep.parStar.optionCode_inv
#print axioms LeanFX2.RawStep.parStar.arrowCode_inv
#print axioms LeanFX2.RawStep.parStar.piTyCode_inv
#print axioms LeanFX2.RawStep.parStar.sigmaTyCode_inv
#print axioms LeanFX2.RawStep.parStar.productCode_inv
#print axioms LeanFX2.RawStep.parStar.sumCode_inv
#print axioms LeanFX2.RawStep.parStar.eitherCode_inv
#print axioms LeanFX2.RawStep.parStar.equivCode_inv
#print axioms LeanFX2.RawStep.parStar.idCode_inv

-- Chain ancillary lemmas: compatibility + image-membership +
-- weaken-inversion + subst-mixers.
#print axioms LeanFX2.RawStep.parStar.rename_compatible
#print axioms LeanFX2.RawStep.parStar.weaken_compatible
#print axioms LeanFX2.RawStep.parStar.target_in_rename_image
#print axioms LeanFX2.RawStep.parStar.target_in_rename_image_of_source_eq
#print axioms LeanFX2.RawStep.parStar.target_in_weaken_image
#print axioms LeanFX2.RawStep.parStar.target_in_weaken_image_of_source_eq
#print axioms LeanFX2.RawStep.parStar.weaken_inv
#print axioms LeanFX2.RawStep.parStar.weaken_inv_of_source_eq
#print axioms LeanFX2.RawStep.parStar.subst_compatible_same
#print axioms LeanFX2.RawStep.parStar.subst0_compatible_same
#print axioms LeanFX2.RawStep.parStar.subst0_par
#print axioms LeanFX2.RawStep.parStar.subst_par

end LeanFX2.Smoke.AuditParStarChainInversion
