import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.ParRed
import LeanFX2.Term.ToRaw
import LeanFX2.Term.Pointwise
import LeanFX2.Bridge
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Algo.WHNF
import LeanFX2.Cubical.Path
import LeanFX2.Cubical.PathLemmas

/-! # AuditPhase12A2Day2 — Day 2 (Phase 12.A.2) zero-axiom audit.

Day 2 of the cubical+2LTT+HOTT sprint shipped:
* D2.5–D2.7 — raw-level reductions, plus typed path-application,
  Glue-elimination, transport-cong, and hcomp-cong parity for D2.5.
  At the raw level the cong rules for all 27 new ctors landed earlier;
  this audit also anchors the D2.5 raw betaPathApp / Glue beta
  increments and the typed beta mirrors.
  Remaining raw β/ι rules for new ctors are still paired with their
  cd-extension in Confluence/RawCd.lean before being claimed.
* D2.9 — RawStep.par 27 new cong rules (DONE in 2afe3493)
* D2.10 — Compat extension for 27 new cong rules in
  RawParRename.lean and RawParCompatible.lean (DONE in 2afe3493)
* D2.11 — THIS audit, plus 27 new inversion lemmas added in this commit.

Strategic deferral:
* D2.5 transport / hcomp computational rules still wait for their full
  typed semantics.  The current typed `transp` and `hcomp` slice is
  congruence parity only.
* D2.6–D2.7 additional typed rules wait for typed Term ctors to land per-need
  (matches D1.9 deferral).

The project build implicitly verifies zero-axiom; this file
explicitly enumerates the Day-2 deliverables.

Every declaration listed must report "does not depend on any axioms".
-/

-- Cong-layer extensions (from prior commits)
#print axioms LeanFX2.RawStep.par.intervalOppCong
#print axioms LeanFX2.RawStep.par.intervalMeetCong
#print axioms LeanFX2.RawStep.par.intervalJoinCong
#print axioms LeanFX2.RawStep.par.pathLamCong
#print axioms LeanFX2.RawStep.par.pathAppCong
#print axioms LeanFX2.RawStep.par.betaPathApp
#print axioms LeanFX2.RawStep.par.betaPathAppDeep
#print axioms LeanFX2.RawStep.par.glueIntroCong
#print axioms LeanFX2.RawStep.par.betaGlueElimIntro
#print axioms LeanFX2.RawStep.par.betaGlueElimIntroDeep
#print axioms LeanFX2.RawStep.par.glueElimCong
#print axioms LeanFX2.RawStep.par.transpCong
#print axioms LeanFX2.RawStep.par.hcompCong
#print axioms LeanFX2.RawStep.par.oeqReflCong
#print axioms LeanFX2.RawStep.par.oeqJCong
#print axioms LeanFX2.RawStep.par.oeqFunextCong
#print axioms LeanFX2.RawStep.par.idStrictReflCong
#print axioms LeanFX2.RawStep.par.idStrictRecCong
#print axioms LeanFX2.RawStep.par.equivIntroCong
#print axioms LeanFX2.RawStep.par.equivAppCong
#print axioms LeanFX2.RawStep.par.refineIntroCong
#print axioms LeanFX2.RawStep.par.betaRefineElimIntro
#print axioms LeanFX2.RawStep.par.betaRefineElimIntroDeep
#print axioms LeanFX2.RawStep.par.refineElimCong
#print axioms LeanFX2.RawStep.par.recordIntroCong
#print axioms LeanFX2.RawStep.par.betaRecordProjIntro
#print axioms LeanFX2.RawStep.par.betaRecordProjIntroDeep
#print axioms LeanFX2.RawStep.par.recordProjCong
#print axioms LeanFX2.RawStep.par.codataUnfoldCong
#print axioms LeanFX2.RawStep.par.codataDestCong
#print axioms LeanFX2.RawStep.par.sessionSendCong
#print axioms LeanFX2.RawStep.par.sessionRecvCong
#print axioms LeanFX2.RawStep.par.effectPerformCong

-- Typed D2.5 path-application parity
#print axioms LeanFX2.Term.toRaw_interval0
#print axioms LeanFX2.Term.toRaw_interval1
#print axioms LeanFX2.Term.toRaw_intervalOpp
#print axioms LeanFX2.Term.toRaw_intervalMeet
#print axioms LeanFX2.Term.toRaw_intervalJoin
#print axioms LeanFX2.Term.toRaw_pathLam
#print axioms LeanFX2.Term.toRaw_pathApp
#print axioms LeanFX2.Cubical.constantPath
#print axioms LeanFX2.Cubical.constantPath_toRaw
#print axioms LeanFX2.Cubical.constantTypePath
#print axioms LeanFX2.Cubical.constantTypePath_toRaw
#print axioms LeanFX2.Cubical.constantPath_rawBetaApp
#print axioms LeanFX2.Cubical.constantPath_betaPathApp
#print axioms LeanFX2.Term.toRaw_glueIntro
#print axioms LeanFX2.Term.toRaw_glueElim
#print axioms LeanFX2.Term.toRaw_transp
#print axioms LeanFX2.Term.toRaw_hcomp
#print axioms LeanFX2.Term.subst_pointwise
#print axioms LeanFX2.Step.par.pathLam
#print axioms LeanFX2.Step.par.pathApp
#print axioms LeanFX2.Step.intervalOppInner
#print axioms LeanFX2.Step.intervalMeetLeft
#print axioms LeanFX2.Step.intervalMeetRight
#print axioms LeanFX2.Step.intervalJoinLeft
#print axioms LeanFX2.Step.intervalJoinRight
#print axioms LeanFX2.Step.par.intervalOppCong
#print axioms LeanFX2.Step.par.intervalMeetCong
#print axioms LeanFX2.Step.par.intervalJoinCong
#print axioms LeanFX2.Step.betaPathApp
#print axioms LeanFX2.Step.par.betaPathApp
#print axioms LeanFX2.Step.par.betaPathAppDeep
#print axioms LeanFX2.Step.par.glueIntro
#print axioms LeanFX2.Step.par.glueElim
#print axioms LeanFX2.Step.betaGlueElimIntro
#print axioms LeanFX2.Step.par.betaGlueElimIntro
#print axioms LeanFX2.Step.par.betaGlueElimIntroDeep
#print axioms LeanFX2.Step.par.transp
#print axioms LeanFX2.Step.par.hcomp
#print axioms LeanFX2.Step.par.toRawBridge
#print axioms LeanFX2.ConvCumul.pathLamCong
#print axioms LeanFX2.ConvCumul.pathAppCong
#print axioms LeanFX2.ConvCumul.intervalOppCong
#print axioms LeanFX2.ConvCumul.intervalMeetCong
#print axioms LeanFX2.ConvCumul.intervalJoinCong
#print axioms LeanFX2.ConvCumul.betaPathAppCumul
#print axioms LeanFX2.ConvCumul.glueIntroCong
#print axioms LeanFX2.ConvCumul.glueElimCong
#print axioms LeanFX2.ConvCumul.betaGlueElimIntroCumul
#print axioms LeanFX2.ConvCumul.transpCong
#print axioms LeanFX2.ConvCumul.hcompCong
#print axioms LeanFX2.ConvCumul.subst_compatible_interval0_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_interval1_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_intervalOpp_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_intervalMeet_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_intervalJoin_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_pathLam_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_pathApp_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_glueIntro_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_glueElim_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_transp_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_hcomp_allais
#print axioms LeanFX2.Term.subst_compatible_pointwise_allais
#print axioms LeanFX2.Term.headCtor
#print axioms LeanFX2.Term.isWHNF

-- Inversion lemmas (this commit) — 27 new cases
#print axioms LeanFX2.RawStep.par.interval0_inv
#print axioms LeanFX2.RawStep.par.interval1_inv
#print axioms LeanFX2.RawStep.par.intervalOpp_inv
#print axioms LeanFX2.RawStep.par.intervalMeet_inv
#print axioms LeanFX2.RawStep.par.intervalJoin_inv
#print axioms LeanFX2.RawStep.par.pathLam_inv
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
#print axioms LeanFX2.RawStep.par.refineIntro_inv
#print axioms LeanFX2.RawStep.par.refineElim_inv
#print axioms LeanFX2.RawStep.par.recordIntro_inv
#print axioms LeanFX2.RawStep.par.recordProj_inv
#print axioms LeanFX2.RawStep.par.codataUnfold_inv
#print axioms LeanFX2.RawStep.par.codataDest_inv
#print axioms LeanFX2.RawStep.par.sessionSend_inv
#print axioms LeanFX2.RawStep.par.sessionRecv_inv
#print axioms LeanFX2.RawStep.par.effectPerform_inv
