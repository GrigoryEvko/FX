import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParInversion

/-! # AuditPhase12A2Day2 — Day 2 (Phase 12.A.2) zero-axiom audit.

Day 2 of the cubical+2LTT+HOTT sprint shipped:
* D2.5–D2.7 — RAW-LEVEL only (typed Step rules deferred with D1.9).
  At the raw level the cong rules for all 27 new ctors landed earlier;
  this audit now also anchors the D2.5 raw betaPathApp and Glue beta
  increments.
  Remaining raw β/ι rules for new ctors are still paired with their
  cd-extension in Confluence/RawCd.lean before being claimed.
* D2.9 — RawStep.par 27 new cong rules (DONE in 2afe3493)
* D2.10 — Compat extension for 27 new cong rules in
  RawParRename.lean and RawParCompatible.lean (DONE in 2afe3493)
* D2.11 — THIS audit, plus 27 new inversion lemmas added in this commit.

Strategic deferral:
* D2.5–D2.7 typed Step rules — wait for typed Term ctors to land
  per-need (matches D1.9 deferral)
* D2.8 typed Step.par — same rationale as D2.5

The 213-job project build implicitly verifies zero-axiom; this file
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
#print axioms LeanFX2.RawStep.par.refineElimCong
#print axioms LeanFX2.RawStep.par.recordIntroCong
#print axioms LeanFX2.RawStep.par.recordProjCong
#print axioms LeanFX2.RawStep.par.codataUnfoldCong
#print axioms LeanFX2.RawStep.par.codataDestCong
#print axioms LeanFX2.RawStep.par.sessionSendCong
#print axioms LeanFX2.RawStep.par.sessionRecvCong
#print axioms LeanFX2.RawStep.par.effectPerformCong

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
