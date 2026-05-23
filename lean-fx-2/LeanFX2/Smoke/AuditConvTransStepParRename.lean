import LeanFX2.Reduction.ParRed.RenameCompatibleTyped

/-! # Smoke/AuditConvTransStepParRename — typed `Step.par` rename-equivariance arms

Reviewer-facing `#print axioms` log for the per-constructor arms of the
typed `Step.par.rename_compatible_typed` headline — the rename-equivariance
cong/β arms shipped incrementally for the typed parallel-reduction layer.

`Reduction/ParRed/RenameCompatibleTyped.lean` carries 94
`rename_compatible_typed_<ctor>` arms plus two HEq-congruence helpers
(`transp_typePath_heqCongr`, `hcompPath_sidesPath_heqCongr`) consumed by
the `transpReflBeta` / `hcompBeta` arms.  Each arm states that the typed
parallel step commutes with a renaming of its source/target, the standard
`ParRed` substitutivity lemma specialized per constructor.

## Gating relationship

The build-failing strict gates live in `Tools/AuditAll/AuditReduction.lean`
(one `#assert_no_axioms` per arm) and, transitively, in the broad
namespace sweep `#audit_namespace LeanFX2` (`Tools/AuditAll/GatesNsSweepAxiom.lean`).
This file is the co-located reviewer log: each `#print axioms` invocation
prints "does not depend on any axioms", keeping the human-readable
zero-axiom certificate adjacent to the kernel source for the rename-arm
family — mirroring the `AuditConvTransB3*` β/ι reviewer logs.

## Root status

Zero-axiom. -/

namespace LeanFX2.SmokeConvTransStepParRename

#print axioms LeanFX2.Step.par.rename_compatible_typed_refl
#print axioms LeanFX2.Step.par.rename_compatible_typed_fst
#print axioms LeanFX2.Step.par.rename_compatible_typed_app
#print axioms LeanFX2.Step.par.rename_compatible_typed_lamPi
#print axioms LeanFX2.Step.par.rename_compatible_typed_natSucc
#print axioms LeanFX2.Step.par.rename_compatible_typed_listCons
#print axioms LeanFX2.Step.par.rename_compatible_typed_optionSome
#print axioms LeanFX2.Step.par.rename_compatible_typed_eitherInl
#print axioms LeanFX2.Step.par.rename_compatible_typed_eitherInr
#print axioms LeanFX2.Step.par.rename_compatible_typed_natElim
#print axioms LeanFX2.Step.par.rename_compatible_typed_natRec
#print axioms LeanFX2.Step.par.rename_compatible_typed_listElim
#print axioms LeanFX2.Step.par.rename_compatible_typed_optionMatch
#print axioms LeanFX2.Step.par.rename_compatible_typed_eitherMatch
#print axioms LeanFX2.Step.par.rename_compatible_typed_modIntro
#print axioms LeanFX2.Step.par.rename_compatible_typed_modElim
#print axioms LeanFX2.Step.par.rename_compatible_typed_subsume
#print axioms LeanFX2.Step.par.rename_compatible_typed_lam
#print axioms LeanFX2.Step.par.rename_compatible_typed_appPi
#print axioms LeanFX2.Step.par.rename_compatible_typed_snd
#print axioms LeanFX2.Step.par.rename_compatible_typed_pair
#print axioms LeanFX2.Step.par.rename_compatible_typed_boolElim
#print axioms LeanFX2.Step.par.rename_compatible_typed_idJ
#print axioms LeanFX2.Step.par.rename_compatible_typed_oeqJCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_idStrictRecCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_intervalOppCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_intervalMeetCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_intervalJoinCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_recordIntroCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_recordProjCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_refineIntroCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_refineElimCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_pathAppCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_glueIntroCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_glueElimCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_transpCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_hcompCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_hcompPathCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_codataUnfoldCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_codataDestCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_sessionSendCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_sessionRecvCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_effectPerformCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_cumulUpInnerCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_eqType
#print axioms LeanFX2.Step.par.rename_compatible_typed_reflCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_funextReflAtIdCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_funextIntroHetCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_arrowCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_piTyCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_sigmaTyCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_productCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_sumCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_listCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_optionCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_eitherCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_idCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_equivCodeCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_equivAppCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_equivApplyCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_uaIntroHetCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_uaToEquivCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_oeqReflCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_idStrictReflCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_pathLamCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_oeqFunextCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_eqArrow
#print axioms LeanFX2.Step.par.rename_compatible_typed_eqTypeHet
#print axioms LeanFX2.Step.par.rename_compatible_typed_eqArrowHet
#print axioms LeanFX2.Step.par.rename_compatible_typed_funextReflCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_equivIntroHetCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_equivIntroCong
#print axioms LeanFX2.Step.par.rename_compatible_typed_pathApp
#print axioms LeanFX2.Step.par.rename_compatible_typed_glueIntro
#print axioms LeanFX2.Step.par.rename_compatible_typed_glueElim
#print axioms LeanFX2.Step.par.rename_compatible_typed_transp
#print axioms LeanFX2.Step.par.rename_compatible_typed_hcomp
#print axioms LeanFX2.Step.par.rename_compatible_typed_pathLam
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaFstPair
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaSndPair
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaGlueElimIntro
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaRecordProjIntro
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaModElimIntro
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaRefineElimIntro
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaCodataDestUnfold
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaModElimIntroDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaCodataDestUnfoldDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaGlueElimIntroDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaRecordProjIntroDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaRefineElimIntroDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaFstPairDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaSndPairDeep
#print axioms LeanFX2.Step.par.castTargetType_cancel
#print axioms LeanFX2.Step.par.castSourceType_cancel
#print axioms LeanFX2.Step.par.transp_typePath_heqCongr
#print axioms LeanFX2.Step.par.rename_compatible_typed_transpReflBeta
#print axioms LeanFX2.Step.par.rename_compatible_typed_transpReflBetaDeep
#print axioms LeanFX2.Step.par.hcompPath_sidesPath_heqCongr
#print axioms LeanFX2.Step.par.rename_compatible_typed_hcompBeta
#print axioms LeanFX2.Step.par.rename_compatible_typed_hcompBetaDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatElimZero
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatElimSucc
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatRecZero
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatRecSucc
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaListElimNil
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaListElimCons
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaOptionMatchNone
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaOptionMatchSome
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaEitherMatchInl
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaEitherMatchInr
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaIdJRefl
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaIdStrictRecRefl
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaBoolElimTrue
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaBoolElimFalse
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaApp
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaAppPi
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatElimZeroDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatElimSuccDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatRecZeroDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaNatRecSuccDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaListElimNilDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaListElimConsDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaOptionMatchNoneDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaOptionMatchSomeDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaEitherMatchInlDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaEitherMatchInrDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaIdJReflDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaIdStrictRecReflDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaPathApp
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaBoolElimTrueDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_iotaBoolElimFalseDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaAppDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaAppPiDeep
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaPathAppDeep
#print axioms LeanFX2.Step.par.pathReflApp_body_heqCongr
#print axioms LeanFX2.Step.par.rename_compatible_typed_betaPathReflApp

end LeanFX2.SmokeConvTransStepParRename
