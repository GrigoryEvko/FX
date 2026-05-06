import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

/-! # Tools/AuditAll — build-failing zero-axiom gate

This file is intentionally executable: importing it runs
`#assert_no_axioms` over load-bearing kernel declarations.  Unlike
`#print axioms`, these gates fail elaboration when any dependency tree
contains an axiom, including Lean core axioms such as `propext`,
`Quot.sound`, or `Classical.choice`.

This is not yet a generated whole-namespace audit.  It is a curated
machine-enforced gate for the current coverage-gap list and typed D2.5
path / Glue parity slices.
-/

namespace LeanFX2.Tools

-- Raw partial-renaming foundation for safe weakening recognition
#assert_no_axioms LeanFX2.PartialRawRenaming
#assert_no_axioms LeanFX2.PartialRawRenaming.lift
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest_weaken
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_dropNewest_weaken_lift
#assert_no_axioms LeanFX2.Option.mapTwo
#assert_no_axioms LeanFX2.Option.mapThree
#assert_no_axioms LeanFX2.RawTerm.partialRename?
#assert_no_axioms LeanFX2.RawTerm.unweaken?
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?
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

-- Term core
#assert_no_axioms LeanFX2.Term.subst
#assert_no_axioms LeanFX2.Term.rename
#assert_no_axioms LeanFX2.Term.toRaw_rename
#assert_no_axioms LeanFX2.Term.toRaw_subst
#assert_no_axioms LeanFX2.Term.toRaw_weaken
#assert_no_axioms LeanFX2.Term.toRaw_subst0
#assert_no_axioms LeanFX2.Term.toRaw_universeCode
#assert_no_axioms LeanFX2.Term.toRaw_cumulUp
#assert_no_axioms LeanFX2.Term.toRaw_equivReflId
#assert_no_axioms LeanFX2.Term.toRaw_funextRefl
#assert_no_axioms LeanFX2.Term.toRaw_equivReflIdAtId
#assert_no_axioms LeanFX2.Term.toRaw_funextReflAtId
#assert_no_axioms LeanFX2.Term.toRaw_equivIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_uaIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_funextIntroHet
#assert_no_axioms LeanFX2.Term.toRaw_arrowCode
#assert_no_axioms LeanFX2.Term.toRaw_piTyCode
#assert_no_axioms LeanFX2.Term.toRaw_sigmaTyCode
#assert_no_axioms LeanFX2.Term.toRaw_productCode
#assert_no_axioms LeanFX2.Term.toRaw_sumCode
#assert_no_axioms LeanFX2.Term.toRaw_listCode
#assert_no_axioms LeanFX2.Term.toRaw_optionCode
#assert_no_axioms LeanFX2.Term.toRaw_eitherCode
#assert_no_axioms LeanFX2.Term.toRaw_idCode
#assert_no_axioms LeanFX2.Term.toRaw_equivCode
#assert_no_axioms LeanFX2.Step.castSourceRaw
#assert_no_axioms LeanFX2.Step.castTargetRaw
#assert_no_axioms LeanFX2.Step.par.castSourceRaw
#assert_no_axioms LeanFX2.Step.par.castTargetRaw

-- Confluence core
#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.par.glueElim_inv
#assert_no_axioms LeanFX2.RawStep.par.pathLam_inv

-- Raw D2.5 cubical beta rules
#assert_no_axioms LeanFX2.RawStep.par.betaPathApp
#assert_no_axioms LeanFX2.RawStep.par.betaPathAppDeep
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaGlueElimIntroDeep
#assert_no_axioms LeanFX2.RawStep.par.betaModElimIntro
#assert_no_axioms LeanFX2.RawStep.par.betaModElimIntroDeep
#assert_no_axioms LeanFX2.RawTerm.cdModElimCase
#assert_no_axioms LeanFX2.RawStep.par.betaCodataDestUnfold
#assert_no_axioms LeanFX2.RawStep.par.betaCodataDestUnfoldDeep
#assert_no_axioms LeanFX2.RawTerm.cdCodataDestCase

-- Typed D2.5 path-application parity
#assert_no_axioms LeanFX2.Term.toRaw_interval0
#assert_no_axioms LeanFX2.Term.toRaw_interval1
#assert_no_axioms LeanFX2.Term.toRaw_intervalOpp
#assert_no_axioms LeanFX2.Term.toRaw_intervalMeet
#assert_no_axioms LeanFX2.Term.toRaw_intervalJoin
#assert_no_axioms LeanFX2.Term.toRaw_pathLam
#assert_no_axioms LeanFX2.Term.toRaw_pathApp
#assert_no_axioms LeanFX2.Cubical.constantPath
#assert_no_axioms LeanFX2.Cubical.constantPath_toRaw
#assert_no_axioms LeanFX2.Cubical.constantTypePath
#assert_no_axioms LeanFX2.Cubical.constantTypePath_toRaw
#assert_no_axioms LeanFX2.Cubical.constantPath_rawRecognized
#assert_no_axioms LeanFX2.Cubical.constantTypePath_rawRecognized
#assert_no_axioms LeanFX2.Cubical.intervalBinderPath
#assert_no_axioms LeanFX2.Cubical.intervalBinderPath_rawRejected
#assert_no_axioms LeanFX2.Cubical.constantPath_rawBetaApp
#assert_no_axioms LeanFX2.Cubical.constantPath_betaPathApp
#assert_no_axioms LeanFX2.Cubical.constantPath_betaPathApp_toRawEndpoint
#assert_no_axioms LeanFX2.Cubical.constantTypePath_betaPathApp
#assert_no_axioms LeanFX2.Cubical.constantTypePath_betaPathApp_toRawEndpoint
#assert_no_axioms LeanFX2.Bridge.constantPathToId
#assert_no_axioms LeanFX2.Bridge.constantPathToId_toRaw
#assert_no_axioms LeanFX2.Bridge.constantPathToId_onCanonical
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath_toRaw
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath_onRefl
#assert_no_axioms LeanFX2.Bridge.constantPath_roundTrip_onCanonical
#assert_no_axioms LeanFX2.Bridge.reflId_roundTrip_onRefl
#assert_no_axioms LeanFX2.Bridge.constantPath_roundTrip_toRaw
#assert_no_axioms LeanFX2.Bridge.reflId_roundTrip_toRaw
#assert_no_axioms LeanFX2.Bridge.pathToIdMeta
#assert_no_axioms LeanFX2.Bridge.idToPathMeta
#assert_no_axioms LeanFX2.Bridge.idToPathMeta_pathToIdMeta
#assert_no_axioms LeanFX2.Bridge.pathToIdMeta_idToPathMeta
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta_toFun
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta_invFun
#assert_no_axioms LeanFX2.Bridge.idEqTypeRefl
#assert_no_axioms LeanFX2.Bridge.idEqTypeHet
#assert_no_axioms LeanFX2.Bridge.constantTypePathToEquivRefl
#assert_no_axioms LeanFX2.Bridge.constantTypePathToEquivRefl_toRaw
#assert_no_axioms LeanFX2.Bridge.constantTypePathToEquivRefl_onCanonical
#assert_no_axioms LeanFX2.Cubical.constantPathToObservationalId
#assert_no_axioms LeanFX2.Cubical.constantPathToObservationalId_toRaw
#assert_no_axioms LeanFX2.Cubical.constantPathToObservationalId_onCanonical
#assert_no_axioms LeanFX2.Cubical.observationalReflToConstantPath
#assert_no_axioms LeanFX2.Cubical.observationalReflToConstantPath_toRaw
#assert_no_axioms LeanFX2.Cubical.constantCubicalTypePathToEquiv
#assert_no_axioms LeanFX2.Cubical.constantCubicalTypePathToEquiv_toRaw
#assert_no_axioms LeanFX2.Cubical.constantCubicalTypePathToEquiv_onCanonical
#assert_no_axioms LeanFX2.Cubical.pathIdMetaEquiv
#assert_no_axioms LeanFX2.Cubical.uaReflConv
#assert_no_axioms LeanFX2.Cubical.uaHetConv
#assert_no_axioms LeanFX2.Cubical.uaConstantTypePathToEquiv
#assert_no_axioms LeanFX2.Cubical.uaConstantTypePathToEquiv_toRaw
#assert_no_axioms LeanFX2.Cubical.uaConstantTypePathToEquiv_onCanonical
#assert_no_axioms LeanFX2.Cubical.uaBetaMeta
#assert_no_axioms LeanFX2.Cubical.uaBetaMetaRefl
#assert_no_axioms LeanFX2.Cubical.uaBetaMetaSymm
#assert_no_axioms LeanFX2.Cubical.uaTransportViaReflEquiv
#assert_no_axioms LeanFX2.Cubical.uaKernelRflAlignsWithMeta
#assert_no_axioms LeanFX2.Translation.cubicalToObservationalTy
#assert_no_axioms LeanFX2.Translation.cubicalToObservationalTy_interval
#assert_no_axioms LeanFX2.Translation.cubicalToObservationalTy_path
#assert_no_axioms LeanFX2.Translation.cubicalToObservationalTy_glue
#assert_no_axioms LeanFX2.Translation.cubicalToObservationalTy_id
#assert_no_axioms LeanFX2.Translation.observationalToCubicalTy
#assert_no_axioms LeanFX2.Translation.observationalToCubicalTy_id
#assert_no_axioms LeanFX2.Translation.observationalToCubicalTy_oeq
#assert_no_axioms LeanFX2.Translation.observationalToCubicalTy_idStrict
#assert_no_axioms LeanFX2.Translation.observationalToCubicalTy_path
#assert_no_axioms LeanFX2.Translation.observationalCubicalRoundTripTy_unit
#assert_no_axioms LeanFX2.Translation.observationalCubicalRoundTripTy_bool
#assert_no_axioms LeanFX2.Translation.observationalCubicalRoundTripTy_nat
#assert_no_axioms LeanFX2.Translation.cubicalObservationalRoundTripTy_unit
#assert_no_axioms LeanFX2.Translation.cubicalObservationalRoundTripTy_bool
#assert_no_axioms LeanFX2.Translation.cubicalObservationalRoundTripTy_nat
#assert_no_axioms LeanFX2.Translation.observationalCubicalRoundTripTy_id
#assert_no_axioms LeanFX2.Translation.cubicalObservationalRoundTripTy_path
#assert_no_axioms LeanFX2.InternalLanguage.unitEqualityTranslationCoherence
#assert_no_axioms LeanFX2.Conservativity.isMLTTOnlyTy
#assert_no_axioms LeanFX2.Conservativity.hottToMLTTTy
#assert_no_axioms LeanFX2.Conservativity.hottToMLTTTy_preserves_isMLTTOnlyTy
#assert_no_axioms LeanFX2.Conservativity.isCubicalFreeTy
#assert_no_axioms LeanFX2.Conservativity.cubicalToObservationalTy_preserves_isCubicalFreeTy
#assert_no_axioms LeanFX2.Conservativity.isModalFreeTy
#assert_no_axioms LeanFX2.Conservativity.modalToObservationalTy
#assert_no_axioms LeanFX2.Conservativity.modalToObservationalTy_preserves_isModalFreeTy
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.appendStr
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.appendNum
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.isAnonymous
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.isAnonymous_anonymous
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.isAnonymous_str
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.isAnonymous_num
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.beq
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.beq_sound
#assert_no_axioms LeanFX2.FX1.LeanKernel.Name.eqResult
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.beq
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.normalize
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.nodeCount
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.leBoolWithFuel
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.leBool
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.le
#assert_no_axioms LeanFX2.FX1.LeanKernel.Level.normalize_zero
#assert_no_axioms LeanFX2.FX1.LeanKernel.FVarId
#assert_no_axioms LeanFX2.FX1.LeanKernel.MVarId
#assert_no_axioms LeanFX2.FX1.LeanKernel.BinderInfo
#assert_no_axioms LeanFX2.FX1.LeanKernel.Literal
#assert_no_axioms LeanFX2.FX1.LeanKernel.MDataEntry
#assert_no_axioms LeanFX2.FX1.LeanKernel.MData
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.recontextualize
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.nodeCount
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.nodeCount_app
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.nodeCount_mdata
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprRenaming
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprRenaming.lift
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprRenaming.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprRenaming.lift_newest
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprRenaming.lift_succ
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.renameWith
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprSubstitution
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprSubstitution.lift
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprSubstitution.singleton
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprSubstitution.singleton_newest
#assert_no_axioms LeanFX2.FX1.LeanKernel.ExprSubstitution.singleton_succ
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.subst
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.instantiate
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.instantiate_bvar_zero
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.instantiate_bvar_succ
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.weaken_bvar
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step.betaStep
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step.zetaStep
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step.metadataStep
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step.betaStep_newest_bvar
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step.betaStep_succ_bvar
#assert_no_axioms LeanFX2.FX1.LeanKernel.Step.zetaStep_newest_bvar
#assert_no_axioms LeanFX2.FX1.LeanKernel.ConstantSpec
#assert_no_axioms LeanFX2.FX1.LeanKernel.ConstructorSpec
#assert_no_axioms LeanFX2.FX1.LeanKernel.InductiveSpec
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstant?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findInductive?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstant?_empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findInductive?_empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList.newest
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList.older
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstant
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.extend
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.weakenEntries
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.extendForBinder
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.HasTypeAt
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.HasTypeAt.newest
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.HasTypeAt.older
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.HasTypeAt.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.HasType
#assert_no_axioms LeanFX2.FX1.LeanKernel.HasType.sort
#assert_no_axioms LeanFX2.FX1.LeanKernel.HasType.bvar
#assert_no_axioms LeanFX2.FX1.LeanKernel.HasType.const
#assert_no_axioms LeanFX2.FX1.LeanKernel.HasType.forallE
#assert_no_axioms LeanFX2.FX1.LeanKernel.HasType.lam
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.ConstantLookupResult
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstantResultInList?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstantResult?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.LookupTypeResult
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.lookupTypeResultInEntries?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Context.lookupTypeResult?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.InferResult
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.inferTypeFromResult?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.inferResult?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.infer?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.inferTypeFromResult?_sound
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.infer?_sound
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.check?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.check?_sound
#assert_no_axioms LeanFX2.FX1.LeanKernel.check
#assert_no_axioms LeanFX2.FX1.LeanKernel.check_sound
#assert_no_axioms LeanFX2.Cubical.glueIntroduction
#assert_no_axioms LeanFX2.Cubical.glueIntroduction_toRaw
#assert_no_axioms LeanFX2.Cubical.glueElimination
#assert_no_axioms LeanFX2.Cubical.glueElimination_toRaw
#assert_no_axioms LeanFX2.Cubical.glueIntroduction_parCong
#assert_no_axioms LeanFX2.Cubical.glueElimination_parCong
#assert_no_axioms LeanFX2.Cubical.glueIntroduction_convCumul
#assert_no_axioms LeanFX2.Cubical.glueElimination_convCumul
#assert_no_axioms LeanFX2.Cubical.glueElimIntro_parBeta
#assert_no_axioms LeanFX2.Cubical.glueElimIntro_convCumulBeta
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition_toRaw
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition_parCong
#assert_no_axioms LeanFX2.Cubical.homogeneousComposition_convCumul
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition_toRaw
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition_parCong
#assert_no_axioms LeanFX2.Cubical.degenerateHomogeneousComposition_convCumul
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_toRaw
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_typeLineRecognized
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceCong
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceCong_toRawBridge
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_sourceConvCumul
#assert_no_axioms LeanFX2.Cubical.constantTypeTransport_betaConvCumul
#assert_no_axioms LeanFX2.Step.par.pathLam
#assert_no_axioms LeanFX2.Step.par.pathLamCong
#assert_no_axioms LeanFX2.Step.par.pathApp
#assert_no_axioms LeanFX2.Step.par.pathAppCong
#assert_no_axioms LeanFX2.Step.betaModElimIntro
#assert_no_axioms LeanFX2.Step.par.betaModElimIntro
#assert_no_axioms LeanFX2.Step.par.betaModElimIntroDeep
#assert_no_axioms LeanFX2.ConvCumul.betaModElimIntroCumul
#assert_no_axioms LeanFX2.ConvCumul.betaModElimIntroCumul_toConv
#assert_no_axioms LeanFX2.Step.toConvCumul
#assert_no_axioms LeanFX2.RawStep.par.iotaIdStrictRecRefl
#assert_no_axioms LeanFX2.RawStep.par.iotaIdStrictRecReflDeep
#assert_no_axioms LeanFX2.Step.intervalOppInner
#assert_no_axioms LeanFX2.Step.intervalMeetLeft
#assert_no_axioms LeanFX2.Step.intervalMeetRight
#assert_no_axioms LeanFX2.Step.intervalJoinLeft
#assert_no_axioms LeanFX2.Step.intervalJoinRight
#assert_no_axioms LeanFX2.Step.par.intervalOppCong
#assert_no_axioms LeanFX2.Step.par.intervalMeetCong
#assert_no_axioms LeanFX2.Step.par.intervalJoinCong
#assert_no_axioms LeanFX2.ConvCumul.intervalOppCong
#assert_no_axioms LeanFX2.ConvCumul.intervalMeetCong
#assert_no_axioms LeanFX2.ConvCumul.intervalJoinCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_intervalOpp_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_intervalMeet_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_intervalJoin_allais
#assert_no_axioms LeanFX2.Step.par.betaPathApp
#assert_no_axioms LeanFX2.Step.par.betaPathAppDeep
#assert_no_axioms LeanFX2.Step.par.toRawBridge
#assert_no_axioms LeanFX2.Step.par.rename_toRawBridge
#assert_no_axioms LeanFX2.Step.par.subst_toRawBridge
#assert_no_axioms LeanFX2.RawStep.par.rename_compatible
#assert_no_axioms LeanFX2.RawStep.par.subst_compatible
#assert_no_axioms LeanFX2.RawStep.par.subst_compatible_same

-- Typed D2.5 Glue-elimination parity
#assert_no_axioms LeanFX2.Term.toRaw_glueIntro
#assert_no_axioms LeanFX2.Term.toRaw_glueElim
#assert_no_axioms LeanFX2.Step.par.glueIntro
#assert_no_axioms LeanFX2.Step.par.glueIntroCong
#assert_no_axioms LeanFX2.Step.par.glueElim
#assert_no_axioms LeanFX2.Step.par.glueElimCong
#assert_no_axioms LeanFX2.Step.par.transpCong
#assert_no_axioms LeanFX2.Step.par.hcompCong
#assert_no_axioms LeanFX2.Step.par.betaGlueElimIntro
#assert_no_axioms LeanFX2.Step.par.betaGlueElimIntroDeep
#assert_no_axioms LeanFX2.ConvCumul.glueIntroCong
#assert_no_axioms LeanFX2.ConvCumul.glueElimCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_glueIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_glueElim_allais
#assert_no_axioms LeanFX2.Term.headCtor
#assert_no_axioms LeanFX2.Term.isWHNF

-- Typed D2.5 transport / hcomp congruence parity
#assert_no_axioms LeanFX2.Term.toRaw_transp
#assert_no_axioms LeanFX2.Term.toRaw_hcomp
#assert_no_axioms LeanFX2.Step.par.transp
#assert_no_axioms LeanFX2.Step.par.hcomp
#assert_no_axioms LeanFX2.ConvCumul.transpCong
#assert_no_axioms LeanFX2.ConvCumul.betaTranspConstantTypeCumul
#assert_no_axioms LeanFX2.ConvCumul.hcompCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_transp_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_hcomp_allais

-- Typed D2.6 OEq congruence parity
#assert_no_axioms LeanFX2.Term.toRaw_oeqRefl
#assert_no_axioms LeanFX2.Term.toRaw_oeqJ
#assert_no_axioms LeanFX2.Term.toRaw_oeqFunext
#assert_no_axioms LeanFX2.Step.oeqJBase
#assert_no_axioms LeanFX2.Step.oeqJWitness
#assert_no_axioms LeanFX2.Step.oeqFunextPointwise
#assert_no_axioms LeanFX2.Step.par.oeqReflCong
#assert_no_axioms LeanFX2.Step.par.oeqJCong
#assert_no_axioms LeanFX2.Step.par.oeqFunextCong
#assert_no_axioms LeanFX2.ConvCumul.oeqJCong
#assert_no_axioms LeanFX2.ConvCumul.oeqFunextCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_oeqRefl_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_oeqJ_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_oeqFunext_allais

-- Typed D2.7 single-field record parity
#assert_no_axioms LeanFX2.Term.toRaw_recordIntro
#assert_no_axioms LeanFX2.Term.toRaw_recordProj
#assert_no_axioms LeanFX2.Step.recordIntroField
#assert_no_axioms LeanFX2.Step.recordProjRecord
#assert_no_axioms LeanFX2.Step.betaRecordProjIntro
#assert_no_axioms LeanFX2.Step.par.recordIntroCong
#assert_no_axioms LeanFX2.Step.par.recordProjCong
#assert_no_axioms LeanFX2.Step.par.betaRecordProjIntro
#assert_no_axioms LeanFX2.Step.par.betaRecordProjIntroDeep
#assert_no_axioms LeanFX2.ConvCumul.recordIntroCong
#assert_no_axioms LeanFX2.ConvCumul.recordProjCong
#assert_no_axioms LeanFX2.ConvCumul.betaRecordProjIntroCumul
#assert_no_axioms LeanFX2.ConvCumul.betaRecordProjIntroCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_recordIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_recordProj_allais

-- Typed D2.7 strict-identity congruence parity plus strict-refl ι-reduction
#assert_no_axioms LeanFX2.Term.toRaw_idStrictRefl
#assert_no_axioms LeanFX2.Term.toRaw_idStrictRec
#assert_no_axioms LeanFX2.Step.idStrictRecBase
#assert_no_axioms LeanFX2.Step.idStrictRecWitness
#assert_no_axioms LeanFX2.Step.iotaIdStrictRecRefl
#assert_no_axioms LeanFX2.Step.par.idStrictReflCong
#assert_no_axioms LeanFX2.Step.par.idStrictRecCong
#assert_no_axioms LeanFX2.Step.par.iotaIdStrictRecRefl
#assert_no_axioms LeanFX2.Step.par.iotaIdStrictRecReflDeep
#assert_no_axioms LeanFX2.ConvCumul.idStrictRecCong
#assert_no_axioms LeanFX2.ConvCumul.iotaIdStrictRecReflCumul
#assert_no_axioms LeanFX2.ConvCumul.iotaIdStrictRecReflCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_idStrictRefl_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_idStrictRec_allais

-- Typed D2.6/D2.8 equivalence-application parity
#assert_no_axioms LeanFX2.Term.toRaw_equivApp
#assert_no_axioms LeanFX2.Step.equivAppEquiv
#assert_no_axioms LeanFX2.Step.equivAppArgument
#assert_no_axioms LeanFX2.Step.par.equivAppCong
#assert_no_axioms LeanFX2.ConvCumul.equivAppCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_equivApp_allais

-- Typed D2.7 refinement intro/elim parity
#assert_no_axioms LeanFX2.Term.toRaw_refineIntro
#assert_no_axioms LeanFX2.Term.toRaw_refineElim
#assert_no_axioms LeanFX2.Step.refineIntroValue
#assert_no_axioms LeanFX2.Step.refineIntroProof
#assert_no_axioms LeanFX2.Step.refineElimValue
#assert_no_axioms LeanFX2.Step.betaRefineElimIntro
#assert_no_axioms LeanFX2.Step.par.refineIntroCong
#assert_no_axioms LeanFX2.Step.par.refineElimCong
#assert_no_axioms LeanFX2.Step.par.betaRefineElimIntro
#assert_no_axioms LeanFX2.Step.par.betaRefineElimIntroDeep
#assert_no_axioms LeanFX2.ConvCumul.refineIntroCong
#assert_no_axioms LeanFX2.ConvCumul.refineElimCong
#assert_no_axioms LeanFX2.ConvCumul.betaRefineElimIntroCumul
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_refineIntro_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_refineElim_allais

-- Typed D2.7 codata congruence parity
#assert_no_axioms LeanFX2.Term.toRaw_codataUnfold
#assert_no_axioms LeanFX2.Term.toRaw_codataDest
#assert_no_axioms LeanFX2.Step.codataUnfoldState
#assert_no_axioms LeanFX2.Step.codataUnfoldTransition
#assert_no_axioms LeanFX2.Step.codataDestValue
#assert_no_axioms LeanFX2.Step.betaCodataDestUnfold
#assert_no_axioms LeanFX2.Step.par.codataUnfoldCong
#assert_no_axioms LeanFX2.Step.par.betaCodataDestUnfold
#assert_no_axioms LeanFX2.Step.par.betaCodataDestUnfoldDeep
#assert_no_axioms LeanFX2.Step.par.codataDestCong
#assert_no_axioms LeanFX2.ConvCumul.codataUnfoldCong
#assert_no_axioms LeanFX2.ConvCumul.codataDestCong
#assert_no_axioms LeanFX2.ConvCumul.betaCodataDestUnfoldCumul
#assert_no_axioms LeanFX2.ConvCumul.betaCodataDestUnfoldCumul_toConv
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_codataUnfold_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_codataDest_allais

-- Typed D2.7 session/effect congruence parity
#assert_no_axioms LeanFX2.Term.toRaw_sessionSend
#assert_no_axioms LeanFX2.Term.toRaw_sessionRecv
#assert_no_axioms LeanFX2.Term.toRaw_effectPerform
#assert_no_axioms LeanFX2.Step.sessionSendChannel
#assert_no_axioms LeanFX2.Step.sessionSendPayload
#assert_no_axioms LeanFX2.Step.sessionRecvChannel
#assert_no_axioms LeanFX2.Step.effectPerformOperation
#assert_no_axioms LeanFX2.Step.effectPerformArguments
#assert_no_axioms LeanFX2.Step.par.sessionSendCong
#assert_no_axioms LeanFX2.Step.par.sessionRecvCong
#assert_no_axioms LeanFX2.Step.par.effectPerformCong
#assert_no_axioms LeanFX2.ConvCumul.sessionSendCong
#assert_no_axioms LeanFX2.ConvCumul.sessionRecvCong
#assert_no_axioms LeanFX2.ConvCumul.effectPerformCong
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_sessionSend_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_sessionRecv_allais
#assert_no_axioms LeanFX2.ConvCumul.subst_compatible_effectPerform_allais

-- Conv core
#assert_no_axioms LeanFX2.Conv.refl
#assert_no_axioms LeanFX2.Conv.fromStep
#assert_no_axioms LeanFX2.Conv.toRawJoin
#assert_no_axioms LeanFX2.Conv.canonicalRaw
#assert_no_axioms LeanFX2.Conv.transRaw

-- Day 3 HoTT equivalence, univalence, funext, and path algebra.
#assert_no_axioms LeanFX2.Equiv.refl
#assert_no_axioms LeanFX2.Equiv.symm
#assert_no_axioms LeanFX2.Equiv.trans
#assert_no_axioms LeanFX2.Equiv.trans_refl_left_toFun
#assert_no_axioms LeanFX2.Equiv.trans_refl_right_toFun
#assert_no_axioms LeanFX2.IsContr.unit
#assert_no_axioms LeanFX2.IsEquiv.identity
#assert_no_axioms LeanFX2.Univalence
#assert_no_axioms LeanFX2.UnivalenceHet
#assert_no_axioms LeanFX2.Univalence.idToEquivMeta
#assert_no_axioms LeanFX2.Univalence.idToEquivMeta_isEquiv_toFun
#assert_no_axioms LeanFX2.Univalence.idToEquivMeta_isEquiv_invFun
#assert_no_axioms LeanFX2.Univalence.ua_beta_meta
#assert_no_axioms LeanFX2.Univalence.ua_beta_toFun_pointwise
#assert_no_axioms LeanFX2.Univalence.ua_beta_invFun_pointwise
#assert_no_axioms LeanFX2.funext
#assert_no_axioms LeanFX2.FunextHet
#assert_no_axioms LeanFX2.Funext.fnEqToPointwiseMeta
#assert_no_axioms LeanFX2.Funext.pointwiseMetaToFnEqAtRefl
#assert_no_axioms LeanFX2.Funext.kernelMetaCorrespondence_atRefl
#assert_no_axioms LeanFX2.Path.trans
#assert_no_axioms LeanFX2.Path.symm
#assert_no_axioms LeanFX2.Path.trans_assoc
#assert_no_axioms LeanFX2.Path.trans_refl_left
#assert_no_axioms LeanFX2.Path.trans_refl_right
#assert_no_axioms LeanFX2.Path.symm_symm
#assert_no_axioms LeanFX2.Path.trans_symm_left
#assert_no_axioms LeanFX2.Path.trans_symm_right
#assert_no_axioms LeanFX2.Path.symm_trans
#assert_no_axioms LeanFX2.PathGroupoidLaws
#assert_no_axioms LeanFX2.PathGroupoidLaws.instance
#assert_no_axioms LeanFX2.Path.trans_left_cancel
#assert_no_axioms LeanFX2.Path.trans_right_cancel

-- HoTT HIT setoid foundation
#assert_no_axioms LeanFX2.HoTT.HIT.EmptyPathLabel
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.hasPathBetween
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.discrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSpec.discrete_hasNoPath
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.preservesRelation
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.discrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.indiscrete
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.fromEquivalence
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.HITSetoid.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.run
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.run_respects
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.constant
#assert_no_axioms LeanFX2.HoTT.HIT.HITRecursor.constant_run
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.run
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.run_respects
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.constant
#assert_no_axioms LeanFX2.HoTT.HIT.HITInductor.constant_run
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec_squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.dependentInductor_intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.dependentInductor_squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.recConstant
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.recConstant_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.path
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec_path
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.dependentInductor_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.dependentInductor_path
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.equality
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec_sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.dependentInductor_intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.dependentInductor_sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.recConstant
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.recConstant_intro
#assert_no_axioms LeanFX2.HoTT.HIT.S1PointLabel
#assert_no_axioms LeanFX2.HoTT.HIT.S1PathLabel
#assert_no_axioms LeanFX2.HoTT.HIT.S1Spec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopSpec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.setoid
#assert_no_axioms LeanFX2.HoTT.HIT.S1.base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.forwardLoop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.backwardLoop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopForward
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopBackward
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopBetween
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.recFromWinding
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec_loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.recFromWinding_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.recFromWinding_loopBetween
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor_loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor_loopBetween
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionPoint
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.setoid
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.meridian
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_meridian
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor_north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor_south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor_meridian
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutCarrier
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.evaluate
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentEvaluate
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.glue
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_glue
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor_left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor_right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor_glue
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.equalize
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec_point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec_equalize
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.dependentInductor_point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.dependentInductor_equalize
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.quotientUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.propTruncUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.setTruncUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.s1BaseUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.suspensionNorthUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.pushoutUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.pushoutLeftUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.coequalizerUnit
#assert_no_axioms LeanFX2.HoTT.HIT.Examples.coequalizerPointUnit

-- Codata stream structural layer
#assert_no_axioms LeanFX2.Codata.Stream
#assert_no_axioms LeanFX2.Codata.Stream.head
#assert_no_axioms LeanFX2.Codata.Stream.tail
#assert_no_axioms LeanFX2.Codata.Stream.iterateState
#assert_no_axioms LeanFX2.Codata.Stream.unfold
#assert_no_axioms LeanFX2.Codata.Stream.Bisim
#assert_no_axioms LeanFX2.Codata.Stream.bisim_refl
#assert_no_axioms LeanFX2.Codata.Stream.bisim_symm
#assert_no_axioms LeanFX2.Codata.Stream.bisim_trans
#assert_no_axioms LeanFX2.Codata.Stream.head_unfold
#assert_no_axioms LeanFX2.Codata.Stream.tail_unfold
#assert_no_axioms LeanFX2.Codata.Stream.bisim_head
#assert_no_axioms LeanFX2.Codata.Stream.bisim_tail
#assert_no_axioms LeanFX2.Codata.Stream.productive
#assert_no_axioms LeanFX2.Codata.constantZero
#assert_no_axioms LeanFX2.Codata.naturals
#assert_no_axioms LeanFX2.Codata.Stream.Destructor
#assert_no_axioms LeanFX2.Codata.Stream.Destructor.Result
#assert_no_axioms LeanFX2.Codata.Stream.Step
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_deterministic
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_deterministic
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_respects_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_respects_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_unfold
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_unfold_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Productive
#assert_no_axioms LeanFX2.Codata.Stream.productive_of_stream
#assert_no_axioms LeanFX2.Codata.Stream.productive_head
#assert_no_axioms LeanFX2.Codata.Stream.productive_tail
#assert_no_axioms LeanFX2.Codata.Stream.productive_unfold
#assert_no_axioms LeanFX2.Codata.Stream.productive_of_bisim

-- Effect row structural layer
#assert_no_axioms LeanFX2.Effects.EffectLabel
#assert_no_axioms LeanFX2.Effects.EffectRow.Member
#assert_no_axioms LeanFX2.Effects.EffectRow.empty
#assert_no_axioms LeanFX2.Effects.EffectRow.singleton
#assert_no_axioms LeanFX2.Effects.EffectRow.subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join
#assert_no_axioms LeanFX2.Effects.EffectRow.member_append_left
#assert_no_axioms LeanFX2.Effects.EffectRow.member_append_right
#assert_no_axioms LeanFX2.Effects.EffectRow.member_append_inv
#assert_no_axioms LeanFX2.Effects.EffectRow.subset_refl
#assert_no_axioms LeanFX2.Effects.EffectRow.subset_trans
#assert_no_axioms LeanFX2.Effects.EffectRow.empty_subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join_subset_left
#assert_no_axioms LeanFX2.Effects.EffectRow.join_subset_right
#assert_no_axioms LeanFX2.Effects.EffectRow.join_least_upper_bound
#assert_no_axioms LeanFX2.Effects.EffectRow.join_idempotent_subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join_commutes_subset
#assert_no_axioms LeanFX2.Effects.EffectRow.join_associates_subset
#assert_no_axioms LeanFX2.Effects.read_subset_writeRead
#assert_no_axioms LeanFX2.Effects.OperationSignature
#assert_no_axioms LeanFX2.Effects.CanPerform
#assert_no_axioms LeanFX2.Effects.CanPerform.mono
#assert_no_axioms LeanFX2.Effects.CanPerform.join_left
#assert_no_axioms LeanFX2.Effects.CanPerform.join_right
#assert_no_axioms LeanFX2.Effects.Action
#assert_no_axioms LeanFX2.Effects.Step
#assert_no_axioms LeanFX2.Effects.Step.mono
#assert_no_axioms LeanFX2.Effects.Step.join_left
#assert_no_axioms LeanFX2.Effects.Step.join_right
#assert_no_axioms LeanFX2.Effects.Step.result_deterministic
#assert_no_axioms LeanFX2.Effects.HandlerCase
#assert_no_axioms LeanFX2.Effects.Handles
#assert_no_axioms LeanFX2.Effects.Handles.to_step
#assert_no_axioms LeanFX2.Effects.Handles.result_deterministic

-- Session protocol structural layer
#assert_no_axioms LeanFX2.SessionProtocol
#assert_no_axioms LeanFX2.SessionProtocol.depth
#assert_no_axioms LeanFX2.SessionProtocol.isFinite
#assert_no_axioms LeanFX2.SessionProtocol.isFinite_of_tree
#assert_no_axioms LeanFX2.SessionProtocol.isFiniteDecidable
#assert_no_axioms LeanFX2.SessionProtocol.isFinite.decidable
#assert_no_axioms LeanFX2.SessionProtocol.dual
#assert_no_axioms LeanFX2.SessionProtocol.dual_end
#assert_no_axioms LeanFX2.SessionProtocol.dual_involutive
#assert_no_axioms LeanFX2.SessionProtocol.Action
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual_involutive
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual_injective
#assert_no_axioms LeanFX2.SessionProtocol.Step
#assert_no_axioms LeanFX2.SessionProtocol.Step.preserves_isFinite
#assert_no_axioms LeanFX2.SessionProtocol.Step.dual
#assert_no_axioms LeanFX2.SessionProtocol.Step.not_from_end
#assert_no_axioms LeanFX2.SessionProtocol.Step.target_deterministic
#assert_no_axioms LeanFX2.SessionProtocol.Step.of_dual
#assert_no_axioms LeanFX2.SessionProtocol.Step.dual_iff
#assert_no_axioms LeanFX2.SessionGlobal
#assert_no_axioms LeanFX2.SessionGlobal.isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.transmit_self_not_isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.choice_self_not_isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.Projects
#assert_no_axioms LeanFX2.SessionGlobal.Projects.local_isFinite

-- Graded core
#assert_no_axioms LeanFX2.Graded.GradeVector.add_mono
#assert_no_axioms LeanFX2.Graded.GradeVector.mul_mono
#assert_no_axioms LeanFX2.Graded.GradeAttribution.add_mono
#assert_no_axioms LeanFX2.Graded.GradeAttribution.scaleBy_mono
#assert_no_axioms LeanFX2.Graded.GradedCtx.le
#assert_no_axioms LeanFX2.Graded.GradedCtx.le_refl
#assert_no_axioms LeanFX2.Graded.GradedCtx.le_trans
#assert_no_axioms LeanFX2.Graded.IsLamCompatible
#assert_no_axioms LeanFX2.Graded.IsLamCompatibleWithAvailable
#assert_no_axioms LeanFX2.Graded.IsLamCompatibleWithAvailable.available_mono
#assert_no_axioms LeanFX2.Graded.GradeAttribution.scaleBy
#assert_no_axioms LeanFX2.Graded.IsAppCompatible.mono
#assert_no_axioms LeanFX2.Graded.IsLetCompatible.mono
#assert_no_axioms LeanFX2.Graded.IsIfCompatible.mono
#assert_no_axioms LeanFX2.Graded.GradedCtx.toCtx
#assert_no_axioms LeanFX2.Graded.GradedTerm
#assert_no_axioms LeanFX2.Graded.GradedTerm.unit
#assert_no_axioms LeanFX2.Graded.GradedTerm.boolTrue
#assert_no_axioms LeanFX2.Graded.GradedTerm.boolFalse
#assert_no_axioms LeanFX2.Graded.GradedTerm.var
#assert_no_axioms LeanFX2.Graded.GradedTerm.lam
#assert_no_axioms LeanFX2.Graded.GradedTerm.app
#assert_no_axioms LeanFX2.Graded.GradedTerm.boolElim
#assert_no_axioms LeanFX2.Graded.GradedTerm.subsumeGrade
#assert_no_axioms LeanFX2.Graded.GradedTerm.underlying_toRaw

-- Dimensions21 registry and aggregate carrier operations
#assert_no_axioms LeanFX2.Graded.allDimensionSlots_length
#assert_no_axioms LeanFX2.Graded.semiringDimensionEntries21
#assert_no_axioms LeanFX2.Graded.joinDimensionEntries21
#assert_no_axioms LeanFX2.Graded.structuralDimensionEntries21
#assert_no_axioms LeanFX2.Graded.semiringDimensionSlots21
#assert_no_axioms LeanFX2.Graded.joinDimensionSlots21
#assert_no_axioms LeanFX2.Graded.structuralDimensionSlots21
#assert_no_axioms LeanFX2.Graded.semiringDimensionEntries21_length
#assert_no_axioms LeanFX2.Graded.joinDimensionEntries21_length
#assert_no_axioms LeanFX2.Graded.structuralDimensionEntries21_length
#assert_no_axioms LeanFX2.Graded.semiringDimensions21_length
#assert_no_axioms LeanFX2.Graded.semiringDimensionSlots21_length
#assert_no_axioms LeanFX2.Graded.joinDimensions21_length
#assert_no_axioms LeanFX2.Graded.joinDimensionSlots21_length
#assert_no_axioms LeanFX2.Graded.structuralDimensionSlots21_length
#assert_no_axioms LeanFX2.Graded.semiringDimensions21_slots_length_match
#assert_no_axioms LeanFX2.Graded.joinDimensions21_slots_length_match
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.bottom
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.one
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.le_refl
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.le_trans
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.joinGrades_bottom_le
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_semiring_one_left
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_semiring_one_right
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_join_left_le
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_join_right_le
#assert_no_axioms LeanFX2.Graded.JoinGradeVector.join_mono
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.join_mono
#assert_no_axioms LeanFX2.Graded.FXGradeVector21.compose_mono

-- FX1/Core minimal syntax and M1 environment scaffold
#assert_no_axioms LeanFX2.FX1.Boolean.and_true_left
#assert_no_axioms LeanFX2.FX1.Boolean.and_true_right
#assert_no_axioms LeanFX2.FX1.EqualityResult
#assert_no_axioms LeanFX2.FX1.EqualityResult.equal
#assert_no_axioms LeanFX2.FX1.EqualityResult.notEqual
#assert_no_axioms LeanFX2.FX1.NaturalNumber.beq
#assert_no_axioms LeanFX2.FX1.NaturalNumber.beq_sound
#assert_no_axioms LeanFX2.FX1.NaturalNumber.eqResult
#assert_no_axioms LeanFX2.FX1.Name
#assert_no_axioms LeanFX2.FX1.Name.appendAtom
#assert_no_axioms LeanFX2.FX1.Name.appendNumber
#assert_no_axioms LeanFX2.FX1.Name.isAnonymous
#assert_no_axioms LeanFX2.FX1.Name.beq
#assert_no_axioms LeanFX2.FX1.Name.nodeCount
#assert_no_axioms LeanFX2.FX1.Name.beq_sound
#assert_no_axioms LeanFX2.FX1.Name.eqResult
#assert_no_axioms LeanFX2.FX1.Level
#assert_no_axioms LeanFX2.FX1.Level.beq
#assert_no_axioms LeanFX2.FX1.Level.nodeCount
#assert_no_axioms LeanFX2.FX1.Expr
#assert_no_axioms LeanFX2.FX1.Expr.beq
#assert_no_axioms LeanFX2.FX1.Expr.nodeCount
#assert_no_axioms LeanFX2.FX1.Declaration
#assert_no_axioms LeanFX2.FX1.Declaration.name
#assert_no_axioms LeanFX2.FX1.Declaration.typeExpr
#assert_no_axioms LeanFX2.FX1.Declaration.valueExpr?
#assert_no_axioms LeanFX2.FX1.Declaration.hasValue
#assert_no_axioms LeanFX2.FX1.Declaration.isAxiomDeclaration
#assert_no_axioms LeanFX2.FX1.Declaration.hasName
#assert_no_axioms LeanFX2.FX1.Environment
#assert_no_axioms LeanFX2.FX1.Environment.empty
#assert_no_axioms LeanFX2.FX1.Environment.extend
#assert_no_axioms LeanFX2.FX1.Environment.declarationCountInList
#assert_no_axioms LeanFX2.FX1.Environment.declarationCount
#assert_no_axioms LeanFX2.FX1.Environment.findInDeclarations?
#assert_no_axioms LeanFX2.FX1.Environment.findWhere?
#assert_no_axioms LeanFX2.FX1.Environment.hasDeclarationWhere
#assert_no_axioms LeanFX2.FX1.Environment.findByName?
#assert_no_axioms LeanFX2.FX1.Environment.hasName
#assert_no_axioms LeanFX2.FX1.Environment.hasAxiomDeclaration
#assert_no_axioms LeanFX2.FX1.Context
#assert_no_axioms LeanFX2.FX1.Context.empty
#assert_no_axioms LeanFX2.FX1.Context.extend
#assert_no_axioms LeanFX2.FX1.Context.lengthInEntries
#assert_no_axioms LeanFX2.FX1.Context.length
#assert_no_axioms LeanFX2.FX1.Context.lookupInEntries?
#assert_no_axioms LeanFX2.FX1.Context.lookup?
#assert_no_axioms LeanFX2.FX1.Context.hasIndex
#assert_no_axioms LeanFX2.FX1.Expr.isScopedIn
#assert_no_axioms LeanFX2.FX1.Renaming
#assert_no_axioms LeanFX2.FX1.Renaming.identity
#assert_no_axioms LeanFX2.FX1.Renaming.shift
#assert_no_axioms LeanFX2.FX1.Renaming.compose
#assert_no_axioms LeanFX2.FX1.Renaming.lift
#assert_no_axioms LeanFX2.FX1.Renaming.lift_ext
#assert_no_axioms LeanFX2.FX1.Renaming.lift_identity_apply
#assert_no_axioms LeanFX2.FX1.Renaming.compose_identity_left_apply
#assert_no_axioms LeanFX2.FX1.Renaming.compose_identity_right_apply
#assert_no_axioms LeanFX2.FX1.Renaming.compose_lift_apply
#assert_no_axioms LeanFX2.FX1.Renaming.compose_shift_lift_apply
#assert_no_axioms LeanFX2.FX1.Expr.rename
#assert_no_axioms LeanFX2.FX1.Expr.weaken
#assert_no_axioms LeanFX2.FX1.Expr.pi_congr
#assert_no_axioms LeanFX2.FX1.Expr.lam_congr
#assert_no_axioms LeanFX2.FX1.Expr.app_congr
#assert_no_axioms LeanFX2.FX1.Expr.rename_ext
#assert_no_axioms LeanFX2.FX1.Expr.rename_identity
#assert_no_axioms LeanFX2.FX1.Expr.rename_compose
#assert_no_axioms LeanFX2.FX1.Expr.rename_shift_lift_commute
#assert_no_axioms LeanFX2.FX1.Substitution
#assert_no_axioms LeanFX2.FX1.Substitution.identity
#assert_no_axioms LeanFX2.FX1.Substitution.ofRenaming
#assert_no_axioms LeanFX2.FX1.Substitution.renameOutput
#assert_no_axioms LeanFX2.FX1.Substitution.renameInput
#assert_no_axioms LeanFX2.FX1.Substitution.compose
#assert_no_axioms LeanFX2.FX1.Substitution.lift
#assert_no_axioms LeanFX2.FX1.Substitution.singleton
#assert_no_axioms LeanFX2.FX1.Substitution.lift_ext
#assert_no_axioms LeanFX2.FX1.Substitution.lift_identity_apply
#assert_no_axioms LeanFX2.FX1.Substitution.ofRenaming_identity_apply
#assert_no_axioms LeanFX2.FX1.Substitution.lift_ofRenaming_apply
#assert_no_axioms LeanFX2.FX1.Substitution.lift_renameOutput_apply
#assert_no_axioms LeanFX2.FX1.Substitution.lift_renameInput_apply
#assert_no_axioms LeanFX2.FX1.Substitution.renameInput_lift_shift_apply
#assert_no_axioms LeanFX2.FX1.Substitution.lift_compose_apply
#assert_no_axioms LeanFX2.FX1.Substitution.compose_identity_left_apply
#assert_no_axioms LeanFX2.FX1.Substitution.compose_identity_right_apply
#assert_no_axioms LeanFX2.FX1.Substitution.singleton_newest
#assert_no_axioms LeanFX2.FX1.Substitution.singleton_older
#assert_no_axioms LeanFX2.FX1.Expr.subst
#assert_no_axioms LeanFX2.FX1.Expr.subst0
#assert_no_axioms LeanFX2.FX1.Expr.subst_ext
#assert_no_axioms LeanFX2.FX1.Expr.subst_identity
#assert_no_axioms LeanFX2.FX1.Expr.subst_ofRenaming
#assert_no_axioms LeanFX2.FX1.Expr.rename_subst_commute
#assert_no_axioms LeanFX2.FX1.Expr.subst_rename_commute
#assert_no_axioms LeanFX2.FX1.Expr.subst_compose
#assert_no_axioms LeanFX2.FX1.Expr.subst0_bvar_zero
#assert_no_axioms LeanFX2.FX1.Expr.subst0_bvar_succ
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.newestDef
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.newestTheorem
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.older
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.weaken
#assert_no_axioms LeanFX2.FX1.Step
#assert_no_axioms LeanFX2.FX1.Step.beta
#assert_no_axioms LeanFX2.FX1.Step.piDomain
#assert_no_axioms LeanFX2.FX1.Step.piBody
#assert_no_axioms LeanFX2.FX1.Step.lamDomain
#assert_no_axioms LeanFX2.FX1.Step.lamBody
#assert_no_axioms LeanFX2.FX1.Step.appFunction
#assert_no_axioms LeanFX2.FX1.Step.appArgument
#assert_no_axioms LeanFX2.FX1.Step.beta_newest_bvar
#assert_no_axioms LeanFX2.FX1.Step.beta_succ_bvar
#assert_no_axioms LeanFX2.FX1.EnvStep
#assert_no_axioms LeanFX2.FX1.EnvStep.beta
#assert_no_axioms LeanFX2.FX1.EnvStep.delta
#assert_no_axioms LeanFX2.FX1.EnvStep.piDomain
#assert_no_axioms LeanFX2.FX1.EnvStep.piBody
#assert_no_axioms LeanFX2.FX1.EnvStep.lamDomain
#assert_no_axioms LeanFX2.FX1.EnvStep.lamBody
#assert_no_axioms LeanFX2.FX1.EnvStep.appFunction
#assert_no_axioms LeanFX2.FX1.EnvStep.appArgument
#assert_no_axioms LeanFX2.FX1.EnvStep.fromStep
#assert_no_axioms LeanFX2.FX1.EnvStep.weaken_environment
#assert_no_axioms LeanFX2.FX1.EnvStep.deltaNewestDef
#assert_no_axioms LeanFX2.FX1.EnvStep.deltaNewestTheorem
#assert_no_axioms LeanFX2.FX1.EnvStep.betaNewestBvar
#assert_no_axioms LeanFX2.FX1.EnvStep.betaSuccBvar
#assert_no_axioms LeanFX2.FX1.StepStar
#assert_no_axioms LeanFX2.FX1.StepStar.refl
#assert_no_axioms LeanFX2.FX1.StepStar.step
#assert_no_axioms LeanFX2.FX1.StepStar.single
#assert_no_axioms LeanFX2.FX1.StepStar.trans
#assert_no_axioms LeanFX2.FX1.EnvStepStar
#assert_no_axioms LeanFX2.FX1.EnvStepStar.refl
#assert_no_axioms LeanFX2.FX1.EnvStepStar.step
#assert_no_axioms LeanFX2.FX1.EnvStepStar.single
#assert_no_axioms LeanFX2.FX1.EnvStepStar.trans
#assert_no_axioms LeanFX2.FX1.EnvStepStar.weaken_environment
#assert_no_axioms LeanFX2.FX1.EnvStepStar.fromStepStar
#assert_no_axioms LeanFX2.FX1.DefEq
#assert_no_axioms LeanFX2.FX1.DefEq.common
#assert_no_axioms LeanFX2.FX1.DefEq.refl
#assert_no_axioms LeanFX2.FX1.DefEq.symm
#assert_no_axioms LeanFX2.FX1.DefEq.weaken_environment
#assert_no_axioms LeanFX2.FX1.Environment.HasDeclaration
#assert_no_axioms LeanFX2.FX1.Environment.HasDeclaration.newest
#assert_no_axioms LeanFX2.FX1.Environment.HasDeclaration.older
#assert_no_axioms LeanFX2.FX1.Environment.HasDeclaration.weaken
#assert_no_axioms LeanFX2.FX1.Context.HasTypeAt
#assert_no_axioms LeanFX2.FX1.Context.HasTypeAt.newest
#assert_no_axioms LeanFX2.FX1.Context.HasTypeAt.newest_weakened_dependency
#assert_no_axioms LeanFX2.FX1.Context.HasTypeAt.older
#assert_no_axioms LeanFX2.FX1.Context.HasTypeAt.weaken
#assert_no_axioms LeanFX2.FX1.HasType
#assert_no_axioms LeanFX2.FX1.HasType.sort
#assert_no_axioms LeanFX2.FX1.HasType.var
#assert_no_axioms LeanFX2.FX1.HasType.const
#assert_no_axioms LeanFX2.FX1.HasType.pi
#assert_no_axioms LeanFX2.FX1.HasType.lam
#assert_no_axioms LeanFX2.FX1.HasType.app
#assert_no_axioms LeanFX2.FX1.HasType.conv
#assert_no_axioms LeanFX2.FX1.HasType.weaken_environment
#assert_no_axioms LeanFX2.FX1.HasType.sortZeroIdentity
#assert_no_axioms LeanFX2.FX1.HasType.identityAppNewestVar_sourceHasType
#assert_no_axioms LeanFX2.FX1.HasType.identityAppNewestVar_targetHasType
#assert_no_axioms LeanFX2.FX1.HasType.identityAppNewestVar_betaStep
#assert_no_axioms LeanFX2.FX1.Context.WellFormed
#assert_no_axioms LeanFX2.FX1.Context.WellFormed.empty
#assert_no_axioms LeanFX2.FX1.Context.WellFormed.extend
#assert_no_axioms LeanFX2.FX1.Context.WellFormed.weaken_environment
#assert_no_axioms LeanFX2.FX1.Environment.NameFresh
#assert_no_axioms LeanFX2.FX1.Environment.NameFresh.empty
#assert_no_axioms LeanFX2.FX1.Environment.NameFresh.older
#assert_no_axioms LeanFX2.FX1.Environment.NameFresh.weaken
#assert_no_axioms LeanFX2.FX1.Declaration.WellTyped
#assert_no_axioms LeanFX2.FX1.Declaration.WellTyped.axiomDecl
#assert_no_axioms LeanFX2.FX1.Declaration.WellTyped.defDecl
#assert_no_axioms LeanFX2.FX1.Declaration.WellTyped.theoremDecl
#assert_no_axioms LeanFX2.FX1.Declaration.WellTyped.weaken_environment
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.newestDef_value_has_type
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.newestTheorem_proof_has_type
#assert_no_axioms LeanFX2.FX1.Environment.TransparentDefinition.source_has_type
#assert_no_axioms LeanFX2.FX1.EnvStep.deltaNewestDef_preserves_empty_type
#assert_no_axioms LeanFX2.FX1.EnvStep.deltaNewestTheorem_preserves_empty_type
#assert_no_axioms LeanFX2.FX1.Declaration.IsReleaseDeclaration
#assert_no_axioms LeanFX2.FX1.Declaration.IsReleaseDeclaration.defDecl
#assert_no_axioms LeanFX2.FX1.Declaration.IsReleaseDeclaration.theoremDecl
#assert_no_axioms LeanFX2.FX1.Declaration.IsReleaseDeclaration.isAxiomDeclaration_false
#assert_no_axioms LeanFX2.FX1.Environment.WellFormed
#assert_no_axioms LeanFX2.FX1.Environment.WellFormed.empty
#assert_no_axioms LeanFX2.FX1.Environment.WellFormed.extend
#assert_no_axioms LeanFX2.FX1.Environment.hasAxiomDeclaration_extend_defDecl
#assert_no_axioms LeanFX2.FX1.Environment.hasAxiomDeclaration_extend_theoremDecl
#assert_no_axioms LeanFX2.FX1.Environment.ReleaseWellFormed
#assert_no_axioms LeanFX2.FX1.Environment.ReleaseWellFormed.empty
#assert_no_axioms LeanFX2.FX1.Environment.ReleaseWellFormed.extend
#assert_no_axioms LeanFX2.FX1.Environment.ReleaseWellFormed.toWellFormed
#assert_no_axioms LeanFX2.FX1.Environment.ReleaseWellFormed.hasAxiomDeclaration_false
#assert_no_axioms LeanFX2.FX1.CheckOption.some_injective
#assert_no_axioms LeanFX2.FX1.Level.checkerBeq
#assert_no_axioms LeanFX2.FX1.Level.checkerBeq_sound
#assert_no_axioms LeanFX2.FX1.Expr.checkerBeq
#assert_no_axioms LeanFX2.FX1.Expr.checkerBeq_sound
#assert_no_axioms LeanFX2.FX1.Environment.LookupDeclarationResult
#assert_no_axioms LeanFX2.FX1.Environment.LookupDeclarationResult.declaration
#assert_no_axioms LeanFX2.FX1.Environment.LookupDeclarationResult.declarationMember
#assert_no_axioms LeanFX2.FX1.Environment.LookupDeclarationResult.rewriteQueryName
#assert_no_axioms LeanFX2.FX1.Environment.FindTypeByNameSoundResult
#assert_no_axioms LeanFX2.FX1.Environment.FindTypeByNameSoundResult.declaration
#assert_no_axioms LeanFX2.FX1.Environment.FindTypeByNameSoundResult.declarationMember
#assert_no_axioms LeanFX2.FX1.Environment.FindTypeByNameSoundResult.typeEquality
#assert_no_axioms LeanFX2.FX1.Environment.findByNameResultInDeclarations?
#assert_no_axioms LeanFX2.FX1.Environment.findByNameResult?
#assert_no_axioms LeanFX2.FX1.Environment.findTypeByNameFromResult?
#assert_no_axioms LeanFX2.FX1.Environment.findTypeByName?
#assert_no_axioms LeanFX2.FX1.Environment.findTypeByName_sound
#assert_no_axioms LeanFX2.FX1.Environment.TransparentLookupResult
#assert_no_axioms LeanFX2.FX1.Environment.TransparentLookupResult.typeExpr
#assert_no_axioms LeanFX2.FX1.Environment.TransparentLookupResult.valueExpr
#assert_no_axioms LeanFX2.FX1.Environment.TransparentLookupResult.transparentDefinition
#assert_no_axioms LeanFX2.FX1.Environment.TransparentLookupResult.rewriteQueryName
#assert_no_axioms LeanFX2.FX1.Environment.FindTransparentValueSoundResult
#assert_no_axioms LeanFX2.FX1.Environment.FindTransparentValueSoundResult.typeExpr
#assert_no_axioms LeanFX2.FX1.Environment.FindTransparentValueSoundResult.transparentDefinition
#assert_no_axioms LeanFX2.FX1.Environment.TransparentLookupResult.weakenOlder
#assert_no_axioms LeanFX2.FX1.Environment.findTransparentDefinitionResultInDeclarations?
#assert_no_axioms LeanFX2.FX1.Environment.findTransparentDefinitionResult?
#assert_no_axioms LeanFX2.FX1.Environment.findTransparentValueFromResult?
#assert_no_axioms LeanFX2.FX1.Environment.findTransparentValue?
#assert_no_axioms LeanFX2.FX1.Environment.findTransparentValue_sound
#assert_no_axioms LeanFX2.FX1.Context.LookupTypeResult
#assert_no_axioms LeanFX2.FX1.Context.LookupTypeResult.typeExpr
#assert_no_axioms LeanFX2.FX1.Context.LookupTypeResult.typeAtIndex
#assert_no_axioms LeanFX2.FX1.Context.lookupTypeResultInEntries?
#assert_no_axioms LeanFX2.FX1.Context.lookupTypeFromResult?
#assert_no_axioms LeanFX2.FX1.Context.lookupTypeInEntries?
#assert_no_axioms LeanFX2.FX1.Context.lookupType?
#assert_no_axioms LeanFX2.FX1.Context.lookupTypeResult?
#assert_no_axioms LeanFX2.FX1.Context.lookupType_sound
#assert_no_axioms LeanFX2.FX1.Expr.HeadStepResult
#assert_no_axioms LeanFX2.FX1.Expr.HeadStepResult.targetExpr
#assert_no_axioms LeanFX2.FX1.Expr.HeadStepResult.reductionStep
#assert_no_axioms LeanFX2.FX1.Expr.headStepResult?
#assert_no_axioms LeanFX2.FX1.Expr.headStepFromResult?
#assert_no_axioms LeanFX2.FX1.Expr.headStep?
#assert_no_axioms LeanFX2.FX1.Expr.headStep?_sound
#assert_no_axioms LeanFX2.FX1.Expr.WhnfResult
#assert_no_axioms LeanFX2.FX1.Expr.WhnfResult.targetExpr
#assert_no_axioms LeanFX2.FX1.Expr.WhnfResult.reductions
#assert_no_axioms LeanFX2.FX1.Expr.whnfResultWithFuel
#assert_no_axioms LeanFX2.FX1.Expr.whnfFromResult
#assert_no_axioms LeanFX2.FX1.Expr.whnfWithFuel
#assert_no_axioms LeanFX2.FX1.Expr.weakHeadFuel
#assert_no_axioms LeanFX2.FX1.Expr.whnf
#assert_no_axioms LeanFX2.FX1.Expr.whnfWithFuel_sound
#assert_no_axioms LeanFX2.FX1.Expr.whnf_sound
#assert_no_axioms LeanFX2.FX1.Expr.DefEqResult
#assert_no_axioms LeanFX2.FX1.Expr.DefEqResult.commonExpr
#assert_no_axioms LeanFX2.FX1.Expr.DefEqResult.leftReductions
#assert_no_axioms LeanFX2.FX1.Expr.DefEqResult.rightReductions
#assert_no_axioms LeanFX2.FX1.Expr.DefEqResult.toDefEq
#assert_no_axioms LeanFX2.FX1.Expr.weakHeadFuelAdd
#assert_no_axioms LeanFX2.FX1.Expr.defEqFuel
#assert_no_axioms LeanFX2.FX1.Expr.defEqResultWithFuel?
#assert_no_axioms LeanFX2.FX1.Expr.isDefEqWithFuel
#assert_no_axioms LeanFX2.FX1.Expr.isDefEq
#assert_no_axioms LeanFX2.FX1.Expr.isDefEqWithFuel_sound
#assert_no_axioms LeanFX2.FX1.Expr.isDefEq_sound
#assert_no_axioms LeanFX2.FX1.Expr.isDefEqWithFuel_sound_defEq
#assert_no_axioms LeanFX2.FX1.Expr.isDefEq_sound_defEq
#assert_no_axioms LeanFX2.FX1.Expr.InferResult
#assert_no_axioms LeanFX2.FX1.Expr.InferResult.typeExpr
#assert_no_axioms LeanFX2.FX1.Expr.InferResult.typeDerivation
#assert_no_axioms LeanFX2.FX1.Expr.inferTypeFromResult?
#assert_no_axioms LeanFX2.FX1.Expr.checkBoolFromResult?
#assert_no_axioms LeanFX2.FX1.Expr.checkBoolFromCoreType?
#assert_no_axioms LeanFX2.FX1.Expr.inferCore?
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_bvar_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_sort_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_const_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_pi_from_branch_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_lam_from_branch_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_app_from_branch_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_none_absurd
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_sound
#assert_no_axioms LeanFX2.FX1.Expr.checkCore?
#assert_no_axioms LeanFX2.FX1.Expr.checkCore_of_inferCore_sound
#assert_no_axioms LeanFX2.FX1.Expr.checkCore_sound
#assert_no_axioms LeanFX2.FX1.Expr.checkCore_bvar_sound
#assert_no_axioms LeanFX2.FX1.Expr.checkCore_sort_sound
#assert_no_axioms LeanFX2.FX1.Expr.inferResult?
#assert_no_axioms LeanFX2.FX1.Expr.infer?
#assert_no_axioms LeanFX2.FX1.Expr.infer?_sound
#assert_no_axioms LeanFX2.FX1.Expr.check?
#assert_no_axioms LeanFX2.FX1.Expr.check?_sound
#assert_no_axioms LeanFX2.FX1.Expr.betaConvertibleSortZeroType
#assert_no_axioms LeanFX2.FX1.Expr.betaConvertibleArgumentContext
#assert_no_axioms LeanFX2.FX1.Expr.betaConvertibleIdentityApp
#assert_no_axioms LeanFX2.FX1.Expr.isDefEq_betaConvertibleSortZeroType
#assert_no_axioms LeanFX2.FX1.Expr.inferCore_accepts_betaConvertibleArgumentDomain
#assert_no_axioms LeanFX2.FX1.Expr.checkCore_accepts_betaConvertibleExpectedType
#assert_no_axioms LeanFX2.FX1.Expr.infer_accepts_betaConvertibleArgumentDomain
#assert_no_axioms LeanFX2.FX1.Expr.check_accepts_betaConvertibleExpectedType
#assert_no_axioms LeanFX2.FX1.check_sound
#assert_no_axioms LeanFX2.FX1.checkCore_sound

-- FX1Bridge staged rich-to-FX1 unit fragment.  These proofs make only a
-- Bridge-status claim: the staged FX1 environment contains object-level
-- axiom declarations, so this is not Root-FX1 release evidence.
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitValueAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitValueName
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitValueExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitValueDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.unitEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodeEmptyCtx
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unit
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unit
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unit_eq_unitTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unit_eq_unitValueExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitValueDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.unitValueName_ne_unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitValueName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.unitEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnit_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unit
#assert_no_axioms LeanFX2.FX1Bridge.unitVarPosition
#assert_no_axioms LeanFX2.FX1Bridge.unitVarRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitVarContext
#assert_no_axioms LeanFX2.FX1Bridge.encodeCtx_unitVar
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitVar
#assert_no_axioms LeanFX2.FX1Bridge.unitVarType_eq_unit
#assert_no_axioms LeanFX2.FX1Bridge.unitVarTerm
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeExpr_has_sort_in_unitEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitVarContext_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.encodedNewestUnitVar_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_newestUnitVar
#assert_no_axioms LeanFX2.FX1Bridge.unitIdentityRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitIdentityType
#assert_no_axioms LeanFX2.FX1Bridge.unitIdentityTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitIdentity
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitIdentity
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeExpr_has_sort_in_encodedUnitVarContext
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitIdentityType_has_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitIdentity_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitIdentity
#assert_no_axioms LeanFX2.FX1Bridge.unitIdentityAppRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitIdentityAppTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitIdentityApp
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitIdentityApp_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitIdentityApp_betaStep
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitIdentityApp
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityType
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitPiIdentity
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitPiIdentity
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentityType_has_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentity_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitPiIdentity
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityAppRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityAppTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitPiIdentityApp
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentityApp_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentityApp_betaStep
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitPiIdentityApp
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeAtomId
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueAtomId
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseAtomId
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeName
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueName
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseName
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueExpr
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseExpr
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.boolEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_bool
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_boolTrue
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_boolFalse
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_bool_eq_boolTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_boolTrue_eq_boolTrueExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_boolFalse_eq_boolFalseExpr
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueName_ne_boolTypeName
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseName_ne_boolTypeName
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseName_ne_boolTrueName
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.boolFalseName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.boolTrueEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.boolEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.boolTypeExpr_has_sort_in_boolEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedBoolTrue_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodedBoolFalse_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_boolTrue
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_boolFalse
#assert_no_axioms LeanFX2.FX1Bridge.natTypeAtomId
#assert_no_axioms LeanFX2.FX1Bridge.natZeroAtomId
#assert_no_axioms LeanFX2.FX1Bridge.natSuccAtomId
#assert_no_axioms LeanFX2.FX1Bridge.natTypeName
#assert_no_axioms LeanFX2.FX1Bridge.natZeroName
#assert_no_axioms LeanFX2.FX1Bridge.natSuccName
#assert_no_axioms LeanFX2.FX1Bridge.natTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.natZeroExpr
#assert_no_axioms LeanFX2.FX1Bridge.natSuccExpr
#assert_no_axioms LeanFX2.FX1Bridge.natSuccTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.natTypeDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.natZeroDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.natSuccDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.natTypeEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.natEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.natSuccEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_nat
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_natZero
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_natSucc
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_natSuccZero
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_nat_eq_natTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_natZero_eq_natZeroExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_natSucc_eq_natSuccExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_natSuccZero_eq_app
#assert_no_axioms LeanFX2.FX1Bridge.natTypeDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.natZeroDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.natTypeExpr_has_sort_in_natEnvironment_with_binder
#assert_no_axioms LeanFX2.FX1Bridge.natSuccTypeExpr_has_sort_in_natEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.natSuccDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.natTypeEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.natZeroName_ne_natTypeName
#assert_no_axioms LeanFX2.FX1Bridge.natSuccName_ne_natTypeName
#assert_no_axioms LeanFX2.FX1Bridge.natSuccName_ne_natZeroName
#assert_no_axioms LeanFX2.FX1Bridge.natZeroName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.natSuccName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.natEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.natSuccEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.natTypeExpr_has_sort_in_natEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedNatZero_has_type
#assert_no_axioms LeanFX2.FX1Bridge.natTypeExpr_has_sort_in_natSuccEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedNatZero_has_type_in_natSuccEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedNatSucc_has_type
#assert_no_axioms LeanFX2.FX1Bridge.natSuccZeroRaw
#assert_no_axioms LeanFX2.FX1Bridge.natSuccZeroTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodedNatSuccZero_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_natZero
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_natSuccZero
#assert_no_axioms LeanFX2.FX1Bridge.encodeUniverseLevel
#assert_no_axioms LeanFX2.FX1Bridge.universeCodeSameLevelRaw
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_universeCodeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_universeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_universeCodeSameLevel_eq_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_universeSameLevel_eq_successor_sort
#assert_no_axioms LeanFX2.FX1Bridge.universeCodeSameLevelTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodedUniverseCodeSameLevel_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_universeCodeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.unitIdEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.unitIdType
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitId
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitIdRefl
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitId_eq_unitIdTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitIdRefl_eq_unitIdReflExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeName_ne_unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeName_ne_unitValueName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflName_ne_unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflName_ne_unitValueName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflName_ne_unitIdTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.unitIdReflName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.unitIdEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.unitIdTypeExpr_has_sort_in_unitIdEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitIdRefl_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitIdRefl
#assert_no_axioms LeanFX2.FX1Bridge.unitIdJRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitIdJTerm
#assert_no_axioms LeanFX2.FX1Bridge.unitIdJ_iotaStep
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitIdJ
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitIdJ_eq_unit
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnit_has_type_in_unitIdEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitIdJ_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitIdJ
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivType
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitEquiv
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitEquivRefl
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitEquiv_eq_unitEquivTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitEquivRefl_eq_unitEquivReflExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeName_ne_unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeName_ne_unitValueName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflName_ne_unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflName_ne_unitValueName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflName_ne_unitEquivTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivReflName_fresh
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.unitEquivTypeExpr_has_sort_in_unitEquivEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitEquivRefl_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitEquivRefl

-- FX1 executable extern-dependency gates.  These are narrower than the axiom
-- gates: they fail if a checker-critical executable primitive delegates to
-- Lean host runtime code such as `String.decEq` or host `Nat.beq`.
#assert_no_extern_dependencies LeanFX2.FX1.NaturalNumber.beq
#assert_no_extern_dependencies LeanFX2.FX1.NaturalNumber.eqResult
#assert_no_extern_dependencies LeanFX2.FX1.Name.beq
#assert_no_extern_dependencies LeanFX2.FX1.Name.eqResult
#assert_no_extern_dependencies LeanFX2.FX1.Level.beq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.beq
#assert_no_extern_dependencies LeanFX2.FX1.Declaration.hasName
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByName?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByNameResultInDeclarations?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByNameResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTypeByNameFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTypeByName?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentDefinitionResultInDeclarations?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentDefinitionResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentValue?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupTypeFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupTypeInEntries?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupType?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.headStep?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnfResultWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnfWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.weakHeadFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnf
#assert_no_extern_dependencies LeanFX2.FX1.Expr.weakHeadFuelAdd
#assert_no_extern_dependencies LeanFX2.FX1.Expr.defEqFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.isDefEqWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.isDefEq
#assert_no_extern_dependencies LeanFX2.FX1.Level.checkerBeq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkerBeq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkBoolFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkBoolFromCoreType?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.inferCore?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkCore?

-- Loaded production namespace sweep.  `#audit_namespace` excludes
-- `LeanFX2.Tools` and `LeanFX2.Smoke`, so this is the broad fail-fast
-- gate for every production declaration imported above, not a
-- replacement for targeted smoke examples.
#audit_namespace LeanFX2

-- Aggregate strict gate.  Walks the same loaded production decls and
-- flags every discipline violation in one error, including
-- `noncomputable`, `@[extern]`, `@[implemented_by]`, and direct
-- `Classical.*` references.  Subsumes `#audit_namespace` (which only
-- looks at axioms) but kept side-by-side as defense in depth.
#audit_namespace_strict LeanFX2

-- Production import-surface gate.  No production module may import
-- `LeanFX2.Tools`, `LeanFX2.Smoke`, `LeanFX2.Sketch`, or the broad
-- `LeanFX2` root as an internal dependency.
#assert_production_import_surface_clean

-- Public umbrella isolation.  Broad entrypoints (`LeanFX2`, `LeanFX2.Kernel`,
-- `LeanFX2.Rich`, `LeanFX2.FX1Bridge`, `LeanFX2.FX1`, `LeanFX2.FX1.Core`) may
-- appear only in the deliberate public-entrypoint chain or in smoke/tooling
-- audits.
#assert_public_umbrella_imports_isolated

-- Rich production host-import gate.  Regular production modules must not
-- import host-heavy modules such as `Lean`, `Std`, `Lake`, `Mathlib`,
-- `Classical`, or host `Quot` directly.  FX1 and tooling are checked by
-- narrower gates below.
#assert_rich_production_host_import_surface_clean

-- Semantic layer gate.  Foundation/Term/Reduction/etc. modules may only
-- import their own layer or earlier layers, so later metatheory cannot leak
-- downward through a convenience import.
#assert_production_layer_imports_clean

-- Redundant direct project-import gate.  Production modules may not keep
-- extra direct `LeanFX2.*` imports that are already reachable through another
-- direct import, except for the four documented semantic core edges.
#assert_no_redundant_production_project_imports

-- FX1/Core host-minimal gate.  This is intentionally scoped to the
-- future minimal-root namespace, not the rich kernel: FX1 declarations
-- must not depend on host-heavy `Lean`, `Std`, `Classical`, host `Quot`,
-- `propext`, `Classical.choice`, `Quot.sound`, `Quot.lift`, or `sorryAx`.
-- It succeeds with zero declarations, so it can be wired before FX1/Core
-- exists and will begin enforcing as soon as FX1 files are imported.
#assert_fx1_core_host_minimal LeanFX2.FX1

-- FX1 direct-import gate.  FX1/Core may only import FX1/Core;
-- FX1/LeanKernel may only import FX1/Core or FX1/LeanKernel.  Like the
-- host-minimal gate, this passes with zero FX1 modules and begins enforcing
-- as soon as the namespace is loaded.
#assert_fx1_import_surface_clean

-- Exact FX1/Core root-DAG gate.  This is stricter than "FX1 imports only
-- FX1": it prevents a minimal-root leaf from importing the Core umbrella or a
-- later metatheory module without an explicit policy update.
#assert_fx1_core_exact_import_shape

-- Exact FX1/LeanKernel DAG gate.  The Lean-kernel model over FX1 is allowed
-- to exist, but every direct dependency edge must be intentional.
#assert_fx1_lean_kernel_exact_import_shape

-- Rich production / FX1 separation.  FX1 is the future minimal TCB root;
-- rich production modules may not import it directly until a deliberate
-- bridge/certificate boundary exists.
#assert_rich_production_fx1_import_surface_clean

-- Legacy Lean-kernel scaffold isolation.  The old pre-FX1
-- `LeanFX2.Lean.Kernel.*` module path must stay absent or quarantined while
-- Day 8 targets `LeanFX2.FX1.LeanKernel`.
#assert_legacy_lean_kernel_scaffold_isolated

-- Explicit host-boundary isolation.  Host shims such as `Surface.HostLex`
-- may be imported by smoke/tool modules, but never by the public umbrella or
-- regular production modules.
#assert_host_boundary_isolated

-- Global host-heavy import allowlist.  The only allowed direct host-heavy
-- edge is the audit implementation importing Lean elaborator APIs.
#assert_host_heavy_import_surface_allowlisted

-- Import census.  These two commands are informational, but keeping them in
-- `AuditAll` makes dependency mass visible in the canonical audit target
-- instead of only in smoke import-surface builds.
#audit_import_family_summary
#audit_import_surface_summary

-- Raw / typed parity gate.  Every constructor of `RawStep.par` must
-- have a same-suffix constructor in `Step.par`.  Catches the failure
-- mode where a raw cubical β rule lands without its typed mirror.
#assert_raw_typed_parity

-- Schematic-payload budget gates.  These do not claim the current payload
-- surface is ideal; they pin today's explicit `RawTerm` / `Nat` constructor
-- payload debt so future rich-kernel edits cannot grow it silently.
#assert_schematic_payload_budget LeanFX2.Ty 12 1
#assert_schematic_payload_budget LeanFX2.Term 39 0

-- Mode-discipline debt gate.  These are known constructors whose names imply
-- strict/univalent-only availability but whose signatures still quantify over
-- arbitrary `mode`.  The budget pins current debt until the ctor signatures
-- acquire real `mode = ...` premises.
#assert_mode_discipline_budget LeanFX2.Term 8

-- Semantic-signature debt gates.  These do not claim the current signatures
-- are sound; they pin the known fake-typing shapes so new ctors cannot repeat
-- them silently and repaired ctors ratchet the budgets downward.
#assert_dependent_eliminator_motive_budget LeanFX2.Term 9
#assert_unit_placeholder_budget LeanFX2.Term 3
#assert_modal_noop_budget LeanFX2.Term 3
#assert_session_no_advance_budget LeanFX2.Term 2
#assert_equiv_coherence_budget LeanFX2.Term 1

-- Exact rich-to-FX1 bridge constructor coverage.  Fragment bridges remain
-- useful, but only exact `FX1Bridge.encodeTermSound_<ctor>` names count as
-- whole-constructor bridge coverage for this matrix.
#assert_bridge_exact_coverage_budget LeanFX2.Term 71

-- Naming discipline gate.  Bans non-ASCII identifiers and short
-- identifiers (< 4 chars) outside the documented whitelist.  Catches
-- regressions like `def f (x) := ...` or pasted Greek-letter names
-- that violate CLAUDE.md naming rules.
#assert_namespace_naming LeanFX2

-- Hypothesis-as-postulate detector.  No theorem signature in the
-- production namespace may take Univalence / funext / their het
-- variants as a hypothesis (CLAUDE.md "Forbidden reasoning patterns":
-- shipping a theorem conditionally on an unprovable hypothesis is
-- semantically identical to adding an axiom).
#assert_no_postulate_hypothesis LeanFX2

-- Headline refl-fragment budget.  The current `Univalence` / `funext`
-- headline family still depends on manufactured raw-alignment Step rules.
-- This pins that debt to four claims and rejects future growth.
#assert_headline_refl_fragment_budget LeanFX2 4

-- Staged FX1 axiom leak detector.  Object-level `axiomDecl` placeholders are
-- allowed inside FX1 itself and the explicit FX1Bridge staging boundary only;
-- regular rich/root production declarations must not depend on them.
#assert_no_root_staged_axiom_leak LeanFX2

-- Per-namespace decl-count snapshot.  Strictly informational; surfaces
-- the count distribution across `LeanFX2.*` sub-namespaces so a
-- coverage regression (whole sub-namespace shrinking unexpectedly)
-- is visible at a glance.
#audit_subnamespace_counts

-- End-of-build summary.  Logs `Total / Clean / Failed` plus per-decl
-- failure list.  Strictly informational (does not throw); the actual
-- blocking happens via `#audit_namespace_strict` above.  Surfaces
-- audit health amid hundreds of OK info lines.
#audit_summary LeanFX2

end LeanFX2.Tools
