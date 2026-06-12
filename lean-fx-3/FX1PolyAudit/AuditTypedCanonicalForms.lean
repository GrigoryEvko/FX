import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.DataReducibilityCoverage
import FX1Poly.Core.DataTaitCandidate
import FX1Poly.Core.FlatCodeTaitCandidate
import FX1Poly.Typed.FlatCodeCanonicalForms
import FX1Poly.Typed.MilestoneASpineValueLayer
import FX1Poly.Typed.MilestoneAEliminatorLayerSpine
import FX1Poly.Typed.BoolElimComputingCanonicity
import FX1Poly.Typed.MatchElimComputingCanonicityTyped
import FX1Poly.Typed.MatchGeneralBranchCanonicity
import FX1Poly.Typed.MetatheoryParityLedger
import FX1Poly.Typed.TypingContext
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.SigmaCodeShape
import FX1Poly.Typed.ListCodeShape
import FX1Poly.Typed.ListFormationSmoke
import FX1Poly.Typed.OptionCodeShape
import FX1Poly.Typed.OptionCodeFormationUnderSubst
import FX1Poly.Typed.OptionFormerMemberLevelIndexed
import FX1Poly.Typed.BoundedGenFormationOptionFromTelescope
import FX1Poly.Typed.OptionFormationSmoke
import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.HasTypeDescElim
import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion
import FX1Poly.Typed.DataFormerInversion
import FX1Poly.Typed.HasTypeDescUniqueness
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeDescSubstitution
import FX1Poly.Typed.HasTypeDescElimWeakening
import FX1Poly.Typed.HasTypeDescElimSubstitution
import FX1Poly.Typed.HasTypeDescApplication
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescPiEtaCoherence
import FX1Poly.Typed.HasTypeDescPiEtaExpansionGrown
import FX1Poly.Typed.HasTypeDescPiEtaExpansionComputes
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.HasTypeDescPiApplication
import FX1Poly.Typed.HasTypeDescPiValidity
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.ConvBoolCodeRigidity
import FX1Poly.Typed.ConvFormationFormerRigidity
import FX1Poly.Typed.ConvFlatFormerRigidity
import FX1Poly.Typed.ConvCrossTableFormerRigidity
import FX1Poly.Typed.ConvFlatCodeInjectivity
import FX1Poly.Typed.ConvDataCodeInjectivity
import FX1Poly.Typed.EmptyTypeCodeConvRigidity
import FX1Poly.Typed.EmptyTypeValueInversion
import FX1Poly.Typed.FormationCanonicalForms
import FX1Poly.Typed.PiTypeFunctionInversion
import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.FormationTypeSafety
import FX1Poly.Typed.GrownCanonicalFormsByClassifier
import FX1Poly.Typed.GrownClosedProgressByClassifier
import FX1Poly.Typed.GrownCanonicalFormsNonVacuity
import FX1Poly.Typed.GrownBetaRedexInAction
import FX1Poly.Typed.GrownOpenProgress
import FX1Poly.Typed.GrownOpenCanonicalFormsByClassifier
import FX1Poly.Typed.GrownOpenProgressByClassifier
import FX1Poly.Typed.GrownOpenTypeSafety
import FX1Poly.Typed.GrownTypeSafetyUnconditional
import FX1Poly.Typed.FormerStepInversionGeneric
import FX1Poly.Typed.SubjectReductionAtFormerGeneric
import FX1Poly.Typed.WfContextDesc
import FX1Poly.Typed.WfContextDescLookup
import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.WfContextDescStronglyNormalizing
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.WfContextDescPi
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc
import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.WfContextDescPiValidity
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiFunctionComponentValidity
import FX1Poly.Typed.HasTypeDescPiSubjectReductionDescPi
import FX1Poly.Typed.HasTypeDescPiSubjectReduction
import FX1Poly.Typed.HasTypeDescPiSubjectReductionMutual
import FX1Poly.Typed.ReducibleEnv
import FX1Poly.Typed.ReducibleEnvAt
import FX1Poly.Typed.ReducibleEnvTypeVariable
import FX1Poly.Typed.SimplyTypedTypeExprFT
import FX1Poly.Typed.AbstractionNonDependentUnderSubstLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprReducibleLevelFree
import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Typed.SimplyTypedTermConfluenceLevelFree
import FX1Poly.Typed.SimplyTypedTermInhabitationLevelFree
import FX1Poly.Typed.SimplyTypedTermInversionLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprClosureLevelFree
import FX1Poly.Typed.SimplyTypedTermRenameLevelFree
import FX1Poly.Typed.SimplyTypedTermSubstLevelFree
import FX1Poly.Typed.SimplyTypedTermSubjectReductionLevelFree
import FX1Poly.Typed.SimplyTypedTermCanonicityLevelFree
import FX1Poly.Typed.SimplyTypedTermConsistencyLevelFree
import FX1Poly.Typed.SimplyTypedConvDecision
import FX1Poly.Typed.MilestoneA0SimplyTypedFloor
import FX1Poly.Typed.SimplyTypedMetatheoryViaSconing
import FX1Poly.Tier0.FxRenamingCategory
import FX1Poly.Tier0.FxBaseRenamingCategory
import FX1Poly.Tier0.FxBaseRenamingVecCategory
import FX1Poly.Tier0.FxBaseRenamingVecIsomorphism
import FX1Poly.Tier0.FxBaseRenamingVecTabulate
import FX1Poly.Tier0.FxBaseRenamingVecPreimage
import FX1Poly.Tier0.FxBaseRenamingVecTryTabulate
import FX1Poly.Tier0.FxBaseRenamingVecRMC
import FX1Poly.Tier0.FxBaseRenamingVecGlobalSections
import FX1Poly.Tier0.FxBaseRenamingVecSconingPreservation
import FX1Poly.Tier0.FxBaseSubstVec
import FX1Poly.Tier0.FxBaseSubstCategory
import FX1Poly.Tier0.FxBaseSubstWeakening
import FX1Poly.Tier0.FxBaseSubstComprehension
import FX1Poly.Tier0.FxBaseSubstSingleton
import FX1Poly.Tier0.FxBaseSubstGlobalSections
import FX1Poly.Tier0.FxBaseSubstScone
import FX1Poly.Tier0.FxBaseSubstWitnessScone
import FX1Poly.Tier0.FxBaseSubstConcreteScone
import FX1Poly.Tier0.IsomorphismCategorical
import FX1Poly.Tier0.FxThinScopeRMC
import FX1Poly.Tier0.FxThinScopeGlobalSections
import FX1Poly.Typed.SimplyTypedNormalForm
import FX1Poly.Typed.SimplyTypedConvEquivalence
import FX1Poly.Typed.ReduceSmokeCorpus
import FX1Poly.Core.RedexExtraction
import FX1Poly.Core.RootStepDispatch
import FX1Poly.Core.FireRootRedex
import FX1Poly.Core.FireRootRedexComplete
import FX1Poly.Core.ReduceOnce
import FX1Poly.Core.ReduceOnceComplete
import FX1Poly.Core.Normalize
import FX1Poly.Core.NormalizeSteps
import FX1Poly.Core.ConvDecisionSteps
import FX1Poly.Core.NormalizeMeta
import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion
import FX1Poly.Core.BoolCanonicalFormsCandidate
import FX1Poly.Core.BoolElimCanonicalComputation
import FX1Poly.Core.BoolElimClosedMembership
import FX1Poly.Core.DataEliminatorMembershipSmoke
import FX1Poly.Core.SigmaProjectionCanonicalComputation
import FX1Poly.Core.IdentityEliminatorCanonicalComputation
import FX1Poly.Core.IdEliminatorClosedMembership
import FX1Poly.Core.OptionEitherMatchCanonicalComputation
import FX1Poly.Core.MatchClosedMembership
import FX1Poly.Core.SigmaProjectionClosedMembership
import FX1Poly.Core.RecursorClosedMembership
import FX1Poly.Core.RecursiveEliminatorBaseComputation
import FX1Poly.Core.BoolCanonicityViaSconing
import FX1Poly.Core.DataCanonicityViaSconing
import FX1Poly.Core.ModalCanonicityViaSconing
import FX1Poly.Core.DataMetatheoryViaSconing
import FX1Poly.Core.ReducibilityNormalizationViaSconing
import FX1Poly.Core.ReducibilityConversionViaSconing
import FX1Poly.Core.ConsistencyViaSconing
import FX1Poly.Core.DataEliminatorProgressViaSconing
import FX1Poly.Core.RecursiveEliminatorProgressViaSconing
import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.PairCanonicalFormsCandidate
import FX1Poly.Core.UnitCanonicalFormsCandidate
import FX1Poly.Core.ModIntroCanonicalFormsCandidate
import FX1Poly.Core.EmptyCanonicalFormsCandidate
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Core.ReflCanonicalFormsCandidate
import FX1Poly.Core.StronglyNormalizingSubst
import FX1Poly.Core.ExistsStepOfNotNormal
import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.NormalFormUnique
import FX1Poly.Core.StronglyNormalizingConvDecision
import FX1Poly.Typed.ReducibleEnvAtAllLevels
import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates
import FX1Poly.Typed.FundamentalWithPositiveTypeCandidates
import FX1Poly.Typed.FundamentalWithTypeValueCandidates
import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.FundamentalAtAllTelescope
import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro
import FX1Poly.Typed.FundamentalAtAllPositiveArguments
import FX1Poly.Typed.NeutralFuelStability
import FX1Poly.Typed.PiTypeSaturationReassembly
import FX1Poly.Typed.StrongNormalizingAllLevelPiComponents
import FX1Poly.Typed.FundamentalAtAllTelescopePositiveArguments
import FX1Poly.Typed.FundamentalAtAllPositiveMemberExtension
import FX1Poly.Typed.FundamentalAtAllCanonicalCandidate
import FX1Poly.Typed.FundamentalAtAllVectorPremises
import FX1Poly.Typed.FundamentalAtAllNonDependentBinders
import FX1Poly.Typed.FundamentalAtUniformVectorPremises
import FX1Poly.Typed.HasTypeDescPiFundamentalVectorFromFormation
import FX1Poly.Typed.HasTypeDescFundamentalAtAllFromGenFormation
import FX1Poly.Typed.FundamentalLevelIndexed
import FX1Poly.Typed.ClosedLevelIndexed
import FX1Poly.Typed.TypeFundamentalLevelIndexed
import FX1Poly.Typed.LeveledContext
import FX1Poly.Typed.ClosedSNSmoke
import FX1Poly.Typed.UntypedOmegaNotStronglyNormalizing
import FX1Poly.Typed.WeaklyNormalizingNotStronglyNormalizing
import FX1Poly.Typed.StepNonDeterministic
import FX1Poly.Typed.ConvValueDiscrimination
import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Typed.TypedChurchBooleans
import FX1Poly.Typed.TypedChurchNegation
import FX1Poly.Typed.TypedChurchNumerals
import FX1Poly.Typed.TypedChurchNumeralIteration
import FX1Poly.Typed.TypedChurchNumeralDiscrimination
import FX1Poly.Typed.TypedChurchNumeralThree
import FX1Poly.Typed.TypedChurchNumeralFaithful
import FX1Poly.Typed.TypedChurchNumeralTyping
import FX1Poly.Typed.TypedChurchNumeralInhabitants
import FX1Poly.Typed.TypedChurchNumeralComputeGeneral
import FX1Poly.Typed.TypedChurchNumeralAddition
import FX1Poly.Typed.TypedChurchNumeralMultiplication
import FX1Poly.Typed.TypedChurchNumeralSemiringLaws
import FX1Poly.Typed.TypedChurchNumeralIsZero
import FX1Poly.Typed.TypedChurchBooleanOperations
import FX1Poly.Typed.TypedFragmentAcyclicity
import FX1Poly.Typed.UnboundedGrowthNotStronglyNormalizing
import FX1Poly.Typed.CurryFixpointDivergence
import FX1Poly.Typed.CurryFixpointCombinator
import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Typed.CombinatoryCompleteness
import FX1Poly.Typed.SymbolicSCombinatorRule
import FX1Poly.Typed.ChurchPairs
import FX1Poly.Typed.ChurchPairsInjective
import FX1Poly.Typed.ChurchSums
import FX1Poly.Typed.ChurchSumsDisjoint
import FX1Poly.Typed.ChurchSumsGeneral
import FX1Poly.Typed.ChurchLists
import FX1Poly.Typed.ChurchListIsEmpty
import FX1Poly.Typed.ChurchListAny
import FX1Poly.Typed.ChurchListAll
import FX1Poly.Typed.ChurchBooleanComplementLaws
import FX1Poly.Typed.ChurchBoolXor
import FX1Poly.Typed.ChurchListFirstOr
import FX1Poly.Typed.ChurchSucc
import FX1Poly.Typed.ChurchSuccApplies
import FX1Poly.Typed.ChurchListLength
import FX1Poly.Typed.TypedNormalizer
import FX1Poly.Typed.IdentityTowerFamily
import FX1Poly.Typed.NormalizeStepsTower
import FX1Poly.Typed.TypedUniverseTower
import FX1Poly.Typed.TypedUniverseNoTop
import FX1Poly.Typed.TypedUniversePredicative
import FX1Poly.Typed.ClosedConvDecision
import FX1Poly.Typed.ClosedNormalForm
import FX1Poly.Typed.ClosedNonConvertibility
import FX1Poly.Typed.ValidTyping
import FX1Poly.Typed.HasTypeDescPiStronglyNormalizingFromFundamental
import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.ReducibleEnvVecTypeVariable
import FX1Poly.Typed.HasTypeDescPiConsistency
import FX1Poly.Typed.HasTypeFormationNoLambdaApplication
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.ListCodeFormationUnderSubst
import FX1Poly.Typed.ListFormerMemberLevelIndexed
import FX1Poly.Typed.ReducibleMemberFormation
import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.DescTelescopeReach
import FX1Poly.Typed.FlatDescTelescope
import FX1Poly.Typed.StandaloneEngineCanonicity
import FX1Poly.Typed.CombinedBoolCanonicalForms
import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.CanonicitySyntacticRoute
import FX1Poly.Typed.GrownRigidityCanonicity
import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.BoolElimValueCanonicity
import FX1Poly.Typed.NatElimComputingCanonicity
import FX1Poly.Typed.NatElimFaithfulArithmetic
import FX1Poly.Typed.ClosedNumeralSubstInvariant
import FX1Poly.Typed.NatElimFaithfulMul
import FX1Poly.Typed.ValueElimHostFold
import FX1Poly.Typed.RecursorHostFold
import FX1Poly.Typed.ListElimComputingCanonicity
import FX1Poly.Typed.ListElimFaithfulLength
import FX1Poly.Typed.MatchElimComputingCanonicity
import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.ClosedNormalEmptyConsistency
import FX1Poly.Typed.ProductEitherCanonicalForms
import FX1Poly.Typed.OptionCanonicalForms
import FX1Poly.Typed.ListCanonicalForms
import FX1Poly.Typed.IdCanonicalForms
import FX1Poly.Typed.PiFormerMembership
import FX1Poly.Typed.FormerChildrenReducible
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.UniverseDomainMemberExtension
import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves
import FX1Poly.Typed.ReducibleTypeAtAllLevelsInduction
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiNeutralDomain
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves
import FX1Poly.Typed.FundamentalTelescopeConsNeutralDomain
import FX1Poly.Typed.FundamentalTelescopeConsWhnfDomain
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsPiMemberExtension
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsHeadExpand
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsConv
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsStronglyNormalizing
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsNonDependentArrow
import FX1Poly.Typed.ReducibleTypeAtAllLevelsNonDependentArrow
import FX1Poly.Typed.RouteAObstruction
import FX1Poly.Typed.ClassifierLevelDiagnosis
import FX1Poly.Typed.ClassifierLevelMeasure
import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.DenoteKeyedReducibilitySmoke
import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.DenoteKeyedLevelIrrelevance
import FX1Poly.Typed.DenoteKeyedReducibleEnv
import FX1Poly.Typed.DenoteKeyedUniverseFormationMember
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate
import FX1Poly.Typed.DenoteKeyedPiFormationFromExistence
import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm
import FX1Poly.Typed.DenoteKeyedUniverseDomainPiArm
import FX1Poly.Typed.DenoteKeyedSingleLevelPi
import FX1Poly.Typed.DenoteKeyedUniformPiCandidate
import FX1Poly.Typed.DenoteKeyedUniformPiAboveThreshold
import FX1Poly.Typed.DenoteKeyedPiFormerAtLevel
import FX1Poly.Typed.DenoteKeyedReducibleTypeLevelLift
import FX1Poly.Typed.DenoteKeyedPiArmDischarge
import FX1Poly.Typed.DenoteKeyedPiFormationUnderSubst
import FX1Poly.Typed.DenoteKeyedApplicationMember
import FX1Poly.Typed.DenoteKeyedConvMember
import FX1Poly.Typed.DenoteKeyedMemberForwardClosed
import FX1Poly.Typed.DenoteKeyedUniverseMemberBetaExpansion
import FX1Poly.Typed.DenoteKeyedMemberWeakHeadExpansion
import FX1Poly.Typed.DenoteKeyedHeadExpansion
import FX1Poly.Typed.DenoteKeyedAbstractionMember
import FX1Poly.Typed.DenoteKeyedAbstractionUnderSubst
import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedFundamentalPiElim
import FX1Poly.Typed.DenoteKeyedFundamentalConv
import FX1Poly.Typed.DenoteKeyedAmbientLevelBridge
import FX1Poly.Typed.DenoteKeyedNonDependentArrow
import FX1Poly.Typed.DenoteKeyedFundamentalPiIntro
import FX1Poly.Typed.DenoteKeyedClosedMember
import FX1Poly.Typed.DenoteKeyedTelescopeReducible
import FX1Poly.Typed.DenoteKeyedUniformReducible
import FX1Poly.Typed.DenoteKeyedUniverseMembershipIntro
import FX1Poly.Typed.DenoteKeyedTelescopeFundamental
import FX1Poly.Typed.DenoteKeyedSigmaFormation
import FX1Poly.Typed.DenoteKeyedSigmaFromChildMembers
import FX1Poly.Typed.DenoteKeyedGenFormationSigmaArm
import FX1Poly.Typed.DenoteKeyedGenFormationPiArm
import FX1Poly.Typed.DenoteKeyedCumulativityObstruction
import FX1Poly.Typed.DenoteKeyedBoundedReducibility
import FX1Poly.Typed.DenoteKeyedBoundedReducibleEnv
import FX1Poly.Typed.DenoteKeyedBoundedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedBoundedConvArm
import FX1Poly.Typed.DenoteKeyedBoundedPiElimArm
import FX1Poly.Typed.DenoteKeyedBoundedPiIntroArm
import FX1Poly.Typed.DenoteKeyedBoundedFormerEngine
import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiArm
import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiDischarge
import FX1Poly.Typed.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Typed.DenoteKeyedBoundedTelescopeReducible
import FX1Poly.Typed.DenoteKeyedBoundedTelescopeFundamental
import FX1Poly.Typed.DenoteKeyedBoundedTelescopeProjection
import FX1Poly.Typed.FormerOutputLevelBounds
import FX1Poly.Typed.BoundedCodomainOpenSN
import FX1Poly.Typed.BoundedDomainInhabitant
import FX1Poly.Typed.BoundedGenFormationPiFromTelescope
import FX1Poly.Typed.BoundedGenFormationSigmaFromTelescope
import FX1Poly.Typed.BoundedGenFormationListFromTelescope
import FX1Poly.Typed.BoundedTelescopeConsSucc
import FX1Poly.Typed.BoundedGrownDispatch
import FX1Poly.Typed.BoundedFormationLeafArms
import FX1Poly.Typed.BoundExceedsDesc
import FX1Poly.Typed.BoundExceedsDischarge
import FX1Poly.Typed.BoundedFormationDispatch
import FX1Poly.Typed.BoundExceedsPi
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Typed.BoundedGrownFundamental
import FX1Poly.Typed.ClosedBoundedReducibleMember
import FX1Poly.Typed.ClosedStronglyNormalizing
import FX1Poly.Typed.OpenStronglyNormalizing
import FX1Poly.Typed.BoundedNeutralMember
import FX1Poly.Typed.BoundedUniverseInversion
import FX1Poly.Typed.BoundedBindingTypeReducible
import FX1Poly.Typed.ReducibleEnvOfWfContext
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.WfContextDecidableConv
import FX1Poly.Typed.OpenSNSmoke
import FX1Poly.Typed.ContextValidityFails
import FX1Poly.Typed.OpenStronglyNormalizingBetaEta
import FX1Poly.Typed.WfContextBetaEtaConfluence
import FX1Poly.Typed.WfContextBetaEtaConfluenceUnconditional
import FX1Poly.Typed.BetaEtaConvGapStatement
import FX1Poly.Typed.BetaEtaConvDecidable
import FX1Poly.Typed.UnitEtaJudgmentalEquality
import FX1Poly.Typed.UnitEtaCongruenceGap
import FX1Poly.Typed.UnitEtaCongruentEquality
import FX1Poly.Typed.UnitVariableCollapse
import FX1Poly.Typed.UnitCollapseIncompleteness
import FX1Poly.Typed.UnitCollapseBinderFence
import FX1Poly.Typed.UnitVariableCollapseDeep
import FX1Poly.Typed.UnitVariableCollapseDeepSound
import FX1Poly.Typed.UnitCollapseNeutralBoundary
import FX1Poly.Typed.UnitNeutralSpineDetection
import FX1Poly.Typed.UnitSpineDetectionBoundary
import FX1Poly.Typed.TypeDirectedUnitReadback
import FX1Poly.Typed.UnitReadbackArgumentBoundary
import FX1Poly.Typed.UnitReadbackFormerChildBoundary
import FX1Poly.Typed.UnitReadbackDeepSpineBoundary
import FX1Poly.Typed.UnitReadbackAnnotationBoundary
import FX1Poly.Typed.FormationClassifierRigidity
import FX1Poly.Typed.TypedNbeNormalizer
import FX1Poly.Typed.TypedNbeConvDecision
import FX1Poly.Typed.LiftedChildNormalizationFromClosure
import FX1Poly.Typed.TelescopeSubstitutedChildrenNormalization
import FX1Poly.Typed.CascadeFreedomLedger
import FX1Poly.Typed.ConsistencyTargetSignature
import FX1Poly.Typed.CandidateBridgeEditViability
import FX1Poly.Typed.CanonicityTargetSignature
import FX1Poly.Typed.NullaryFormerFormation
import FX1Poly.Typed.GrownUniverseFormationStrictness
import FX1Poly.Typed.GrownFormerFormationStrictness
import FX1Poly.Typed.GrownTypingNotUnique
import FX1Poly.Typed.GrownEngineHonesty
import FX1Poly.Typed.GrownUniverseConsistency
import FX1Poly.Typed.GrownVariableHonesty
import FX1Poly.Typed.RawStepNotStronglyNormalizing
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.VarHeadedAppContextConversion
import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.HasTypeDescPiCongruence
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescPiContextConversionConditional
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.HasTypeDescPiContextConversionWf
import FX1Poly.Typed.HasTypeDescPiContextConversionValidityReduction
import FX1Poly.Typed.GrownMutualMetatheoryFromPiValidity
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimEquivalence
import FX1Poly.Typed.HasTypeDescPiContextStepConversion
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimUnderWf
import FX1Poly.Typed.HasTypeDescPiContextConversionFlexibleUnderWf
import FX1Poly.Typed.ConvContextPreservesPiValidityFormationFragment
import FX1Poly.Typed.ConvContextPreservesPiValidityFormerStep
import FX1Poly.Typed.GenFormerValidityContextConversion
import FX1Poly.Typed.ConvContextPiValidityModelNeutral
import FX1Poly.Typed.TypedTypeValidityRelation
import FX1Poly.Typed.TypedTypeValidityBoxedRelation
import FX1Poly.Typed.TypedTypeValidityLeveled
import FX1Poly.Typed.TypedTypeValidityLeveledTransport
import FX1Poly.Typed.TypedTypeValidityLeveledTransportUnderWf
import FX1Poly.Typed.TypedTypeValidityLeveledCompleteness
import FX1Poly.Typed.WfContextTypedLrValid
import FX1Poly.Typed.TypedTypeValidityBoxedRename
import FX1Poly.Typed.WfContextTypedLrValidLookup
import FX1Poly.Typed.PiElimClassifierConvResidual
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiDataHeadUntyped
import FX1Poly.Typed.HasTypeDescPiRootGeneric
import FX1Poly.Typed.DenoteKeyedUniverseBoundedCumulativity
import FX1Poly.Typed.DenoteKeyedClosedTypeCodeSN
import FX1Poly.Typed.DenoteKeyedUniverseDomainPiMemberSN
import FX1Poly.Typed.DenoteKeyedNonDependentArrowMemberSN
import FX1Poly.Typed.DenoteKeyedCodomainMemberWiring
import FX1Poly.Typed.ClassifierLevelSpike
import FX1Poly.Typed.SNStrategy
import FX1Poly.Typed.LogRelSpec
import FX1Poly.Typed.LevelingBridge
import FX1Poly.Typed.ConsistentStratification
import FX1Poly.Typed.ValidTypingLevelFlexible
import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.ValidTypingConvArm
import FX1Poly.Typed.ValidTypingPiArms
import FX1Poly.Typed.ValidTypingFormerArms
import FX1Poly.Typed.ValidTypingVariableLevelPinned
import FX1Poly.Typed.FormationEngineFundamentalReduction
import FX1Poly.Typed.FormationEngineFundamental
import FX1Poly.Typed.FormationEngineFundamentalAssembly
import FX1Poly.Typed.HasTypeDescPiConditionalConfluence
import FX1Poly.Typed.HasTypeDescPiUniqueNormalForm
import FX1Poly.Typed.FirstOrderSimplyTypedReducibility
import FX1Poly.Typed.HigherOrderSimplyTypedReducibility
import FX1Poly.Typed.DependentPiOverNeutralDomain
import FX1Poly.Typed.DependentPiNeutralCodomain
import FX1Poly.Typed.DependentlyTypedNeutralDomainFragment
import FX1Poly.Typed.FirstOrderSimplyTypedSubsumption
import FX1Poly.Typed.UniverseCumulativity
import FX1Poly.Typed.SimplyTypedTermReducibility
import FX1Poly.Typed.HasTypeDescPiTypingNonUnique
import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.HasTypeDescPiVariableInversion
import FX1Poly.Typed.HasTypeDescPiCheckVariable
import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion
import FX1Poly.Typed.HasTypeDescPiCheckUniverseCode
import FX1Poly.Typed.HasTypeDescPiApplicationUniqueness
import FX1Poly.Typed.HasTypeDescPiCheckApplication
import FX1Poly.Typed.HasTypeDescPiFormationUniqueness
import FX1Poly.Typed.HasTypeDescPiCheckFormation
import FX1Poly.Typed.HasTypeDescPiFormationCodomainReTyping
import FX1Poly.Typed.IntroRuleDesc
import FX1Poly.Typed.ElimRuleDesc
import FX1Poly.Typed.GenElimIotaComputation
import FX1Poly.Typed.TypingRoleClassifier
import FX1Poly.Typed.TypingRoleEngineBridge
import FX1Poly.Typed.TypingRoleCoverage
import FX1Poly.Typed.UntypableHeadDecision
import FX1Poly.Typed.TypingHeadKindClassifier
import FX1Poly.Typed.TypedBySomeEngine
import FX1Poly.Typed.GeneratorSemanticTier
import FX1Poly.Typed.GeneratorHonestyOverview
import FX1Poly.Typed.StaticTypingSoundness
import FX1Poly.Typed.SemanticTierSoundness
import FX1Poly.Typed.ClassifierRefinement
import FX1Poly.Typed.GeneratorHonestyLedger
import FX1Poly.Typed.CertifiedWordReductionTermination
import FX1Poly.Typed.CertifiedWordReductionConfluence
import FX1Poly.Typed.HasTypeDescPiFormerStepDomainFormationCodomain
import FX1Poly.Typed.HasTypeDescPiSubjectReductionArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionFormerArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms
import FX1Poly.Typed.ConsistencyConditionalOnSubjectReduction
import FX1Poly.Typed.EmptyTypeConsistencySyntactic
import FX1Poly.Typed.ConsistencyOfPiElimArm
import FX1Poly.Typed.PiElimUpToClassifierConv
import FX1Poly.Typed.ClassifierRespectsConvRefuted
import FX1Poly.Typed.TypedCertificationStackingRefuted
import FX1Poly.Typed.EmptyTypeConsistencyUnconditional
import FX1Poly.Typed.FormationNormalSmoke
import FX1Poly.Typed.BoolTypeCodeSubstrate
import FX1Poly.Typed.NatTypeCodeSubstrate
import FX1Poly.Typed.GrownNoTypeInType
import FX1Poly.Typed.IsTypeDescRigidity
import FX1Poly.Typed.IsTypeDescDecidable
import FX1Poly.Typed.HasTypeDescNativeDecidable
import FX1Poly.Typed.IsTypeDescDecidableGeneric
import FX1Poly.Typed.IsTypeDescGenericSmoke
import FX1Poly.Typed.KnownUnsoundnessCorpus
import FX1Poly.Typed.UniverseClassificationAcyclic
import FX1Poly.Modal.SecurityNoninterferenceGeneral
import FX1Poly.Modal.GradedApplicationFlow
import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.FuzzCorpusConvertibility
import FX1Poly.Typed.FuzzCorpusNormalizes
import FX1Poly.Typed.LambdaValueFuzzFamily
import FX1Poly.Typed.MechanizedProofCrossReference
import FX1Poly.Typed.FormalReviewGate
import FX1Poly.Typed.SelfVerifiedMetatheory
import FX1Poly.Typed.GrownStrengthening
import FX1Poly.Typed.GrownStrengtheningRefutation
import FX1Poly.Typed.GrownCheck
import FX1Poly.Typed.GrownCheckContextConversion
import FX1Poly.Typed.GrownCheckSoundnessRefutation
import FX1Poly.Typed.ConvExistentialStrengtheningRefutation
import FX1Poly.Typed.PinnedPiImageComponents
import FX1Poly.Typed.PinnedPiRenameImage
import FX1Poly.Typed.PinnedReflectionContext
import FX1Poly.Typed.PinnedReflectionPiIntro
import FX1Poly.Typed.FormationPinnedReflection
import FX1Poly.Typed.GrownPinnedReflection
import FX1Poly.Typed.PinnedReflectionPiElimCore
import FX1Poly.Typed.GrownWfOpenStronglyNormalizing
import FX1Poly.Typed.PinnedReflectionPiElimDispatcher
import FX1Poly.Typed.PlateauDescentSubstrate
import FX1Poly.Typed.GuardedPinnedReflection
import FX1Poly.Typed.PlateauPinnedReflection
import FX1Poly.Typed.NeutralReductResidualDischarge
import FX1Poly.Typed.PinnedReflectionLamClassifierResidual
import FX1Poly.Typed.FlagCoherentReflectionCondition
import FX1Poly.Typed.UniverseClassificationUnique
import FX1Poly.Typed.NeutralClassifierUnique
import FX1Poly.Typed.NormalAppNeutral
import FX1Poly.Typed.TelescopeUniverseDeterminism
import FX1Poly.Typed.GenericFormerTelescopeInversion
import FX1Poly.Typed.NormalUniverseClassificationUnique
import FX1Poly.Typed.ConvUniverseClassificationUnique
import FX1Poly.Typed.RenameAlongFlagCoherent
import FX1Poly.Typed.PinSelectsCallerPair
import FX1Poly.Typed.PinnedReflectionFlagCoherent
import FX1Poly.Typed.LamReductResidualDischarge
import FX1Poly.Typed.PinnedReflectionFlagCoherentMaster
import FX1Poly.Typed.GrownEtaSubjectReduction

/-! # FX1PolyAudit/AuditTypedCanonicalForms — typed-layer zero-axiom gates: canonical forms, canonicity, consistency, progress, and type safety
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/


/-! ### Closed-form consequences for the description formation engine: closed subjects are intrinsic
    description types, have universe/Pi/Sigma type-former shape, and have classifiers convertible to
    universe codes.  All three — `closedSubjectIsTypeDesc` (via the scope-generalised
    `closedSubjectIsTypeDescGeneral` workhorse), the STRUCTURAL `closedSubjectIsTypeFormer` (native
    `closedSubjectHeadIsFormerOrUniverse` + the `eq_*Cell_of_headGenerator` head-to-children
    reconstructions), and `closedClassifierConvUniverseCode` (native uniqueness) — are proved directly on the
    native formation recursion. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectIsTypeDescGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectIsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectHeadIsFormerOrUniverse
-- FORMATION-ENGINE CONSISTENCY: no closed formation-engine term inhabits the empty type
-- (HasTypeDesc .empty t emptyTypeCell → False). Every classifier a closed formation derivation reaches has
-- head gen_universeCode (universeFormation / genFormation outputs) or — for a conv reclassifier — a Π/Σ/universe
-- head (subjectIsVariableOrFormerHead, variable disjunct killed by closedness); none is gen_emptyCode. The
-- FORMATION half of SN-050; no reconstruction, no value-inversion. Zero-axiom (recursor + Generator.noConfusion).
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.noClosedFormationTermAtEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedNormalSubjectHead
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtEmptyType
-- CANONICAL FORMS PER TYPE (GrownCanonicalFormsByClassifier.lean): the classifier-sharp refinement of
-- closedNormalSubjectHead. closedNormalFunctionIsLambda = a closed normal FUNCTION-typed term (Π classifier) is a
-- λ with body extracted (the three type-former heads refuted by the *NotTypedAtPiType inversions). closedNormalTypeIsFormer
-- = a closed normal TYPE (universe classifier) is a type FORMER head piTy/sigmaTy/univ, never λ (lam refuted by
-- lam_notTypedAtUniverseCode). #672-independent, no SR — pure inversion over the closed-canonical-forms recursor.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedNormalFunctionIsLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedNormalTypeIsFormer
-- CANONICAL-FORMS NON-VACUITY (GrownCanonicalFormsNonVacuity.lean): concrete closed witnesses showing the
-- canonical-forms-per-type theorems FIRE. closedUniverseCodeTyping = Type@s : Type@(s+1) (universeFormation);
-- closedIdentityLambdaTyping = λ(x:Type@s).x : Π(Type@s).Type@s (piIntro + var) — the first NAMED concrete closed
-- POSITIVE typing derivations (complement to the GrownEngineHonesty 0-FP corpus). The two *_nonVacuous theorems
-- feed Type@0 / the identity lambda through closedNormalTypeIsFormer / closedNormalFunctionIsLambda.
#assert_no_axioms FX1Poly.Typed.closedUniverseCodeTyping
#assert_no_axioms FX1Poly.Typed.closedIdentityLambdaTyping
#assert_no_axioms FX1Poly.Typed.closedNormalTypeIsFormer_nonVacuous
#assert_no_axioms FX1Poly.Typed.closedNormalFunctionIsLambda_nonVacuous
-- TYPE SAFETY IN ACTION (GrownBetaRedexInAction.lean): a concrete closed REDUCING term threaded through the
-- safety pipeline. closedIdentityAppRedexTyping = (λ(x:Type@1).x)(Type@0) : Type@1 (piElim). betaStep = it
-- Step.beta's to Type@0. safety = the reduct Type@0 is STILL typed at Type@1 (betaSubjectReduction PRESERVATION)
-- AND is a canonical value (closedNormalTypeIsFormer) — progress + preservation + canonical forms on one
-- reducing closed term, the concrete instantiation of "a well-typed term steps to a well-typed value".
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedexTyping
-- That SR-along-↝* residual is now DISCHARGED: HasTypeDescPi.subjectReductionStar is unconditional (SR-U4),
-- so emptyTypeConsistencySyntactic instantiates it at the empty context (WfContextDescPi.emptyIsWellFormed)
-- and EmptyType classifier — the UNCONDITIONAL syntactic-route empty consistency, the twin of the
-- candidate-route emptyTypeConsistency that survives into the substantive-Empty regime.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.emptyTypeConsistencySyntactic
-- GROWN TYPE SAFETY (GrownTypeSafety.lean, five-layer-defense L4 §27.3): the named preservation/progress safety
-- statements over the grown engine. closedProgress = PROGRESS unconditional (a closed grown-typed term is a
-- canonical value — canonical head + normal — or it steps; no stuck closed terms; typing is load-bearing in the
-- normal case via closedNormalSubjectHead). closedTypeSafetyOfSubjectReductionStar = TYPE SAFETY conditional on
-- SR-along-↝* (every closed grown-typed term evaluates to a canonical value: OB-5 SN + weak normalization + the
-- preservation hypothesis + canonical forms), the lone gate being the SN-055 master dispatcher, exactly as the
-- consistency route.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedProgress
-- FORMATION TYPE SAFETY (FormationTypeSafety.lean, five-layer-defense L4 §27.3): the UNCONDITIONAL half of the
-- preservation/progress parity.  The formation engine HasTypeDesc types only normal forms (subjectAdmitsNoStep),
-- so closedFormationProgress is a canonical value with NO "or it steps" disjunct, and closedFormationTypeSafety
-- evaluates to the term ITSELF (StepStar.refl) with NO subjectReductionStar hypothesis — the SR gate the grown
-- closedTypeSafetyOfSubjectReductionStar carries is ELIMINATED here.
#assert_no_axioms FX1Poly.Typed.RawTerm.IsFormationCanonicalHead
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedFormationSubjectIsNormal
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedFormationProgress
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedFormationTypeSafety
-- OPEN PROGRESS (GrownOpenProgress.lean, five-layer-defense L4 §27.3): the OPEN generalization of closedProgress
-- off the empty context. openNormalSubjectCanonicalOrNeutral = OPEN CANONICAL FORMS — a grown-typed NORMAL term in
-- ANY well-formed context is a canonical head (IsGrownCanonicalHead) or a Core.IsNeutral term; the recursor mirrors
-- closedNormalSubjectHead but drops the (Fin scope → False) premise, rerouting the two leaves closedness eliminated
-- (var → IsNeutral.var, neutral-function app → IsNeutral.app, where variableCell/appCell are definitionally the
-- mkGen gen_var/gen_app cells the constructors expect). openProgress = OPEN PROGRESS unconditional — a grown-typed
-- term in any context is a normal canonical-value-or-neutral or it steps (by_cases on decidable normality), no
-- stuck terms in ANY context. #672-independent — pure inversion, no SR, no SN.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openNormalSubjectCanonicalOrNeutral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openProgress
-- UNCONDITIONAL GROWN TYPE SAFETY (GrownTypeSafetyUnconditional.lean, HARVEST-TS): discharge the SR-along-↝*
-- hypothesis of the four conditional capstones above via SR-U4 (subjectReductionStar, now unconditional under the
-- benign WfContextDescPi presupposition).  closedTypeSafety / closedTypeSafetyUnique feed the empty-context witness
-- (WfContextDescPi.emptyIsWellFormed); openTypeSafety / openTypeSafetyUnique lift the WfContextDesc presupposition
-- to the grown WfContextDescPi via WfContextDescPi.ofWfContextDesc.  Progress + preservation (+ confluence) with NO
-- hypothesis: every closed/open grown-typed term EVALUATES TO ITS (unique) canonical[-or-neutral] value.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafety
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyUnique
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafety
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyUnique
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.consistencyOfPiElimArm
-- ★ SN-050 UNCONDITIONAL (EmptyTypeConsistencyUnconditional.lean): emptyTypeConsistency DROPS the piElim/SR
-- conditionality above. Once emptyTypeCellHasNoTyping (the data-head boundary, last commit) existed, grown
-- VALIDITY (classifierIsTypeDescPi, WFG-3) closes consistency in two lines: t : emptyTypeCell forces
-- emptyTypeCell : universe (validity), refuted by emptyTypeCellHasNoTyping. Honest scope: the current engine,
-- where emptyTypeCell is not yet a substantive type (typingRuleDescOf gen_emptyCode = none); the
-- canonicity-grounded consistency for a formation-row Empty (CON-A3) is independent + future.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.emptyTypeConsistency
-- EXTRACTION twin of the decision lane: from the FT-derived closed SN, the normalizer EXTRACTS the canonical
-- normal form (closedNormalFormFromLevelIndexed) with its metatheory — converts to it, it is normal, and NF
-- equality is a COMPLETE conversion invariant (closedConv_iff_normalForm_eq). The cherries are PROVEN (not
-- just decidable): the closed β-redex normalizes to its reduct Type@e; the closed identity is its own NF.
#assert_no_axioms FX1Poly.Typed.closedNormalFormFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.closedNormalForm_conv
#assert_no_axioms FX1Poly.Typed.closedNormalForm_isStepNormalForm
-- NEGATIVE non-vacuity capstone: closed normal terms convert IFF syntactically equal
-- (closedNormalConv_iff_syntacticEq, the isStepNormalForm-stated rigidity), so distinct head generators are
-- PROVABLY non-convertible. Complements betaRedexConvertsToReduct (positive) — the decidable-Conv lane
-- decides both convertible AND non-convertible closed pairs. Unconditional (no FT/SN — just normality).
#assert_no_axioms FX1Poly.Typed.closedNormalConv_iff_syntacticEq
#assert_no_axioms FX1Poly.Typed.normalizeFirstCanonicalizer_isIncomplete
-- STANDALONE-ENGINE CANONICITY (StandaloneEngineCanonicity, CANON-1 increment): combined closed-canonical-forms
-- over the two NON-grown engines (data-intro values + base-type codes). ★ standaloneBoolCanonicalForms = a
-- subject typed at boolTypeCell by EITHER engine is boolTrue/boolFalse (data-intro gives it; base-type is ruled
-- out since its classifier is Type@0 != boolCode, via classifierIsType0 + headGenerator/Generator.noConfusion).
-- standaloneEmptyUninhabited = nothing typed at emptyTypeCell by either engine (standalone half of SN-050).
-- dataIntroAndBaseTypeSubjectsDisjoint = the value layer and type layer never type the same term (disjoint heads).
-- The grown disjunct (HasTypeDescPi at boolCode via conv/piElim) is the remaining CANON-1 residual. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.standaloneBoolCanonicalForms
#assert_no_axioms FX1Poly.Typed.standaloneEmptyUninhabited
-- INTERVAL NATIVE-ENGINE CANONICITY (NATIVE-10, the interval twin of standaloneBoolCanonicalForms): a subject
-- typed at intervalTypeCell by EITHER standalone engine is interval0/interval1 — the two bridge-dimension
-- endpoints. The 4th/5th coordinated data-intro rows give the endpoint directly; the bool/unit rows and the
-- base-type disjunct (Type@0 != intervalCode) are ruled out by classifier-head Generator.noConfusion.
-- ★ intervalEndpointsDistinct = interval0 != interval1 (head-generator mismatch); the faithfulness companion.
-- ★ standaloneIntervalCanonicalFormsExactlyTwo = canonicity + distinctness bundled (exactly two distinct closed
-- canonical inhabitants, the interval analogue of bool's {true,false} two-element canonicity). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.standaloneIntervalCanonicalForms
#assert_no_axioms FX1Poly.Typed.intervalEndpointsDistinct
#assert_no_axioms FX1Poly.Typed.standaloneIntervalCanonicalFormsExactlyTwo
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtBoolType
#assert_no_axioms FX1Poly.Typed.closedNormalBoolCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedBoolCanonicalForms
-- SYNTACTIC-ROUTE CANONICITY TARGET SIGNATURE (CanonicitySyntacticRoute, the candidate-bridge-free twin of
-- CanonicityTargetSignature.dataCanonicityFromCandidateBridge). ★ dataCanonicityFromSyntacticRoute = generic
-- SN-047/048/049 signature: standalone-engine canonicity (value engines) + grown vacuity ⟹ 3-engine canonicity,
-- with NO §5 candidate bridge (the grown vacuity is grown SN + SR-U4 + closed-normal forms, all shipped). Nat
-- (SN-048) / data (SN-049) instantiate it once their standalone canonicity + grown vacuity land.
-- boolCanonicityViaSyntacticRoute = the first instance, witnessing non-vacuity (= closedBoolCanonicalForms).
-- Eliminator-computing canonicity (4th engine HasTypeDescDataElim) is the follow-on, off this signature. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.dataCanonicityFromSyntacticRoute
#assert_no_axioms FX1Poly.Typed.boolCanonicityViaSyntacticRoute
-- ★ MILESTONE-A ELIMINATOR-LAYER SPINE: discharges the eliminator-layer frontier the VALUE-layer spine deferred.
-- Five fields, one per data eliminator, each a shipped unconditional computing-canonicity theorem: bool
-- (boolElimValueCanonicity, value-branch engine, one ι-step), nat (natElimCopyComputesToNumeral, RECURSIVE
-- IH-threaded copy fold), list (listElimLengthComputesToNumeral, RECURSIVE length fold), option/either
-- (closedOption/EitherMatchIntoBoolComputes, firing-64 typed match-into-bool). Every closed well-formed
-- eliminator instance reduces to a canonical value; zero-axiom. Honest scope: this is the per-eliminator
-- computing layer, NOT a unified eliminator:dataType judgment (the combined intro/elim table-residency, whose
-- formation/grown half GTL-18/20 is shipped, data-elim half open). Advances #556/#1138.
#assert_no_axioms FX1Poly.Typed.eliminatorLayerCanonicitySpineHolds
#assert_no_axioms FX1Poly.Typed.dataCanonicityFromGrownRigidity
#assert_no_axioms FX1Poly.Typed.boolCanonicityViaGrownRigidity
-- ★ SN-049: CLOSED DATA CANONICITY for Option/List/Product(Σ)/Either(Sum) (ClosedDataCanonicity, the bulk of the
-- closed-data-canonicity family after bool SN-047 + nat SN-048). Each is the SAME per-type instantiation of the
-- generic grown-rigidity packaging (dataCanonicityFromGrownRigidity): the standalone arm is the shipped
-- subjectIs<Type>Constructor inversion (the data-intro term IS a constructor, so StepStar.refl), and the two
-- Conv-rigidities are the shipped <code>_not_piTyCode / _not_universeCode from the closed-NORMAL companions
-- (OptionCanonicalForms / ListCanonicalForms / ProductEitherCanonicalForms). Product/Either use piTyCode_not_conv
-- flipped (.sym) since they are FLAT-table formers. The grown-vacuity disjunct is derived inside. ★ the four
-- closed<X>CanonicalForms = SN-049: a closed term at the data type code (intro OR grown engine) reduces to a
-- constructor. The .smoke witnesses (optionNone / nil / pair / eitherInl of universe codes) prove non-vacuity.
-- Unit deferred (its type-code rule-out not yet landed; reducibility-route candidate shipped #720). The recursive
-- eliminator-computing canonicity (#1138) is the follow-on. Zero-axiom.
-- ELIMINATOR-ENGINE CLOSED-NORMAL VACUITY: retired by NATIVE-43 — the per-engine vacuity statements
-- (BoolElimClosedNormalForms / BoolElimArbitrarySubjectCanonicity / MatchClosedNormalForms) named the
-- bespoke elim judgments; their content (a closed eliminator on a closed value scrutinee always
-- ι-fires) is carried by the union lane master's eliminator arms (every elim arm refutes normality
-- through the scrutinee IH) and the per-lane closed-normal corollaries over the ONE judgment.
#assert_no_axioms FX1Poly.Typed.boolElimValueCanonicity
-- GROWN CLOSED-NORMAL CLASSIFIER SHAPE (GrownClosedNormalClassifierShape, CANON-1 generalization): the POSITIVE
-- characterization behind every data-classifier rule-out. ★ closedNormalClassifierIsFunctionOrType = a closed
-- normal grown-typed term's classifier is Conv a Π-code OR Conv a universe code (the grown engine inhabits only
-- FUNCTION types via λ + UNIVERSES via formers, nothing else — dual of closedNormalFunctionIsLambda/TypeIsFormer).
-- noClosedNormalTermAtDataClassifier = the rule-out corollary (classifier Conv neither → no closed-normal grown
-- inhabitant), the reusable engine subsuming boolType/emptyType. ★ noClosedNormalTermAtSigmaType = NEW Σ instance
-- (grown has Σ-formation, no Σ-introduction). closedNormalSigmaTypeUninhabited = combined 3-engine: no engine
-- inhabits a Σ-type yet (honest current state until DI-2 Σ-intro). Unconditional (classifier read at normal subject).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedNormalClassifierIsFunctionOrType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtDataClassifier
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtSigmaType
#assert_no_axioms FX1Poly.Typed.closedNormalSigmaTypeUninhabited
-- EMPTY-TYPE COMBINED CONSISTENCY (ClosedNormalEmptyConsistency, CANON-1c instance): the consistency-type twin of
-- closedNormalSigmaTypeUninhabited. noClosedNormalTermAtEmptyTypeViaGeneric = the grown empty rule-out re-derived
-- via the CANON-1c corollary noClosedNormalTermAtDataClassifier (emptyTypeCell Conv neither Π nor universe code,
-- via Conv.piTyCode_not_emptyTypeCode/.universeCode_not_emptyTypeCode + .sym) — demonstrates the abstraction
-- subsumes the concrete noClosedNormalTermAtEmptyType. ★ closedNormalEmptyTypeUninhabited = combined 3-engine: NO
-- engine (data-intro/base-type/grown) inhabits Empty for closed-normal subjects → the new standalone engines
-- PRESERVE consistency. Unconditional (classifier read at normal subject). Full closed consistency = SN-050/CON-A5.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtEmptyTypeViaGeneric
#assert_no_axioms FX1Poly.Typed.closedNormalEmptyTypeUninhabited
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtProductType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtEitherType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtOptionType

-- CAN-4/CAN-5 RETIRED by NATIVE-42: the TypedByValueEngine zoo mini-union and its
-- closedNormalSubjectHeadCombined / closedNormalNatCanonicalFormsCombined assemblies are
-- superseded by the ONE-judgment NATIVE-38 union lane master and its per-lane corollaries
-- (HasTypeNativeUnion.closedNormalLaneCanonicalForms + closedNormalNatCanonicalForms etc.,
-- gated in AuditHasTypeNativeUnionCanonicalForms and re-verified in CapstoneSignoff).

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtListType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtIdType
-- DATA-CANONICITY FOUNDATION: CanonicalFormsPredicate isValue = SN ∧ (neutral ∨ reduces-to-value), the sharper
-- canonicity-bearing candidate (vs the bare SN candidate the model gives data leaves). Generic over the value
-- predicate (bool→true/false, Empty→empty pred, nat→zero/succ). CR1 (stronglyNormalizing) = first conjunct; CR3
-- (neutralExpansion) = Acc.intro over reducts' SN + Or.inl (shipped SN-candidate CR3 pattern); containsVariable
-- via vacuous CR3. CR2 DEFERRED (needs IsNeutral-closed-under-Step + per-term confluence) — so this is the
-- honest 2-of-3 foundation, NOT yet a full IsReducibilityCandidate. #672-free. Toward SN-063/047.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.neutralExpansion
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.containsVariable
-- CR2 NOW DISCHARGED (was deferred last tick): closedUnderStep — a member's reduct stays a member, the disjunct
-- preserved by neutralClosedUnderStep (neutral case) or per-term confluence + value rigidity (reduces-to-value
-- case: value is an NF, confluence_of_localJoin_and_accessible joins the reduct with the value-chain,
-- eq_of_noStep collapses the apex onto the value). isReducibilityCandidate = the FULL CR1+CR2+CR3 bundle: the
-- canonical-forms predicate IS a Girard reducibility candidate given the two data facts (IsNeutral closed under
-- Step + data values are normal). Per-term confluence only (no global-confluence assumption). #672-free; the
-- honest unconditional foundation for data canonicity (SN-063 bool reducibility / SN-047 bool canonicity).
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.closedUnderStep
-- CANONICITY EXTRACTION (#672-free): a CLOSED candidate member cannot be neutral (IsNeutral.noClosed), so it
-- reduces to a designated value. Generic closedReducesToValue + bool specialization (closed bool member
-- reduces to true/false). The structural core of SN-047/049 canonicity; only the membership half (closed
-- well-typed term is a member) awaits the typed reducibility fundamental theorem.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.closedReducesToValue
#assert_no_axioms FX1Poly.Core.boolClosedReducesToTrueOrFalse
-- WEAK-HEAD EXPANSION (backward closure) for the data candidate, in the regime where it HOLDS: a redex into
-- a value-reaching contractum, itself SN, is a member (r ↝ contractum ↝* value gives r ↝* value). The data
-- candidate is NOT weak-head-expansion-closed for a NEUTRAL contractum (a fired redex is non-neutral yet
-- reduces to the stuck neutral, satisfying neither disjunct) — that boundary is the honest scope, documented
-- in the file. weakHeadExpansionOfMemberNotNeutral is the directly-usable member form (ι contractum is a
-- non-neutral closed branch member). The closed-canonicity recursor-assembly step; #672-independent.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.weakHeadExpansionOfValueReaching
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.ofStepStarReachingValue
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.weakHeadExpansionOfMemberNotNeutral
#assert_no_axioms FX1Poly.Core.boolElimCanonicalScrutineeReducesToBranch
-- ELIMINATION MEMBERSHIP (#672-free, SN-063 eliminator half): a closed boolElim on a canonical bool scrutinee
-- with member branches is ITSELF a member of the result candidate. The cell is SN (boolElim SN from the
-- members' CR1 witnesses), reduces to the selected branch (boolElimCanonicalScrutineeReducesToBranch), and that
-- closed branch member reaches a value (closedReducesToValue) — value-reaching weak-head expansion
-- (ofStepStarReachingValue, #735) lifts membership back to the cell. The recursor lands in the candidate, not
-- merely normalizes — closed-layer assembly, no fundamental theorem.
#assert_no_axioms FX1Poly.Core.boolElimClosedIsMember
-- Concrete eliminator-membership regression (DataEliminatorMembershipSmoke, SN-149 corpus seed): a CONCRETE
-- closed boolElim on canonical bool members is itself a bool-candidate member — boolElimClosedIsMember fed the
-- shipped concrete value-members compose into an actual closed inhabitant (not an alias). The data-eliminator
-- membership layer (bool/Σ/option/either/idJ/idStrictRec/refl + recursive nat/list) is complete; this exercises it.
#assert_no_axioms FX1Poly.Core.boolElimClosedMembershipSmoke
-- Concrete idJ / idStrictRec membership regression (DataEliminatorMembershipSmoke, SN-149 corpus): the closed
-- idJ / idStrictRec cells with base case boolTrue and witness (refl boolTrue) are themselves bool-candidate
-- members via idJClosedIsMember / idStrictRecClosedIsMember fed the refl member (witness inner term step-normal
-- by decide) and boolTrueCell_isMember — extending the concrete eliminator-membership corpus past boolElim.
#assert_no_axioms FX1Poly.Core.idJClosedMembershipSmoke
#assert_no_axioms FX1Poly.Core.idStrictRecClosedMembershipSmoke
-- Concrete fst / snd PROJECTION membership regression (DataEliminatorMembershipSmoke, SN-149 corpus): the closed
-- fst / snd cells over the canonical pair (boolTrue, boolFalse) are bool-candidate members via fstClosedIsMember /
-- sndClosedIsMember. The component obligation (∀ first second, scrutinee ↝* pairCell _ _ → member) is discharged by
-- inversion: the pair is a structural normal form (isStepNormalForm_blocks_step on `by decide`), so eq_of_noStep
-- forces the reach reflexive and the mkGen/childCons injection (scope/shift/restShifts/childHead/childTail, five
-- outputs) pins the component to the canonical bool value. The value-PROJECTING half of the corpus, concrete.
#assert_no_axioms FX1Poly.Core.fstClosedMembershipSmoke
#assert_no_axioms FX1Poly.Core.sndClosedMembershipSmoke
-- Concrete optionMatch / eitherMatch BRANCH-APPLYING membership regression (DataEliminatorMembershipSmoke,
-- SN-149 corpus): the closed optionMatch (on none) / eitherMatch (on inl boolTrue) over the constant branch
-- λ_. boolTrue are bool-candidate members via optionMatchClosedIsMember / eitherMatchClosedIsMember. The
-- branch-respect-SN obligation (branch applied to an arbitrary SN argument lands in the candidate) is
-- discharged by constLamBoolTrue_respectsSN: app (λ_. boolTrue) value β-reduces (WeakHeadStep.beta.toStep,
-- subst0 boolTrue value = boolTrue definitional) to the bool value boolTrue, SN by appLamBoolTrue..., lifted by
-- ofStepStarReachingValue. The "constant-branch weak-head expansion" — completes the non-recursive eliminator
-- smoke corpus (only recursive natElim/natRec/listElim remain deferred).
#assert_no_axioms FX1Poly.Core.constLamBoolTrue_app_stepStar
#assert_no_axioms FX1Poly.Core.constLamBoolTrue_respectsSN
#assert_no_axioms FX1Poly.Core.optionMatchClosedMembershipSmoke
#assert_no_axioms FX1Poly.Core.eitherMatchClosedMembershipSmoke
-- Concrete recursive-eliminator BASE-CASE membership regression (DataEliminatorMembershipSmoke, SN-149 corpus):
-- natElim/natRec on natZero and listElim on listNil fire root-ι to the base branch with NO recursion, so the
-- cell is SN by the branch-SN-only helper (natElimZero_isStronglyNormalizing_of_branches and twins — no
-- per-predecessor recursor-SN obligation), and ofStepStarReachingValue lifts the base-branch member. The SN-061/
-- 062/064 base half at concrete witnesses; the IH-carrying succ/cons case remains the lone deferral.
#assert_no_axioms FX1Poly.Core.natElimZeroClosedMembershipSmoke
#assert_no_axioms FX1Poly.Core.natRecZeroClosedMembershipSmoke
#assert_no_axioms FX1Poly.Core.listElimNilClosedMembershipSmoke
#assert_no_axioms FX1Poly.Core.pairCanonicalScrutineeProjectsToComponents
#assert_no_axioms FX1Poly.Core.idJCanonicalWitnessReducesToBase
#assert_no_axioms FX1Poly.Core.idStrictRecCanonicalWitnessReducesToBase
-- IDENTITY-ELIMINATOR MEMBERSHIP (#672-free, the SN-068/069 elimination half, closed-layer): a closed idJ/
-- idStrictRec whose witness is a canonical identity member and whose base case is a member of a result candidate
-- is ITSELF a member of that candidate. The exact clean analogue of boolElimClosedIsMember — idJ/idStrictRec are
-- the non-growing (passive-base) eliminators whose single iota selects the base case DIRECTLY from the witness
-- position (no payload app, no recursion). The cell is SN (idJ/idStrictRec_isStronglyNormalizing_of_strongly_
-- normalizing_base, the SN-base strengthening, on the members' CR1 SN), reduces to the base case (idJ/
-- idStrictRecCanonicalWitnessReducesToBase), and that closed base-case member reaches a value (closedReducesTo-
-- Value) — value-reaching weak-head expansion (ofStepStarReachingValue, #735) lifts membership to the cell. The
-- recursor lands in the candidate, not merely normalizes; no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.idJClosedIsMember
#assert_no_axioms FX1Poly.Core.idStrictRecClosedIsMember
#assert_no_axioms FX1Poly.Core.optionMatchCanonicalScrutineeReduces
#assert_no_axioms FX1Poly.Core.eitherMatchCanonicalScrutineeReduces
-- APPLIED-BRANCH eliminator MEMBERSHIP (#672-free, the SN-065/066 elimination half, closed-layer): a closed
-- optionMatch/eitherMatch whose scrutinee is a canonical member and whose branches RESPECT SN arguments (map SN
-- args to result-candidate members) is ITSELF a member. The applied-branch twin of boolElim/idJ closed
-- membership — the some/inl/inr ι applies the branch to the wrapped payload, so the cell-SN ingredient is the
-- SN-from-SN-branches matcher lemma (someContractumTerminates from branchRespectsSN's CR1), and the contractum
-- app branch payload reaches a value because the payload is SN (canonical scrutinee subterm via descendStepStar
-- + value-subterm) and branchRespectsSN payload is a member. ofStepStarReachingValue (#735) lifts to the cell.
#assert_no_axioms FX1Poly.Core.optionMatchClosedIsMember
#assert_no_axioms FX1Poly.Core.eitherMatchClosedIsMember
-- PROJECTION eliminator MEMBERSHIP (#672-free, the SN-058 elimination half, closed-layer): a closed fst/snd on
-- a canonical pair scrutinee whose projected component is a result-candidate member is ITSELF a member. The
-- projection twin of the branch-eliminator membership, completing the closed-membership track for ALL
-- non-recursive eliminators. Cell SN is the shipped fst/snd_isStronglyNormalizing_of_argument (contractum is a
-- subterm, no respect-hypothesis); pairCanonicalScrutineeProjectsToComponents reduces the cell to the component;
-- firstComponentMember/secondComponentMember (conditional on the witnessed scrutinee ->* pairCell) is a member,
-- so reaches a value; ofStepStarReachingValue (#735) lifts to the cell.
#assert_no_axioms FX1Poly.Core.fstClosedIsMember
#assert_no_axioms FX1Poly.Core.sndClosedIsMember
-- RECURSIVE eliminator MEMBERSHIP (#672-free, the deferred half of SN-061, closed-layer): a closed natElim/
-- natRec on a member Nat scrutinee with a reducible (function-space) succ branch is ITSELF a member. The
-- recursive twin of the eliminator-membership track — instantiates natElim/natRecValueReducibility (#732) at the
-- closed data candidate (headExpand from weakHeadExpansionOfMemberNotNeutral + WeakHeadStep.toStep + IsNeutral.
-- noClosed), discharges redexStronglyNormalizing + cell SN via the natElim/natRec SN-from-SN-branches recursors
-- (prior tick), lifts the numeral-case membership through the scrutinee congruence by ofStepStarReachingValue
-- (#735). succContractumTerminates is the honest recursor-SN IH-premise (the same conditional-arm discipline
-- #732 uses for redexStronglyNormalizing).
#assert_no_axioms FX1Poly.Core.natElimClosedIsMember
#assert_no_axioms FX1Poly.Core.natRecClosedIsMember
-- The list twin (deferred half of SN-064, closed-layer): a closed listElim on a member List scrutinee with a
-- reducible (3-argument function-space) cons branch is ITSELF a member. Instantiates listElimValueReducibility
-- (#733) at the closed data candidate; consBranchApplication takes the head in isStepNormalForm form (not SN)
-- and the tail as IsListValue; consContractumTerminates is the honest recursor-SN IH-premise.
#assert_no_axioms FX1Poly.Core.listElimClosedIsMember
-- SCONING LEG (Path C, the INDEPENDENT canonicity route; SN-092/100): the FIRST concrete data-type sconing
-- witness. boolCanonicityScone instantiates the generic BKS SconingWitness for bool with the SHARP canonical-form
-- notion (reduces to true/false): computable = bool candidate, EXTRACTION discharged #672-free by
-- boolClosedReducesToTrueOrFalse, fundamental (well-typed bool -> candidate member = the FT) the explicit sole
-- obligation. boolCanonicityViaSconing = SconingWitness.canonicity applied: given fundamental, closed well-typed
-- bool reduces to true/false. Shows the sconing route reaches the SAME bool canonicity as Tait, modulo the SAME
-- #672 fundamental — extraction is free, so Path C adds no obligation beyond Path A's. No fundamental proven here.
#assert_no_axioms FX1Poly.Core.boolCanonicityScone
#assert_no_axioms FX1Poly.Core.boolCanonicityViaSconing
-- GENERIC data-canonicity sconing witness (SN-048/049/093): generalizes the bool witness above (a SPECIAL CASE).
-- EVERY data candidate shares ONE uniform #672-free extraction (CanonicalFormsPredicate.closedReducesToValue,
-- generic in the value predicate), so dataCanonicityScone is parametric in isValue: computable = data candidate,
-- extraction = the uniform closedReducesToValue, fundamental (well-typed -> candidate member) the explicit sole
-- obligation. dataCanonicityViaSconing = canonicity applied generically. nat/list/option/either/pair instances
-- are one-line specializations at the concrete value predicates — the "one functor => canonicity for all data"
-- realization (toward SN-110), each the §3.12 canonicity headline per type via Path C. No fundamental proven here.
#assert_no_axioms FX1Poly.Core.dataCanonicityScone
#assert_no_axioms FX1Poly.Core.dataCanonicityViaSconing
#assert_no_axioms FX1Poly.Core.natCanonicityViaSconing
#assert_no_axioms FX1Poly.Core.listCanonicityViaSconing
#assert_no_axioms FX1Poly.Core.optionCanonicityViaSconing
#assert_no_axioms FX1Poly.Core.eitherCanonicityViaSconing
#assert_no_axioms FX1Poly.Core.pairCanonicityViaSconing
#assert_no_axioms FX1Poly.Core.identityCanonicityViaSconing
-- modIntro (modal box) canonicity via sconing (SN-073): the modal-box former joins the generic sconing witness
-- (isModIntroValue), completing canonicity-via-sconing coverage to ALL formers with a canonical-forms candidate
-- (data + modal box). #672-free extraction, conditional only on the per-type fundamental, so genuinely unblocked.
#assert_no_axioms FX1Poly.Core.modIntroCanonicityViaSconing
-- BKS BUNDLING CAPSTONE for the data axis (SN-096/110): one fundamental obligation => BOTH metatheorems.
-- DataMetatheory bundles normalization (every well-typed term is SN) + canonicity (reduces to a constructor).
-- dataMetatheoryViaSconing: from the single fundamental (well-typed -> candidate member), normalization is the
-- candidate's CR1 first conjunct (stronglyNormalizing), canonicity is the closed extraction
-- (closedReducesToValue = dataCanonicityViaSconing). The data-axis realization of "one functor => many
-- metatheorems" (BKS sconing-is-enough). Both halves #672-free; the shared fundamental is the sole #672 gate.
-- Does NOT flip the Tier-0 ln.hasBKSMetatheoryPackage flag (that tracks the categorical glued-model package).
#assert_no_axioms FX1Poly.Core.DataMetatheory
#assert_no_axioms FX1Poly.Core.dataMetatheoryViaSconing
-- CONSISTENCY via the sconing leg (SN-050/053): the third corner of the sconing-leg triad (normalization +
-- canonicity + consistency). consistencyScone is the sconing witness at the empty type — computable = the empty
-- candidate, canonical-form notion the DEGENERATE fun _ => False (the empty type has no canonical forms),
-- EXTRACTION the #672-free emptyHasNoClosedMember (no closed term inhabits the empty candidate, as a closed
-- member would reduce to a value but an empty value is False). consistencyViaSconing = canonicity applied:
-- given the fundamental, every closed well-typed empty term yields False. Consistency IS canonicity at the
-- empty type. The fundamental (closed well-typed empty -> member) is the explicit sole #672 obligation.
#assert_no_axioms FX1Poly.Core.consistencyScone
#assert_no_axioms FX1Poly.Core.consistencyViaSconing
-- PROGRESS via the sconing fundamental (SN-058/063): the operational complement to canonicity. Where
-- canonicity says what value a closed well-typed data term reduces to, progress says a closed well-typed
-- eliminator is never STUCK. Composes the sconing fundamental (well-typed scrutinee -> candidate member,
-- the explicit #672 obligation) with the #672-free eliminator computation. Restricted to the NON-RECURSIVE
-- eliminators (boolElim branch selection, fst/snd projection) whose iota fires once with no recursive
-- sub-term; the recursive natElim/natRec/listElim only progress #672-free on their base constructor.
#assert_no_axioms FX1Poly.Core.boolElimProgressViaSconing
#assert_no_axioms FX1Poly.Core.pairProjectionProgressViaSconing
-- Progress completion for the REMAINING non-recursive eliminators (option/either case selection, idJ/idStrictRec
-- base selection): same composition pattern (fundamental + #672-free eliminator computation). With boolElim +
-- fst/snd above, this closes the progress track for EVERY non-recursive data eliminator — never stuck on
-- well-typed input, modulo the one shared #672 fundamental.
#assert_no_axioms FX1Poly.Core.optionMatchProgressViaSconing
#assert_no_axioms FX1Poly.Core.eitherMatchProgressViaSconing
#assert_no_axioms FX1Poly.Core.idJProgressViaSconing
#assert_no_axioms FX1Poly.Core.idStrictRecProgressViaSconing
-- Progress for the RECURSIVE data eliminators (RecursiveEliminatorProgressViaSconing.lean, SN-061/SN-064): lifts
-- the exclusion noted above. The recursive succ/cons ι re-invokes the eliminator, which the prior progress file
-- said "needs Tait" — that Tait piece is RecursorClosedMembership (natElim/natRec/listElimClosedIsMember, the
-- #672-free scrutinee-reduction half, fed the honest recursor-SN IH-premise). Threads the sconing fundamental
-- (well-typed Nat/List scrutinee -> data-candidate member) into the scrutinee position and reads off
-- closedReducesToValue: a well-typed recursor with a reducible branch interface REDUCES TO A VALUE. The SN-061/
-- SN-064 canonicity payoff via the sconing leg, closing the recursive corner of the eliminator-progress track.
#assert_no_axioms FX1Poly.Core.natElimProgressViaSconing
#assert_no_axioms FX1Poly.Core.natRecProgressViaSconing
#assert_no_axioms FX1Poly.Core.listElimProgressViaSconing
-- A normal value is a member of its candidate (the generic constructor-reducibility helper).
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.memberOfValue
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.canonicalSplit
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.closedNormalIsLambda
#assert_no_axioms FX1Poly.Tier0.witnessScone_semanticIsCanonical
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectRootGeneratorGeneric

-- RAW NON-SN — the honest NEGATIVE counterpart to SN-043 (five-layer-defense L1, §27.3). SN-043 proves
-- WELL-TYPED terms are strongly normalizing; this proves the RAW Step relation is NOT (Ω = (λx.x x)(λx.x x)
-- β-steps to itself, so it is not Acc StepSuccessor), confirming the typing restriction is load-bearing and
-- that global raw SN (HasStrongNormalization) is FALSE, not merely unproved. The first non-SN witness in the
-- kernel. notAccessibleOfSelfLoop is the general Acc self-loop fact; divergentOmega_stepsToSelf is Step.beta
-- (the subst0 of the self-applicator into its body computes to Ω definitionally).
#assert_no_axioms FX1Poly.Typed.divergentOmega_stepsToSelf
#assert_no_axioms FX1Poly.Typed.notAccessibleOfSelfLoop
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectHeadHasRoleOrIsUniverseCode
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_progress
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_progress
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_progress
#assert_no_axioms FX1Poly.Typed.crossRef_progress
#assert_no_axioms FX1Poly.Typed.crossRef_consistency
#assert_no_axioms FX1Poly.Typed.crossRef_universePredicativity
#assert_no_axioms FX1Poly.Typed.consistency_hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.formationMetatheory_progress
#assert_no_axioms FX1Poly.Typed.grownMetatheory_progress
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationBeta
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationFormerArm
#assert_no_axioms FX1Poly.Typed.incompleteMetatheory_missingProgress

-- SN-082 (DataReducibilityCoverage): the reducibility-coverage gate over the ten data-former families.
-- `hasReducibilityCandidate` is the total dependent dispatch — every family's CanonicalFormsPredicate is a
-- full Girard candidate (each arm its OWN shipped candidate, indexed by valuePredicate so no cross-family
-- discharge). A regression gate: adding a DataFormerFamily ctor without a candidate fails to compile.
-- Non-vacuity: bool's candidate is inhabited (boolTrueCell); empty's is the bottom (no closed member).
#assert_no_axioms FX1Poly.Core.DataFormerFamily.valuePredicate

/- The piElim-residual whnf DISPATCHER (PinnedReflectionPiElimDispatcher): the FULL residual
reduces to the two head-specific residuals (λ-after-whnf + neutral-reduct-after-whnf, the latter's
bare-var instance pre-discharged) via grown-wf SN → normalize → SR-star → the wf-FREE canonical
forms (copies of the shipped open canonical forms with the vestigial formation-wf premise
deleted). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalSubjectCanonicalOrNeutralOfTyping
#assert_no_axioms FX1Poly.Typed.cascadeAnchor_canonicalFormsBrick
#assert_no_axioms FX1Poly.Typed.canonicalForms_isBoundedBricks
#assert_no_axioms FX1Poly.Typed.cost_discriminates_dispatch_vs_canonicalForms
