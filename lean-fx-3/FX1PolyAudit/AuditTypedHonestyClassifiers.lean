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
import FX1Poly.Typed.GeneratorAdmissionSplit
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

/-! # FX1PolyAudit/AuditTypedHonestyClassifiers — typed-layer zero-axiom gates: the generator honesty classifiers and faithfulness witnesses
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.RawTerm.headGenerator

/-! ### Universe-code cell destructor — recovers
    `universeCodeCell e flag` from `headGenerator = gen_universeCode` via the
    `RawTermChildren.eq_childNil` brick; the raw destructor `Decidable IsType`
    needs to apply `HasType.universeFormation`. -/

#assert_no_axioms FX1Poly.Typed.eq_universeCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.eq_variableCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.headGenerator_universeCodeCell
#assert_no_axioms FX1Poly.Typed.headGenerator_variableCell

/-! ### Π-formation shape bricks — `piTyCodeCell`
    smart ctor + head-generator computation + the two-child destructor that
    the `piFormation` arm + the decider consume. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_piTyCodeCell_of_headGenerator

/-! ### Σ-formation shape substrate — the complete
    raw-cell substrate for the Σ-formation arm, the dual of the Π substrate.
    `gen_sigmaTyCode` is structurally identical to `gen_piTyCode` ([0, 1] binder
    shifts, `Unit` payload), so each brick is the exact analog of its
    `piTyCodeCell` counterpart with the head generator swapped: the smart-ctor
    head computation, the two-child destructor, injectivity, non-stepping (pure
    type former), the `rename`/`subst` commutations (both `rfl`), and the
    `RawTerm.size` `decreasing_by` bricks.  The Σ arm + its decider consume
    these. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_sigmaTyCodeCell_of_headGenerator
-- GTL-11 canonical-forms substrate: the one-child listCode head→children reconstruction (the data-former twin
-- of eq_sigmaTyCodeCell_of_headGenerator) the formation canonical-forms consumers need for the listCode head.
#assert_no_axioms FX1Poly.Typed.eq_listCodeCell_of_headGenerator
-- GTL-13 part 1: the row-INDEPENDENT optionCode reducibility/shape substrate (the "reducibility-candidate
-- identification" half) — the one-child optionCode twins of the listCode shape reconstruction, the under-subst
-- universe-membership, the level-indexed telescope member, and the bounded genFormationPi recursor arm. They
-- land ahead of the typingRuleDescOf optionCode row (the formation row + ~18-site canonical-forms cascade follow).
#assert_no_axioms FX1Poly.Typed.eq_optionCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.Conv.formationFormerGeneratorEq
#assert_no_axioms FX1Poly.Typed.Conv.flatFormationFormerGeneratorEq
-- PIELIM-KILLING TOOLKIT (PiTypeFunctionInversion.lean): the ingredients for the grown closed-canonical-forms
-- piElim case. eq_lamCell_of_headGenerator = the 4th head→shape reconstruction (λ companion to pi/sigma/
-- universe/var). The three *NotTypedAtPiType inversions = a type former / universe code is not a member of a
-- Π-type (its classifier is Conv a universe code, which a Π-code is not) — the Π-classifier analogue of the
-- *NotTypedAtEmptyType value inversions. Together they discharge every non-λ shape the app function can take.
#assert_no_axioms FX1Poly.Typed.eq_lamCell_of_headGenerator

/-! ### genFormationPi former weak-head-normality — the `genFormationPi` arm's WHN obligation.
    `typingRuleDescOf` is `some` only for `gen_piTyCode` / `gen_sigmaTyCode` (the dependent type-formers),
    both weak-head normal, so the fundamental theorem's generic formation arm discharges the
    `reducibleOfWeakHeadNormalFormer` weak-head-normality hypothesis with no per-former proof at the
    induction site. -/
#assert_no_axioms FX1Poly.Typed.formationGenerator_noWeakHeadStep

-- Root-classification corollaries: a formation-typed subject's root generator is neither lam nor app. The
-- table-generic family in HasTypeDescPiRootGeneric (subjectRootGeneratorGeneric /
-- closedSubjectRootGeneratorGeneric, gated below) drives these ne_lam/ne_app corollaries, so a new formation
-- row extends them with no change.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_lam
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_app
-- ★ ELIMINATOR-LAYER bool canonicity (the deferred CANON-1 follow-on, via the COMPONENT-typing route):
-- a closed boolElim(scrutinee, then, else) with a 3-engine-typed scrutinee at boolType AND data-VALUE-typed
-- branches reduces to boolTrue/boolFalse -- the eliminator genuinely COMPUTES (scrutinee canonicity +
-- StepStar.boolElimScrutinee congruence + ι + branch value). Non-vacuous (smoke: boolElim(true,true,false)),
-- precisely the eliminator the vacuous standalone HasTypeDescBoolElim cannot type (value branches). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.closedBoolElimComputesToValue
#assert_no_axioms FX1Poly.Typed.closedBoolElimComputesToValue.smoke
-- ★ TYPED option/either MATCH eliminator-computing canonicity (MatchElimComputingCanonicityTyped), extending
-- the boolElim result to the PAYLOAD-CARRYING match family via the scrutinee congruence: a closed
-- optionMatch(scrutinee, boolTrue, λ_.boolTrue) / eitherMatch(scrutinee, λ_.boolTrue, λ_.boolFalse) with a typed
-- option/either scrutinee reduces to boolTrue/boolFalse. The scrutinee reduces to a constructor value
-- (closedOption/EitherCanonicalForms), the congruence carries it under the match, ι selects+applies the branch,
-- and the constant bool branch β-reduces PAST any SOME/INL/INR payload (sidestepping the payload-normality
-- requirement of the general operational optionMatchComputesToValue). Non-vacuous (smokes on optionNone /
-- eitherInl(Type@0)). Constant-branch corner; general-branch case is the named CANON-1 follow-on. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.closedOptionMatchIntoBoolComputes
#assert_no_axioms FX1Poly.Typed.closedEitherMatchIntoBoolComputes
#assert_no_axioms FX1Poly.Typed.closedOptionMatchIntoBoolComputes.smoke
#assert_no_axioms FX1Poly.Typed.closedEitherMatchIntoBoolComputes.smoke
-- ★ GENERAL-BRANCH option/either match canonicity (MatchGeneralBranchCanonicity): the structural reduction
-- abstracted over the branch canonicity, so it covers ARBITRARY (payload-using) branches, not just constant ones.
-- closedOption/EitherMatchComputes discharge the scrutinee part (canonical forms + congruence + ι) and take branch
-- canonicity as a hypothesis; the prior constant-branch result is recovered as a corollary
-- (closedOptionMatchIntoBoolFromGeneral). The identity-branch witnesses (closedOption/EitherMatchIdentityIntoBool)
-- CONSUME the stored payload and re-emit it — past the constant-branch corner the prior file flagged. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.closedOptionMatchComputes
#assert_no_axioms FX1Poly.Typed.closedEitherMatchComputes
#assert_no_axioms FX1Poly.Typed.closedOptionMatchIntoBoolFromGeneral
#assert_no_axioms FX1Poly.Typed.closedOptionMatchIdentityIntoBool
#assert_no_axioms FX1Poly.Typed.closedEitherMatchIdentityIntoBool
-- ★ RECURSIVE eliminator-computing canonicity (NatElimComputingCanonicity, the nat analogue of
-- boolElimValueCanonicity, the recursive heart of #1138). boolElim is non-recursive (value branches, one ι-step);
-- natElim is RECURSIVE: iotaNatElimSucc reintroduces a natElim subterm AND feeds it to the successor FUNCTION
-- branch, so the recursive call must compute and the function branch must β-reduce. ★ natElimComputesToNumeral =
-- a closed natElim(n, z, s) with numeral z and a step s that produces a numeral from a numeral predecessor+rec
-- result (stepProduces) computes ↝* to a numeral, by induction on n's IsNatNumeral (zero: iotaNatElimZero; succ:
-- iotaNatElimSucc + IH reduces inner natElim via StepStar.appArgument + stepProduces finishes). stepProduces IS
-- the recursive-eliminator's honest content (the function branch's β-computation, which the bool value-branch case
-- lacked). constNatZeroStep (λλnatZero, discards rec) + copyNatStep (λλ(natSucc rec), USES rec → rebuilds the
-- numeral) discharge stepProduces concretely (two β-steps, subst0 computes definitionally through the binders),
-- instantiating the abstract theorem; .two = a fully-concrete numeral-2 smoke. The full standalone typed
-- HasTypeDescNatElimValue judgment (grown-typed succ branch feeding stepProduces unconditionally) is the GTL
-- table-residency follow-on (#832/#1138). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.natElimComputesToNumeral
#assert_no_axioms FX1Poly.Typed.natElimConstZeroComputesToNumeral
#assert_no_axioms FX1Poly.Typed.natElimCopyComputesToNumeral
#assert_no_axioms FX1Poly.Typed.natElimCopyComputesToNumeral.two
#assert_no_axioms FX1Poly.Typed.natElimAddFaithful
#assert_no_axioms FX1Poly.Typed.natElimAddFaithful.twoPlusThree
-- ClosedNumeralSubstInvariant (HON-13 Nat.mul crack): the substrate breaking the subst-no-compute wall that
-- blocks native Nat.mul faithfulness. mulStep embeds the multiplicand numeral under binders; its β-reduction
-- must push subst through a SYMBOLIC numeral, which is a stuck match (no rfl). natNumeralAt_subst proves a closed
-- numeral is fixed by ANY substitution by induction on m (subst_natSucc_reduces exposes the succ, IH closes),
-- so the mulStep β-reduct is rewritten explicitly. natNumeralAt = scope-general numeral (the existing
-- natNumeralCell is scope-0 only; under binders it lives at scope 2); the _zero bridge connects to
-- natElimAddFaithful for the eventual Nat.mul induction. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.natNumeralAt
#assert_no_axioms FX1Poly.Typed.natNumeralAt_subst
#assert_no_axioms FX1Poly.Typed.natElimMulFaithful
#assert_no_axioms FX1Poly.Typed.natElimMulFaithful.threeTimesTwo
-- ★ HON-5 NEGATIVE soundness of the honest static-typing classifier: a head hasSomeTypingRule reports RESERVED
-- (= false) is typed by NO surviving standalone engine. Grown leg = the propext-free bridge
-- hasSomeTypingRule_false_imp_isUntypableHead (peels the 27-disjunct || chain via orEqFalse_left/rightFalse,
-- reduces typingRoleOf via if_neg, discharges with decide_eq_true) feeding the shipped isUntypableHead_sound.
-- The bespoke HasTypeDescBridge engine was RETIRED (NATIVE-45): its rows are now arms of HasTypeNativeUnion, so
-- bridgeReservedUntyped is gone and reservedHeadUntypedBySurvivingEngines now carries the lone grown leg. The
-- every-native-rule statement lives in HasTypeNativeUnion.reservedHeadUntyped (UnionStaticTypingSoundness). Turns
-- hasSomeTypingRule = false from a Bool into a TRUTHFUL "statically reserved" verdict.
#assert_no_axioms FX1Poly.Typed.orEqFalse_leftFalse
#assert_no_axioms FX1Poly.Typed.orEqFalse_rightFalse
#assert_no_axioms FX1Poly.Typed.notEqTrue_ofEqFalse
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_false_imp_isUntypableHead
#assert_no_axioms FX1Poly.Typed.grownReservedUntyped
#assert_no_axioms FX1Poly.Typed.reservedHeadUntypedBySurvivingEngines
-- ★ RECURSIVE list-eliminator computing canonicity (ListElimComputingCanonicity), completing the
-- recursive-eliminator computing-canonicity family (nat + list). listElim's cons ι-rule is a TRIPLE-nested app
-- (the cons branch is a 3-arg curried function Elt→List→C→C) reintroducing a listElim over the tail. ★
-- listElimComputesToValue = a closed listElim(s, nil, cons) with an isResultValue nil-branch and a cons branch
-- that produces an isResultValue from a head/tail/value-rec (stepProduces) computes ↝* to an isResultValue, by
-- induction on s's IsListValue (nil: iotaListElimNil; cons: iotaListElimCons + IH reduces inner listElim via
-- StepStar.appArgument + stepProduces finishes). General over the result predicate. constNatZeroStep3
-- (λλλnatZero, discards all 3) + lengthNatStep (λλλ(natSucc rec), USES rec → counts the list ⟹ listElim folds a
-- list to its LENGTH as a numeral) discharge stepProduces by 3 β-steps each (subst0 computes through the
-- binders, double StepStar.appFunction reaches past the triple-app's two function layers). .two = a concrete
-- 2-element-list length smoke. Same GTL combined-engine follow-on (#832/#1138) as natElim. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.listElimComputesToValue
#assert_no_axioms FX1Poly.Typed.listElimConstZeroComputesToNumeral
#assert_no_axioms FX1Poly.Typed.listElimLengthComputesToNumeral
#assert_no_axioms FX1Poly.Typed.listElimLengthComputesToNumeral.two
-- ★ FAITHFUL list-length (ListElimFaithfulLength, HON-12): SHARPENS listElimLengthComputesToNumeral from "reaches
-- A numeral" to the EXACT host List.length — listElim(rawListReplicate n, natZero, lengthStep) ↝* natNumeral n
-- for ALL n (the n-element list folds to the numeral n), so gen_listElim truthfully encodes List.length. The
-- list analogue of natElimAddFaithful (native natElim = exact Nat.add). Structural recursion on n: iotaListElimNil
-- projects natZero; iotaListElimCons + IH (StepStar.appArgument over the tail recursor) + lengthNatStepComputesExact
-- (3 β, simple natSucc body — no subst0 wall) wraps one natSucc, natSucc(natNumeral n) ≡ natNumeral (n+1). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.rawListReplicate_isListValue
#assert_no_axioms FX1Poly.Typed.lengthNatStepComputesExact
#assert_no_axioms FX1Poly.Typed.listElimLengthFaithful
#assert_no_axioms FX1Poly.Typed.listElimLengthFaithful.three
-- ★ SEMANTIC-TIER soundness (SemanticTierSoundness): the unified live/reserved ledger's RESERVED verdict is
-- TRUTHFUL. semanticTier g = .reserved decomposes (semanticTier_reserved_imp_both_false) into BOTH classifier
-- Bools false — were the || true the tier if would yield .live, refuted by SemanticTier.noConfusion — feeding
-- the HON-5 static leg (reserved ⟹ untyped by every engine; grown representative + full-16 bundle) and the
-- HON-6 operational leg (reserved ⟹ no root redex). semanticTierReservedSound is the headline: a reserved
-- generator is semantically dead (grown-untyped AND operationally inert). The soundness that makes the honest
-- 203-generator partition a VERIFIED ledger, not an unchecked Bool. Zero-axiom (cases on the || + if_pos + the
-- shipped HON-5/HON-6 legs).
#assert_no_axioms FX1Poly.Typed.semanticTier_reserved_imp_both_false
#assert_no_axioms FX1Poly.Typed.reservedTierOperationallyInert
#assert_no_axioms FX1Poly.Typed.reservedTierUntypedByGrownEngine
#assert_no_axioms FX1Poly.Typed.reservedTierUntypedBySurvivingEngines
#assert_no_axioms FX1Poly.Typed.semanticTierReservedSound
-- ★ CLASSIFIER REFINEMENT (ClassifierRefinement): the full-union static classifier hasSomeTypingRule STRICTLY
-- refines the grown-only untypability decision isUntypableHead. Refinement (union-reserved ⟹ grown-untypable =
-- the HON-5 bridge) + containment (grown-typable ⟹ union-typed, Bool-contrapositive) + STRICT witness
-- (gen_boolTrue: grown-untypable yet union-typed, since the standalone HasTypeDescDataIntro engine types it).
-- The union's typed-set strictly contains the grown-typable set — the standalone data engines genuinely EXTEND
-- typability beyond the grown core, so the honest 203-table classifier is not the grown decision in disguise.
-- Zero-axiom (cite HON-5 bridge + cases/rw/Bool.noConfusion + ⟨rfl, rfl⟩ witness).
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_refines_isUntypableHead
#assert_no_axioms FX1Poly.Typed.grownTypable_imp_unionTyped
#assert_no_axioms FX1Poly.Typed.boolTrue_grownUntypableButUnionTyped
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRuleStrictlyRefinesUntypableHead
-- ★ THE HONESTY-ARC CAPSTONE (GeneratorHonestyLedger): one machine-checked ledger bundling the arc's four
-- pillars over the 203-generator table — SOUNDNESS (reserved ⟹ semantically dead, via semanticTierReservedSound),
-- REFINEMENT (the union classifier strictly refines the grown untypability decision), FAITHFULNESS (a live
-- eliminator computes its exact host fold: boolElim ↝ cond), NON-VACUITY (the two classifier axes are
-- complementary). generatorHonestyLedgerHolds discharges every pillar by its shipped zero-axiom theorem — the
-- single object certifying the table is honestly classified. A build-time #eval prints the capstone status on
-- every default build alongside the HON-4 count overview (GUARANTEE line to its SCOPE line). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.generatorHonestyLedgerHolds
-- ★ NON-RECURSIVE function-branch eliminator-computing canonicity (MatchElimComputingCanonicity), COMPLETING
-- the eliminator-computing-canonicity coverage across all four structural shapes: bool (projection/value),
-- nat+list (recursive function), option+either (non-recursive function, HERE). optionMatch/eitherMatch fire a
-- 1-arg app-chain ι (optionMatch (some v) n s ↝ app s v) — no recursion, but the some/inl/inr branch is a
-- FUNCTION applied to the wrapped value (the content the value-branch bool case lacked). ★
-- optionMatchComputesToValue / eitherMatchComputesToValue = a closed match with a result-valued projection
-- branch + a function branch producing a result value from the wrapped (normal) payload (stepProduces) computes
-- ↝* to a result value, by rcases on the isOptionValue/isEitherValue disjunction (none/some, inl/inr) + the ι
-- step + stepProduces. General over the result predicate. const fold (λ_.natZero → numeral) +
-- ★ id fold (λx.x USES the wrapped payload, returns it → a normal form) discharge stepProduces by one Step.beta.
-- .smoke witnesses prove non-vacuity. Same GTL combined-engine follow-on (#832/#1138) as the recursive
-- eliminators. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.optionMatchComputesToValue
#assert_no_axioms FX1Poly.Typed.eitherMatchComputesToValue
#assert_no_axioms FX1Poly.Typed.optionMatchConstComputesToNumeral
#assert_no_axioms FX1Poly.Typed.eitherMatchConstComputesToNumeral
#assert_no_axioms FX1Poly.Typed.optionMatchIdComputesToValue
#assert_no_axioms FX1Poly.Typed.optionMatchIdComputesToValue.smoke
#assert_no_axioms FX1Poly.Typed.eitherMatchConstComputesToNumeral.smoke
#assert_no_axioms FX1Poly.Typed.Generator.gen_piTyCode_binderShifts_eq
#assert_no_axioms FX1Poly.Typed.Generator.gen_sigmaTyCode_binderShifts_eq
-- GTL-11: the one-child listCode binderShifts = consecutiveShifts 0 1 bridge for the FT data-former branch.
#assert_no_axioms FX1Poly.Typed.Generator.gen_listCode_binderShifts_eq
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecCategory_faithful
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_gen_sigmaTyCode

-- Table-generic root classification (HasTypeDescPiRootGeneric.lean, the cascade-death brick for typed root
-- inversion toward the generic typing layer, polycell.md §3.16.19). subjectRootGenerator HARD-CODES the
-- formation table (enumerates gen_piTyCode/gen_sigmaTyCode, proving typingRuleDescOf=none for all else), so a
-- new formation row breaks it. subjectRootGeneratorGeneric instead concludes "four non-former heads (var/
-- universeCode/lam/app) ∨ ∃ rule, typingRuleDescOf root = some rule" — the genFormationPi arm becomes a
-- one-liner ⟨rule, isFormation⟩ (witness already in the arm), pi/sigma absorbed via the typingRuleDescOf_*
-- table facts, so adding a formation row leaves it intact. cellHasNoTypingWhenRootGenericallyExcluded is the
-- future-proof refutation (data ctors/elims have typingRuleDescOf=none permanently, refuted for all time).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectRootGeneratorGeneric

-- Table-generic root classification — formation engine + closed grown (HasTypeDescPiRootGeneric.lean,
-- completing the generic root-classification family). HasTypeDesc.subjectRootGeneratorGeneric is the
-- FORMATION-engine table-generic root inversion (var/universeCode ∨ ∃ rule, typingRuleDescOf root = some
-- rule); the grown subjectRootGeneratorGeneric's ofFormation arm now DELEGATES to it (removing the last
-- hard-coded gen_piTyCode/gen_sigmaTyCode dependency from grown root inversion). closedSubjectRootGenerator
-- Generic is the empty-context twin (drops the gen_var disjunct via the Fin 0 payload) — the consistency
-- inversion that survives table growth. Together with last fire's subjectRootGeneratorGeneric these make the
-- whole root-classification family table-generic.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGeneratorGeneric
-- not_of_rootGenerator = the decider's default leaf: a cell whose root is neither gen_var nor gen_universeCode
-- nor a formation former (typingRuleDescOf = none) is NOT a formation type. Table-generic via
-- subjectRootGeneratorGeneric — the formation-former case is the single typingRuleDescOf=some disjunct, so a
-- future formation row needs no change here.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.not_of_rootGenerator
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_genElim_computesTypeStably
#assert_no_axioms FX1Poly.Typed.TypingRole
#assert_no_axioms FX1Poly.Typed.typingRoleOf
#assert_no_axioms FX1Poly.Typed.typingRoleOf_formation_of
#assert_no_axioms FX1Poly.Typed.typingRoleOf_intro_of
#assert_no_axioms FX1Poly.Typed.typingRoleOf_elim_of
#assert_no_axioms FX1Poly.Typed.typingRoleOf_isNone_iff
#assert_no_axioms FX1Poly.Typed.typingRoleOf_piTyCode_smoke
#assert_no_axioms FX1Poly.Typed.typingRoleOf_lam_smoke
#assert_no_axioms FX1Poly.Typed.typingRoleOf_app_smoke
#assert_no_axioms FX1Poly.Typed.typingRoleOf_boolTrue_smoke

-- UntypableHeadDecision (GTL-ROLE follow-up): the DECIDABLE cascade-free untypability decision procedure.
-- isUntypableHead is a pure-syntax Bool — decide (typingRoleOf g = none ∧ g ≠ gen_var ∧ g ≠ gen_universeCode)
-- — and isUntypableHead_sound is THE cascade-free untypability theorem: isUntypableHead g = true ⟹ a cell
-- rooted at g has no grown typing (of_decide_eq_true → cellUntypedWhenRolelessAndNonBespoke). A new data
-- former's untypability becomes a rfl-check, never a new proof. The witnesses show the procedure ACCEPTS every
-- untyped-head shape (boolTrue constructor / fst projection / natElim recursor / emptyCode deferred type-code,
-- all = true by rfl) and REJECTS the typed heads (var/universeCode bespoke + lam table-driven, all = false);
-- natElimCellUntypedViaDecision rederives the bespoke untyping through the single decidable route. All
-- zero-axiom (decide over flat-enum DecidableEq + of_decide_eq_true, NOT decide_eq_true_eq which pulls propext).
#assert_no_axioms FX1Poly.Typed.isUntypableHead
#assert_no_axioms FX1Poly.Typed.isUntypableHead_sound
#assert_no_axioms FX1Poly.Typed.isUntypableHead_boolTrue
#assert_no_axioms FX1Poly.Typed.isUntypableHead_fst
#assert_no_axioms FX1Poly.Typed.isUntypableHead_natElim
#assert_no_axioms FX1Poly.Typed.isUntypableHead_emptyCode
#assert_no_axioms FX1Poly.Typed.isUntypableHead_var_false
#assert_no_axioms FX1Poly.Typed.isUntypableHead_universeCode_false
#assert_no_axioms FX1Poly.Typed.isUntypableHead_lam_false

-- TypingHeadKindClassifier (GTL-ROLE capstone): the COMPLETE decidable 6-way head-kind taxonomy. TypingHeadKind
-- (formation/introduction/elimination/bespokeVariable/bespokeUniverse/untypable) + typingHeadKindOf totally
-- partition all 196 generators (bespoke heads split first since they are roleless yet typed, then dispatch on
-- typingRoleOf). The six headKind_* rfl witnesses exhibit one head of each kind. headKind_untypable_imp/of_
-- isUntypableHead characterize the untypable kind as EXACTLY #987's isUntypableHead (both directions);
-- headKind_untypable_sound is the engine tie (untypable kind ⟹ no grown typing via isUntypableHead_sound);
-- headKind_bespoke{Variable,Universe}_imp pin the two roleless-yet-typed heads to gen_var / gen_universeCode.
-- All zero-axiom (if/match + rfl; of_decide_eq_true/decide_eq_true bridging isUntypableHead; by_cases over the
-- head guards + cases on the typingRoleOf Option and TypingHeadKind ctor mismatches).
#assert_no_axioms FX1Poly.Typed.TypingHeadKind
#assert_no_axioms FX1Poly.Typed.typingHeadKindOf
#assert_no_axioms FX1Poly.Typed.headKind_piTyCode
#assert_no_axioms FX1Poly.Typed.headKind_lam
#assert_no_axioms FX1Poly.Typed.headKind_app
#assert_no_axioms FX1Poly.Typed.headKind_var
#assert_no_axioms FX1Poly.Typed.headKind_universeCode
#assert_no_axioms FX1Poly.Typed.headKind_boolTrue
#assert_no_axioms FX1Poly.Typed.headKind_untypable_imp_isUntypableHead
#assert_no_axioms FX1Poly.Typed.headKind_untypable_of_isUntypableHead
#assert_no_axioms FX1Poly.Typed.headKind_untypable_sound
#assert_no_axioms FX1Poly.Typed.headKind_bespokeVariable_imp
#assert_no_axioms FX1Poly.Typed.headKind_bespokeUniverse_imp

-- TypedBySomeEngine (HON-1): the honest TOTAL static-typing classifier. hasSomeTypingRule consults EVERY typing
-- engine's selector (grown trio + flat + base + dataIntroNullary + the 16 standalone intro/elim heads + the 2
-- bespoke heads), so it computes the honest UNION — unlike typingRoleOf/typingHeadKindOf/isUntypableHead, which
-- are grown-engine-only and brand genuinely-typed data heads (gen_boolTrue/gen_fst) "untypable", conflating them
-- with reserved names (gen_hilbertSpace). The isUntypableHead_overclaims_* theorems pin that overclaim
-- (untypable=true ∧ hasSomeTypingRule=true), and classifiersAgree_hilbertSpace shows the two agree on a genuinely
-- reserved head. All zero-axiom (Option.isSome over pure-syntax selectors + decide over DecidableEq Generator,
-- NO wildcard match; every witness rfl / ⟨rfl,rfl⟩).
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_piTyCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_arrowCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_boolCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_boolTrue
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_natZero
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_fst
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_lam
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_var
-- NATIVE-11: interval heads stay classified-true via the TABLE selectors after the bespoke decides were
-- dropped (intervalCode via baseTypeRuleDescOf, interval0/1 via dataIntroNullaryRuleDescOf); bridgeCode is
-- the one cubical head that REMAINS a decide (its term-indexed former table lands at NATIVE-12).  Each is a
-- load-bearing `rfl` pin: it would fail to compute `true` had the −3 collapse mis-subsumed a head.
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_intervalCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_interval0
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_interval1
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_bridgeCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_hilbertSpace
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_natElim
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_idCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_quantumGate
#assert_no_axioms FX1Poly.Typed.isUntypableHead_overclaims_boolTrue
#assert_no_axioms FX1Poly.Typed.isUntypableHead_overclaims_fst
#assert_no_axioms FX1Poly.Typed.classifiersAgree_hilbertSpace

-- GeneratorSemanticTier (HON-3): the unified live/reserved ledger. semanticTier g = live iff hasSomeTypingRule g
-- (HON-1 static axis) OR g.hasRedexHead (HON-2 operational axis); else reserved. The two axes are genuinely
-- complementary: natElim_reducesButUntyped_stillLive (natElim REDUCES yet is statically reserved — caught by the
-- operational axis) + boolTrue_typedNotRedex_stillLive (a typed value, not a redex head — caught by the static
-- axis) prove neither axis alone suffices. semanticTier_discriminates is the non-vacuity guard (noConfusion, NOT
-- decide-on-Ne). Reserved-soundness (reserved ⟹ untyped ∧ inert) is HON-7. Zero-axiom (if-over-Bool || ; rfl
-- witnesses; rw + SemanticTier.noConfusion).
#assert_no_axioms FX1Poly.Typed.semanticTier
#assert_no_axioms FX1Poly.Typed.semanticTier_app
#assert_no_axioms FX1Poly.Typed.semanticTier_boolTrue
#assert_no_axioms FX1Poly.Typed.semanticTier_natElim
#assert_no_axioms FX1Poly.Typed.semanticTier_piTyCode
#assert_no_axioms FX1Poly.Typed.semanticTier_hilbertSpace
#assert_no_axioms FX1Poly.Typed.semanticTier_idCode
#assert_no_axioms FX1Poly.Typed.semanticTier_quantumGate
#assert_no_axioms FX1Poly.Typed.natElim_reducesButUntyped_stillLive
#assert_no_axioms FX1Poly.Typed.boolTrue_typedNotRedex_stillLive
#assert_no_axioms FX1Poly.Typed.semanticTier_discriminates

-- GeneratorAdmissionSplit (M30-Z1): the explicit syntactic-vs-semantic admission split, both DECIDABLE.
-- Syntactic = a SupportedGenerator row exists (TOTAL under fxProfile, syntacticallyAdmissible_total);
-- semantic = typed-or-reduces, exactly the HON-3 tier verdict (isSemanticallyAdmissible_iff_tierLive).
-- The split is STRICT (admissionSplit_isStrict: gen_hilbertSpace is a legal cell head yet semantically
-- dead) and refining (semanticallyAdmissible_implies_syntactically), with computable type-level admission
-- witnesses on both notions. Zero-axiom (table lookups; rfl witnesses; if_neg + noConfusion tier bridge;
-- Bool.decEq Decidable instances).
#assert_no_axioms FX1Poly.Typed.isSyntacticallyAdmissible
#assert_no_axioms FX1Poly.Typed.isSemanticallyAdmissible
#assert_no_axioms FX1Poly.Typed.SyntacticallyAdmissible
#assert_no_axioms FX1Poly.Typed.SemanticallyAdmissible
#assert_no_axioms FX1Poly.Typed.syntacticallyAdmissible_total
#assert_no_axioms FX1Poly.Typed.admissionWitnessOfSyntactic
#assert_no_axioms FX1Poly.Typed.semanticallyAdmissible_implies_syntactically
#assert_no_axioms FX1Poly.Typed.admissionWitnessOfSemantic
#assert_no_axioms FX1Poly.Typed.isSemanticallyAdmissible_iff_tierLive
#assert_no_axioms FX1Poly.Typed.app_isSemanticallyAdmissible
#assert_no_axioms FX1Poly.Typed.natElim_isSemanticallyAdmissible
#assert_no_axioms FX1Poly.Typed.idJ_isSemanticallyAdmissible
#assert_no_axioms FX1Poly.Typed.hilbertSpace_isSemanticallyAdmissible_false
#assert_no_axioms FX1Poly.Typed.admissionSplit_isStrict

-- GeneratorHonestyOverview (HON-4): the build-time honesty dashboard. allGenerators enumerates all 203 via the
-- total tag-inverse Generator.fromTag over 0..202; the four count defs fold the HON-1/HON-2/HON-3 classifiers
-- over it (statically-typed 34 / operational redex-heads 11 / semantically-live 38 / RESERVED 159). A #eval in
-- the file prints the dashboard on every build that re-elaborates it — the forcing function keeping the gap
-- visible. The s!-interpolation lives in the #eval COMMAND (not a gated decl), so its toString-propext never
-- touches a kernel theorem; the count DEFS below are pure List.filter/length over the zero-axiom classifiers.
#assert_no_axioms FX1Poly.Typed.allGenerators
#assert_no_axioms FX1Poly.Typed.typedGeneratorCount
#assert_no_axioms FX1Poly.Typed.redexHeadGeneratorCount
#assert_no_axioms FX1Poly.Typed.liveGeneratorCount
#assert_no_axioms FX1Poly.Typed.reservedGeneratorCount

-- CertifiedWordReductionTermination (SN-131): Leg-3 word-rewrite termination on the CERTIFIED fragment.
-- certifiedReductionInducesWordChain is the bridge (a Step sequence's toCode images form an fxStepSystem
-- word-rewrite chain via Step.toWordRewrite). typedRootWordReductionTerminates is the headline — a reduction
-- sequence rooted at a WELL-TYPED term cannot be infinite (notStronglyNormalizing_of_infiniteReduction +
-- stronglyNormalizingOfWfContextDesc / SN-043), so the induced certified word chain terminates — consuming
-- ROOT SN only, NO subject reduction (GrownCtxConv-5-free). untypedWordReductionDiverges is the necessity: the FULL
-- word system diverges on an UNTYPED word (growingDivergentTerm.toCode), whose source is non-SN — the
-- word-layer mirror of SN-NECESSITY (#950). All zero-axiom (Step.toWordRewrite pointwise; apply + rw + the
-- SN-043 witness; the concrete growing-divergence sequence images).
#assert_no_axioms FX1Poly.Typed.certifiedReductionInducesWordChain
#assert_no_axioms FX1Poly.Typed.typedRootWordReductionTerminates
#assert_no_axioms FX1Poly.Typed.untypedWordReductionDiverges

-- CertifiedWordReductionConfluence (SN-132): Leg-3 word-rewrite CONFLUENCE on the certified fragment, the
-- companion to SN-131's termination. certifiedWordLocalConfluence is the literal SN-132 ask — two single
-- Steps from a common term have toCode-images that JOIN as fxStepSystem word reductions, via the term cd_lemma
-- local join (StepStar.localJoin_of_cdLemma) lifted through StepStar.toWordRewrites (NO string-rewriting
-- critical-pair analysis — the full word system isn't even terminating per SN-131). certifiedWordConfluence is
-- the GLOBAL upgrade on the certified fragment: two StepStar reductions from a WELL-TYPED root join, combining
-- the SN-131 ingredient (typed SN / stronglyNormalizingOfWfContextDesc, SN-043) with term-layer Newman
-- (StepStar.confluence_of_localJoin_and_accessible) lifted through toWordRewrites — so the certified fragment
-- is terminating (SN-131) AND confluent (here), Newman's two ingredients, reflected to the word layer; needs
-- the ROOT typed only (GrownCtxConv-5-free). All zero-axiom (obtain the term join, toWordRewrites each leg).
#assert_no_axioms FX1Poly.Typed.certifiedWordLocalConfluence
#assert_no_axioms FX1Poly.Typed.certifiedWordConfluence

-- §27.3 Layer-1 known-unsoundness corpus: every cataloged §27.2 type-theory bug is a permanent rejection
-- test (or an honest pending-ledger entry).  GENUINELY-NEW content: universe-typing acyclicity — the
-- relation `Type@a : Type@b` is exactly the successor function (`grownUniverseTypingForcesSuccessor`),
-- hence has no Girard 2-cycle (`grownUniverseTypingHasNoTwoCycle`), strengthening the shipped length-1
-- no-`Type:Type`.  The catalog (`KnownTypeTheoryBug` + `dimension`/`literatureSource`/`isEncodableNow`) is
-- machine-checked data; the re-exported witnesses (`corpusRejectsAtkeyBrokenLam` / `…NaiveGradeCheck`) and
-- the `…_isEncodableNow` / `…_isPending` ledger facts pin which bugs are rejected vs await their dimension.
#assert_no_axioms FX1Poly.Typed.grownUniverseTypingForcesSuccessor
#assert_no_axioms FX1Poly.Typed.grownUniverseTypingHasNoTwoCycle
#assert_no_axioms FX1Poly.Typed.corpusRejectsTypeInType
#assert_no_axioms FX1Poly.Typed.KnownTypeTheoryBug
