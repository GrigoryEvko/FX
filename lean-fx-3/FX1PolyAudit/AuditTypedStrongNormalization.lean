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

/-! # FX1PolyAudit/AuditTypedStrongNormalization — typed-layer zero-axiom gates: strong normalization and the accessibility assemblies
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/


/-! ### Strong normalization and typed conversion for the description formation engine.
    Native: subject SN (`subjectStronglyNormalizingNative`, the public `isStronglyNormalizing` delegating to it),
    type SN (`IsTypeDesc.isStronglyNormalizing` — the `IsTypeDesc` witness's subject IS the classifier), and
    typed-middle transitivity (`Conv.trans_of_hasTypeDescMiddle` — the unconditional raw `Conv.trans`, its
    `IsTypeDesc` premise vacuous).  The `WfContext`-validity-bound classifier-SN package
    (`classifierStronglyNormalizing` / `subjectAndClassifier*`) is scoped to the formation engine; no grown
    reducibility claim.  Cascade-free: `formerCellStronglyNormalizingOfChildren` routes through the generic
    `former_step_inv` + the N-child accessibility substrate (`StepChildrenSuccessor` /
    `accStepChildrenSuccessor_cons` / `accStepChildrenSuccessor_of_allStronglyNormalizing` /
    `formerCell_isStronglyNormalizing_of_accChildren`) rather than a per-former `by_cases isPi/isSigma` — so a new
    ≥1-child formation row extends it with no change, mirroring the cascade-free formation `subjectReduction`. -/
#assert_no_axioms FX1Poly.Core.RawTermChildren.allStronglyNormalizing
#assert_no_axioms FX1Poly.Core.accStepChildrenSuccessor_of_allStronglyNormalizing
#assert_no_axioms FX1Poly.Core.formerCell_isStronglyNormalizing_of_accChildren
#assert_no_axioms FX1Poly.Typed.formerCellStronglyNormalizingOfChildren
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectStronglyNormalizingNative
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectAndClassifierStronglyNormalizing
-- FORMATION CLASSIFIER-SN over WfContextDesc (WfContextDescStronglyNormalizing.lean): the classifier of a
-- HasTypeDesc-typed cell is strongly normalizing, routed through classifierIsTypeDescNative then
-- IsTypeDesc.isStronglyNormalizing. A consumer of the native validity target.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierStronglyNormalizingNative
-- SN-026 (cross-check route status, documented-as-deferred per its DONE): the Kripke / all-levels route
-- (HasTypeDescPiAllLevelFundamentalTheorem = HasTypeDescPi → FundamentalConclusionAtAll, the ∀-level
-- ReducibleEnvAtAllLevels shape) is the SECOND route to the unconditional FT, parallel to the SN-022/023
-- ValidTyping bridge. Its machinery is shipped + gated: the interface + its corollaries (gated below), the
-- CONDITIONAL all-levels FT fundamentalAtAllFromFormation (gated here) + allLevelFundamentalTheoremFromFormationVector
-- (gated below), and the all-levels leaf arms (FundamentalAtAllLeafArms: var/conv/piIntro). Both routes bottom out
-- at the SAME formation-FT obstruction (the var + ∀-aboveLevel former-domain content of SN-022..025); an
-- UNCONDITIONAL HasTypeDescPiAllLevelFundamentalTheorem value therefore awaits that shared discharge. Per SN-005
-- the ValidTyping bridge is PRIMARY, so this Kripke route is kept as the CROSS-CHECK and its unconditional value
-- is completed together with the primary assembly (SN-027) — not independently duplicated here.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromFormation

-- ALL-LEVEL FORMATION FT, var/conv/universeFormation discharged, genFormation factored (#496 progress).
-- The downstream SN chain (the FromFormation block above) is conditional on the formation engine HasTypeDesc
-- satisfying the FT.  This peels the three NON-former formation arms off that obligation: over the all-level
-- environment, var is off-by-one-free (fundamentalVarAtAll), conv/universeFormation dispatch to their AtAll
-- arms; the genFormation former arm (whose telescope binder obligation = the recursive
-- codomain-under-argument premise) is the sole explicit hypothesis.  Reduces the formation FT to the
-- genFormation former arm alone — the formation-engine analog of fundamentalVectorFromFormation.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.fundamentalAtAllFromGenFormation
-- FIRST UNCONDITIONAL SN results via the level-indexed FT: concrete closed terms whose FT conclusion is built
-- directly from the shipped arms at the empty context (no recursor), discharged to plain IsStronglyNormalizing
-- by the closed-SN handoff. End-to-end validation that the arms + handoff compose into hypothesis-free SN.
#assert_no_axioms FX1Poly.Typed.universeCode_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.closedPiBetweenUniverses_stronglyNormalizing
-- The closed identity λx.x : Π Type@e. Type@e is unconditionally SN — first such result with a LAMBDA +
-- BOUND VARIABLE, composing piIntro + var arms end-to-end (the heart of the FT). Fin-1 index via ⟨0,_⟩.
#assert_no_axioms FX1Poly.Typed.closedIdentityOnUniverse_stronglyNormalizing
-- The closed β-redex (λx.x) Type@e is unconditionally SN — first such result with an APPLICATION, composing
-- piElim over (piIntro + var) and universeFormation; exercises the subst0 in piElim's conclusion end-to-end.
#assert_no_axioms FX1Poly.Typed.closedIdentityApplication_stronglyNormalizing
-- Corpus extension: the Σ-formation arm end-to-end (first unconditional SN exercising fundamentalSigma-
-- FormationLevelIndexed — the Σ twin of closedPiBetweenUniverses, non-vacuous + hypothesis-free), plus the
-- argument-DISCARDING β path: the constant λx.Type@0 (var-free piIntro body) and its erasing application
-- (λx.Type@0) Type@e (piElim where subst0 discards the argument) — the complement of the substituting identity.
#assert_no_axioms FX1Poly.Typed.closedSigmaBetweenUniverses_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.closedConstantLambda_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.closedConstantApplication_stronglyNormalizing
-- NESTED formers: a former whose CHILD is itself a former — the Π/Σ formation arms COMPOSE end-to-end into
-- hypothesis-free SN (the inner arm supplies the outer arm's binder-extended codomain premise). Π-over-Σ,
-- Σ-over-Π (the dual), and Π-over-Π (the binary function type, deepest nesting).
#assert_no_axioms FX1Poly.Typed.closedNestedPiOverSigma_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.closedNestedSigmaOverPi_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.closedNestedPiOverPi_stronglyNormalizing
-- The SN-043 TYPING HYPOTHESIS IS ESSENTIAL (UntypedOmegaNotStronglyNormalizing): the closed smokes above
-- show every well-typed closed term is SN; this is the converse witness that typing is doing real work. The
-- raw Ω = (λx.x x)(λx.x x) is a closed RAW term that β-steps to itself (omegaCombinator_betaSelfStep), hence
-- is NOT SN (omegaCombinator_notStronglyNormalizing, via accessibleElementNotSelfRelated: a self-looping
-- element cannot be Acc). Ω is untypable, so SN-043 rightly excludes it. The headline records the sharper
-- non-closure fact: λx.x x IS SN (selfApplicationLambda_stronglyNormalizing — a closed normal form) yet its
-- self-application is not, so SN is NOT preserved under application — the β-redex side condition discharged by
-- the reducibility argument is load-bearing, not decoration.
#assert_no_axioms FX1Poly.Typed.accessibleElementNotSelfRelated
#assert_no_axioms FX1Poly.Typed.selfApplicationLambda_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.applicationOfStronglyNormalizingNotAlwaysStronglyNormalizing
-- WEAK ≠ STRONG normalization in the raw calculus (WeaklyNormalizingNotStronglyNormalizing): sharper than Ω
-- above (Ω has NO normalizing path; this term DOES). The Barendregt separating example (λx.Type@0) Ω has a
-- terminating β-path to the normal form Type@0 (betaReachesBody — subst0 is identity on the nullary universe-
-- code body by computation, no cancellation lemma) AND a divergent path looping in the discarded Ω argument
-- (argumentSelfLoop, the uniform Step.cong rule stepping the second app child via StepChildren.there, fed the
-- Step Ω Ω self-step). So weakly-normalizing does NOT imply strongly-normalizing — the headline. This is WHY
-- SN-043 proves STRONG normalization: weak normalization alone permits the adversarial "reduce the discarded
-- argument forever" strategy, which typing must (and does) rule out.
#assert_no_axioms FX1Poly.Typed.discardingApplicationOnOmega_betaReachesBody
#assert_no_axioms FX1Poly.Typed.discardingApplicationOnOmega_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.weaklyNormalizingDoesNotImplyStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.identityOnUniverse_stronglyNormalizing
-- The ELIMINATION (application) form + concrete subject reduction (TypedLambdaDerivations, extending the
-- piIntro derivations above): identityApplicationOnUniverseCode applies the identity at Type@(e+1) to the
-- universe code Type@e (which inhabits Type@(e+1) by universeFormation — no data-code machinery), typed by
-- piElim; the result-type subst0 Type@(e+1) Type@e is defeq Type@(e+1) (constant codomain ignores the arg).
-- identityApplication_subjectReduction: the redex β-reduces to its argument Type@e and BOTH redex and reduct
-- type at the SAME Type@(e+1) — concrete subject reduction on an honest piElim derivation.
#assert_no_axioms FX1Poly.Typed.identityApplicationOnUniverseCode_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.identityApplicationOnUniverseCode_betaReducesToArgument
#assert_no_axioms FX1Poly.Typed.polymorphicIdentity_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiation_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityTwoArg_stronglyNormalizing
-- Σ-FORMATION in the typing engine: the generic genFormationPi arm types a dependent PAIR type, not
-- only Π. The reducibility layer already had Σ formation (fundamentalSigmaFormationLevelIndexed); these
-- are the first in the TYPING judgment (HasTypeDescPi). genFormationPiTypesBothPiAndSigmaFormers bundles
-- Π and Σ at one identical context+classifier — the conjuncts differ only in the head former, i.e. only
-- in the Generator argument to the same arm: the cascade-free typing thesis, a former is a table row.
#assert_no_axioms FX1Poly.Typed.dependentPairTypeOverTypeVariable_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.closedDependentPairType_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.closedDependentPairType_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.ValidTyping.fundamental
-- SN-022 (LevelingBridge.lean): the leveling bridge HasTypeDescPi → ∃ contextLevels subjectLevel, ValidTyping …
-- — var/conv/universeFormation arms. var + universeFormation are UNCONDITIONAL leaves (direct ValidTyping ctor
-- applications; var concludes at subjectLevel := contextLevels index, the SN-024 off-by-one dodge); conv is the
-- coordinated-input wrapper (cross-sub-derivation level coordination is the inductive assembly's job, SN-027).
-- Composed with the PROVEN ValidTyping.fundamental ⟹ unconditional dependent reducibility/SN. Binder/former
-- arms = SN-023.
#assert_no_axioms FX1Poly.Typed.validTypingBridgeVar
-- SN-043 endgame reframe (LevelingBridge.lean): hasTypeDescPiStronglyNormalizingFromTotalBridge — the SN twin of
-- hasTypeDescPiReducibleFromTotalBridge, composing the total bridge with the UNCONDITIONAL
-- ValidTyping.substStronglyNormalizing. Operationalizes the finding that ValidTyping.fundamental is unconditional
-- (composite-domain Π handled by its env-extension codomain IH), so SN-043's ONLY residual is the leveling bridge
-- (totalBridge / #662) — NOT the fuel gate HasPositiveMemberExtension… (#672), which is OFF this path.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPiStronglyNormalizingFromTotalBridge
-- SN-043 headline (LevelingBridge.lean): hasTypeDescPiClosedStronglyNormalizingFromEmptyBridge — the LITERAL
-- closed SN-043 shape HasTypeDescPi .empty t T → SN t, modulo the empty-context leveling bridge. Composes with
-- the unconditional ValidTyping.closedStronglyNormalizing; uses the empty bridge (producing emptyLevelVector
-- directly) to stay coercion-free (no funext over Fin 0). The closed plain-SN specialization of the open form.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPiClosedStronglyNormalizingFromEmptyBridge
-- SN-027 piElim diagnosis (read-validated against fundamentalPiElimLevelIndexed + applicationUnderSubst): the
-- piElim arm runs at a UNIFORM subjectLevel — function (: Π), argument (: domain), and result are ALL at one
-- level (applicationUnderSubst closes at any COMMON level). The per-arm block validTypingBridgePiElim (SN-023)
-- already discharges it given function+argument at a common level, so piElim needs NO further per-arm lemma; the
-- residual is purely the induction's LEVEL-ALIGNMENT of function vs argument. That alignment is clean for
-- universe-code-classified members (type codes: membership in Type@e is L-independent in its decoded-at-denote-e
-- part) but case-dependent for Π-classified function TERMS (Π-membership depends on the level). So the remaining
-- SN-027 work is the single ASSEMBLY theorem: the HasTypeDescPi induction threading contextLevels with the refined
-- motive (∀-level type-code subjects, single-level terms) + the member-level alignment for piElim + the
-- ofFormation/HasTypeDesc inversion — all per-arm ingredients (conv, type-code flexibility, piElim block) now in hand.
-- SN-027 update (infra located, prior pessimism CORRECTED): the term arms' member-level alignment is NOT
-- blocked on missing math — the reducibility layer already has a rich, gated IsReducibleMemberAtAllPositiveLevels
-- framework (.atLevel / .headExpand / .universeCode_iff / .ofUniverseMember{NonPiNonUniverse,UniverseCode,
-- PiNeutralDomain}Argument / .ofNeutralClassifier / .piTypeMemberExtension / .castAlongConvOfAllLevels +
-- IsReducibleMemberAt.extendsToAllPositiveAtUniverseCodeOfLowerTypeExtendsToAllLevels). ValidTyping itself has NO
-- syntactic level subsumption (var pins its level), so the assembly routes the TERM arms (piElim/piIntro) through
-- this all-levels MEMBER machinery (reducibility layer) rather than through syntactic ValidTyping re-leveling.
-- NET: the unconditional assembly is tractable WIRING (refined-motive HasTypeDescPi induction over existing infra),
-- not infra-blocked — the focused remaining work of SN-027.
#assert_no_axioms FX1Poly.Typed.ValidTyping.closedStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.validTyping_universeCode_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.validTyping_identity_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.validTyping_piBetweenUniverses_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.validTyping_sigmaBetweenUniverses_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.ValidTyping.substStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.validTyping_openVariable_substStronglyNormalizing
-- PER-ARM RECURSOR NON-VACUITY CORPUS (ValidTyping.lean): completing piElim + conv. betaRedex = a closed
-- β-redex (λx.x)(Type@e) SN through the piElim arm (genuinely reducing); convRefl = a universe code re-typed
-- through the conv arm (reflexive conversion — closed ValidTyping terms never have a redex type, so the arm's
-- level coordination subjectLevel/subjectLevel+1 + tarskiDecode + castAlongConv is exercised but the conversion
-- is refl). All 7 recursor arms now have a non-vacuity SN witness.
#assert_no_axioms FX1Poly.Typed.validTyping_betaRedex_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.validTyping_convRefl_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.fundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.substitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.closedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toReducibilityAndStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.hasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem_iff_typeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValueReducibilityAndStrongNormalizationTheoremFromFormationVectorAndAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValueReducibilityAndStrongNormalizationTheoremFromFormationVectorAndPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
-- FLAT-ENGINE STRONG NORMALIZATION (#935, next increment): the flat twin of
-- HasTypeDesc.subjectStronglyNormalizingNative. flatFormerCellStronglyNormalizingOfChildren reuses the GENERIC
-- Core accessibility substrate (formerCell_isStronglyNormalizing_of_accChildren) with the firing-45 congruence-
-- only inversion swapped in; FlatDescTelescope.childrenStronglyNormalizing is a plain (non-mutual) structural
-- recursion calling HasTypeDesc.subjectStronglyNormalizingNative on each head; HasTypeDescFlat.subjectStronglyNormalizing
-- is the headline; the five closed witnesses show each flat former TYPES and is SN.

-- SN-006 (contingency spec, fallback-only): the Adjedj derivation-indexed LogRel.  Key finding: `HasTypeDescPi`
-- is Prop-valued, so a Nat derivation-size is BLOCKED (no large elim from Prop); the fallback is Prop-motive
-- structural recursion on the derivation (same scheme as ValidTyping.fundamental, impredicativity-robust).
-- The marker is the fallback's deferred TARGET statement (= the primary SN goal), a checked Prop, no obligation.
#assert_no_axioms FX1Poly.Typed.DerivationIndexedStrongNormalizationFallback
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.stronglyNormalizing
-- The full CR3 neutral leaf (generalizes containsVariable past the vacuous variable case): a STRONGLY-
-- NORMALIZING NEUTRAL term is a member of every canonical-forms candidate, by well-founded recursion on its SN
-- accessibility (reducts stay neutral via closedUnderStep, are SN-smaller, hence members by IH; neutralExpansion
-- lifts). The reducibility leaf any neutral-eliminator (stuck app/fst/boolElim over a neutral head) member
-- argument consumes; isValue-agnostic.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral
-- The GENERIC head-expansion-closed data Tait candidate (dataTaitCandidate isValue), generalizing
-- emptyTaitCandidate from the empty value set to ANY data value predicate ("SN AND every reachable normal
-- form is a value or neutral").  It is a reducibility candidate (CR1/CR2/CR3) and head-expansion-closed
-- (so it serves as a Π codomain candidate across the fundamental theorem) for every isValue; a CLOSED
-- member reduces to a VALUE (closedReducesToValue) — the candidate-bridge-ready data-canonicity payload
-- each data type code (bool/nat/…) instantiates exactly as emptyTypeCell instantiates emptyTaitCandidate.
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityRedexStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingClosed

-- CHURCH-ROSSER + NORMAL-FORM UNIQUENESS for simply-typed terms: the SN result fed the per-term Newman bridge
-- (`confluence_of_localJoin_and_accessible`) gives confluence (`reductsJoinUnderSubst`), and `eq_of_noStep`
-- gives normal-form uniqueness (`normalFormUnique{UnderSubst,Closed}`) — the foundation for deciding conversion
-- on the simply-typed fragment.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reductsJoinUnderSubst
#assert_no_axioms FX1Poly.Typed.identityStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.arrowIdentityIsSimplyTyped
#assert_no_axioms FX1Poly.Typed.arrowIdentityStronglyNormalizing

-- PRODUCTIVE REDEX EXTRACTION (toward weak normalization, #267/#374): the converse of
-- `isStepNormalForm_blocks_step` per root-redex shape — a fired root check yields an actual `Step`, witness
-- produced.  This batch covers the FUNCTION (beta) and PRODUCT (fst/snd) redexes (+ the shallow source
-- inversions); inductive-eliminator iotas are deferred to subsequent bricks.
#assert_no_axioms FX1Poly.Core.isLamSource_eq_lam
#assert_no_axioms FX1Poly.Core.hasAppBetaRoot_exists_step
#assert_no_axioms FX1Poly.Core.isPairSource_eq_pair
#assert_no_axioms FX1Poly.Core.hasPairProjectionIotaRoot_exists_step_fst
#assert_no_axioms FX1Poly.Core.hasPairProjectionIotaRoot_exists_step_snd

-- Redex-extraction bricks: BOOLEAN (boolElim) + NATURAL (natElim/natRec).  The two-constructor eliminators'
-- disjunctive root check is split propext-free (`cases h : isXxxSource`, NOT `rw [Bool.or_eq_true]`).
#assert_no_axioms FX1Poly.Core.isBoolTrueSource_eq_boolTrue
#assert_no_axioms FX1Poly.Core.isBoolFalseSource_eq_boolFalse
#assert_no_axioms FX1Poly.Core.hasBoolElimIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.isNatZeroSource_eq_natZero
#assert_no_axioms FX1Poly.Core.isNatSuccSource_eq_natSucc
#assert_no_axioms FX1Poly.Core.hasNatElimIotaRoot_exists_step_natElim
#assert_no_axioms FX1Poly.Core.hasNatElimIotaRoot_exists_step_natRec

-- Redex-extraction bricks completing the per-redex layer: LIST + OPTION + EITHER + IDENTITY eliminators.
-- listCons is the first BINARY-constructor inversion; eitherMatch has two unary scrutinees; idJ/idStrictRec
-- have a single (non-disjunctive) isReflSource check on the witness child.  With every root-redex shape
-- covered, `hasRootStepSource → ∃ step` is now assemblable.
#assert_no_axioms FX1Poly.Core.isListNilSource_eq_listNil
#assert_no_axioms FX1Poly.Core.isListConsSource_eq_listCons
#assert_no_axioms FX1Poly.Core.isOptionNoneSource_eq_optionNone
#assert_no_axioms FX1Poly.Core.isOptionSomeSource_eq_optionSome
#assert_no_axioms FX1Poly.Core.isEitherInlSource_eq_eitherInl
#assert_no_axioms FX1Poly.Core.isEitherInrSource_eq_eitherInr
#assert_no_axioms FX1Poly.Core.isReflSource_eq_refl
#assert_no_axioms FX1Poly.Core.hasListElimIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.hasOptionMatchIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.hasEitherMatchIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.hasIdElimIotaRoot_exists_step_idJ
#assert_no_axioms FX1Poly.Core.hasIdElimIotaRoot_exists_step_idStrictRec
#assert_no_axioms FX1Poly.Core.Conv.decidableOfStronglyNormalizing
-- Conv.iff_normalize_eq_of_isStronglyNormalizing: the SEMANTIC NbE soundness+completeness iff — two SN terms
-- convert IFF RawTerm.normalize maps them to the SAME term (the explicit biconditional decidableOfStronglyNorm-
-- alizing is decidable_of_iff over). Sharper than iff_normalForms_eq (NFs as opaque args): RHS is a literal
-- RawTerm equality via the actual normalizer.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalize_eq_of_isStronglyNormalizing

-- SN REFLECTED BY SUBSTITUTION: SN of `subst σ term` ⇒ SN of bare `term` (Acc reflected along `subst σ` via
-- Step.subst + Subrelation.accessible ∘ InvImage.accessible).  This pulls the FT's SN-of-substituted back to
-- SN-of-bare, removing the closing-substitution wart: decidableOfSimplyTypedBareClosed decides conversion of
-- the BARE closed terms themselves — the cleanest "simply-typed fragment has decidable conversion".
#assert_no_axioms FX1Poly.Core.StepStar.stronglyNormalizing_of_subst
#assert_no_axioms FX1Poly.Typed.emptyClosingSubst

-- simplyTypedBareClosedStronglyNormalizing (Milestone A0 simply-typed floor, SN half): the standalone reusable
-- form of "a closed simply-typed term is strongly normalizing". The simply-typed FT's stronglyNormalizingClosed
-- reflected to the bare term
-- via stronglyNormalizing_of_subst. With decidableOfSimplyTypedBareClosed (the decidable-Conv half) this names
-- the UNCONDITIONAL defensible-kernel floor: the simply-typed fragment has SN PROVEN (not assumed), so typing
-- alone decides conversion. Honest qualifier boundary: simply-typed fragment ONLY; broader fragments need SN-043.
#assert_no_axioms FX1Poly.Typed.simplyTypedBareClosedStronglyNormalizing
-- simplyTypedDefensibleKernel (Milestone A0 bundle witness, #666/#557): the named SimplyTypedDefensibleKernel
-- structure (SN proven + Conv decidable) witnessed by the shipped unconditional theorems
-- (simplyTypedBareClosedStronglyNormalizing + Conv.decidableOfSimplyTypedBareClosed). The formal declaration of
-- Milestone A0 over the simply-typed fragment, NOT gated on SN-043 (no SN hypothesis carried). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.simplyTypedDefensibleKernel

-- CANONICAL NORMAL FORM for closed simply-typed terms — the NORMALIZE companion to the bare-closed DECIDE.
-- stronglyNormalizingBare: bare SN (the sole use site of stronglyNormalizing_of_subst); normalForm: the
-- computable RawTerm 0; conv_normalForm / normalForm_isStepNormalForm: term ↝* its NF and NF is normal;
-- normalForm_eq_self_of_isStepNormalForm: no spurious rewriting on a normal input; conv_iff_normalForm_eq:
-- two terms convert IFF their NFs coincide (the canonical NF is a complete conversion invariant — the
-- explicit characterization behind decidableOfSimplyTypedBareClosed).
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingBare

-- WEAK NORMALIZATION: a strongly-normalizing term reaches a structural normal form, with the reduction
-- chain produced by descending the `Acc StepSuccessor` witness and extracting a real Step at every
-- non-normal node.  The StepStar-existence half of normalization (uniqueness comes from confluence) —
-- the strongly-normalizing-fragment door to decidable Conv (#267) and the WHNF normalizer (#374).
#assert_no_axioms FX1Poly.Core.exists_normalForm_of_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.exists_unique_normalForm_of_isStronglyNormalizing

-- SN-FRAGMENT DECIDABLE CONV: Conv = normal-form equality on the strongly-normalizing fragment, with the
-- global StepStar.HasConfluence hypothesis of PolygraphConvergentDecision DISCHARGED per-term from the SN
-- witnesses (confluence_of_localJoin_and_accessible).  The honest raw-layer decider modulo the normalizer
-- function (#261/#480) that supplies the normal-form witnesses.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalForms_eq_of_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.Conv.decidableOfNormalForms_of_isStronglyNormalizing

-- GIRARD CR BUNDLE (per-decl gates on the load-bearing reducibility-candidate primitives): the
-- IsReducibilityCandidate triple CR1/CR2/CR3 (structure fields), the base SN-is-a-candidate witness,
-- candidate-congruence under PointwiseIff, and candidate variable-membership.
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_isReducibilityCandidate
#assert_no_axioms FX1Poly.Typed.universeDomainPiMemberStronglyNormalizing
-- Member-SN companion to the shipped type-level non-dependent universe-domain arrow (universeDomainNonDependent
-- Arrow): the MEMBER half of the unconditional slice of #752 (DenoteKeyedNonDependentArrowMemberSN.lean). A
-- non-dependent arrow Type@e -> codomainBase has its codomain cross the binder as a pure weakening, so the
-- weaken-cancellation (RawTerm.weaken_subst_singleton) collapses SN-D7's per-argument codomain obligation to a
-- constant -- the domain candidate's per-level DRIFT (the #752 obstruction) is never consumed. universeDomainNon
-- DependentArrowMemberStronglyNormalizing: the general member-companion (codomainBase reducible-at-level with a CR
-- => members of Type@e -> codomainBase are SN). universeToUniverseArrowMemberStronglyNormalizing: the fully-
-- UNCONDITIONAL concrete witness -- a reducible member of Type@e -> Type@e' (function between two universes) is SN
-- at any level above both decoded levels, NO codomain hypotheses. First unconditional universe-domain function-
-- type member-SN in the denote model; completes the unconditional #752 slice (type + member). Only the genuinely
-- DEPENDENT composite-domain Pi stays gated on #752/#753. Both zero-axiom.
#assert_no_axioms FX1Poly.Typed.universeDomainNonDependentArrowMemberStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.universeToUniverseArrowMemberStronglyNormalizing
#assert_no_axioms FX1Poly.Core.reducibilityNormalizationScone
#assert_no_axioms FX1Poly.Core.normalizationViaSconing
#assert_no_axioms FX1Poly.Tier0.boolValueScone_semanticIsStronglyNormalizing

-- SN-for-well-typed, CLOSED case (ClosedStronglyNormalizing.lean, BFT-14 = SN-043-closed). Every closed grown
-- derivation has a strongly-normalizing subject, unconditionally. Composes closedBoundedReducibleMember (BFT-13) →
-- stronglyNormalizing_of_memberAtBoundedSucc (scope+1 bounded CR1) → StepStar.stronglyNormalizing_of_subst (SN
-- reflects through the closing substitution). Capstone of the bounded reducibility route (BFT-1..14) for closed
-- terms; what closed-term canonicity (SN-047/048/049) and consistency (SN-050) consume. Arbitrary-context SN-043
-- (#546) additionally needs the neutral-variable open-term closing env — tracked separately.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedStronglyNormalizing

-- SN-for-well-typed, OPEN form / the SN-043 wiring (OpenStronglyNormalizing.lean). Any grown derivation in an
-- arbitrary context is SN GIVEN a BoundExceedsPi budget + a bound-reducible closing environment. Same
-- member→SN→reflect composition as BFT-14, parameterized over an arbitrary closing env (closed = the .empty
-- instance). Reduces fully-unconditional #546 to ONE residual: reducibleEnvOfWfContext (the identity closing subst
-- is bound-reducible over a well-formed context — the classical reducible-substitution lemma).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfReducibleEnv

-- ★ SN-043 OPEN (OpenStronglyNormalizingUnconditional.lean, OB-5): every well-typed grown term in a WELL-FORMED
-- context is strongly normalizing, UNCONDITIONALLY. WfContextDesc Γ → HasTypeDescPi Γ subject classifier →
-- IsStronglyNormalizing subject. The open generalization of closedStronglyNormalizing (BFT-14) from .empty to
-- arbitrary Γ. Composes existsBound (budget) + reducibleEnvOfWfContextDesc (OB-3, the reducible closing env over
-- the native WfContextDesc.headIsTypeDesc + HasTypeDesc.toHasTypeDescPi) at a common SUM bound, fed to
-- stronglyNormalizingOfReducibleEnv (reflects SN internally). The OB-1..OB-5 capstone — reached with NO #672, NO
-- KB merged candidate, NO renaming closure. The wf-hypothesis stays external (since HasTypeDescPi → WfContext
-- provably FAILS, ContextValidityFails). Closes #546.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDesc

-- OSN-2 (OpenSNSmoke.lean): open-context SN regression corpus via open SN-043 (OB-5). Four concrete terms in the
-- non-empty well-formed context Γ = (.empty).cons (Type@e) — a universe code (ofFormation), the context
-- variable var 0 (var rule), the identity lambda (piIntro binder), and the β-redex (λx.x) Type@s (piElim)
-- — each discharged to IsStronglyNormalizing by HasTypeDescPi.stronglyNormalizingOfWfContextDesc (OB-5 over the
-- native IsTypeDesc-based WfContextDesc + wfContextDesc_universeBinding). The β-redex entry is the
-- NON-VACUOUS one: a term that actually reduces, whose termination OB-5 certifies. The open analogue of
-- ClosedSNSmoke (SN-044).
#assert_no_axioms FX1Poly.Typed.openUniverseCode_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.openContextVariable_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.openIdentityLambda_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.openBetaRedex_stronglyNormalizing

-- OSN-1 (OpenStronglyNormalizingBetaEta.lean): the η-reduct of a well-typed open term is β-SN. Well-typed open
-- terms are β-SN (OB-5) AND η-SN (unconditional, since η shrinks RawTerm.size) separately. The UNION βη-SN is
-- NOT their conjunction (β/η interleave), but the SN-of-union assembly is the Geser criterion accUnionBetaEta;
-- the η-postponement crux EtaQuasiCommutesOverBeta is discharged (etaQuasiCommutesOverBeta, the per-η-ctor
-- critical-pair assembly over all 5 η constructors). etaReductOfWellTypedIsBetaStronglyNormalizing is the
-- EtaPreservesBetaStronglyNormalizing payoff. No sorry/placeholder. (The WfContextDesc open βη-SN twins are
-- gated below.)
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaReductOfWellTypedIsBetaStronglyNormalizing
-- The WfContextDesc twins (the βη leg): the componentwise + conditional + headline open βη-SN
-- (OpenStronglyNormalizingBetaEta.lean) and the Geuvers βη-CR + unique-βη-NF (WfContextBetaEtaConfluence.lean),
-- all routed through the bridge-free stronglyNormalizingOfWfContextDesc — the η-SN component + the Geser union
-- criterion + the βη-Newman bridge are context-predicate-agnostic, so NO HasType on the path.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.componentwiseStronglyNormalizingOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.divergentOmega_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.rawStep_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_stronglyNormalizing

-- §27.3 Layer-3 defense: every core metatheory rule cross-referenced to a PUBLISHED MECHANIZED proof and
-- ANCHORED to the real kernel theorem that realizes it.  The `crossRef_*` anchors (`def := @kernelTheorem`)
-- verify each cited rule EXISTS and — via these gates — RE-CERTIFY each classical rule's kernel proof is
-- zero-axiom.  `KernelMetatheoryRule` + `mechanizedSource`/`hasClassicalPrecedent`/`kernelAnchor` is the
-- machine-checked catalog; the `…_hasClassicalPrecedent`/`…_isFxOriginal` rfl-facts pin the honest
-- classical-vs-FX-original split (9 classical anchored + 2 FX-original).
#assert_no_axioms FX1Poly.Typed.KernelMetatheoryRule
#assert_no_axioms FX1Poly.Typed.KernelMetatheoryRule.mechanizedSource
#assert_no_axioms FX1Poly.Typed.KernelMetatheoryRule.hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.KernelMetatheoryRule.kernelAnchor
#assert_no_axioms FX1Poly.Typed.crossRef_correctedLam
#assert_no_axioms FX1Poly.Typed.crossRef_strongNormalization
#assert_no_axioms FX1Poly.Typed.strongNormalization_hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.parityAnchor_strongNormalization_formation
#assert_no_axioms FX1Poly.Typed.parityAnchor_strongNormalization_grown
#assert_no_axioms FX1Poly.Typed.strongNormalization_grownNeedsWfContext
#assert_no_axioms FX1Poly.Typed.notStronglyNormalizing_of_infiniteReduction
#assert_no_axioms FX1Poly.Typed.growingReductionSequence_steps
#assert_no_axioms FX1Poly.Typed.growingDivergentTerm_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.growingFirstReduct_ne_source
#assert_no_axioms FX1Poly.Typed.nonSelfLoopingDivergenceExists
#assert_no_axioms FX1Poly.Typed.idTower_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.idTower_reducesToValue
#assert_no_axioms FX1Poly.Typed.idTowerUniformlyTypedReducesToValue
#assert_no_axioms FX1Poly.Typed.curryOmega_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDescPi

/-! ### ConvDecisionSteps — the SN-fragment Conv decider's exact cost witness (M19)

The decider's reducer cost = the sum of the two operands' exact normalizer counters
(`decideStronglyNormalizingSteps`), tied to the verdict + the two counted chains in ONE object
(`costAccounting`), zero exactly on the normal fragment, EXACT (= m + n) on tower pairs, and
unbounded.  HONEST M19 closure: `DecisionComplexity` is deliberately NOT instantiated for raw
`Conv` (two β-normalization runs admit no truthful size-polynomial — Statman 1979,
literature-cited); the §11.8.7 "decidable but EXP-tower" loophole is closed by exact DISCLOSURE,
with the polynomial witness reserved for deciders where it is true (the LevelExpr instance). -/

#assert_no_axioms FX1Poly.Core.Conv.decideStronglyNormalizingSteps
#assert_no_axioms FX1Poly.Core.Conv.decideStronglyNormalizing_costAccounting
#assert_no_axioms FX1Poly.Core.Conv.decideStronglyNormalizingSteps_eq_zero_iff_normalForms

/-! ### LiftedChildNormalizationFromClosure — the GTL-06 kernel's brick 1 (#820)

The reusable fresh-variable instantiation, extracted from the Π/Σ former-membership interiors
and strictly generalized (abstract domain term, ARBITRARY child classifier): a cons-closure at
a one-level-up-reducible domain yields strong normalization of the LIFTED-open substituted
binder-child.  This is the one genuinely new piece the table-generic dispatch arm needs at
shift-1 children; depth-0 children are CR1, shift ≥ 2 is a named non-blocker (no current
formation row).  The module docstring records the GO verdict + the remaining #820 assembly. -/

#assert_no_axioms FX1Poly.Typed.IsStronglyNormalizing.liftedSubstOfConsClosureAtFreshVariable
#assert_no_axioms FX1Poly.Typed.cascadeAnchor_strongNormalization
#assert_no_axioms FX1Poly.Typed.strongNormalization_isZeroArm
