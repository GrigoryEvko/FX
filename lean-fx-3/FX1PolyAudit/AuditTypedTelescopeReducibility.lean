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

/-! # FX1PolyAudit/AuditTypedTelescopeReducibility — typed-layer zero-axiom gates: telescope reducibility and the former-children logical relation
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.optionFormerFromTelescope
-- FLAG-UNIQUENESS substrate (GTL-09): the `levels ≠ []` guard of HasTypeDesc.uniquenessNative, made generic over
-- the formation generator. levels_length_eq_binderShifts is a structural telescope recursion (level list and
-- shift list have equal length); typingRuleDescOf_binderShiftsNonEmpty is the ≥1-child-family table fact
-- (pi/sigma both carry [0,1]) — extends by ONE by_cases row per ≥1-child data type code, breaks ONLY on a
-- nullary Empty former (CON-A1, the documented future branch); levels_ne_nil_of_isFormation is the combined
-- consumer-facing form. This retires the last per-former by_cases in the formation-family metatheory.
#assert_no_axioms FX1Poly.Typed.DescTelescope.levels_length_eq_binderShifts
#assert_no_axioms FX1Poly.Typed.DescTelescope.levels_ne_nil_of_isFormation
#assert_no_axioms FX1Poly.Typed.DescTelescope

/-! ### Eliminator-shape SUBSTRATE for the description engine (`HasTypeDescElim`).
    `DescTermTelescope` — the maximally-general typed-children spine over the
    PRIMARY engine `HasTypeDesc`: each child typed at an ARBITRARY classifier (the
    eliminator shape — scrutinee/motive/branches at motive-dependent types, NOT
    universes), the §11.8.5 PREMISE-side seam past formation (the output-side seam
    is `outputType`).  Non-vacuous: `DescTelescope.toTermTelescope` shows
    the formation spine is an INSTANCE (so the substrate subsumes formation);
    `descTermTelescope_heterogeneous` witnesses a telescope at arbitrary classifiers
    the universe-only spine cannot express.  Standalone (HasTypeDesc positive in
    `cons` only); `toTermTelescope` is the propext-free term-mode `match`,
    self-recursive only. -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.toTermTelescope
#assert_no_axioms FX1Poly.Typed.descTermTelescope_heterogeneous
#assert_no_axioms FX1Poly.Typed.DescTelescope.childrenStronglyNormalizingNative
-- Generic former-TELESCOPE inversion (HasTypeDescFormerTelescopeInversion.lean): the wall-bearing half
-- of the generic former inversion — recover the children DescTelescope for ANY formation generator. The
-- documented dependent-subst wall (free generator vs arm generator) turned out NAVIGABLE in the
-- free-subject+thread-Eq shape: subst generatorAgree (the free-generator subst) SUCCEEDS, then injection
-- subjectEq + subst_vars aligns the children — the same propext-free idiom the per-former inversions use.
-- Unblocks HasTypeDescUniqueness (GTL-09) + the arity-bound reducibility arms.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionFormerTelescopeGeneric
#assert_no_axioms FX1Poly.Typed.DescTelescope.renameRespectingTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.substRespectingTelescope

/-! ### INTRINSIC renaming/weakening (P6) for the ELIMINATOR-shape term spine
    (`HasTypeDescElimWeakening`).  polycell.md §11.8.5 P6 applied to `DescTermTelescope` — the
    maximally-general typed-children spine (each child at an ARBITRARY classifier) that the
    eliminator `gen`-arm (the non-uniform seam PAST formation) consumes.  This is the
    eliminator spine's cartesian-lift fibration leg.

    Standalone: `DescTermTelescope` is a STANDALONE inductive (`HasTypeDesc` appears only
    positively in `cons`'s `headTyped`), so this touches `HasTypeDesc`'s constructors not at all.
    SELF-recursive (not a mutual block): the head child's
    typing is re-renamed by `HasTypeDesc.renameRespectingContext` on the opaque
    `headTyped`; the only recursion is the strictly-smaller `restTyped`, so Lean's structural
    recursion lands it without `termination_by` — exactly like `DescTelescope.toTermTelescope`.
    The arbitrary classifier renames generically (no universe-code brick); the tail's lifted
    context-condition reuses `rename_lift_weaken_commute` at every depth.  `weakenUnderBinding`
    is the depth-0 corollary whose context-condition holds definitionally (`fun _ => rfl`, via
    `iterateLiftRaw _ 0 ≡ _` and `lookup_cons_succ`). -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.renameRespectingTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.weakenUnderBinding

/-! ### INTRINSIC substitution (P6, the β-engine) for the ELIMINATOR-shape term spine
    (`HasTypeDescElimSubstitution`).  polycell.md §11.8.5 P6 applied to `DescTermTelescope` —
    the SUBSTITUTION leg completing the pair with the renaming/weakening leg above.  Together
    they are the eliminator spine's two fibration legs (cartesian lift + β-substitution).

    SELF-recursive (not mutual): the head child's typing is re-substituted by
    `HasTypeDesc.substRespectingContext` on the opaque `headTyped`; only recursion is on
    `restTyped` ⇒ structural recursion w/o `termination_by`.  The arbitrary classifier
    substitutes generically (no `subst_universeCodeCell` brick).  The tail's lifted
    substitution-condition's `0`/successor split is IDENTICAL to the formation spine — `0` →
    fresh `var`, `k+1` → the substituent weakened across the binder via the intrinsic
    `HasTypeDesc.weakenUnderBinding` (eliminator-spine subst stands on intrinsic HasTypeDesc
    weakening).  `substituteUnderBinding` is the depth-0
    `subst0` corollary (singleton-cancel side-condition, symmetric to `weakenUnderBinding`).
    Standalone: `DescTermTelescope` touches `HasTypeDesc` ctors not at all. -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.substRespectingTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.substituteUnderBinding

/-! ### GENERIC GROWN FORMATION ARM — `genFormationPi` + `DescTelescopePi` (cascade-death at the
    grown layer, the §5-endgame direction).  `HasTypeDescPi` is a mutual block with the grown
    premise spine `DescTelescopePi`; its sole formation arm `genFormationPi` is generic over
    `typingRuleDescOf` (the grown mirror of `HasTypeDesc.genFormation`) — a new dependent former is
    ONE table row, ZERO new arms (P13).  The generic arm types a former with GROWN components (the
    `DescTelescopePi` heads are `HasTypeDescPi`, not just formation) with NO per-former dispatch,
    which is what makes the grown engine SUBSTITUTION-CLOSED generically — a per-former arm would
    force a partial-match on the child telescope (the indexed-inductive propext trap).
    `toDescTelescopePi` + `genFormationToHasTypeDescPi` exhibit that every formation Π/Σ is a
    `genFormationPi`.  The renaming leg `HasTypeDescPi.renameRespectingContext` is mutual with the
    spine companion `DescTelescopePi.renameRespectingTelescope`. -/
#assert_no_axioms FX1Poly.Typed.DescTelescopePi
#assert_no_axioms FX1Poly.Typed.DescTelescope.toDescTelescopePi
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.renameRespectingTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.substIntoGrown
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.substRespectingTelescope

/-! ### GROWN Π/Σ-CODE COMPONENT DESCENT — the inversion eliminator output-validity + canonicity
    consume.  `HasTypeDescPi.inversionPiCodeComponents` (resp. `…Sigma…`) recovers, from a
    `piTyCodeCell`/`sigmaTyCodeCell` SUBJECT's grown typing, that the domain is a grown type and the
    codomain is a grown type under the domain binder.  The grown analogue of the formation
    `HasTypeDesc.inversionPiCodeComponents`, with the classifier-`Conv` conjunct DROPPED: the
    consumers `_`-discard that `Conv`, so dropping it lets the `conv` arm simply
    recurse (no `Conv.trans`).  The `ofFormation` arm routes through the formation workhorse +
    `toDescTelescopePi`; `genFormationPi` is the base (premise telescope verbatim); `piIntro`/`piElim`
    are refuted by `headGenerator` clash. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeTelescopeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionSigmaCodeTelescopeGeneral
#assert_no_axioms FX1Poly.Typed.DescTelescope.uniquenessAgreeNative
-- GROWN CLASSIFIER-VALIDITY, the grown-engine payoff (HasTypeDescPiClassifierValidity.lean, WFG-3): a grown-typed
-- subject's classifier is a grown type (IsTypeDescPi) under the EXTENDABLE WfContextDescPi — the leg the master SR
-- dispatcher (SN-055/TG-3) consumes (WfContext can't extend at a grown piIntro binder; WfContextDescPi can). The
-- piElim arm's Pi-code inversion is broken free of the WfContext entanglement by routing through the Conv-free,
-- WfContext-free formation inversion inversionPiCodeGeneral: this yields an UNCONDITIONAL grown Pi-code inversion
-- chain (Telescope/Components/piCodeInstantiationIsType, no well-formedness), so classifierIsTypeDescPi needs only
-- WfContextDescPi with no Conv.trans/HasType.classifierIsType obstruction.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeTelescopeUnconditional
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeNilAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromPositiveMemberExtensionAndZeroMemberTail
#assert_no_axioms FX1Poly.Typed.IsTelescopeReducibleAtVector
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalVectorFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalAtAllFromFormation
-- SN-027 #674 COMPLETE formation-engine FT assembly (FormationEngineFundamentalAssembly.lean). The formation
-- telescope DescTelescope and the grown telescope DescTelescopePi have STRUCTURALLY IDENTICAL nil/cons ctors
-- (cons carries HasTypeDesc vs HasTypeDescPi head; else identical), so the grown engine's proven recursor
-- assembly ports near-verbatim to HasTypeDesc.rec MINUS piIntro/piElim. IsTelescopeReducibleAtVectorFormation is
-- the formation-telescope motive_2 (same body as the grown IsTelescopeReducibleAtVector, indexed by DescTelescope).
#assert_no_axioms FX1Poly.Typed.IsTelescopeReducibleAtVectorFormation
-- The 4-arm HasTypeDesc.rec assembly: universeFormation/conv reuse the shipped arms; genFormation ports the proven
-- grown genFormationPi former arm (by_cases gen_piTyCode/gen_sigmaTyCode + FormerChildrenReducible.ofTelescope-
-- Reducible .toPiMember/.toSigmaMember, swapping DescTelescope.twoChildLevels for the grown one); the telescope
-- nil/cons arms thread the head member + rest under ReducibleEnvVec.cons. EVERY arm proven outright EXCEPT var,
-- which consumes the single explicit variablesAllPositive hypothesis = #672. So this collapses the entire SN-027
-- dependent metatheory (and SN-043 + ~35 downstream) to the ONE statement #672, with genFormation+telescope no
-- longer residual. Wires through HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental (shipped).
#assert_no_axioms FX1Poly.Typed.formationFundamentalVectorOfAllVariablesPositive
-- GTL-11 level-indexed reassembly: the listCode former-membership FROM the one-child telescope (the
-- level-indexed twin of the bounded fundamentalGenFormationListFromTelescopeAtBoundedSucc; CR1 element-SN +
-- listCodeFormationUnderSubst). Makes the FundamentalLevelIndexed + vector arms one-line calls.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.listFormerFromTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.consInversion
-- GTL-10 substrate: the TYPING companion to twoChildLevels — a 2-child [0,1] formation telescope yields BOTH
-- component typings (domain a type under context, codomain a type under context.cons child0). Composed with
-- the generic inversionFormerTelescopeGeneric (GTL-08) it gives generic 2-child former component inversion for
-- ANY dependent binary formation former, factoring the telescope-walk half of the bespoke pi/sigma component
-- inversions. Same single-live-cons discipline as twoChildLevels (no propext / Quot.sound).
#assert_no_axioms FX1Poly.Typed.DescTelescope.twoChildComponents
-- GTL-10: the arity-1 TYPING companion (the data-former [0] analogue of twoChildComponents) — a 1-child
-- formation telescope yields the element child's typing at its level. Completes the formation telescope-
-- projection family across arities; substrate of the data-former inversion corollaries (DataFormerInversion).
#assert_no_axioms FX1Poly.Typed.DescTelescope.oneChildComponent
#assert_no_axioms FX1Poly.Typed.DescTelescope.binderShiftsAreCumulative
#assert_no_axioms FX1Poly.Typed.DescTelescope.binderShiftsAreCumulativeFromZero
#assert_no_axioms FX1Poly.Typed.DescTelescope.noFlatTwoChildTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.productCodeFormationTelescopeImpossible
-- FLAT telescope (FlatDescTelescope): the non-cumulative premise shape for the [0,0] data formers — a STANDALONE
-- (non-mutual) inductive, all children typed under the same base context (shift 0). binderShiftsAreAllZero
-- (direct induction, the flat twin of binderShiftsAreCumulative); twoChildComponents projection;
-- productTypeZeroFlatPremise (product (Type@0)(Type@0)'s children DO form a flat telescope);
-- productChildrenFlatButNotCumulative bundles it with noFlatTwoChildTelescope = the "strictly more expressive on
-- the [0,0] shape" payoff. The #934 substrate first increment (engine arm deferred).
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.binderShiftsAreAllZero
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.twoChildComponents
#assert_no_axioms FX1Poly.Typed.productTypeZeroFlatPremise
#assert_no_axioms FX1Poly.Typed.productChildrenFlatButNotCumulative
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.renameRespectingTelescope
-- FLAT-ENGINE SUBSTITUTION (#938, P6 β-engine): the flat twin of HasTypeDescSubstitution, completing the flat
-- structural-metatheory quartet (SR/SN/weakening/substitution). FlatDescTelescope.substRespectingTelescope is
-- DRAMATICALLY lighter than the cumulative one — flat cons doesn't extend the context, so NO iterateLiftRaw, NO
-- 0/successor split, NO weakenUnderBinding (the tail recurses with the SAME substitution-condition);
-- HasTypeDescFlat.substRespectingContext reuses it + reconstructs the cell table-generically;
-- substituteUnderBinding is the subst0 β-corollary (ambient singleton split, mirrors the cumulative proof).
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.substRespectingTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.consInversion
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.ofTelescopeReducible
#assert_no_axioms FX1Poly.Typed.TelescopeReducible

-- ASSEMBLY: the formation-FT telescope-cons (binder) arm CLOSES for a neutral / data-former domain — the
-- member-side leaf composed with the all-positive-argument cons companion.  The binder arm that has carried
-- the lone all-level-assembly `sorry` is discharged for every non-type-polymorphic former, given only the
-- tail recursion (supplied by the FT's own IH).
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllNeutralDomain

-- ASSEMBLY: the same binder arm CLOSES for a weak-head-reducible domain — the member-side `whnfExpand` arm
-- (this iteration) composed with the all-positive-argument cons companion.  Sibling of the neutral-domain
-- lemma; chaining the two covers every former whose substituted domain weak-head-normalises to neutral/data.
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllWhnfDomain
#assert_no_axioms FX1Poly.Typed.BoundExceedsTelescope

-- The BFT-12 discharge core (BoundExceedsDischarge.lean): monotonicity + existence of the universe-level budget.
-- `monotoneInBound` lifts a budget to any larger bound (term-mode match on the budget; conv arm pins the implicit
-- Conv proof in the pattern); `existsBound` constructs a bound for every formation derivation by structural
-- recursion (universeFormation supplies denote(lsucc e)env+1; recursive arms take the SUM of sub-bounds — NOT max,
-- whose Init le-lemmas leak propext — and lift via monotoneInBound). existsBound routes through HasTypeDesc.rec /
-- DescTelescope.rec (propext-free) rather than a match on the indexed family. Feeds the BFT-12 bound-choice that
-- threads a single bound through the bounded grown FT toward SN-043.
#assert_no_axioms FX1Poly.Typed.BoundExceeds.monotoneInBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsTelescope.monotoneInBound
#assert_no_axioms FX1Poly.Typed.BoundExceeds.existsBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsTelescope.existsBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPiTelescope

-- The BFT-12b grown-budget discharge (BoundExceedsPiDischarge.lean): monotonicity + existence for BoundExceedsPi.
-- Mirror of BoundExceedsDischarge over the grown engine; existsBound's ofFormation arm delegates to
-- BoundExceeds.existsBound (origin of the fuel), the piIntro arm sums THREE sub-bounds (Nat.le_trans chain). Feeds
-- the BFT-12c grown-FT bound-choice toward SN-043.
#assert_no_axioms FX1Poly.Typed.BoundExceedsPi.monotoneInBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPiTelescope.monotoneInBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPi.existsBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPiTelescope.existsBound
#assert_no_axioms FX1Poly.Typed.DescTelescope.childrenAdmitNoStep
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.contextConversionTelescopeExact

-- typeValiditySurvivesReductionUnderWf: the FULL-engine, well-formed-context form of the flexible-route residual
-- TypeCodeValidityRespectsReduction (#1094) — a direct corollary of subjectReductionStar (the universe classifier is
-- preserved at every step).  Subsumes the formation-fragment validityRespectsReductionOfFormation (#1095) and the
-- head-β validityRespectsBetaRedex (#1127) over the ENTIRE grown type-code fragment (incl. type-level-computing
-- applications).  The cost is the well-formed-context presupposition, which is IRREDUCIBLE (HasTypeDescPi →
-- WfContextDesc is refuted in ContextValidityFails.lean) but BENIGN — exactly what the flexible grown
-- context-conversion bundle already carries (its var arm reads target validity off WfContextDescPi.lookupIsType).  So
-- once master SR is unconditional (SR-U4), the residual #1094 called "routes through the logical relation" is NOT
-- logical-relation-hard — only well-formed-context-gated.  Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValiditySurvivesReductionUnderWf

-- Conv-KEEPING Π/Σ-code former inversion (HasTypeDescPiFormerInversion.lean, the former head for the SR cong arm
-- #458). inversionPiCodeComponents drops the classifier Conv (its telescope workhorse discards _convToCode/_converts),
-- which suffices for output validity but NOT for re-assembling piTyCodeCell domainCode' codomainCode at the ORIGINAL
-- classifier. invertPiTyCode/invertSigmaTyCode keep it: ofFormation is HANDLED via inversionPiCodeWithConvGeneral
-- (a former IS a formation term, unlike λ/app), conv re-threads via Conv.trans converts.sym recursiveConv, piIntro/
-- piElim refuted by headGenerator clash, and genFormationPi is the match (output definitionally universeCodeCell
-- (lmaxAll levels) flag once the rule is pinned by typingRuleDescOf_piTyCode, so the Conv is Conv.refl). The corollary
-- destructures the two-entry telescope and yields domain/codomain typings + Conv classifier (universeCodeCell
-- (lmaxAll [domainLevel, codomainLevel]) flag). The former analogue of invertLam (#454) / invertApp (#769).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertPiCodeTelescopeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertSigmaCodeTelescopeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.DescTelescope.decideSynthGeneric
#assert_no_axioms FX1Poly.Typed.DescTelescope.decideAtFlagGeneric
#assert_no_axioms FX1Poly.Typed.GrownCheckTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.pinnedReflectionTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.pinnedReflectionTelescopeConditional
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.pinnedReflectionTelescopeGuarded

/- E2.7 former-arm core (TelescopeUniverseDeterminism): two grown telescopes over the same
children agree on levels, and on the flag for nonempty children — IH-parameterized (the
strong-size-induction seam), table-generic, budget through size peeling. -/

#assert_no_axioms FX1Poly.Typed.DescTelescopePi.universeDeterminismOfChildIH

/- E2.7 former-arm inversion (GenericFormerTelescopeInversion): ONE table-generic grown
inversion for every formation row — keeps the premise telescope over the subject's own children
AND pins the classifier to the universe former's output code.  Unconditional; new rows need no
new arm. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertFormerTelescopeWithConvGeneric
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.levelsNonemptyOfShiftsNonempty
#assert_no_axioms FX1Poly.Typed.DescTelescope.renameAlongFlagCoherentToGrownTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.renameAlongFlagCoherentTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.pinnedReflectionTelescopeFlagCoherentConditional

/-! ### TelescopeSubstitutedChildrenNormalization — the GTL-06 kernel's brick 2 (#820)

Telescope reducibility yields SN of every substituted child at each arity the formation table
uses: count-1 via head-membership CR1; count-2 via head CR1 + brick 1 at the LIFTED binder
position; the spine corollaries package these as `allStronglyNormalizing` of the literal
substituted spines — the exact input of `formerCellStronglyNormalizingOfChildren`.  Brick 3
(the table-generic dispatch arm over the six dispatch files) consumes these. -/

#assert_no_axioms FX1Poly.Typed.TelescopeReducible.substitutedOneChildStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.TelescopeReducible.substitutedTwoChildrenStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.TelescopeReducible.substitutedOneChildSpineStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.TelescopeReducible.substitutedTwoChildSpineStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.cascadeAnchor_contextConversion_telescopeStep
