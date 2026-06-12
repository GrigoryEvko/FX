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
import FX1Poly.Typed.FormationTableShapeFacts

/-! # FX1PolyAudit/AuditTypedTypingEngines — typed-layer zero-axiom gates: the typing engines (formation, grown, flat, data) and their inversions
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/


/-! ### TypingContext — native de Bruijn telescope + lookup + coherence -/

#assert_no_axioms FX1Poly.Typed.TypingContext
#assert_no_axioms FX1Poly.Typed.TypingContext.length
#assert_no_axioms FX1Poly.Typed.TypingContext.length_eq_scope
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listFormerNotTypedAtEmptyType
-- GTL-14: the reusable one-child data-former formation reconstruction (the grown twin of piFormation/sigma-
-- FormationViaGenArm) + a CONCRETE non-vacuous witness that the grown engine types a real `List (Type@0) :
-- Type@1` — the honest GTL-11 payoff exhibited (not merely "compiles"), locked in as regression protection.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listFormationViaGenArm
#assert_no_axioms FX1Poly.Typed.listFormationSmoke
-- GTL-13 part 2: the optionCode formation row landed (typingRuleDescOf + the ~18-site canonical-forms cascade);
-- the grown engine now types `Option A : Type@(level A)`.  The reconstruction + concrete `Option (Type@0) :
-- Type@1` witness, the option twin of listFormationViaGenArm/listFormationSmoke.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.optionFormationViaGenArm
#assert_no_axioms FX1Poly.Typed.optionFormationSmoke
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_optionCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.optionFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.optionFormerNotTypedAtEmptyType
#assert_no_axioms FX1Poly.Typed.TypingRuleDesc
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_piTyCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_sigmaTyCode
-- Formation-family invariant (HasTypeDesc.lean): every typingRuleDescOf row outputs universeFormerOutput,
-- enumerated ONCE. The cascade-death substrate for the formation-family metatheory — consumers obtain
-- rule.outputType = universeFormerOutput from here instead of their own unfold + pi/sigma split, so a new
-- universeFormerOutput row (data type code) is absorbed by adding one by_cases case HERE.
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_outputIsUniverseFormer
-- Cell-RECONSTRUCTION helpers (HasTypeDesc.lean, the category-C consumer substrate). formationRuleImpliesNotVariable
-- discharges the generator ≠ gen_var side condition of RawTerm.subst/rename_mkGen_of_ne_var (typingRuleDescOf
-- gen_var = none). formationRuleIsUniverseFormer upgrades the output equation to the full structure equation
-- (rule = {outputType := universeFormerOutput}) so `obtain rfl` makes rule concrete — the generic successor
-- of the per-branch Option.some.inj.
#assert_no_axioms FX1Poly.Typed.formationRuleImpliesNotVariable
#assert_no_axioms FX1Poly.Typed.formationRuleIsUniverseFormer
-- The "current formation table = {pi, sigma}" enumeration (the former-tag tool a dispatch consumer reads
-- from isFormation). Docstring records the GTL-05/06 boundary: the reducibility-FT genFormation arm's
-- by_cases is entangled with generator-ARITY (2-child spine ill-typed over abstract generator) + dual
-- telescope inductives, so the former-membership dispatch needs the arity-generic candidate-bridge
-- (BFT-15/CON-A3), not this enumeration. Typing layer = table-generic; reducibility former-closure = deep.
-- GTL-11 LANDED (2026-06-07): `gen_listCode` IS a `typingRuleDescOf` row — `List A : Type@(level A)` types in
-- BOTH the formation and grown engines, zero-axiom. The TYPING-judgment metatheory absorbed it one-case each
-- (validity / subst / weaken / inversion / uniqueness, exactly as typingRuleDescOf_outputIsUniverseFormer's
-- docstring predicts). The MEASURED cascade was a bounded ~18-site, two-layer fan-out (NOT the §5 model-change
-- the spike feared): (a) reducibility-FT — the 6 genFormationPi dispatch arms (FundamentalLevelIndexed,
-- HasTypeDescPiFundamentalVectorFromFormation, FormationEngineFundamentalAssembly, BoundedGrownDispatch,
-- BoundedFormationDispatch, BoundedGrownFundamental) each gained a 1-child listCode branch routing through the
-- arity-generic IsReducibleMemberAt.dataFormerInUniverse (the listFormerFromTelescope /
-- fundamentalGenFormationListFromTelescopeAtBoundedSucc bricks); (b) canonical-forms — the var/former head
-- disjunction (FormationCanonicalForms.subjectIsVariableOrFormerHead + the grown closedNormalSubjectHead) gained
-- a `head = gen_listCode` disjunct, cascading to ~10 consumers (closed/open canonical forms, type safety,
-- progress, non-vacuity, beta-redex-in-action), the genuinely-content piElim crux discharged by the new
-- head-agnostic GROWN former-classifier inversion (formerClassifierConvUniverseGeneric → listFormerNotTypedAt-
-- {Pi,Empty}Type). HONEST TG-5 finding: cascade-freedom is PARTIAL — the typing judgment is table-generic, but
-- the reducibility-FT and canonical-forms layers cost bounded per-former bricks (every consumer noConfusion-s /
-- reconstructs each head, so the head enumeration is CORRECT, not accidental). optionCode (GTL-13) is now a
-- near-mechanical clone of these same sites. Canonicity SN-047/48/49 still needs the SEPARATE empty-candidate
-- model (CON-A3 #810, sconing leg) — data FORMATION (this) is distinct from data CANONICITY.
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_isPiOrSigmaOrListOrOptionCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_listCode
#assert_no_axioms FX1Poly.Typed.HasTypeDesc
#assert_no_axioms FX1Poly.Typed.hasTypeDesc_piFormation_viaGenArm
#assert_no_axioms FX1Poly.Typed.hasTypeDesc_sigmaFormation_viaGenArm

/-! ### Intrinsic VALIDITY of the description engine (`HasTypeDescValidity`).
    `IsTypeDesc` = the intrinsic "inhabits a universe" over `HasTypeDesc`; it gives the
    description engine its own metatheory.  (Native formation validity lands as
    `HasTypeDesc.classifierIsTypeDescNative`, gated below.) -/
#assert_no_axioms FX1Poly.Typed.IsTypeDesc

/-! ### INVERSION (P8 descent, premise half) for the description engine
    (`HasTypeDescInversion`).  polycell.md §11.8.5 P8: from a `piTyCodeCell`'s
    `HasTypeDesc`-typing recover the domain/codomain child typings (at a shared
    universe flag).  `Conv`-FREE: the children are fixed by the subject, so the
    `conv` arm forwards the child-typing IH verbatim (no `Conv.trans`, no
    `WfContext`) — isolating the descent content (the children's types, what the
    typechecker + canonicity consume) from the `Conv`-blocked classifier conjunct.
    Term-mode recursive `match` (NOT `induction`, which rejects the mutual
    `HasTypeDesc`) + `injection`/`subst_vars` + `congrArg RawTerm.headGenerator` +
    `Generator.noConfusion` (the propext-free inversion recipe).
    Covers BOTH the dependent-binary formers (Π over `gen_piTyCode`, Σ over
    `gen_sigmaTyCode`).  `…General` is the subject-generalized recursive workhorse;
    `inversion{Pi,Sigma}Code` the concrete `{pi,sigma}TyCodeCell` entry points. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCode
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCode
-- Generic former-CLASSIFIER inversion (HasTypeDescInversion.lean): the WALL-FREE half of the generic
-- former inversion (GTL-08/10 down-payment). Generic over the formation generator (no concrete pi/sigma
-- pinning) — a typed formation cell's classifier converts to Type@(lmaxAll levels, flag). Sidesteps the
-- dependent-subst wall (the file header's documented blocker) by extracting the CLASSIFIER only: the
-- genFormation arm `obtain rfl`s the TypingRuleDesc (children-independent), NEVER substing the generator.
-- Empirically isolates the wall to the telescope-extraction (the residual hard half).
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionFormerClassifierGeneric

-- GTL-10 (DataFormerInversion): per-former inversion corollaries for the one-child DATA type-code formers,
-- giving them inversion parity with the two-child Π / Σ formers (inversionPiCodeWithConv / inversionSigma-
-- CodeWithConv). A typed listCode / optionCode cell recovers the element child's typing and the classifier
-- Conv to Type@(lmaxAll [elementLevel]) — by specializing inversionFormerWithConvGeneric at the listCode /
-- optionCode row and projecting the one-child telescope (DescTelescope.oneChildComponent's inline twin). With
-- these the per-former inversion family is complete across the two shipped formation arities (1: list/option;
-- 2: pi/sigma); everything else in the formation metatheory is already table-generic (the GTL-07/08/09 census).
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionListCode
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionOptionCode

/-! ### Leaf inversions (`var`, `universeCode`) for the description engine — the two
    NON-compound subjects, completing the per-shape inversion suite (var / universeCode
    / Π / Σ).  A variable cell's classifier is convertible to its context lookup; a
    universe-code cell's to the next universe.  Analogues of the bespoke
    `HasType.inversion{Variable,UniverseCode}`, via the term-mode recursive `match` (the
    mutual `HasTypeDesc` rejects `induction`): the `conv` arm composes through the
    premise's classifier (a type by validity) with `Conv.trans_of_typedMiddle`; the
    impossible `genFormation` arm is refuted by `subst`-ing the pinned non-formation
    generator and a `contradiction` against `typingRuleDescOf … = some rule` (the
    whitelist reduces to `none` for `gen_var` / `gen_universeCode`); the matching leaf
    arm closes by `Conv.refl` after `injection`.  These are the leaf cases intrinsic
    UNIQUENESS (P7) consumes when inverting the second derivation. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionVariableGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionVariable
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionUniverseCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionUniverseCode

/-! ### Component descent (P8) — projecting the typed CHILDREN of a Π/Σ formation cell
    (`HasTypeDescInversion`).  The `…WithConv` inversions yield the premise telescope; the
    typechecker / canonicity consume the DOMAIN and CODOMAIN typings directly.  These
    corollaries case the two-child `binderShape` telescope to project `HasTypeDesc Γ domain Type@(dl,f)` ∧
    `HasTypeDesc (Γ.cons domain) codomain Type@(cl,f)` ∧ `Conv classifier Type@(lmax dl cl, f)`.  Two definitional
    facts keep it transport-free: `scope + 0 ≡ scope` (binderShape's `Nat.add_zero ▸ domain`
    head is just `domain`) and `lmaxAll [dl, cl] ≡ lmax dl cl`.  The Π-code inversion in
    component form. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeComponents

/-! ### INTRINSIC renaming/weakening (P6, the β-engine) for the description engine
    (`HasTypeDescWeakening`).  polycell.md §11.8.5 P6: typing is preserved along a context
    morphism.  `HasTypeDesc.renameRespectingContext` (with its telescope companion
    `DescTelescope.renameRespectingTelescope`) preserves `HasTypeDesc` along any renaming
    respecting the context; `HasTypeDesc.weakenUnderBinding` is the weakening special case.
    An intrinsic-BY-INDUCTION `HasTypeDesc` metatheorem (validity / inversion / uniqueness are
    case-analysis; this is genuine MUTUAL recursion).  Lands as a clean mutual recursion because it has NO
    second-derivation inversion (cross-calls on pristine `match`-bound subterms);
    the genFormation companion cross-call is HOISTED before the `by_cases` so
    `premises` stays pristine for the structural-recursion checker.  The telescope
    companion's lifted context-condition is the N-binder generalization of the
    `piFormation` codomain handling, reusing `rename_lift_weaken_commute` at every depth
    (`iterateLiftRaw ρ (cd+1) ≡ lift (iterateLiftRaw ρ cd)`). -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.renameRespectingContext

/-! ### INTRINSIC substitution (P6, the β-engine) for the description engine
    (`HasTypeDescSubstitution`).  polycell.md §11.8.5 P6: the SUBSTITUTION half of whiskering
    — the engine `app`'s β-reduction `b[a]` needs to preserve typing.
    `HasTypeDesc.substRespectingContext` (with companion `DescTelescope.substRespectingTelescope`)
    preserves `HasTypeDesc` along any substitution whose substituents are target-typed at the
    substituted source-binding types; `HasTypeDesc.substituteUnderBinding` is the `subst0`
    corollary the β-rule cites.  An intrinsic-by-induction mutual metatheorem — same
    clean shape as intrinsic weakening (no second-derivation inversion), and the decouple
    COMPOUNDS: the companion's successor case reuses the intrinsic
    `HasTypeDesc.weakenUnderBinding` to weaken the substituent across the binder.  `Conv.subst`
    (#370) rides the `conv` arm — no `Conv.trans`, so the β-engine does not depend on raw
    confluence.  A purely intrinsic `HasTypeDesc` recursion. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaCoherence_formationBody
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaCoherence_formationFunction
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaCoherenceGrown
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.genFormationToHasTypeDescPi

/-! ### GROWN-ENGINE SUBSTITUTION — `ofFormation` leg.  `HasTypeDesc.substIntoGrown` carries a
    formation derivation along a substitution whose substituents are `HasTypeDescPi`-typed, into the
    grown engine (a formation subject substituted by a grown term is no longer a formation term, so
    the result lands in `HasTypeDescPi`).  Its `genFormation` case rebuilds through the generic
    `genFormationPi` from a substituted grown spine (`DescTelescope.substIntoGrown` → `DescTelescopePi`)
    with no per-former child projection.  Mutual structural recursion on the formation derivation; the
    recursion stays within the `HasTypeDesc`/`DescTelescope` family, so no cross-inductive boundary. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substIntoGrown
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substRespectingContext

/-! ### GROWN β SUBJECT REDUCTION — the subst0 corollary + general β-coherence.
    `HasTypeDescPi.substituteUnderBinding` specializes `substRespectingContext` to the singleton
    substitution (substitute a grown-typed `argument` for de Bruijn 0) — the grown β-engine, mirror
    of the formation `HasTypeDesc.substituteUnderBinding`.  `HasTypeDescPi.betaCoherence` is the
    first FULLY-GENERAL non-vacuous β subject reduction: a redex `appCell (lamCell body) argument`
    from GROWN components and its β-reduct `subst0 body argument` are BOTH typed at the same
    `subst0 codomainCode argument` (redex by `piElim ∘ piIntro`, reduct by `substituteUnderBinding`).
    It strictly generalizes `betaCoherence_formationBody` to arbitrary grown body/argument/domain. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaCoherence
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionSigmaCodeComponents

/-! ### GROWN DEPENDENT-ELIMINATOR OUTPUT-VALIDITY — the inversion composed with the β-engine.
    `HasTypeDescPi.piCodeInstantiationIsType` (resp. `…sigma…`) proves the motive-instantiated output
    `subst0 codomainCode argument` is a grown type, given the type-former's well-formedness and an
    argument of the domain.  Composes `inversionPiCodeComponents` + `substituteUnderBinding`; the
    universe classifier lands by the `subst0`/`subst_universeCodeCell` defeq.  The type-former
    well-formedness is a HYPOTHESIS (full grown validity is blocked at the `piIntro` domain/codomain
    flag — see the file docstring); it is exactly the witness SR/canonicity carry. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piCodeInstantiationIsType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaCodeInstantiationIsType
-- VALUE-CASE inversions (EmptyTypeValueInversion.lean): the typing-layer consequence of the rigidity — NONE of
-- the grown engine's canonical values is typed at emptyTypeCell. A λ's classifier is Conv a Π-code (invertLam),
-- a Π/Σ-former's classifier is Conv a universe code (invertPiTyCode/invertSigmaTyCode); neither is Conv-equal to
-- emptyTypeCell. The value-case half of consistency (with SN + SR a closed t:Empty reduces to such a value).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.lambdaNotTypedAtEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormerNotTypedAtEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerNotTypedAtEmptyType
-- Family COMPLETED: the universe-code value case (via the shipped HasTypeDescPi.inversionUniverseCode, the
-- SN-052 checker leaf). λ / Π-former / Σ-former / universe-code are ALL the canonical values the grown engine
-- types — so no canonical value is typed at emptyTypeCell (the value-case half of consistency, done).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCodeNotTypedAtEmptyType
-- FORMATION-ENGINE CANONICAL FORMS (FormationCanonicalForms.lean): the formation engine has no intro/elim
-- forms, so a CLOSED formation-typed subject's head is exactly gen_piTyCode / gen_sigmaTyCode /
-- gen_universeCode (the variable disjunct vacuous at Fin 0). The structural progress fact the closed-canonicity
-- / closed-consistency arguments consume, and the ofFormation foundation of the grown canonical forms. Proved by
-- the propext-free mutual recursor (trivial telescope motive) — zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectIsVariableOrFormerHead
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCodeNotTypedAtPiType
-- GROWN CANONICAL FORMS (GrownCanonicalForms.lean): a closed NORMAL grown-typed term has head
-- gen_lam/gen_piTyCode/gen_sigmaTyCode/gen_universeCode (closedNormalSubjectHead, via the propext-free recursor;
-- piElim crux killed by appNormal_functionNormal + not_isStepNormalForm_beta_smoke + the *NotTypedAtPiType
-- inversions). noClosedNormalTermAtEmptyType = grown NORMAL-FORM consistency: no closed normal term inhabits
-- Empty (canonical forms + the *NotTypedAtEmptyType value inversions, NO SR). Full SN-050 adds SN (OB-5) + SR.
#assert_no_axioms FX1Poly.Typed.appNormal_functionNormal
-- OPEN CANONICAL FORMS PER TYPE (GrownOpenCanonicalFormsByClassifier.lean, five-layer-defense L4 §27.3): the open
-- generalizations of closedNormalFunctionIsLambda / closedNormalTypeIsFormer, admitting the neutral disjunct.
-- openNormalFunctionIsLambdaOrNeutral = a normal grown-typed term at a Π type in ANY WfContext is a λ or a
-- Core.IsNeutral (the type-former heads refuted at a Π classifier by the *NotTypedAtPiType inversions).
-- openNormalTypeIsFormerOrNeutral = a normal grown-typed term at a universe in ANY WfContext is a type former or a
-- Core.IsNeutral (the λ head refuted by lam_notTypedAtUniverseCode). Exactly the type-directed NbE / η-long readback
-- dichotomy (TY-CONV-quote / η-M15 line). #672-independent — pure inversion, no SR, no SN.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openNormalFunctionIsLambdaOrNeutral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openNormalTypeIsFormerOrNeutral
-- FORMATION CONTEXT WELL-FORMEDNESS (WfContextDesc.lean): the IsTypeDesc-based context predicate. It stores
-- IsTypeDesc bindings, keeping lookups + extensions inside HasTypeDesc. Lighter than the grown WfContextDescPi
-- (formation IsTypeDesc < grown IsTypeDescPi).
#assert_no_axioms FX1Poly.Typed.WfContextDesc
#assert_no_axioms FX1Poly.Typed.WfContextDesc.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextDesc.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextDesc.headIsTypeDesc
#assert_no_axioms FX1Poly.Typed.WfContextDesc.cons
#assert_no_axioms FX1Poly.Typed.wfContextDesc_universeBinding
-- FORMATION VALIDITY over WfContextDesc (WfContextDescValidity.lean): a HasTypeDesc-typed cell's classifier is a
-- formation type (IsTypeDesc), proved over WfContextDesc. The var arm reads WfContextDesc.lookupIsTypeDesc
-- directly. The canonical formation validity.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierIsTypeDescNative
-- FORMATION UNIQUENESS (P7) over WfContextDesc (WfContextDescUniqueness.lean): a genuine MUTUAL recursion
-- uniquenessNative/uniquenessAgreeNative — the head child recurses into uniquenessNative itself and the rest
-- extends via WfContextDesc.cons whose IsTypeDesc binding IS the head typing; arms invert via the param-free
-- inversions. The canonical formation uniqueness.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.uniquenessNative
-- GROWN CONTEXT WELL-FORMEDNESS (WfContextDescPi.lean, WFG-1): the grown context predicate over IsTypeDescPi. It
-- IS extendable at a grown piIntro binder (a grown domain typing is an IsTypeDescPi) — the substrate prerequisite
-- the master SR dispatcher (TG-3/SN-055) threads through binders. Structural-recursion def + And-projection
-- inversions, propext-free.
#assert_no_axioms FX1Poly.Typed.WfContextDescPi
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.headIsType
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.cons
#assert_no_axioms FX1Poly.Typed.wfContextDescPi_universeBinding
-- GROWN-FROM-FORMATION CONTEXT LIFT (WfContextDescPiFromWfContextDesc.lean): a formation-well-formed context
-- (WfContextDesc, IsTypeDesc bindings) lifts to a grown-well-formed one (WfContextDescPi, IsTypeDescPi bindings)
-- via the native HasTypeDesc.toHasTypeDescPi formation -> grown embed on each binding.
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.ofWfContextDesc
-- GROWN TYPE-STABILITY, substitution dual (WfContextDescPiLookup.lean): IsTypeDescPi survives single-
-- substitution (the subst dual of weakenUnderBinding), so a grown type in a cons-context becomes a grown type
-- in the prefix after substituting a typed argument. The universe-code witness is subst-invariant (same
-- definitional fact that makes IsType.substituteUnderBinding a 2-liner); completes the grown type-stability
-- pair (weaken + subst) the dependent Π-elimination output classifier needs.
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi.substituteUnderBinding
-- FORMATION→GROWN TYPE EMBEDDING (WfContextDescPiValidity.lean): the IsType-level functoriality mirror of the
-- term-level HasTypeDesc.toHasTypeDescPi — a formation type (IsTypeDesc) is a grown type (IsTypeDescPi) via
-- ofFormation. The named extraction of the .ofFormation-arm re-wrap recurring across the grown classifier-
-- validity family, lifting formation-type outputs uniformly.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.toIsTypeDescPi
-- GROWN CLASSIFIER-VALIDITY, formation leaf (WfContextDescPiValidity.lean, WFG-3a): a FORMATION-typed cell's
-- classifier is a grown type (IsTypeDescPi) under the grown well-formedness WfContextDescPi. The var arm reads
-- WfContextDescPi.lookupIsType directly (under a grown context a formation variable's type is grown); the rest
-- lift the formation universe-typing via ofFormation. The formation-engine leaf of grown classifier-validity;
-- the grown HasTypeDescPi.classifierIsTypeDescPi + the piCodeInstantiationIsType/betaSR WfContextDescPi twins
-- feed toward the master SR (TG-3).
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierIsTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeComponentsUnconditional
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piCodeInstantiationIsTypeUnconditional
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierIsTypeDescPi
-- FUNCTION-COMPONENT VALIDITY presuppositions (HasTypeDescPiFunctionComponentValidity.lean): a function's DOMAIN
-- and CODOMAIN are types. Composes classifierIsTypeDescPi (the function's Pi classifier is a type) with the
-- unconditional inversionPiCodeComponentsUnconditional (whose two conjuncts ARE the domain/codomain typings). The
-- load-bearing presuppositions the SR congruence arms + the grown context-conversion piElim residual (GrownCtxConv-5)
-- consume to context-convert / re-type a function's components — named so they cite a presupposition, not the
-- composite.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.functionDomainIsType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.functionCodomainIsType
-- reclassifyArgumentToFunctionDomain: the first consumer — re-type an argument (Conv to the function's domain) at
-- the domain itself, with functionDomainIsType supplying the conv rule's universe witness. The argument-retyping
-- step of the grown β / context-conversion piElim arms (toward GrownCtxConv-5/SN-055).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.reclassifyArgumentToFunctionDomain
#assert_no_axioms FX1Poly.Typed.genFormationPiTypesBothPiAndSigmaFormers
-- INTRODUCTION + ELIMINATION rule TABLES drive a concrete term: the identity application
-- (λ(x:Type@(e+1)).x)(Type@e) typed end-to-end through hasTypeDescPi_piIntro_viaIntroDesc (the intro
-- table) composed with hasTypeDescPi_piElim_viaElimDesc (the elim table). Output is the elim rule-DATA
-- output piElimOutput, resolving (rfl) to Type@(e+1) = the explicit-engine classifier; SN via SN-043.
-- Completes the formation/intro/elim cascade-free-typing demonstration trio (Σ-formation is above).
#assert_no_axioms FX1Poly.Typed.identityLambdaViaIntroTable
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables
#assert_no_axioms FX1Poly.Typed.validTypingBridgeUniverseFormation
#assert_no_axioms FX1Poly.Typed.validTypingBridgePiFormation
#assert_no_axioms FX1Poly.Typed.validTypingBridgeSigmaFormation
#assert_no_axioms FX1Poly.Typed.validTypingBridgeGenFormationPi
-- SN-024 VERIFIED 2026-06-02 (subsumed by SN-022's var arm; end-to-end off-by-one resolution confirmed):
-- validTypingBridgeVar (gated above) assigns subjectLevel := contextLevels index, making the variable's level a
-- FUNCTION of the context rather than a free parameter; ValidTyping.fundamental's var arm
-- (fundamentalVarLevelIndexed, gated above, via ReducibleEnvVec.lookupReducible) then discharges it with NO
-- level-equality side condition. This is precisely where the uniform-level recursor route is STUCK — it demands
-- envLevels index = predLevel+1 for independently-quantified envLevels/predLevel. The formal basis is
-- isFundamentalConclusionAtVector_iff_forall_levelIndexed (gated above): the uniform-vector var is unprovable
-- because it would force membership at predLevel+1 for EVERY predLevel, whereas a var is reducible only at its
-- env-fixed contextLevels index.
-- SN-025 (LevelingBridge.lean): the ∀-aboveLevel former-domain premise — GO case discharged. A UNIVERSE-CODE
-- domain Type@innerLevel is ValidTyping-valid at EVERY level via the level-polymorphic universeFormation
-- (validTypingForallAboveLevelUniverseDomain), exactly the fuel-polymorphic premise piFormation/sigmaFormation
-- need for a universe-code domain (the SN-004-GO-underwritten case). DEFERRED (honest): a bare TYPE-VARIABLE
-- domain is NOT produced syntactically — ValidTyping.var pins its level at contextLevels i (the SN-001 obstruction
-- at the syntactic layer); it is handled at the REDUCIBILITY level (IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain
-- / ReducibleEnvAtAllLevels.consTypeVariable / allLevelsReducible_piOverNeutralVariableDomain), which the bridge
-- assembly SN-027 routes the type-variable domain through.
#assert_no_axioms FX1Poly.Typed.validTypingForallAboveLevelUniverseDomain
-- The universe-domain Pi formation bridged (the #672-sidestep made concrete): Pi(X:Type@e).C is
-- ValidTyping-valid via the level-polymorphic universeFormation domain premise — NO impredicative
-- member-extension (the fuel-route #672 obstruction). Composes validTypingBridgePiFormation with the GO-case
-- forall-aboveLevel producer; demonstrates the per-level route closes the universe-domain Pi the fuel route stalls on.
#assert_no_axioms FX1Poly.Typed.validTypingBridgePiFormation_universeDomain
-- SN-027 (type-code level-flexibility, former recursive cases): a Π/Σ type code over a level-flexible domain
-- + codomain is itself valid at EVERY level (via piFormation/sigmaFormation at predLevel := aboveLevel). With
-- the universeFormation base above, this is the structural induction establishing that every NON-variable type
-- code carries the ∀-level conclusion the refined motive needs (type variables = the sole escape → reducibility).
#assert_no_axioms FX1Poly.Typed.validTypingForallAboveLevelPiFormer
#assert_no_axioms FX1Poly.Typed.validTypingForallAboveLevelSigmaFormer
#assert_no_axioms FX1Poly.Typed.universeFormation_isLevelFlexible
#assert_no_axioms FX1Poly.Typed.piFormation_isLevelFlexible
#assert_no_axioms FX1Poly.Typed.sigmaFormation_isLevelFlexible
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.universeFormation
-- the revised-motive TERM wrapper: a single-level-valid subject whose classifier is not convertible to any
-- universe code satisfies the motive (conjunct-2 vacuous via the unsatisfiable convertibility guard). The
-- binder/elim term-output arms consume it with Conv.piTyCode_not_universeCode / Conv.sigmaTyCode_not_universeCode.
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.ofTermValidity
-- the BINDER/ELIMINATION term arms (ValidTypingPiArms.lean). piIntro: classifier is a Π code, conjunct-2 vacuous
-- via Conv.piTyCode_not_universeCode (a PROOF). piElim: function+argument ALIGNED at one subjectLevel
-- (ValidTyping.piElim is same-level — the bare-existential motive cannot align, verified), conjunct-2 vacuous
-- via the resultNotConvUniverse hypothesis the assembly discharges (type-family case routes separately, pinned).
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.piIntro
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.piElim
-- the SECOND level-synthesis mechanism (ValidTypingPiArms.lean): the piElim arm for a TYPE ARGUMENT
-- (impredicative/polymorphic application). The argument is a type (classifier a universe code), hence
-- LEVEL-FLEXIBLE, so ValidTyping.piElim's same-level alignment discharges WITHOUT hypothesis — the function sits
-- at positive level predLevel+1 (every totalBridge subject does) and the argument's flexibility supplies it at
-- exactly that level. Type arguments float to any level. (Residual hard case: a TERM argument needs the
-- assembly's level inference.)
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.piElimTypeArgument
-- the GENERIC-FORMER arm (ValidTypingFormerArms.lean): genFormationPi is a TYPE CODE whose classifier is the
-- generic rule.outputType (not syntactically a universe code). conjunct-1 fires ValidTyping.genFormationPi at the
-- carried predLevel; conjunct-2 (when the classifier is CONVERTIBLE to a universe code) refires it at every level
-- and reclassifies through the convertibility witness via ValidTyping.conv (the old syntactic-guard motive used a
-- bare eq ▸). The premises are predLevel-independent — the same freedom the fixed formers exploit. This COMPLETES
-- the TotalBridgeConclusion arm-set; only the HasTypeDescPi.rec assembly + level synthesis remain for #662.
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.genFormationPi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeApplication
-- FLAT-FORMER TYPING (HasTypeDescFlat): the #934 CAPABILITY — the non-dependent [0,0] type-code formers now TYPE
-- via a STANDALONE judgment (mirrors the grown HasTypeDescPi; NOT a HasTypeDesc mutual-block arm, so zero
-- cascade). flatTypingRuleDescOf table (product/sum/either/arrow/equiv → universeFormerOutput); the partition
-- fact (typingRuleDescOf_productCode_none: product is NOT cumulative); flatTypingRuleDescOf_outputIsUniverseFormer
-- metadata; HasTypeDescFlat inductive; productFlatFormationSmoke = product (Type@0)(Type@0) : Type@(lmax 1 1).
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_productCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_productCode_none
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_outputIsUniverseFormer
-- DATA-INTRO ENGINE (HasTypeDescDataIntro, DI-1): the standalone data-CONSTRUCTOR typing judgment, FLAT pattern
-- (references nothing of HasTypeDescPi in the nullary arm; a NEW relation, so the grown engine's data-head-
-- untyped refutations stay true — boolTrue is still untyped in HasTypeDescPi). Nullary arm + dataIntroNullary
-- RuleDescOf table (boolTrue/boolFalse -> boolCode); the constructors the grown engine PROVES untyped now have a
-- typing in the dedicated judgment. boolTrueTyped/boolFalseTyped = the two closed bool canonical members; the
-- partition witness typingRuleDescOf_boolTrue_none documents that ONLY this engine types boolTrue (it is a VALUE,
-- not a type-former). First brick toward non-vacuous bool canonicity (link-4, CANON-1). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_boolTrue
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_boolFalse
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_boolTrue_none
-- NATIVE-07: the two interval endpoints (gen_interval0 / gen_interval1) join the nullary table as data
-- VALUES typed at intervalCode (the bridge dimension's type code, formed by HasTypeDescBaseType per
-- NATIVE-06). The boolTrue/boolFalse template; the values the bridge engine previously typed only at a
-- context-bound interval variable now have a native typing at the fixed intervalCode. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_interval0
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_interval1
-- DATA-INTRO INVERSION + BOOL CANONICAL FORMS (HasTypeDescDataIntroInversion, DI-1/DI-4 inversion slice). The
-- twin of HasTypeDescFlatInversion: inversion = single-arm cases (nullaryIntro context is the auto-index, binds 5);
-- dataIntroNullaryRuleDescOf_isBoolConstructor = the table holds exactly boolTrue/boolFalse. subjectIsBoolConstructor
-- (★) = the closed-canonical-forms content CANON-1 (link-4) consumes: a data-intro-typed subject IS boolTrueCell or
-- boolFalseCell (combined with SN+SR -> closed t:boolCode reduces to a bool value). Cell normalization: cases payload
-- (Unit -> ()) + cases children (RawTermChildren [] -> childNil), rfl each branch. Refines as DI-2/DI-3 add ctors.
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleTableHitIsValueConstructor
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.piCodeDetection_completeOnFormationClassifiers
#assert_no_axioms FX1Poly.Typed.asPiCode?_firesOnFormationClassifiers

/-! ### UNIT-3a — the row-shape-agnostic formation-output interface (staged nullary-row migration)

The strong table fact (`rule = universeFormerOutput`) becomes FALSE when the nullary `unitCode`
formation row lands (its output must IGNORE the floating flag of the nil telescope to preserve
uniqueness).  These interface lemmas state only what consumers NEED — the output is SOME universe
code, rename-stable, subst-stable — true for both row shapes; the ~27 consumer files migrate off
the strong equation one green commit at a time, then the table flips. -/

#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_output_isUniverseCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_output_renameStable
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_output_substStable
-- BASE-TYPE FORMATION ENGINE (HasTypeDescBaseType, #1061 / DI-1b-flagpin): the standalone NULLARY type-FORMER
-- judgment, the FORMATION twin of HasTypeDescDataIntro (which types the VALUES). A new relation (not an arm of
-- HasTypeDescPi), so the grown-engine refutations stay true. The single baseFormation arm + baseTypeRuleDescOf
-- table (boolCode/emptyCode -> Type@0(standard)) PINS the universe flag IN the rule — the fix for the obstruction
-- that blocked routing nullary formers through the generic genFormation arm (a free flag breaks uniqueness, and
-- for emptyCode contradicts emptyTypeCellHasNoTyping / SN-050). boolCodeTyped = Bool:Type@0 (bool-canonicity
-- formation half); emptyCodeTyped = Empty:Type@0 (SN-050 formation half / non-vacuity, the standalone-route
-- concretization of NullaryFormerFormation's parametric target). The typingRuleDescOf_*_none partition witnesses
-- document that the generic table deliberately excludes these (emptyCode's exclusion KEEPS consistency). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_boolCode
#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_emptyCode
#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_natCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_boolCode_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_emptyCode_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_natCode_none
-- BASE-TYPE METATHEORY (HasTypeDescBaseTypeMetatheory, #1062 / DI-1b-meta): inversion + determinism + SR/SN,
-- the DI-4 analogue for the type-FORMER judgment. ★ classifierDetermined = the PROOF the flag-pinning design
-- works (two derivations of one subject reach the SAME classifier — not just Conv, EQUAL — the determinism a
-- free flag would have broken); a propext-free corollary of classifierIsType0 (each pins Type@0 independently,
-- no cases-on-both / mkGen-index unification). subjectIsBaseTypeCode = closed forms (boolTypeCell/emptyTypeCell).
-- subjectHasNoStep/StronglyNormalizing = type codes are no-step normal-form leaves (isStepNormalForm by rfl).
#assert_no_axioms FX1Poly.Typed.baseTypeRuleTableHitIsNullaryBaseCode
#assert_no_axioms FX1Poly.Typed.baseTypeRuleTableOutputIsType0
-- COMBINED BOOL CANONICAL FORMS (CombinedBoolCanonicalForms, CANON-1 #1048): the grown disjunct ruled out for
-- NORMAL subjects, UNCONDITIONALLY (no GrownCtxConv-5 #842, no §5). The grown engine has no closed-normal inhabitant of
-- boolCode: closedNormalSubjectHead gives λ / Π / Σ / universe / list / option, each refuted at boolTypeCell —
-- a λ's classifier is Conv a Π-code (boolTypeCell_not_piTyCode), a former's is Conv a universe code
-- (boolTypeCell_not_universeCode). ★ noClosedNormalTermAtBoolType = the grown vacuity; the 6 *NotTypedAtBoolType
-- are the per-head refutations (boolType twins of *NotTypedAtEmptyType). ★ closedNormalBoolCanonicalForms = the
-- 3-engine combined: a closed-NORMAL term typed at boolCode by ANY engine is boolTrue/boolFalse. Unconditional
-- since the classifier is read only at an already-normal subject (no reduction step typed → no piElim conv arm).
-- Residual for full canonicity: reduce arbitrary closed t to NF preserving the classifier (SN-043 + SR / #842).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.lambdaNotTypedAtBoolType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormerNotTypedAtBoolType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerNotTypedAtBoolType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCodeNotTypedAtBoolType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listFormerNotTypedAtBoolType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.optionFormerNotTypedAtBoolType
-- CLOSED BOOL CANONICITY for an ARBITRARY subject (ClosedBoolCanonicity, the SYNTACTIC route — discharges the
-- residual named in the CombinedBoolCanonicalForms docstring: "reduce arbitrary closed t : boolCode to its NF
-- preserving the classifier (SN-043 + SR)"). Both ingredients now ship: grown SN
-- (HasTypeDescPi.stronglyNormalizingOfWfContextDesc) + the unconditional SR-along-↝* SR-U4
-- (HasTypeDescPi.subjectReductionStar). ★ noClosedGrownTermAtBoolType = the GROWN engine has NO closed bool
-- inhabitant (bool twin of consistency's noClosedTermAtEmptyType — the grown engine types only λ/Π/Σ/formation,
-- never data VALUES). ★ closedBoolCanonicalForms = the 3-engine combined: a closed term typed at boolCode by ANY
-- engine reduces by ↝* to boolTrue/boolFalse, NO `normal` hypothesis, NO §5 candidate bridge. Non-vacuous via the
-- data-intro VALUE disjunct. ELIMINATOR-computing canonicity (boolElim, the 4th engine HasTypeDescDataElim) is the
-- follow-on (needs GTL-18 to fold DataElim into the grown table). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtBoolType
-- GENERIC GROWN-RIGIDITY CANONICITY ENGINE (GrownRigidityCanonicity): lifts #1065's normal-only
-- noClosedNormalTermAtDataClassifier to ARBITRARY subjects, making every data canonicity a per-type one-liner.
-- ★ noClosedGrownTermAtDataClassifier = generic arbitrary-subject grown vacuity (grown SN + SR-U4 + #1065);
-- subsumes noClosedGrownTermAtBoolType. ★ dataCanonicityFromGrownRigidity = generic packaging deriving the grown
-- vacuity from two shipped Conv-rigidities (strengthens dataCanonicityFromSyntacticRoute, which assumed it).
-- boolCanonicityViaGrownRigidity = bool through the engine (non-vacuity). noClosedGrownTermAtSigmaType = the Σ
-- arbitrary-subject grown vacuity (grown half of future Σ-canonicity, arbitrary-subject twin of #1065's
-- normal-only version). Two type families (nullary classifier + binary former) = genuinely generic. SN-049
-- per-type instances now one-liners; eliminator engine (#1138) is the follow-on. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtDataClassifier
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtSigmaType
-- SN-048 NOTE: the zoo-premised closed-Nat-canonicity statements (subjectIsNatNumeral /
-- standaloneNatCanonicalForms / closedNatCanonicalForms) were retired by NATIVE-42; the live deep
-- restatement is HasTypeNativeUnion.closedNormalNatNumeral (AuditNatNumeralUnionCanonicity).
-- ClosedNatCanonicity keeps IsNatNumeral + the natTypeCell cross-former rigidities (gated below
-- with the canonical-forms shard's rigidity block).
-- ARBITRARY-SUBJECT 4-ENGINE BOOL CANONICITY (BoolElimArbitrarySubjectCanonicity): upgrades the closed-normal
-- 4-engine forms OFF the `normal` hypothesis. ★ KEY: the bool-elim engine's branches are GROWN-typed and the
-- grown engine has no closed boolCode inhabitant, so a closed boolElim AT boolTypeCell is impossible by inverting
-- to a branch + noClosedGrownTermAtBoolType — NO SN/SR. ★ noClosedBoolElimAtBoolType = the eliminator vacuity at
-- boolCode (arbitrary subject). ★ closedBoolCanonicalFormsWithElim = the 4-engine arbitrary-subject bool canonicity
-- (DataIntro∨BaseType∨Pi∨BoolElim ⟹ ↝* boolTrue/boolFalse). HONEST FINDING: the current eliminator requires
-- grown branches so it cannot type boolElim b true false : Bool (data-value branches) — eliminator-computing
-- canonicity AT a data type is VACUOUS for it; the non-vacuous version needs a stronger combined intro/elim engine
-- (deferred #1138 / GTL table-residency). Zero-axiom.
-- ★ NON-VACUOUS ELIMINATOR-COMPUTING CANONICITY (BoolElimValueCanonicity): the FIRST canonicity in which the
-- eliminator genuinely COMPUTES (not a vacuity). The four prior firings (45-48) found the eliminator VACUOUS at a
-- data type because the existing HasTypeDescBoolElim has GROWN branches (can't type boolElim b true false : Bool).
-- ★ HasTypeDescBoolElimValue = the bool eliminator INTO Bool with DATA-VALUE branches (data-intro at boolCode), so
-- boolElim b true false : Bool IS typeable. smoke = boolElim(boolTrue,boolTrue,boolFalse) : Bool (non-vacuous
-- typing). boolElimValueTrue/FalseIotaTyped = typed ι-computation (the eliminator fires + the branch stays typed,
-- SR value-case). ★ boolElimValueCanonicity = a closed boolElim b t e : Bool COMPUTES by one ι-step to a bool
-- value (scrutinee is boolTrue/boolFalse, eliminator fires to the selected branch which is a bool value). The
-- principled unification (one combined intro/elim engine for general eliminators with nested-computation branches)
-- remains the deferred GTL table-residency work (#832/#1138). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescBoolElimValue.smoke
#assert_no_axioms FX1Poly.Typed.boolElimValueTrueIotaTyped
#assert_no_axioms FX1Poly.Typed.boolElimValueFalseIotaTyped
-- PAIR INTRODUCTION (HasTypeDescPairIntro, DI-2): the standalone n-ary data-constructor judgment typing the Σ
-- VALUE pair(a,b) : product(A,B) from grown components a:A, b:B — the first non-vacuous Σ-value the kernel types
-- (cascade-free, mirroring HasTypeDescBaseType, NOT an arm of HasTypeDescDataIntro/HasTypeDescPi). pairOfUniverse
-- CodesTyped = the smoke pair(Type@0,Type@0) : product(Type@1,Type@1). subjectIsPair/classifierIsProduct = the
-- SR-free closed-forms inversions (subject is a pairCell, classifier a productTypeCell). The SR/SN quartet is the
-- GrownCtxConv-5-entangled deferral (pair steps when a component steps → consumes grown master SR / #842).
-- EITHER INTRODUCTION (HasTypeDescEitherIntro, DI-2 sum half): the standalone coproduct judgment typing the sum
-- VALUES eitherInl(a) / eitherInr(b) : either(A,B) — each arm has ONE value premise + ONE type-formedness premise
-- for the un-injected (free) component (the asymmetry vs pair, whose two components are both value-pinned).
-- eitherInl/InrOfUniverseCodeTyped = the smokes eitherInl/Inr(Type@0) : either(Type@1,Type@1). subjectIsEither
-- Injection/classifierIsEither = the SR-free closed-forms inversions (subject is an inl/inr cell, classifier an
-- eitherTypeCell). Completes the DI-2 "pair / eitherInl / eitherInr" value-typing scope (SR quartet GrownCtxConv-5-deferred).
-- OPTION INTRODUCTION (HasTypeDescOptionIntro, DI-2c): the standalone option judgment typing the option VALUES
-- optionNone / optionSome(a) : option(A). The optionNone arm carries a type-formedness premise for the FREE
-- element type A (the None asymmetry — None carries no payload, exactly like eitherInl's free un-injected side);
-- the optionSome arm a value premise a:A that PINS A. The scrutinee-typing prerequisite for the option ELIMINATOR
-- (DI-5c, next). optionNone/SomeOfUniverseCodeTyped = the smokes optionNone:option(Type@0) /
-- optionSome(Type@0):option(Type@1). subjectIsOptionConstructor/classifierIsOption = the SR-free closed-forms
-- inversions (subject is a none/some cell, classifier an optionTypeCell). SR quartet GrownCtxConv-5-deferred.
-- BOOL ELIMINATOR + TYPED ι-COMPUTATION (HasTypeDescBoolElim, DI-5 first brick): the kernel's data story from
-- INTRODUCTION to ELIMINATION. The standalone non-dependent boolElim judgment (boolElim(s,t,e):C from scrutinee
-- s:boolCode via data-intro + branches t,e:C via grown). boolElimOfUniverseCodesTyped = the smoke boolElim(boolTrue,
-- Type@0,Type@0):Type@1. subjectIsBoolElim = free-index inversion. ★ boolElimTrue/FalseIotaComputesTyped = the
-- TYPED ι-COMPUTATION: a typed boolElim on a value ι-reduces (Step.iotaBoolTrue/False) to the typed branch — the
-- eliminator COMPUTES and PRESERVES TYPING (constructor-side, so SR-free + propext-free; full SR is the GrownCtxConv-5-gated
-- branch-congruence deferral). Advances DI-5 #1047 (boolElim brick).
-- EITHER ELIMINATOR + TYPED APP-CHAIN ι-COMPUTATION (HasTypeDescEitherMatch, DI-5 second brick): the coproduct
-- eliminator, the FIRST with the app-chain ι shape. boolElim's ι SELECTS a branch (boolElim(boolTrue,t,e) ↝ t);
-- eitherMatch's ι APPLIES the matching handler to the wrapped payload (eitherMatch(eitherInl(v),l,r) ↝ app(l,v),
-- Step.iotaEitherMatchInl), so the branches are FUNCTIONS l:A→C / r:B→C and the reduct is an APPLICATION typed by
-- piElim. The standalone non-dependent judgment (scrutinee:either(A,B) via the either-intro engine + branches at
-- the non-dependent arrows piTyCodeCell A/B (weaken C) via grown). subjectIsEitherMatch = free-index inversion.
-- ★ eitherMatchInl/InrIotaComputesTyped = the typed app-chain ι-computation: a typed eitherMatch on an injection
-- ι-reduces to app(branch, payload), typed at C via piElim with the non-dependent codomain (weaken C).subst0 v
-- collapsing to C (RawTerm.weaken_subst_singleton). Constructor-side, so SR-free + propext-free (full SR is the
-- GrownCtxConv-5-gated branch-congruence deferral). Advances DI-5 #1047 (eitherMatch brick, the second eliminator shape).
-- OPTION ELIMINATOR + the FIRST MIXED-ι typed computation (HasTypeDescOptionMatch, DI-5c): optionMatch is the
-- first eliminator whose two ι rules have DIFFERENT shapes — optionMatch(optionNone,n,sm) ↝ n is branch-SELECTION
-- (boolElim shape, the None branch n is a VALUE at C); optionMatch(optionSome(v),n,sm) ↝ app(sm,v) is APP-CHAIN
-- (eitherMatch shape, the Some branch sm is a FUNCTION A→C). So the judgment carries a value branch (n:C) AND a
-- function branch (sm at piTyCodeCell A (weaken C)), scrutinee:option(A) via the option-intro engine (DI-2c).
-- subjectIsOptionMatch = free-index inversion. ★ optionMatchNoneIotaComputesTyped = the branch-selection typed ι
-- (reduct IS the selected value branch; needs the element-type-formedness witness for the optionNone scrutinee);
-- ★ optionMatchSomeIotaComputesTyped = the app-chain typed ι (reduct app(sm,v):C via piElim + the (weaken C).subst0
-- v → C collapse). Constructor-side, so SR-free + propext-free (full branch-congruence SR GrownCtxConv-5-deferred). ONE
-- eliminator now demonstrates BOTH ι shapes typed-and-computing. Advances DI-5 #1047 (third eliminator brick).
-- Σ-PROJECTION ELIMINATOR + the THIRD ι shape (HasTypeDescSigmaProjection, DI-5d): completes the Σ/pair data story
-- (intro DI-2a + canon DI-2-canon + this elim). fst/snd carry the CONTENT-PROJECTION ι (fst(pair(a,b)) ↝ a;
-- snd(pair(a,b)) ↝ b) — the reduct is a CHILD of the SCRUTINEE, not a branch (boolElim) nor a handler-applied-to-
-- payload (eitherMatch). The SIMPLEST typed ι: the reduct's typing IS one of the pair's component typings directly
-- (no branch, no piElim, no subst0). The 2-arm judgment (scrutinee:product(A,B) via the pair-intro engine → fst:A /
-- snd:B). fstOfUniverseCodesTyped = the smoke fst(pair(Type@0,Type@0)):Type@1. subjectIsSigmaProjection = free-index
-- inversion. ★ fst/sndProjectionIotaComputesTyped = the typed content-projection ι. Constructor-side, SR-free +
-- propext-free (full scrutinee-congruence SR GrownCtxConv-5-deferred). All THREE non-recursive ι shapes now typed-and-
-- computing across the data eliminators. Advances DI-5 #1047 / SN-058 (#446, Σ projections).
-- IDENTITY DATA STORY (HasTypeDescIdIntro DI-2d + HasTypeDescIdElim DI-5e): reflexivity intro + idJ eliminator.
-- INTRO: refl(x):Id(A,x,x) is the PINNED reflexive intro (witness x:A pins A and BOTH endpoints, which are EQUAL).
-- reflOfUniverseCodeTyped = the smoke refl(Type@0):Id(Type@1,Type@0,Type@0). subjectIsRefl + classifierIsReflexiveId
-- = the SR-free inversions (subject is a reflCell, classifier a REFLEXIVE idTypeCell — both endpoints same term).
-- ELIM: gen_idJ carries the Phase-Z spine (motive under two binders, baseCase, witness — shifts [2,0,0]);
-- on refl its ι SELECTS the base case (idJ(m,b,refl(x)) ↝ b, Step.iotaIdJRefl) — the BRANCH-SELECTION shape (the
-- boolElim shape reused on identity). idJOfUniverseCodesTyped = the smoke idJ(Type@0,refl(Type@0)):Type@1.
-- subjectIsIdJ = free-index inversion. ★ idJReflIotaComputesTyped = the typed branch-selection ι (reduct IS the
-- base case, typed verbatim). Constructor-side → SR-free + propext-free (full witness-congruence SR GrownCtxConv-5-deferred).
-- Completes the identity data story (intro + elim). Advances DI-5 #1047 / SN-067/068 (#450, refl + idJ).
-- LIST INTRODUCTION (HasTypeDescListIntro, DI-2e): the FIRST RECURSIVE data constructor. nil:List(A) is the
-- NULLARY-free arm (free element type A, type-formedness premise, like optionNone); cons(h,t):List(A) is the
-- RECURSIVE arm — head h:A (pins A) + tail t:List(A) typed BY THE SAME judgment (the first self-referential
-- standalone data-intro arm, strictly positive). listNilOfUniverseCodeTyped = nil:List(Type@0).
-- listConsOfUniverseCodesTyped = the one-element list cons(Type@0,nil):List(Type@1) EXERCISING the recursive arm
-- (tail nil typed by the same engine). subjectIsListConstructor/classifierIsList = the SR-free closed-forms
-- inversions (subject is a nil/cons cell, classifier a listTypeCell). The scrutinee-typing prerequisite for the
-- list ELIMINATOR (listElim, the first RECURSIVE eliminator, a future brick). SR quartet GrownCtxConv-5-deferred.
-- NAT INTRODUCTION (HasTypeDescNatIntro, DI-3): the nat constructors at the nat type code natTypeCell. natZero:Nat
-- is the NULLARY arm with NO premise (Nat is a closed ground type, simpler than listNil's free element type);
-- natSucc(p):Nat is the RECURSIVE arm — predecessor p:Nat typed BY THE SAME judgment (strictly positive, the nat
-- twin of listConsIntro). natZeroTyped = 0:Nat; natOneTyped = succ 0:Nat (EXERCISING the recursive arm);
-- natTwoTyped = succ(succ 0):Nat (recursion nested twice). subjectIsNatConstructor/classifierIsNat = the SR-free
-- closed-forms inversions (subject a natZero/natSucc cell, classifier natTypeCell). Cascade-free standalone
-- judgment using natTypeCell as a RAW classifier (no Nat:Type@0 base-type-formation dependency). The
-- scrutinee-typing prerequisite for the nat ELIMINATORS (natElim/natRec) + nat canonicity (SN-048). SR quartet
-- engine-separation-deferred (#1078).

-- CAN-1 / DI-5f (HasTypeDescNatElim): the RECURSIVE Nat eliminator judgments + typed recursive
-- ι-computation — the recursive-eliminator wall DI-5 deferred (#1078 engine-separation finding).
-- The succ ι-reduct app(app sb p)(natElim p z sb) is NOT grown-typable (the predecessor is
-- DATA-engine-typed; piElim demands grown arguments), so the judgment carries the reduct shapes as
-- arms: natElimIntro (the cell) + mixedStepApplication (grown step fn × data predecessor : C → C,
-- the cross-engine rule piElim can't express; non-dependent output baked in, no subst0 collapse) +
-- recursiveResultApplication (both parts typed by THIS judgment — recursion in the typing mirrors
-- recursion in the computation).  natRec = the substrate-identical twin.  The ★★ succ theorems are
-- the first typed RECURSIVE ι-computations: typed eliminator + Step.iotaNat{Elim,Rec}Succ + typed
-- reduct with the recursive call typed at the predecessor.  Constructor-side (SR-free,
-- propext-free); full SR of these judgments is CAN-3.  Closed forms are honestly 3-shape
-- (cell OR application) — unlike the single-shape non-recursive DI-5 judgments.

-- CAN-2 / DI-5g (HasTypeDescListElim): the SHAPE-5 recursive List eliminator — closes DI-5
-- (#1047).  The cons ι-reduct is the TRIPLE chain app(app(app cb h) t)(listElim t nb cb); the
-- payload splits across engines (head GROWN-typed per listConsIntro, tail LIST-INTRO-typed), so
-- only ONE new mixed arm is needed: innermost app cb h is plain piElim + weaken_subst_singleton
-- (both grown; the eitherMatch pattern), middle app(app cb h) t is mixedTailApplication (grown
-- partial fn at List(A) → C → C × DATA-engine tail), outer is recursiveResultApplication (both
-- parts typed by the judgment; recursive call typed at the TAIL).  consBranch inhabits the
-- 3-arg curried listStepFunctionType A → List(A) → C → C.  ★★ listElimConsIotaComputesTyped is
-- the deepest typed ι in the kernel.  With CAN-1, EVERY live eliminator family
-- (bool/either/option/Σ/id/nat/list) now has a standalone typed judgment with typed
-- ι-computation.  Constructor-side (SR-free, propext-free); full SR is CAN-3.
-- FLAT-ENGINE INVERSION (#935, first increment): the flat twin of HasTypeDesc.inversionListCode. inversion =
-- generic single-arm cases recovering the flatFormation fields; inversionProductCodeComponents projects the
-- two-child flat telescope (twoChildComponents) to recover both child typings + pins the classifier shape to
-- Type@(lmax [firstLevel,secondLevel]) via the gen_productCode row.
-- FLAT-FORMER FAMILY COMPLETION (#935): the other four flat formers (sum/either/arrow/equiv) TYPE — each a row
-- lemma (rfl) + a formation smoke (the children + premise are former-agnostic, only the generator/row differ),
-- completing the five-former flat-formation corpus alongside the existing productFlatFormationSmoke.
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_sumCode
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_eitherCode
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_arrowCode
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_equivCode
-- FLAT-ENGINE WEAKENING (#937, P6 structural metatheory): the flat twin of HasTypeDescWeakening. The two flat
-- former-table helpers (flatFormationRuleImpliesNotVariable / flatFormationRuleIsUniverseFormer) mirror the
-- cumulative formationRule* helpers. FlatDescTelescope.renameRespectingTelescope is LIGHTER than the cumulative
-- one (flat cons doesn't extend the context, so NO iterateLiftRaw — tail recurses with the SAME context-condition);
-- HasTypeDescFlat.renameRespectingContext reuses it + reconstructs the cell table-generically; weakenUnderBinding
-- instantiates at RawRenaming.weaken (context-condition fun _ => rfl).
#assert_no_axioms FX1Poly.Typed.flatFormationRuleImpliesNotVariable
#assert_no_axioms FX1Poly.Typed.flatFormationRuleIsUniverseFormer
-- FLAT-ENGINE VALIDITY + TELESCOPE AGREEMENT (#939): formation-engine-parity properties.
-- classifierIsTypeDescNative = flat regularity (UNCONDITIONAL — flat has no var arm, classifier always a universe
-- code; lighter than the formation twin which needs WfContextDesc). FlatDescTelescope.uniquenessAgree = two flat
-- telescopes over equal children agree on levels/flag (the uniqueness substrate; flat rest-recursion keeps the
-- SAME context, no WfContextDesc.cons). The uniqueness headline itself is DEFERRED (propext via dependent mkGen
-- second-derivation injection — needs a propext-free flat inversionFormerWithConv analogue).
-- WfContextDefensibleKernel + wfContextDefensibleKernel (#484): the SN-043 WIDENING of the floor from the
-- simply-typed fragment to EVERY well-formed context. SN proven (stronglyNormalizingOfWfContextDesc) + Conv
-- decidable (decidableOfWellTypedInWfContextDesc) with the WF presupposition alone, NO SN and NO SR hypothesis
-- (the milestone-ledger correction: SR is not a decidability ingredient; the joint canonicity apex stays open).
#assert_no_axioms FX1Poly.Typed.WfContextDefensibleKernel
#assert_no_axioms FX1Poly.Typed.wfContextDefensibleKernel

-- SIMPLY-TYPED GENERATION (INVERSION) LEMMAS — the "extract the premises" foundation of subject reduction.
-- SimplyTypedTermLF has no conv arm, so inversions conclude EQUALITIES: a variable's type IS its lookup, an
-- application's type IS the function's arrow codomain, a lambda's type IS a Π-code over a weakened codomain.
-- Proven by the cell-index inversion recipe (generalize subject + thread Eq + headGenerator/noConfusion +
-- injection past the mkGen/childCons index-eqs).  SR-β consumes inversionApplication then inversionLambda.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionVariable
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionApplication
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionLambda

-- DenoteKeyedUniverseFormationMember (route D leaf brick, the denote FT's universeFormation arm): the universe
-- code Type@e is a denote-reducible MEMBER (above denote (lsucc e) env) of its classifier Type@(lsucc e) —
-- the denote-layer no-Type-in-Type at the membership level. Composes universeMembership_levelIrrelevant (the
-- classifier candidate) + isStronglyNormalizing_of_noStep∘noStep_universeCode (SN conjunct) +
-- universeCode_isReducibleAtDenote (reducible-type conjunct); a single anonymous-constructor term, no induction.
#assert_no_axioms FX1Poly.Typed.universeFormationMemberAtDenote
-- universeFormationMemberUnderClosingSubstitution: the FT-shaped universe-formation member arm. The universe
-- codes are closed (childNil) so subst σ is rfl on them; reduces to universeFormationMemberAtDenote. Completes
-- the member-arm-under-subst leaf set (conv / Π-elimination / universeFormation).
#assert_no_axioms FX1Poly.Typed.universeFormationMemberUnderClosingSubstitution

-- sigmaFormationMemberAtDenote (SN-D5d, the Σ case of the genFormationPi denote-FT arm; denote analogue of the
-- fuel IsReducibleMemberAt.sigmaFormationUnderSubst): under a closing substitution, Σ domain. codomain is a
-- denote-reducible MEMBER of its universe Type@levelExpr given its substituted children are SN. The FIRST
-- genFormationPi denote-FT arm closing FULLY (both conjuncts), unconditional — the Σ case carries NO threshold
-- hypothesis exactly because its reducible-as-type half is the FREE neutral arm (smoke_sigmaFormer); SN via the
-- two-child former-SN, packaged by universeMembershipIntroAtDenote. typingRuleDescOf is some only for {Π, Σ},
-- so this + the Π piType arm (the #752 threshold residual) cover the whole 2-case genFormationPi split.
#assert_no_axioms FX1Poly.Typed.sigmaFormationMemberAtDenote
#assert_no_axioms FX1Poly.Typed.sigmaFormationFromChildMembersAtDenote
#assert_no_axioms FX1Poly.Typed.universeFormationMemberAtBounded
#assert_no_axioms FX1Poly.Typed.universeFormationMemberUnderClosingSubstitutionBounded

-- DenoteKeyedPiFormationUnderSubst (the denote FT's Π-formation binder arm, denote #493): from a uniform
-- domain candidate for the substituted domain + the codomain reducible-at-all-levels under the cons-extended
-- substitution (the codomain IH shape), the substituted Π code is denote-reducible. subst distributes over the
-- Π cell by rfl; uniformDomainPi_reducibleFromCodomainExistence + subst_cons_eq_subst0_lift discharge it. The
-- first genuine FT binder arm over the denote relation, choice-free.
#assert_no_axioms FX1Poly.Typed.piFormationUnderClosingSubstitution
-- universeDomainPiFormationUnderClosingSubstitution: the impredicative twin — Π over a closed universe-code
-- domain under a closing substitution. Domain closed (childNil) ⇒ subst leaves it fixed (rfl distribution);
-- routes through universeDomainPi_reducibleFromCodomainExistence + subst_cons_eq_subst0_lift. Completes the
-- binder-arm-under-subst family (uniform/neutral/universe).
#assert_no_axioms FX1Poly.Typed.universeDomainPiFormationUnderClosingSubstitution

-- DenoteKeyedApplicationMember (the denote FT's Π-elimination member arm, the first MEMBER-level arm): a
-- denote-reducible member of Π domainCode codomainCode applied to a denote-reducible member of domainCode is a
-- denote-reducible member of subst0 codomainCode argumentTerm. Reads directly off the piType candidate via
-- piTypeInversion (domain/codomain candidates + application-form PointwiseIff) + deterministic (aligns the
-- argument's candidate with the domain candidate). No backward-closure, no new machinery.
#assert_no_axioms FX1Poly.Typed.applicationMemberAtDenote
-- applicationMemberUnderClosingSubstitution: the FT-shaped elimination arm — substituted function member +
-- substituted argument member ⟹ substituted application is a member of the substituted dependent codomain. subst
-- distributes over app/Π cells by rfl; the dependent result type commutes via RawTerm.subst0_subst_commute into
-- applicationMemberAtDenote's output shape.
#assert_no_axioms FX1Poly.Typed.applicationMemberUnderClosingSubstitution
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectConfluenceOfWfContextDesc
-- SN-052 variable leaf: grown variable inversion (any classifier a variable receives is Conv to its context
-- lookup) — the per-subject UNIQUENESS the COMPARE step consumes at a variable. ofFormation delegates; conv
-- chains via unconditional Conv.trans; piIntro/piElim/genFormationPi impossible on a variable subject.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionVariableGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionVariable
-- SN-052 universe-code leaf: grown universe-code inversion (any classifier a universe code receives is Conv to
-- the next universe) — the per-subject UNIQUENESS the COMPARE step consumes at a universe-code position. Same
-- recipe as the variable inversion with the universe-formation model: ofFormation delegates; conv chains via
-- unconditional Conv.trans; piIntro/piElim/genFormationPi impossible on a universe-code subject.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionUniverseCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionUniverseCode
-- SN-052 application uniqueness ingredient: the COMPARE-step `uniqueAtSubject` at an APPLICATION position,
-- PARAMETERIZED over the function's type uniqueness. Unlike the var/universeCode leaves, an application's type
-- is not unconditionally unique (it inherits the function's non-uniqueness — a bare λ in function position has
-- many Π types); given the function is unique up to Conv, invertApp + Conv.piTyCode_inj + Conv.subst0 push the
-- codomain Conv through the SAME argument to make the dependent output subst0 codomainCode argument unique.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.applicationTypeUniqueGivenFunction
-- SN-052 Π/Σ-FORMATION uniqueness ingredient: the COMPARE-step uniqueAtSubject at a former position,
-- PARAMETERIZED over the components' type uniqueness (a former's type universeCodeCell (lmaxAll [domLevel,
-- codLevel]) flag is pinned by the components' levels/flags; invertPiTyCode/invertSigmaTyCode force both
-- components at the SAME flag, levelFlag_eq_of_conv gives SYNTACTIC level/flag equality, subst aligns the
-- output universe codes). The former analogue of applicationTypeUniqueGivenFunction.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormationTypeUniqueGivenComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormationTypeUniqueGivenComponents
-- SN-055 toward the former-domain SR: re-type a FORMATION codomain under a Conv-stepped domain — the
-- dischargeable half of congPiDomain/congSigmaDomain's codomainReTyping (the common formation-codomain case),
-- UNCONDITIONAL via the part-2a convContextOfFormation + convBackToUniverseCode (no grown-context-conversion
-- bundle). Pointwise context-Conv: index 0 via Conv.rename weaken; successors via Conv.refl.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.formationCodomainReTyping
-- FormationNormalSmoke: a NON-VACUOUS regression for subjectAdmitsNoStep on a concrete closed two-child
-- former — the Π-code Π(Type@0).Type@0, formation-typed via the genFormation arm, provably admits no Step.
-- Exercises the genFormation + telescope arms of the no-step mutual on a real former (not a leaf); the
-- formation-engine analogue of the SN smoke corpora.
#assert_no_axioms FX1Poly.Typed.formationNormalSmoke_piCodeTyped
#assert_no_axioms FX1Poly.Typed.contextValidityPresuppositionFails
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.lamJoinableGuardOfTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.hereditaryLamJoinableOfTyped
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_nullaryFormation_viaGenArm

-- GROWN-ENGINE level strictness (GrownUniverseFormationStrictness.lean, SN-140 L1): the no-Type-in-Type /
-- no-inflation / no-deflation corpus for the LIVE engine HasTypeDescPi (the one carrying piIntro/piElim
-- through which a Type:Type paradox would encode a fixpoint), via HasTypeDescPi.inversionUniverseCode +
-- universeCodeCell_inj_of_conv + the predicativity guards. universeCode_notTypedAtSelf is the §1.4 "Type:Type /
-- Girard's paradox structurally impossible" claim (§27.2 dependent-type known-unsoundness rejection) for the
-- engine that carries the metatheory (SN-043, consistency, safety). In ANY level, ANY context: no Type:Type
-- (e = lsucc e, ne_lsucc_self), no inflation, no deflation (ne_lsuccLsucc_self).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCode_notTypedAtSelf
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCode_notTypedAboveSuccessor
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCode_notTypedBelowSuccessor
-- GROWN-ENGINE dependent-former level strictness (GrownFormerFormationStrictness.lean, SN-140 L1): the Π/Σ analog
-- of the grown universe strictness, for the LIVE engine HasTypeDescPi. A grown Π/Σ-type code is NEVER classified
-- by the bottom universe Type@0 — in ANY context, with ANY components: invertPiTyCode/invertSigmaTyCode expose the
-- true classifier as Conv to Type@(lmaxAll [dL,cL]) = Type@(lmax dL cL) (definitionally), universeCodeCell_inj_of_conv
-- forces lzero = lmax dL cL, refuted by LevelExpr.noConfusion (any context, any components, no level-pinning) —
-- completes the grown formation-family level-strictness (universe + Π + Σ) for the engine that carries
-- SN-043/consistency/safety.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piTyCode_notTypedAtZero
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaTyCode_notTypedAtZero
-- GROWN TYPING NON-UNIQUENESS (GrownTypingNotUnique.lean, metatheory guard / PI-1 spike verdict): the grown
-- engine's lamCell is CURRY-style (domain-free, one child), so piIntro picks the domain freely and the SAME
-- closed identity λ(var 0) types at Π(Type@0).Type@0 AND Π(Type@1).Type@1 (two instances of the shipped
-- closedIdentityLambdaTyping). grownTypingNotUnique exhibits the two non-Conv classifiers — refuted convertible
-- via the SHIPPED Conv.piTyCode_inj (Π-injectivity, a pure raw-confluence corollary, separable from GrownCtxConv-5) +
-- universeCodeCell_inj_of_conv + LevelExpr.ne_lsucc_self. Permanent guard: grown FULL uniqueness is FALSE (so the
-- bidirectional checker is check-mode against a target, not infer-mode); any exact-classifier result must restrict
-- to TYPE-CODE subjects. Confirms reflection conclusion #1 (injectivity is free) and refutes conclusion #2.
#assert_no_axioms FX1Poly.Typed.grownTypingNotUnique

-- GROWN-engine 0-FP honesty (GrownEngineHonesty.lean): the HasTypeDescPi analog of the formation strictness,
-- pinning a classifier's SHAPE from its subject's. A λ inhabits ONLY a Π type (invertLam forces classifier Conv
-- to a piTyCode, refuted against universe/sigma/variable by the conv-rigidity family) — it is not a type, not a
-- pair-typed thing, not a stuck variable. A Π/Σ-type CODE inhabits ONLY a universe (invertPiTyCode/invertSigmaTyCode
-- force classifier Conv to a universe code, refuted against a Π-type classifier). The §1.4 "a function is not a
-- type, a type is not a function" impossibilities at the grown engine.
#assert_no_axioms FX1Poly.Typed.lam_notTypedAtUniverseCode
#assert_no_axioms FX1Poly.Typed.lam_notTypedAtSigmaTyCode

-- Π-introduction (λ) inversion for the GROWN engine (HasTypeDescPiLamInversion.lean, TY-INVN #454). A `lamCell
-- body` typed at `classifier` in HasTypeDescPi has `classifier` Conv to a Π-code, with the domain/codomain grown
-- types at a shared flag and the body typed at the codomain under the domain binder. The grown analogue of the
-- simply-typed `nbda`; the inversion HasTypeDescPi.lean's β-SR docstring names as the gap for fully-general subject
-- reduction. The conv arm re-threads the classifier Conv through the UNCONDITIONAL raw Conv.trans (no toHasType /
-- WfContext needed), so the Conv conjunct survives where the type-code inversions dropped it.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertLamGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertLam

-- Π-elimination (app) inversion for the GROWN engine (HasTypeDescPiAppInversion.lean, TY-INVN #454/#769, dual of
-- invertLam). An `appCell f a` typed at `classifier` has f : piTyCodeCell dom cod, a : dom, and classifier Conv to
-- the dependent output RawTerm.subst0 cod a. The OUTER inversion fully-general β-SR consumes; with invertLam,
-- app(lam b,a):T → f=lam b:Π dom cod, a:dom, T Conv subst0 cod a → invertLam(lam b) → inject Π-Conv → subst lemma.
-- Same subject-generalised recipe; piElim is the match (two-child appCell injection via the nlication drilling),
-- ofFormation/piIntro/genFormationPi refuted, conv re-threads via the unconditional raw Conv.trans.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertAppGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertApp
-- VARIABLE inversion for the grown engine (HasTypeDescPiVarInversion.lean): a variableCell index typed at
-- classifier has Conv classifier (context.lookup index). The spine-re-typing prerequisite for the
-- Abel-reflection neutral-application reconstruction of GrownCtxConv-5 (#842): invertVar on the source typing
-- (Conv classifier (src.lookup j)) + the context-conversion premise (Conv (src.lookup j) (tgt.lookup j)) + the
-- var rule under tgt produces the functionConverted that reassembleApplicationUnderContextConversion (#1092)
-- consumes. Same subject-generalised recipe as invertApp at BOTH engine layers; var is the real case (Conv.refl
-- after the subject injection), conv re-threads via the unconditional Conv.trans, universeFormation/piIntro/
-- piElim refuted by headGenerator clash, genFormation(Pi) by typingRuleDescOf gen_var = none. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.invertVarFormationGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertVarGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertVar

-- Grown-engine congruence-at-typing building blocks (HasTypeDescPiCongruence.lean, the λ/app cong arms of the SR
-- master dispatcher #458, modulo the stepped child's SR). Each takes the child's type-preservation as a HYPOTHESIS
-- (childPreserves : ∀ {S}, … child S → … child' S) — exactly the "preserves ANY classifier" shape Step subject
-- reduction supplies — so they are recursion-free and leak no existential domain/codomain to the caller. congLamBody
-- inverts via invertLam + rebuilds via piIntro; congFunction/congArgument invert via invertApp + rebuild via piElim,
-- with congArgument additionally moving the dependent output (subst0 cod a ⤳ subst0 cod a') by Conv.subst0 over the
-- step's Conv argument argument'. All three close to the original classifier by validity (classifierIsTypeDesc) + conv.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congLamBody
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congFunction
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congArgument

-- Grown-engine FORMER codomain-congruence (HasTypeDescPiFormerCongruence.lean, the Step.cong-into-a-Π/Σ-codomain
-- cases of the SR dispatcher #458/SN-055). piFormationViaGenArm/sigmaFormationViaGenArm are the grown Π/Σ formation
-- INTRODUCTIONS through the generic genFormationPi arm (output universeFormerOutput [domL,codL] reduces to Type@(lmax
-- domL codL) by lmaxAll, no new arm). congPiCodomain/congSigmaCodomain are the codomain SR cong arms (the congLamBody
-- recipe one dimension over): invertPiTyCode/invertSigmaTyCode + reFire + conv. CODOMAIN cong is context-conversion-FREE
-- (cons domain unchanged); the DOMAIN cong (needs context-conversion) is the deferred sibling brick.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormationViaGenArm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormationViaGenArm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congPiCodomain
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congSigmaCodomain

-- Former-DOMAIN congruence SR arms (HasTypeDescPiFormerCongruence.lean, the dual of congPi/SigmaCodomain,
-- completing the cong-arm family for the SR dispatcher #458/SN-055). congPiDomain/congSigmaDomain: stepping a
-- Π/Σ DOMAIN changes the codomain's context binding (cons domain ⤳ cons domain'), so the codomain is re-typed
-- there via an explicit codomainReTyping hypothesis = the head-CONTEXT-CONVERSION (the deferred grown
-- context-conversion / mutual fundamental-metatheory bundle, #814; dischargeable for FORMATION codomains via
-- convContextOfFormation). Mirrors congPiCodomain (invertPiTyCode/invertSigmaTyCode + piFormationViaGenArm + conv).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congPiDomain
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.congSigmaDomain

-- piElimArmUnderWfTarget: the flexible grown context-conversion piElim arm, UNCONDITIONAL under target
-- well-formedness — the FIRST unconditional discharge of the obstruction every prior context-conversion firing left
-- "reduced to the Π-validity residual."  The well-formed-context twin of piElimArmFromValidityRespectsReduction
-- (#1094): same Conv.reducesToPiTyCode + reassembleApplicationFromConvEqualPiValidity, but the global
-- TypeCodeValidityRespectsReduction residual application is replaced by typeValiditySurvivesReductionUnderWf at the
-- (well-formed) target.  It is the IH-consuming piElim CASE of a flexible context-conversion mutual: functionFlexible
-- is NOT a separate recursion — under the target wf it derives from functionConverted via classifierIsTypeDescPi, so a
-- flexible mutual built on this arm needs only the single term-conversion recursion.  Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piElimArmUnderWfTarget
#assert_no_axioms FX1Poly.Typed.smoke_variableTypeIsTypedValid
-- LR-WEAKENING: the boxed typed LR respects context renaming — the genuinely-new proof the lookup lemma needs (a
-- context entry typed at a prefix scope transports to the full scope). renameRespectingContextExists mirrors
-- HasTypeDescPi.renameRespectingContext over the 3 LR arms (existential box): neutral via IsNeutral.rename, universe
-- via rename_universeCodeCell, piType via the lift-ρ codomain recursion + piTypeViaSnCodFamily reassembly (the lift
-- is why a weaken-only statement is insufficient — weakening descends the binder). IsTypeDescPi.renameRespectingContext
-- = the grown-validity rename helper each arm delegates to. weakenUnderBinding = the single-step corollary (ρ=weaken,
-- condition definitional) the lookup threads down a context telescope. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piElimArmFromValidityRespectsReduction

-- GrownCtxConv-5 formation BASE of the validity-respects-reduction residual (same file, GrownCtxConv-5-FORMBASE, toward #842).
-- IsTypeDesc.respectsReductionStar: formation type validity survives reduction UNCONDITIONALLY -- HasTypeDesc
-- .subjectReduction preserves the universe classifier and is itself unconditional (its telescope arm re-types a
-- former's codomain under a stepped domain binder via the UNCONDITIONAL formation convTelescope, the exact move the
-- grown engine cannot make = why GrownCtxConv-5 was then open), iterated along StepStar. validityRespectsReductionOfFormation: the
-- grown corollary (formation-typed type code, S⤳*T ⟹ grown IsTypeDescPi T, via ofFormation). This discharges the
-- grown residual TypeCodeValidityRespectsReduction (#1094) on the FORMATION fragment for free, precisely localizing
-- the then-open part to the type-level-computing (genuinely-grown) type codes -- the logical-relation
-- obligation (since closed unconditionally via SR-U4/SR-U5). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.respectsReductionStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.validityRespectsReductionOfFormation

-- The HEAD-β extension of the unconditional fragment (same file, toward #842). validityRespectsBetaRedex: a β-redex
-- type code (λ.body)(arg)'s validity survives the contraction to subst0 body arg, UNCONDITIONALLY mod WfContextDescPi --
-- a direct wrap of the shipped betaSubjectReduction (substitution lemma + classifierIsTypeDescPi, no logical relation).
-- A β-redex is NOT formation-typed (formation types neither λ nor app), so this lies OUTSIDE #1095's formation fragment:
-- together they form the FULL unconditional fragment of TypeCodeValidityRespectsReduction. The unconditional boundary is
-- precise: a grown type code's only HEAD redex is β (the engine types no type-level eliminators), and head-β is now
-- discharged; everything open is CONGRUENCE into a type-level-computing child = the GrownCtxConv-5 piElim arm / FX
-- logical relation. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.validityRespectsBetaRedex
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertPiTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertSigmaTyCode

-- NO Type:Type — the grown engine is PREDICATIVE (GrownNoTypeInType.lean, §27.2 / SN-140 L1). Girard's paradox
-- needs a self-containing universe (Type@e : Type@e); the grown engine rejects it by ANY derivation route.
-- universeClassifierLevelIsSucc = the predicativity inversion (Type@e : Type@e' forces e' = e+1 ∧ flag' = flag),
-- via the grown universe inversion + universeCodeCell_inj_of_conv. noUniverseInItself specialises at e' = e,
-- refuted by LevelExpr.ne_lsucc_self (e ≠ e+1). noClosedUniverseInItself = the closed permanent witness. The
-- §27.3 L1 Type:Type corpus entry for the grown engine (twin of #442 M35-T1's old-engine no-Type-in-Type probe).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeClassifierLevelIsSucc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noUniverseInItself
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedUniverseInItself
-- universeStrictlyBelowClassifierLevel = the SEMANTIC strict hierarchy: Type@e : Type@e' ⟹ denote e env <
-- denote e' env (every env). Strengthens the syntactic universeClassifierLevelIsSucc (e' = e+1) to the semantic
-- order via denote_lt_lsucc (SN-003). noUniverseInItself is the degenerate e' = e case (level not < itself).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeStrictlyBelowClassifierLevel
-- IsTypeDescDecidable = the concrete-children Π/Σ former-code inversions. The cascade-free
-- IsTypeDesc.decideTypeGeneric below decides formation type-hood, absorbing any future formation row zero-touch.
-- inversionPiCodeChildren/inversionSigmaCodeChildren = WfContext-FREE concrete-children unpacking (vs the
-- WfContext-carrying ...Components and the generic inversionFormerWithConvGeneric, which existentially repack),
-- a reusable inversion API for the dependent type-formers.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeChildren
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeChildren

-- GTL-15 (#829): the INTRODUCTION-rule description table — the intro analogue of the formation
-- `typingRuleDescOf` machinery.  `IntroRuleDesc.outputType` carries the introduced TYPE as rule-DATA
-- (a function of the rule's type-parameters), realizing the §11.8.5 non-uniform-output seam for
-- INTRODUCTION (formation output was a universe code from levels; intro output is a built type).
-- `introRuleDescOf` is the one-row (`gen_lam`) table; the metadata lemmas are the cascade-death
-- substrate mirroring `typingRuleDescOf_outputIsUniverseFormer` / `_isPiOrSigma`; and
-- `hasTypeDescPi_piIntro_viaIntroDesc` is the NON-VACUOUS reconstruction (a real λ types at the
-- rule-data output — the intro twin of `hasTypeDesc_piFormation_viaGenArm`).  Additive: it does NOT
-- modify `HasTypeDescPi` (the engine-level fold of `piIntro` into a generic `genIntro` row is GTL-16).
#assert_no_axioms FX1Poly.Typed.IntroRuleDesc
#assert_no_axioms FX1Poly.Typed.introRuleDescOf
#assert_no_axioms FX1Poly.Typed.introRuleDescOf_lam
#assert_no_axioms FX1Poly.Typed.introRuleDescOf_outputIsPiIntro
#assert_no_axioms FX1Poly.Typed.introRuleDescOf_isLam
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_piIntro_viaIntroDesc
-- GTL-16 dispatch consumer: route an ARBITRARY intro-carrying generator through the table. Generic over the
-- generator (not hardwired to gen_lam), it obtains the generator identity from introRuleDescOf_isLam and routes
-- to the piIntro reconstruction — the cascade-death CONSUMER shape (a new intro row extends the table +
-- introRuleDescOf_isLam by one case, this dispatcher absorbs it with no cascade). The consumer-side brick of
-- the generic genIntro fold; the remaining GTL-16 work is the abstract engine-level genIntro arm. Non-vacuous.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_genIntro_dispatchViaTable

-- GTL-17 (#831): the ELIMINATION-rule description table — the elim twin of IntroRuleDesc (GTL-15).
-- KEY: the eliminator output is CHILDREN-DEPENDENT (`subst0 codomainCode argument` = motive applied to
-- scrutinee), so `ElimRuleDesc.outputType` reads off a CHILD (the argument) — the genuinely-new part of
-- the §11.8.5 non-uniform-output seam that formation (level-output) and introduction (parameter-output)
-- never exercise.  `elimRuleDescOf` is the one-row (`gen_app`) table; the metadata lemmas mirror the
-- intro/formation cascade-death lemmas; `hasTypeDescPi_piElim_viaElimDesc` is the NON-VACUOUS
-- reconstruction (a real application types at the scrutinee-dependent rule-data output).  Additive: it
-- does NOT modify `HasTypeDescPi` (the engine fold of `piElim` into a generic `genElim` row is GTL-18).
#assert_no_axioms FX1Poly.Typed.ElimRuleDesc
#assert_no_axioms FX1Poly.Typed.elimRuleDescOf
#assert_no_axioms FX1Poly.Typed.elimRuleDescOf_app
#assert_no_axioms FX1Poly.Typed.elimRuleDescOf_outputIsPiElim
#assert_no_axioms FX1Poly.Typed.elimRuleDescOf_isApp
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_piElim_viaElimDesc

-- GTL-18 (#1097): the generic ι-computation typing rule — the COMPUTATION half of the elimination story
-- (GTL-17's reconstruction is the introduction half: an eliminator application TYPES at the rule-DATA
-- output).  hasTypeDescPi_genElimIota_viaElimDesc: an eliminator's ι-contractum types at the SAME
-- table-driven output (built by typing the redex via the GTL-17 reconstruction `HasTypeDescPi.piElim`,
-- then carrying the contractum to the same output by the shipped TY-SR-β `betaSubjectReduction` / #474).
-- hasTypeDescPi_genElim_computesTypeStably bundles BOTH the redex and its ι-contractum at the one
-- rule-DATA output — the elimination arm in the exact shape the GTL-20 mutual fundamental-metatheory
-- bundle consumes to discharge the grown context-conversion piElim residual (GrownCtxConv-5 / #842 via GTL-21).
-- Additive: no `HasTypeDescPi` arm; reads the existing engine through the elim table.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_genElimIota_viaElimDesc

-- GTL-19 (#985): the UNIFIED typing-role classifier over the three rule tables (TypingRoleClassifier).
-- typingRoleOf consults typingRuleDescOf (formation) / introRuleDescOf (intro) / elimRuleDescOf (elim) in
-- order; the ROLE-UNIQUENESS core (typingRuleDescOf_excludesIntro / _excludesElim / introRuleDescOf_excludes
-- Elim + the symmetric elimRuleDescOf_excludesIntro) proves the three tables are PAIRWISE DISJOINT — a
-- generator carries at most one typing rule, so its role is unique and the consultation order is immaterial.
-- Each disjointness is the enumeration-lemma (introRuleDescOf_isLam / elimRuleDescOf_isApp) + rfl-reduction of
-- the excluded table to none on the now-concrete former (gen_lam/gen_app are not formation formers, and
-- gen_lam ≠ gen_app). typingRoleOf_{formation,intro,elim}_of are the COMPLETENESS directions (every
-- table-member is classified, the intro/elim directions consuming the disjointness since formation is checked
-- first); typingRoleOf_isNone_iff characterizes the untyped generators (NO role iff in NONE of the tables —
-- the data constructors/eliminators). The substrate a unified GTL-20 fundamental-metatheory bundle + the
-- SN-055 SR master dispatcher route over (which table to consult per generator). All zero-axiom (enumeration
-- + subst + rfl; unfold + if_pos/if_neg over the Option.isSome guards; decide over the structural DecidableEq).
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_excludesIntro
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_excludesElim
#assert_no_axioms FX1Poly.Typed.introRuleDescOf_excludesElim
#assert_no_axioms FX1Poly.Typed.elimRuleDescOf_excludesIntro

-- TypingRoleEngineBridge: the classifier ↔ engine coherence (GTL-ROLE follow-up). subjectHeadHasRoleOrBespoke
-- is the COMPLETENESS of typingRoleOf w.r.t. the engine — every grown-typed subject's head either carries a
-- typingRoleOf role OR is one of the two BESPOKE non-table typed heads (gen_var via the var arm,
-- gen_universeCode via ofFormation∘universeFormation). closedSubjectHeadHasRoleOrIsUniverseCode drops the
-- gen_var disjunct in the empty context (Fin 0 var payload). cellUntypedWhenRolelessAndNonBespoke is the
-- contrapositive — the HONEST untyping criterion: roleless (typingRoleOf = none) AND neither bespoke head ⟹
-- no grown typing (routing typingRoleOf_isNone_iff into the table-generic refutation). The notGenLam/notGenApp
-- helpers convert introNone/elimNone into the head-distinctness the refutation needs. All zero-axiom (rcases on
-- subjectRootGeneratorGeneric + the #985 completeness lemmas; subst + table-rfl + cases on some = none).
#assert_no_axioms FX1Poly.Typed.notGenLam_ofIntroRuleDescNone
#assert_no_axioms FX1Poly.Typed.notGenApp_ofElimRuleDescNone
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectHeadHasRoleOrBespoke
-- TypingRoleCoverage (GTL-19 coverage capstone): the exhaustive FIVE-class head-classification of grown-typed
-- mkGen cells — every typed head is a formation former / intro former / elim former / bespoke gen_var /
-- bespoke gen_universeCode. Resolves the existential role of subjectHeadHasRoleOrBespoke into the three concrete
-- TypingRole ctors and reads the head off the mkGen index (rootGenerator = generator by rfl). The exhaustive-
-- partition coherence headline of the cascade-free extensibility gate (FRAME-2): the 3 rule tables + 2 bespoke
-- arms cover EVERY typed head, so a new former is one new table row, never a partition change. closed* drops
-- the gen_var class in the empty context (Fin 0 var payload) → the four-way closed taxonomy.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.headClassificationExhaustive
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedHeadClassificationExhaustive
#assert_no_axioms FX1Poly.Typed.universeFormationReview_positiveTest
#assert_no_axioms FX1Poly.Typed.universeFormationReview_negativeTest
#assert_no_axioms FX1Poly.Typed.universeFormationReview_metatheoryReProof
#assert_no_axioms FX1Poly.Typed.universeFormationReviewGate
#assert_no_axioms FX1Poly.Typed.universeFormationReviewGate_passes
#assert_no_axioms FX1Poly.Typed.incompleteReviewGate
#assert_no_axioms FX1Poly.Typed.incompleteReview_fails
#assert_no_axioms FX1Poly.Typed.incompleteReview_missingNegativeTest

-- §27.3 Layer-4 defense (SelfVerifiedMetatheory): the bundled self-verified-metatheory layer — preservation +
-- progress as anchored FX theorems, the peer assembly Layers 1/2/3/5 each already had.  Each guarantee
-- ANCHORED (`…_<guarantee> := @<shippedWitness>`).  formationIsUnconditionallySelfVerified (both guarantees
-- unconditional) vs grownIsSelfVerified + grownNotUnconditionallySelfVerified (the honest GrownCtxConv-5 boundary: the
-- grown preservation MASTER `subjectReductionOfGrownTelescopeSR` is telescope-SR-conditional, #842/#845).
-- Non-vacuity: incompleteMetatheory missing progress is NOT self-verified.  Closes SN-143 — five-layer arc
-- L1-L5 now each has a dedicated assembly file.
#assert_no_axioms FX1Poly.Typed.MetatheoryGuarantee
#assert_no_axioms FX1Poly.Typed.MetatheoryGuarantee.describe
#assert_no_axioms FX1Poly.Typed.SelfVerifiedMetatheory
#assert_no_axioms FX1Poly.Typed.SelfVerifiedMetatheory.guaranteed
#assert_no_axioms FX1Poly.Typed.SelfVerifiedMetatheory.isSelfVerified
#assert_no_axioms FX1Poly.Typed.SelfVerifiedMetatheory.isUnconditionallySelfVerified
#assert_no_axioms FX1Poly.Typed.formationMetatheory_preservation
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationOfFormationArm
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationConditionalMaster
#assert_no_axioms FX1Poly.Typed.formationSelfVerifiedMetatheory
#assert_no_axioms FX1Poly.Typed.grownSelfVerifiedMetatheory
#assert_no_axioms FX1Poly.Typed.formationIsUnconditionallySelfVerified
#assert_no_axioms FX1Poly.Typed.grownIsSelfVerified
#assert_no_axioms FX1Poly.Typed.grownNotUnconditionallySelfVerified
#assert_no_axioms FX1Poly.Typed.incompleteMetatheory
#assert_no_axioms FX1Poly.Typed.incompleteMetatheory_notSelfVerified
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piTargetExposure

/- The formation-engine MASTER reflection (FormationPinnedReflection) — UNCONDITIONAL and PIN-FREE:
the formation engine has no piElim, so the full mutual (term + telescope legs) closes with no
residual.  retypeAtUniverse is the telescope-head re-pin move (injective Conv reflection + the conv
rule); renameEqMkGenInversion the non-var subject destructuring; the telescope leg reflects EXACTLY
(exact-image heads at the depth-lifted renaming). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDesc.retypeAtUniverse
#assert_no_axioms FX1Poly.Typed.renameEqMkGenInversion

/- THE CONDITIONAL GROWN MASTER reflection (GrownPinnedReflection): the full pinned reflection over
HasTypeDescPi/DescTelescopePi with ofFormation (pin-free formation master) / conv (re-pin through
the conversion) / piIntro (the brick-6 arm) / genFormationPi (grown telescope leg, heads pinned by
rename-invariant universe codes) all discharged — piElim is the ONE explicit residual
(PinnedReflectionPiElimResidual, the function-Π float, the campaign's open core). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.retypeAtUniverse
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalFunctionIsLambdaOrNeutralOfTyping

/- Enrichment brick E1 (FlagCoherentReflectionCondition): the flag-coherent reflection condition —
per-variable SHARED-universe validity pairs (the Π-pin reassembly's flag-coherence payload),
with the non-circular strengthening base instance (wf-lookup validity + weakening; the
implication-form payload would BE universe-classified strengthening at the root) and the
Kripke extension step. -/

#assert_no_axioms FX1Poly.Typed.SharedUniverseValidityWithImage.toSharedUniverseValidity
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.variableUniverseClassificationUnique

/- Enrichment brick E2.6 (NeutralClassifierUnique): neutral classifier-class uniqueness,
table-generic and UNCONDITIONAL — the generic non-grown-root refutation (one corollary of
subjectRootGeneratorGeneric covering all 10 eliminator neutrals, formation-table-growth-proof),
the var+app spine induction (inversionVariable / invertApp + Π-injectivity + Conv.subst), and
the universe corollary the flag-coherent extraction consumes. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.untypedAtNonGrownRoot
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.neutralClassifierUnique
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.neutralUniverseClassificationUnique

/- E2.7 app-arm closure (NormalAppNeutral): a normal grown-typed application is NEUTRAL (λ
function would be a β-redex), so classifier-class uniqueness extends to all normal apps.
Remaining E2.7 piece: the row-bearing former arm (telescope determinism by child recursion). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalAppIsNeutral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalAppClassifierUnique
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalUniverseClassificationUniqueAtBudget
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalUniverseClassificationUnique

/- E3 capstone (PinSelectsCallerPair): THE flag wall closed — a pinned base's universe pair is
forced to the caller's (forward renaming + Conv-lifted uniqueness), and any ∃-flag pin base
re-types at the caller's EXACT (level, flag).  The λ-reduct Π-components inherit invertLam's
shared flag; piIntro reassembles. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinSelectsCallerPair
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinBaseValidAtCallerPair
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaExpandContractRoundTrip
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_output_eq_outputData
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_formerEnumeration

/-! ### SigmaEtaEngineGate — the Σ-η spike (#361): two engine gates + underivability

The mandated pre-construction spike for Σ-η in the readback.  Machine-checks WHY the quote has
no Σ arm: (1) the scrutinee gate — the Σ-projection engine types only LITERAL-pair scrutinees
(`scrutineeIsLiteralPair`), so `fst(x)` of a variable is untypeable in EVERY engine
(`fstOfVariableHasNoTyping` here + the shipped grown refutations); (2) the chaining gate — even
on literal pairs, `pair(fst p, snd p)` is untypeable because `pairIntro` demands GROWN component
typings while projections are grown-untyped (`componentsGrownTyped` +
`etaPairExpansion_hasNoPairIntroTyping`); the standalone engines do not chain.  CONSEQUENCE:
pair cells are outside the typed judgmental equality's domain entirely
(`pairCellOutsideDomain`), so the Σ-η equation is UNDERIVABLE at every classifier
(`sigmaEtaEquation_underivable`) — engine-gated, not readback-gated.  The module docstring
carries the costed Route A (widen standalone engines, 4 bricks, pending user sign-off per the
T2 precedent) vs Route B (grown-engine cascade, rejected) decision record; these gates are the
regression tripwires the Route-A widening must consciously revisit. -/

#assert_no_axioms FX1Poly.Typed.uniqueness_isZeroArm
#assert_no_axioms FX1Poly.Typed.inversion_isZeroArm

/-! ### FormationTableShapeFacts — generic shape equation + arity bound (GTL-06 brick 3b support)

The two call-site facts of the by_cases-free dispatch refit: `DescTelescope.shiftsShape`
extracts the binder-shifts shape equation GENERICALLY from the premise telescope (levels
induction + telescope cases — retires the per-generator binderShifts_eq rfl lemmas at dispatch
sites), and the arity bound (the ONE table-mirroring fact, five defeq cases) in both the
binder-shifts and levels-length forms via `consecutiveShifts_length`. -/

#assert_no_axioms FX1Poly.Typed.consecutiveShifts_length
#assert_no_axioms FX1Poly.Typed.DescTelescope.shiftsShape
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.shiftsShape
#assert_no_axioms FX1Poly.Typed.formationRowArityBound
#assert_no_axioms FX1Poly.Typed.formationLevelsArityBound
#assert_no_axioms FX1Poly.Typed.formationRowIsNotEmpty
#assert_no_axioms FX1Poly.Typed.formationRowIsNotFlat
#assert_no_axioms FX1Poly.Typed.formationRowNullaryIsUnit
#assert_no_axioms FX1Poly.Typed.DescTelescope.nilAtChildless
#assert_no_axioms FX1Poly.Typed.formationRowOutputLevel

/-! ## NATIVE-44 — the grown flat premise telescope (FlatDescTelescopePi)

The union's `flatFormation` arm states its children premise at the GROWN engine
(`FlatDescTelescopePi`) — the substitution-stable repair for the retired formation-typed
flat telescope (a formation-typed flat child substituted by a grown-typed image loses
formation typability, so the union's grown-image substitution lemma demands the grown
premise).  `FlatDescTelescope.toPi` embeds every subject the retired flat engine typed. -/

#assert_no_axioms FX1Poly.Typed.FlatDescTelescopePi
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.toPi
#assert_no_axioms FX1Poly.Typed.FlatDescTelescopePi.renameRespectingTelescope
#assert_no_axioms FX1Poly.Typed.FlatDescTelescopePi.substRespectingTelescope
#assert_no_axioms FX1Poly.Typed.FlatDescTelescopePi.twoChildComponents
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_boolTrue_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_boolCode_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_emptyCode_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_natCode_none
