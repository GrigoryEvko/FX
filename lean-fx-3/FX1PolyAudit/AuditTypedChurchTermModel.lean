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
import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.HasTypeDescFlatInversion
import FX1Poly.Typed.HasTypeDescFlatSubjectReduction
import FX1Poly.Typed.HasTypeDescFlatStronglyNormalizing
import FX1Poly.Typed.HasTypeDescFlatWeakening
import FX1Poly.Typed.HasTypeDescFlatSubstitution
import FX1Poly.Typed.HasTypeDescFlatValidity
import FX1Poly.Typed.HasTypeDescFlatFormerInversion
import FX1Poly.Typed.HasTypeDescFlatUniqueness
import FX1Poly.Typed.HasTypeDescDataIntro
import FX1Poly.Typed.HasTypeDescDataIntroInversion
import FX1Poly.Typed.HasTypeDescDataIntroMetatheory
import FX1Poly.Typed.HasTypeDescBaseType
import FX1Poly.Typed.HasTypeDescBaseTypeMetatheory
import FX1Poly.Typed.StandaloneEngineCanonicity
import FX1Poly.Typed.CombinedBoolCanonicalForms
import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.CanonicitySyntacticRoute
import FX1Poly.Typed.GrownRigidityCanonicity
import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.BoolElimClosedNormalForms
import FX1Poly.Typed.MatchClosedNormalForms
import FX1Poly.Typed.BoolElimArbitrarySubjectCanonicity
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
import FX1Poly.Typed.HasTypeDescPairIntro
import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Typed.ProductEitherCanonicalForms
import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.HasTypeDescEitherMatch
import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.HasTypeDescOptionMatch
import FX1Poly.Typed.OptionCanonicalForms
import FX1Poly.Typed.HasTypeDescSigmaProjection
import FX1Poly.Typed.HasTypeDescIdIntro
import FX1Poly.Typed.HasTypeDescIdElim
import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.HasTypeDescNatElim
import FX1Poly.Typed.HasTypeDescListElim
import FX1Poly.Typed.DataIntroSubjectReductionRecursive
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
import FX1Poly.Typed.SigmaEtaEngineGate
import FX1Poly.Typed.EliminatorMotiveShapeRecord
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

/-! # FX1PolyAudit/AuditTypedChurchTermModel — typed-layer zero-axiom gates: the Church-encoded term model (booleans, numerals, pairs, sums, lists, SKI)
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.etaExpandedChurchNumeral_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.etaExpandedChurchNumeral_appliedReducesToIterate
#assert_no_axioms FX1Poly.Typed.omegaCombinator_betaSelfStep
#assert_no_axioms FX1Poly.Typed.omegaCombinator_notStronglyNormalizing
-- CHURCH-BOOLEAN ENCODING (TypedChurchBooleans): the formation-only engine proves the data CONSTRUCTORS
-- (boolTrue/boolFalse) untyped, yet the polymorphic Π-fragment TYPES the Church encoding of booleans.
-- churchTrue λA.λt.λf.t and churchFalse λA.λt.λf.f are both typed at Π(A:Type@0).Π(t:A).Π(f:A).A via three
-- nested piIntro over the nested dependent codomain Π(t:A).Π(f:A).A (churchOuterArrow nesting churchInner
-- Arrow, at lmax 0 (lmax 0 0)); churchTrue's body t is the NON-innermost var (deeper de Bruijn lookup than
-- the poly-identity). Both SN via SN-043. The Π-fragment is expressive enough to encode the data it cannot
-- primitively introduce. Zero-axiom: constructor applications + nested lmaxAll threading + var-lookup defeqs.
#assert_no_axioms FX1Poly.Typed.churchInnerArrow
#assert_no_axioms FX1Poly.Typed.churchOuterArrow
#assert_no_axioms FX1Poly.Typed.churchTrue_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchTrue_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.churchFalse_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchFalse_stronglyNormalizing
-- CHURCH-BOOLEAN β-SELECTION (TypedChurchBooleans): beyond typing+SN, the encodings COMPUTE the right branch.
-- Applied to Type@0 and branches Type@0/Type@1, churchTrue β-reduces (3 steps: 2 under app-function congruence
-- + outer β) to the THEN branch Type@0, churchFalse to the ELSE branch Type@1 — DIFFERENT results on identical
-- inputs, so the booleans are computationally distinguished. De Bruijn note: churchFalse's body is the
-- innermost var 0 (substitutes directly, holds symbolically); churchTrue's body is var 1 (threads the subst0
-- lifting fold, only fully computes on concrete args). Zero-axiom: Step.cong/Step.beta chain + StepStar.refl.
#assert_no_axioms FX1Poly.Typed.churchTrue_selectsThenBranch
#assert_no_axioms FX1Poly.Typed.churchFalse_selectsElseBranch
-- CHURCH-BOOLEAN NON-CONVERTIBILITY (TypedChurchBooleans): the computational distinction is also a DEFINITIONAL
-- one. churchTrue ≢ churchFalse, proved NOT through their syntax (the bodies differ only in a de Bruijn index,
-- a propext-risky payload distinction) but through observable behaviour: were they convertible, three layers of
-- app-congruence (Conv.app_cong) plus the selections would force the non-equal universe codes Type@0 ≡ Type@1,
-- refuted because distinct universe levels are distinct no-step normal forms (Conv collapses to Eq via
-- Conv.iff_eq_of_noStep, refuted by the propext-free DecidableEq + decide). The universe-level non-degeneracy
-- churchTypeZeroCode ≢ churchTypeOneCode is the supporting lemma (the Type@e analogue of boolTrue ≢ boolFalse).
#assert_no_axioms FX1Poly.Typed.churchTypeZeroCode_notConvertible_churchTypeOneCode
#assert_no_axioms FX1Poly.Typed.churchTrue_notConvertible_churchFalse
-- CHURCH-NEGATION (TypedChurchNegation): the term model COMPUTES Boolean negation, and negation is an
-- INVOLUTION. churchNot = λb. b A churchFalse churchTrue applies the bound boolean as a selector over the
-- FLIPPED candidate pair. churchNotBody_substitutesToFlippedApplication: the β-contractum reshape — subst0
-- collapses the weakened constants (weaken_subst_singleton) and resolves the head var 0 to the argument.
-- churchTrueOnFlippedBranches_reducesToFalse / churchFalseOnFlippedBranches_reducesToTrue: the flipped
-- selection (concrete closed branches, so churchTrue's non-innermost var 1 body resolves fully through the
-- subst0 fold — the symbolic wall flagged in TypedChurchBooleans does not bite). churchNot_negatesTrue/
-- negatesFalse (★): not true ↝* false, not false ↝* true — one outer β + the selection. churchNot_double
-- NegatesTrue/False (★): not (not b) =Conv b — the double-negation involution, via Conv.app_cong (congruence
-- under application) + Conv.fromStepStar + Conv.trans. Parallel to the session-duality involution dual(dualS)=S,
-- a second self-inverse kernel operation, here by COMPUTATION. Zero-axiom: Step.cong/Step.beta chains closing
-- by StepStar.refl + the conversion-congruence package; no propext/Quot.sound/Classical/sorry.
#assert_no_axioms FX1Poly.Typed.churchNotBody_substitutesToFlippedApplication
#assert_no_axioms FX1Poly.Typed.churchTrueOnFlippedBranches_reducesToFalse
#assert_no_axioms FX1Poly.Typed.churchFalseOnFlippedBranches_reducesToTrue
#assert_no_axioms FX1Poly.Typed.churchNot_negatesTrue
#assert_no_axioms FX1Poly.Typed.churchNot_negatesFalse
#assert_no_axioms FX1Poly.Typed.churchNot_doubleNegatesTrue
#assert_no_axioms FX1Poly.Typed.churchNot_doubleNegatesFalse
-- TypedChurchNumerals (CHURCH-NAT): the Church-NUMERAL encoding typed by the grown engine, extending the
-- booleans to the recursive datum. churchNatArrow/churchNatRest/churchNatCodomain are the arrow-headed
-- formation helpers (the Church Nat type's middle binder is the FUNCTION type A→A, not the variable A — richer
-- than the booleans' all-variable binders). churchNatType_formation: the polymorphic iterator type
-- Π(A:Type@0).Π(f:A→A).Π(x:A).A is well-formed at Type@(lmax 1 (lmax (lmax 0 0)(lmax 0 0))); its code is SN
-- (churchNatType_stronglyNormalizing). churchOne_hasTypeDescPi: λA.λf.λx. f x typed at the Church Nat type —
-- the body f x types by piElim (f's arrow type applied to x), the first Church-encoding whose body USES a bound
-- function (cannot be a re-typed boolean; churchZero is omitted as it shares churchFalse's raw term and would
-- hit uniqueness-of-typing #469). churchOne is SN (churchOne_stronglyNormalizing). All zero-axiom (direct
-- constructor applications + lmaxAll level threading + piElim with the looked-up arrow/var types ascribed to
-- their reduced piTyCode/var forms so the implicit domain/codomain unify).
#assert_no_axioms FX1Poly.Typed.churchNatArrow
#assert_no_axioms FX1Poly.Typed.churchNatRest
#assert_no_axioms FX1Poly.Typed.churchNatCodomain
#assert_no_axioms FX1Poly.Typed.churchNatType_formation
#assert_no_axioms FX1Poly.Typed.churchNatType_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.churchOne_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchOne_stronglyNormalizing
-- TypedChurchNumeralIteration (CHURCH-NAT-2): the Church numerals COMPUTE their iteration. churchOne_applied
-- ReducesToIterate: one A f x β-reduces (3 steps) to f x (the step applied ONCE) — numeral analogue of the
-- boolean β-selection. churchTwo_hasTypeDescPi: two = λA.λf.λx. f (f x) typed at the Church Nat type via a
-- NESTED piElim (outer f applied to the inner f x) — extends churchOne's single piElim; churchTwo SN via
-- SN-043. churchTwo_appliedReducesToIterate: two A f x β-reduces to f (f x) (applied TWICE). So one/two compute
-- distinct iterates (f x vs f (f x)) — the iteration COUNT. (churchZero omitted: its raw term is churchFalse,
-- and grownTypingNotUnique already records the Curry-style non-uniqueness, so churchZero-at-Nat is redundant.)
-- All zero-axiom (StepStar.trans of Step.beta under gen_app congruence; nested piElim with reduced-form
-- ascriptions).
#assert_no_axioms FX1Poly.Typed.churchOne_appliedReducesToIterate
#assert_no_axioms FX1Poly.Typed.churchTwo_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchTwo_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.churchTwo_appliedReducesToIterate
-- TypedChurchNumeralDiscrimination (CHURCH-NAT-DISCRIM): the Church numerals are FAITHFULLY DISTINCT —
-- churchOne ≢ churchTwo — the Nat analogue of churchTrue ≢ churchFalse (#983). Via the COMPUTATIONAL route, not
-- a de Bruijn payload inspection: applied to Type@0/Type@0/Type@1 the numerals reduce (the shipped
-- churchOne/Two_appliedReducesToIterate) to the distinct iterates f x = app(Type@0,Type@1) vs f (f x) =
-- app(Type@0, app(Type@0,Type@1)); churchOneIterate_notConvertible_churchTwoIterate proves those non-convertible
-- (both no-step normal forms via isStepNormalForm_blocks_step on a decide'd normality + Conv.iff_eq_of_noStep +
-- decide — the iterates differ at their SECOND child, distinct root generators, so decide never compares Fin
-- indices, keeping it propext-free). churchOne_notConvertible_churchTwo (★) then forces a contradiction via
-- Conv.app_cong ×3 + the two iteration reductions. So the encoding distinguishes the iteration COUNT 1 from 2.
#assert_no_axioms FX1Poly.Typed.churchOneIterate_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.churchTwoIterate_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.churchOneIterate_notConvertible_churchTwoIterate
#assert_no_axioms FX1Poly.Typed.churchOne_notConvertible_churchTwo
-- TypedChurchNumeralThree (CHURCH-NAT-3): the third numeral + the {1,2,3} pairwise-non-convertibility
-- ANTICHAIN. churchThree = λA.λf.λx. f (f (f x)) typed at the Church Nat type via a TRIPLE-nested piElim (clone
-- of churchTwo's double nesting, the outer f applied to the churchTwo body); SN via SN-043; its iterate
-- reduction three A f x ↝* f (f (f x)) is the same 3-β peel as one/two. churchOne/Two_notConvertible_churchThree
-- by the firing-119 iterate route (the iterates f x / f (f x) / f (f (f x)) are pairwise distinct no-step normal
-- forms — they bottom out in Type@1 vs an application, distinct root generators, so decide is propext-free).
-- churchNumerals_oneTwoThree_pairwiseNotConvertible (★) bundles the 3-antichain — a concrete sample of the
-- general faithfulness (ℕ injects into the term model up to Conv).
#assert_no_axioms FX1Poly.Typed.churchThree_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchThree_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.churchThreeIterate_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.churchThree_appliedReducesToIterate
#assert_no_axioms FX1Poly.Typed.churchOneIterate_notConvertible_churchThreeIterate
#assert_no_axioms FX1Poly.Typed.churchTwoIterate_notConvertible_churchThreeIterate
#assert_no_axioms FX1Poly.Typed.churchOne_notConvertible_churchThree
#assert_no_axioms FX1Poly.Typed.churchTwo_notConvertible_churchThree
#assert_no_axioms FX1Poly.Typed.churchNumerals_oneTwoThree_pairwiseNotConvertible
-- TypedChurchNumeralFaithful (CHURCH-NAT-FAITHFUL-GENERAL): ★ the GENERAL faithfulness — ℕ injects into the FX
-- term model up to Conv. iteratedApplication n stepFn base = f^n base; churchNumeralLambda n = λA.λf.λx. f^n x.
-- churchNumeralLambda_notConvertible_of_ne (★): ∀ m≠n, churchNumeral m ≢ churchNumeral n — uniform in n, no
-- per-numeral case work. ROUTE = the structural SIZE measure (avoids the de-Bruijn-payload decide + childCons
-- drilling): iteratedApplication_isStepNormalForm (a var-headed app is not a β-redex, appCell NF eqn is rfl) ⟹
-- churchNumeralLambda_isStepNormalForm (every numeral is a closed normal form); iteratedApplication_size_var
-- (size = 4n+1, each app adds 4 nodes) ⟹ churchNumeralLambda_size (4n+7); churchNumeralLambda_injective (size
-- injective via Nat.succ.inj ×7 to strip +7 — Nat.add_right_cancel LEAKS propext, avoided — + Nat.eq_of_mul_eq_
-- mul_left, both clean). The headline = Conv.iff_eq_of_noStep on the two normal forms + injectivity. The general
-- construction defeq-specializes to the concrete numerals (churchNumeralLambda_{one,two,three}_eq = rfl), so it
-- SUBSUMES the {1,2,3} antichain (churchNumerals_pairwiseNotConvertible_general).
#assert_no_axioms FX1Poly.Typed.iteratedApplication_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.iteratedApplication_size_var
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_size
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_injective
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_notConvertible_of_ne
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_one_eq
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_two_eq
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_three_eq
#assert_no_axioms FX1Poly.Typed.churchNumerals_pairwiseNotConvertible_general
-- TypedChurchNumeralTyping (CHURCH-NAT-TYPED-GENERAL): the TYPING capstone of the Church arc (complements the
-- faithfulness #1006) — every churchNumeralLambda n is well-typed at the Church Nat type Π(A:Type@0).Π(f:A→A).
-- Π(x:A).A, for ALL n. iteratedApplicationBody_hasTypeDescPi: in [A:Type@0, f:A→A, x:A], iteratedApplication n
-- f x : A (var2) by induction (n=0 = var-x rule; succ = piElim of f:A→A against the IH — the piElim's subst0
-- codomain is A ARGUMENT-INDEPENDENTLY since the arrow codomain A is a free var). churchNumeralLambda_hasType
-- DescPi (★): 3 nested piIntros over churchNatArrow/Rest/Codomain wrapping the iterate body. _stronglyNormalizing
-- via SN-043. churchOneLambda_hasTypeDescPi_viaGeneral = the n=1 instance (churchNumeralLambda 1 = churchOneLambda
-- defeq), so the general typing subsumes the concrete numeral typings.
#assert_no_axioms FX1Poly.Typed.iteratedApplicationBody_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.churchNumeralLambda_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.churchOneLambda_hasTypeDescPi_viaGeneral
-- TypedChurchNumeralInhabitants (CHURCH-NAT-INHABITANTS-INFINITE): ★ the EXPRESSIVENESS capstone — the
-- formation-only Π-fragment's Church Nat type Π(A:Type@0).Π(f:A→A).Π(x:A).A has INFINITELY MANY definitionally-
-- distinct closed inhabitants. churchNatType_hasInfinitelyManyDistinctInhabitants bundles an injective family
-- ℕ→RawTerm 0 (the Church numerals) all typed at ChurchNat (#1007) and pairwise non-convertible (#1006). Plus
-- the reusable iteratedApplication substitution metatheory: subst_iteratedApplication / rename_iteratedApplication
-- (subst/rename distribute over the iterate by induction; the appCell subst/rename equation is rfl) — the
-- substitution backbone for the deferred general iteration computation (#1009).
#assert_no_axioms FX1Poly.Typed.subst_iteratedApplication
#assert_no_axioms FX1Poly.Typed.rename_iteratedApplication
#assert_no_axioms FX1Poly.Typed.churchNatType_hasInfinitelyManyDistinctInhabitants
-- CHURCH-NAT-COMPUTE-GENERAL (TypedChurchNumeralComputeGeneral, #1009 — NO LONGER DEFERRED): the general
-- iteration computation. ★ churchNumeral_appliedReducesToIterate_general: ∀ n, ANY closed typeA/handlerF/baseX,
-- (churchNumeralLambda n) typeA handlerF baseX ↝* iteratedApplication n handlerF baseX (= f^n x) — the iterator
-- iterates its step n times over its base, for an ARBITRARY step+base (subsumes the concrete churchOne/Two/Three
-- fixtures). THREE β-steps, each contractum reshaped via the shipped subst_iteratedApplication (#1008): R1
-- churchNumeral_substType (A-binder discard, A unused), R2 churchNumeral_substStep (f-subst → weaken handlerF), R3
-- iteratedApplication_subst0_weaken_step (the symbolic HEART: subst0 ((weaken f)^n var0) base = f^n base via
-- weaken_subst_singleton + innermost-var). KEY CORRECTION: NO double-weaken (each bound var weakened ≤ once), so it
-- is pure ASSEMBLY over shipped subst metatheory — NOT the "multi-lemma de Bruijn wall" the task was deferred as.
-- iteratedApplication_subst0_weaken_step is the reusable symbolic-heart reshape. All rfl-after-subst_iterated
-- Application / weaken_subst_singleton; zero-axiom.
#assert_no_axioms FX1Poly.Typed.iteratedApplication_subst0_weaken_step
#assert_no_axioms FX1Poly.Typed.churchNumeral_substType
#assert_no_axioms FX1Poly.Typed.churchNumeral_substStep
#assert_no_axioms FX1Poly.Typed.churchNumeral_appliedReducesToIterate_general
-- CHURCH-ADD (#1029): the term model COMPUTES arithmetic. iteratedApplication_add = the arithmetic heart
-- (f^(m+n) x = f^m (f^n x), structural induction + Nat.zero_add/succ_add, both propext-free). Step.appArgCong =
-- the argument-position single-step congruence (StepChildren.there/here). ★ churchAdditionBodyComputes: the
-- Church-addition body m A f (n A f x) ↝* f^(m+n) x for general m,n + symbolic A/f/x — the computational content
-- of Church addition, via the shipped general-compute #1009 twice + StepStar.congAt + the add lemma.
-- churchTwoPlusThreeComputes = the concrete 2+3=5 smoke. Pairs with #1006 (ℕ injects) for adequacy of (ℕ,+).
#assert_no_axioms FX1Poly.Typed.iteratedApplication_add
#assert_no_axioms FX1Poly.Typed.churchAdditionBodyComputes
#assert_no_axioms FX1Poly.Typed.churchTwoPlusThreeComputes
-- CHURCH-MUL (#1030): the term model computes MULTIPLICATION, completing (ℕ,+,×) as a faithful model (with #1006
-- faithfulness + #1029 addition). churchMultiplicationStepIterate = the multiplicative induction (iterating the
-- n-fold step (n A f) outer-many times = f^(outer*n) x, via Step.appArgCong + general-compute #1009 per step +
-- iteratedApplication_add #1029 + Nat.succ_mul/add_comm, all propext-free). ★ churchMultiplicationBodyComputes:
-- m A (n A f) x ↝* f^(m*n) x for general m,n + symbolic A/f/x. churchTwoTimesThreeComputes = the 2*3=6 smoke.
#assert_no_axioms FX1Poly.Typed.churchMultiplicationStepIterate
#assert_no_axioms FX1Poly.Typed.churchMultiplicationBodyComputes
#assert_no_axioms FX1Poly.Typed.churchTwoTimesThreeComputes
-- CHURCH-SEMIRING-LAWS (#1031): the algebraic capstone (§16.6) — the Church-encoded +/× satisfy the commutative-
-- semiring AXIOMS up to definitional equality (Conv = StepStar.Join). Each law = ⟨commonIterate, leftComputes,
-- natLaw ▸ rightComputes⟩: both operation-bodies reduce (via #1029/#1030/#1009) to a common iterate, equated by
-- the corresponding Nat law (add_comm/add_assoc/mul_comm/mul_one/mul_add, all propext-free). Seven axioms:
-- add comm/assoc/zero-identity, mul comm/one-identity/zero-annihilation, ★ left-distributivity. With #1006
-- (numerals distinct) this is the FULL "Church encoding ⊨ commutative semiring (ℕ,+,·,0,1)" both ways.
#assert_no_axioms FX1Poly.Typed.churchAdditionCommutes
#assert_no_axioms FX1Poly.Typed.churchAdditionAssociates
#assert_no_axioms FX1Poly.Typed.churchAddZeroIsIdentity
#assert_no_axioms FX1Poly.Typed.churchMultiplicationCommutes
#assert_no_axioms FX1Poly.Typed.churchMulOneIsIdentity
#assert_no_axioms FX1Poly.Typed.churchMulZeroAnnihilates
#assert_no_axioms FX1Poly.Typed.churchMultiplicationDistributesOverAddition
#assert_no_axioms FX1Poly.Typed.churchIsZeroBody_substitutes
#assert_no_axioms FX1Poly.Typed.churchIsZero_onZero
#assert_no_axioms FX1Poly.Typed.churchIsZero_onSucc
#assert_no_axioms FX1Poly.Typed.churchIsZero_discriminates
-- CHURCH-BOOL-OPS (#1056, TypedChurchBooleanOperations): the term model COMPUTES conjunction and disjunction,
-- completing the Boolean operations (with CHURCH-NOT #1038). churchAnd = λa.λb. a P b churchFalse; churchOr =
-- λa.λb. a P churchTrue b. churchFalseSelectsElse (symbolic, var-0 innermost) / churchTrueSelectsConcrete{True,
-- False} (var-1 needs concrete first branch) are the selection helpers; *Body_subst_a (subst_lift_singleton_
-- weaken_weaken + rfl var resolutions) + *PartialBody_subst_b are the two β reshapes; *_reducesToApplied chains
-- them. ★ THE SYMBOLIC-LEFT-STRICTNESS FINDING: churchOr_trueAnything (or true _ ↝* true) + churchOr_falseAnything
-- (or false b ↝* b) determine OR symbolically by its FIRST arg, while churchAnd_falseAnything (and false _ ↝*
-- false) is symbolic but `and true b` needs CONCRETE b (churchAnd_trueTrue/trueFalse). The asymmetry is
-- structural: churchTrue's body is the non-innermost var 1 (stuck on a symbolic branch), churchFalse's is the
-- innermost var 0 (resolves symbolically), so an op reduces symbolically exactly when the selected branch is the
-- SECOND/else (or false→b, and false→churchFalse) or a CONCRETE first (or true→churchTrue). deMorgan_and_{trueTrue,
-- trueFalse,falseTrue,falseFalse}: ¬(a∧b) =Conv (¬a)∨(¬b) on every truth-table input (both sides compute to the
-- same bool, via Conv.app_cong over the negation reductions). churchAnd_discriminates: and true true ≢ and true
-- false. COMPUTATIONAL not typed (same predicativity wall as CHURCH-ISZERO #1055: ChurchBool : Type@1 can't
-- instantiate the selector's A:Type@0; the type arg is the inert branchMotivePlaceholder). Zero-axiom:
-- Step.beta/cong + StepStar.trans/trans_compose + Conv.app_cong/fromStepStar/trans/sym; no propext/Quot.sound/
-- Classical/sorry/native_decide/omega.
#assert_no_axioms FX1Poly.Typed.churchFalseSelectsElse
#assert_no_axioms FX1Poly.Typed.churchTrueSelectsConcreteTrue
#assert_no_axioms FX1Poly.Typed.churchTrueSelectsConcreteFalse
#assert_no_axioms FX1Poly.Typed.churchAndBody_subst_a
#assert_no_axioms FX1Poly.Typed.churchAndPartialBody_subst_b
#assert_no_axioms FX1Poly.Typed.churchAnd_reducesToApplied
#assert_no_axioms FX1Poly.Typed.churchAnd_falseAnything
#assert_no_axioms FX1Poly.Typed.churchAnd_trueTrue
#assert_no_axioms FX1Poly.Typed.churchAnd_trueFalse
#assert_no_axioms FX1Poly.Typed.churchOrBody_subst_a
#assert_no_axioms FX1Poly.Typed.churchOrPartialBody_subst_b
#assert_no_axioms FX1Poly.Typed.churchOr_reducesToApplied
#assert_no_axioms FX1Poly.Typed.churchOr_trueAnything
#assert_no_axioms FX1Poly.Typed.churchOr_falseAnything
#assert_no_axioms FX1Poly.Typed.deMorgan_and_trueTrue
#assert_no_axioms FX1Poly.Typed.deMorgan_and_trueFalse
#assert_no_axioms FX1Poly.Typed.deMorgan_and_falseTrue
#assert_no_axioms FX1Poly.Typed.deMorgan_and_falseFalse
#assert_no_axioms FX1Poly.Typed.churchAnd_discriminates
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.kCombinator
#assert_no_axioms FX1Poly.Typed.omegaCombinator_notClosedWellTyped
#assert_no_axioms FX1Poly.Typed.typingRulesOutSelfLooping
-- NON-SN BY UNBOUNDED GROWTH (UnboundedGrowthNotStronglyNormalizing): the SECOND archetype of untyped
-- divergence, qualitatively different from Ω's 1-step self-loop. accessibleElementHasNoInfiniteChain is the
-- general well-foundedness fact (sibling of accessibleElementNotSelfRelated, which is its 1-cycle special
-- case) — an Acc element admits no infinite descending chain, via Acc.rec with the shifted tail.
-- notStronglyNormalizing_of_infiniteReduction is its reduction face: ANY infinite Step chain ⟹ ¬SN of the head
-- (the canonical non-SN characterization, reusable). The witness tripler=λx.(x x)x, growingDivergentTerm=
-- (tripler)(tripler) β-reduces to (self) tripler — one application LARGER — so growingReductionSequence strictly
-- grows; growingReductionSequence_steps proves each step (root β index 0 via the nullary-subst defeq that makes
-- Ω's self-step bare Step.beta, function-child congruence index n+1). growingDivergentTerm_notStronglyNormalizing
-- feeds it to the general lemma; growingFirstReduct_ne_source (decide, propext-free RawTermDecEq) shows the
-- reduct DIFFERS from the source — NOT a self-loop, so the general lemma (not accessibleElementNotSelfRelated)
-- is required. nonSelfLoopingDivergenceExists packages the contrast with Ω; both archetypes excluded by SN-043.
#assert_no_axioms FX1Poly.Typed.accessibleElementHasNoInfiniteChain
#assert_no_axioms FX1Poly.Typed.universeNotCumulativeBySkip
-- CURRY FIXPOINT DIVERGENCE (CurryFixpointDivergence): generalize bare Ω (#950/#960) to the Curry fixpoint core
-- Ω_g = (λx. g(xx))(λx. g(xx)) over an arbitrary closed g. curryOmega_step (★): Ω_g ↝ g(Ω_g) in ONE β-step — the
-- fixpoint UNFOLDING (Curry's fix g = g(fix g) at the self-replicating core); contractum via weaken_subst_singleton
-- (the subst0 (weaken g) arg = g cancellation, RawTermSubst0Commute.lean:39) keeping the weakened g + var0 recopy.
-- curryDivergentSequence + _steps: the strictly-growing g^n(Ω_g) chain (index 0 = unfolding, index k+1 = ARGUMENT-
-- position congruence Step.cong .gen_app () + StepChildren.there/here with EXPLICIT parentScope/headShift/restShifts
-- — the scope of `there`'s head is otherwise an unsolvable ?+?=0 metavar). curryOmega_notStronglyNormalizing (★):
-- ∀ g, ¬IsStronglyNormalizing (Ω_g) via notStronglyNormalizing_of_infiniteReduction (#960). Every term carries a
-- non-terminating fixpoint — exactly why a fixpoint operator is untypable in the SN engine (SN-043 #546).
#assert_no_axioms FX1Poly.Typed.curryOmega_step
#assert_no_axioms FX1Poly.Typed.curryDivergentSequence_steps
-- CURRY Y COMBINATOR (CurryFixpointCombinator): the actual fixpoint combinator fix = λf. (λx. f(xx))(λx. f(xx))
-- on the curryOmega substrate (#1013). fixCombinator_applied_step: appCell fix g ↝ Ω_g via Step.beta — the
-- UNDER-BINDER subst0 fixInnerHalf g = curryHalf g computes by RFL (the lifted singleton sends inner de Bruijn 1
-- to weaken g; verified empirically, no lemma needed). fixCombinator_reducesToUnfolding: fix g ↝* g(Ω_g) (2 steps).
-- fixCombinator_isFixpoint (★): Conv (fix g) (g (fix g)) — the DEFINING fixpoint equation, both sides reduce to the
-- common g(Ω_g) (Conv.fromStepStar + trans/sym; right side = 1 argument-congruence Step.cong .gen_app () via
-- StepChildren.there/here). fixCombinator_applied_notStronglyNormalizing: fix g diverges via Acc.inv (SN = Acc of
-- the REVERSED step, so a reduct of an SN term is SN) against #1013. The untyped FX calculus has general recursion
-- (Turing-complete) and every fix g diverges — exactly why typing is indispensable for SN-043 (#546).
#assert_no_axioms FX1Poly.Typed.fixCombinator_applied_step
#assert_no_axioms FX1Poly.Typed.fixCombinator_reducesToUnfolding
#assert_no_axioms FX1Poly.Typed.fixCombinator_isFixpoint
#assert_no_axioms FX1Poly.Typed.fixCombinator_applied_notStronglyNormalizing
-- SKI COMBINATORS (CombinatoryLogic): the combinator basis I=λx.x, K=λx.λy.x, S=λx.λy.λz.(xz)(yz) lives in the
-- λ-fragment. combinator{I,K,S}_stronglyNormalizing: each is a closed step-NORMAL-FORM value ⇒ SN, via
-- isStronglyNormalizing_of_noStep + isStepNormalForm_blocks_step (by decide — CLEAN, isStepNormalForm inspects
-- generators/structure, never Fin indices, so no propext leak). combinatorI_reduces: I a ↝ a (bare Step.beta).
-- combinatorK_reduces: K a b ↝* a — function-position Step.cong .gen_app () β reduces K a → λy.(weaken a) (the
-- under-binder subst0 (λy.x) a = λy.(weaken a) computes by RFL), then outer β + weaken_subst_singleton cancellation.
-- The S-rule (S a b c ↝* ac(bc)) + SKK=I are DEFERRED to #1016 (3-binder nested weakenings). Combinatory logic.
#assert_no_axioms FX1Poly.Typed.combinatorI_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.combinatorK_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.combinatorS_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.combinatorI_reduces
#assert_no_axioms FX1Poly.Typed.combinatorK_reduces
-- COMBINATORY COMPLETENESS (CombinatoryCompleteness): the classic SKK=I. skkReducesToIdentity (★): S K K x ↝* x —
-- S K K x β-reduces through Sa=λy.λz.(Kz)(yz) and Sab=λz.(Kz)(Kz) (intermediate reducts saTerm/sabTerm compute by
-- RFL because K is CONCRETE+closed: the under-binder subst-through-weaken collapses definitionally, where general
-- S a b c would need a weaken/subst commutation lemma), then K x (K x) ↝* x via combinatorK_reduces (#1015). Three
-- Step.beta lifted through function-position Step.cong .gen_app () + StepChildren.here (explicit scopes), chained by
-- StepStar.trans. skkApplied_conv_identityApplied: Conv (S K K x) (I x) — both reduce to x. The GENERAL S-rule
-- (S a b c ↝* ac(bc), symbolic a,b,c) stays deferred (needs subst (lift (singleton b)) (weaken² a) = weaken a, NOT
-- rfl). SKK=I is combinatory completeness in miniature.
#assert_no_axioms FX1Poly.Typed.skkReducesToIdentity
#assert_no_axioms FX1Poly.Typed.combinatorS_reduces
-- CHURCH PAIRS (ChurchPairs): products in the Π-fragment via polymorphism, complementing Church bool (#981)/nat
-- (#989). pairTerm a b = λf. f a b; churchFst = λp. p K; churchSnd = λp. p secondProjector (= λx.λy.y).
-- secondProjector_reduces: (λx.λy.y) a b ↝* b — (λx.λy.y) a discards x → λy.y = I by RFL (x absent from body),
-- then I-rule. pairFst_reduces: fst (pair a b) ↝* a — β to (pair a b) K, β to K a b (symbolic components re-emerge
-- via subst0 (weaken a) K = a, named subst0-typed weaken_subst_singleton cancellation so the rw matches), K-rule
-- #1015. pairSnd_reduces: snd (pair a b) ↝* b (dual). pairProjectionsRecover (★): ∀ a b, fst (pair a b) ↝* a ∧
-- snd (pair a b) ↝* b — the pair faithfully STORES+RECOVERS both components, SYMBOLIC a,b. Products realized in the
-- pure Π-fragment, no primitive Σ.
#assert_no_axioms FX1Poly.Typed.secondProjector_reduces
#assert_no_axioms FX1Poly.Typed.pairFst_reduces
#assert_no_axioms FX1Poly.Typed.pairSnd_reduces
#assert_no_axioms FX1Poly.Typed.pairProjectionsRecover
#assert_no_axioms FX1Poly.Typed.churchNil_isValue
#assert_no_axioms FX1Poly.Typed.churchCons_isValue
#assert_no_axioms FX1Poly.Typed.churchCons_subst_consHandler
#assert_no_axioms FX1Poly.Typed.foldCons
#assert_no_axioms FX1Poly.Typed.foldSingleton
-- CHURCH LIST IS-EMPTY (ChurchListIsEmpty, CHURCH-LIST-ISEMPTY): the FIRST defined OPERATION on Church lists —
-- isEmpty list = fold (λh.λacc. false) true list, the null predicate as a right-fold, connecting the list encoding
-- (#1081/#1082) to the Church BOOLEAN encoding (#981); the list analogue of churchIsZero (#1055). isEmptyHandler_const:
-- isEmptyHandler h acc ↝* false (constant-false handler discards both args — h via #1023 double-weaken collapse, acc via
-- single-weaken). isEmptyNil (★): isEmpty nil ↝* true, directly via foldNil. isEmptyConsNil (★): isEmpty (cons h nil) ↝*
-- false, via foldSingleton then the constant handler. isEmptyDistinguishes (★): ¬ Conv (isEmpty nil) (isEmpty (cons h
-- nil)) — the predicate genuinely separates empty from non-empty (else true ≡ false, refuted by #983). Raw Step/Conv; no
-- typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.isEmptyHandler_const
#assert_no_axioms FX1Poly.Typed.isEmptyNil
#assert_no_axioms FX1Poly.Typed.isEmptyConsNil
#assert_no_axioms FX1Poly.Typed.isEmptyDistinguishes
-- CHURCH LIST ANY (ChurchListAny, CHURCH-LIST-ANY): the disjunction fold any list = fold or false list — "does the
-- list contain a true?", the existential quantifier over a boolean list. Unlike isEmpty (constant handler, sees only
-- SHAPE), the cons-handler is the shipped churchOrLambda (#1056) applied directly, so any inspects element VALUES.
-- anyNil: any nil ↝* false (foldNil). anyConsTrueNil (★): any [true] ↝* true (foldSingleton + churchOr_trueAnything).
-- anyConsFalseNil: any [false] ↝* false (foldSingleton + churchOr_falseAnything). anyConsFalseConsTrueNil (★): any
-- [false,true] ↝* true — the RECURSIVE disjunction at depth 2 (foldCons + StepStar.appArgument-lifted inner fold +
-- churchOr_falseAnything; false ∨ (true ∨ false) = true). anyDistinguishesByContent (★): ¬ Conv (any [true]) (any
-- [false]) — same SHAPE, different CONTENT, distinguished (else true ≡ false, refuted by #983). No new de Bruijn
-- reshape — chains the shipped fold lemmas + shipped OR reductions. Raw Step/Conv; no typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.anyNil
#assert_no_axioms FX1Poly.Typed.anyConsTrueNil
#assert_no_axioms FX1Poly.Typed.anyConsFalseNil
#assert_no_axioms FX1Poly.Typed.anyConsFalseConsTrueNil
#assert_no_axioms FX1Poly.Typed.anyDistinguishesByContent
-- CHURCH LIST ALL (ChurchListAll, CHURCH-LIST-ALL): the conjunction fold all = fold and true — the UNIVERSAL
-- quantifier (∀) over a boolean list, dual to any (∃, #1084). Cons-handler is the shipped churchAndLambda (#1056)
-- applied directly. allNil: all nil ↝* true (vacuous truth, foldNil). allConsTrueNil: all [true] ↝* true
-- (foldSingleton + churchAnd_trueTrue). allConsFalseNil: all [false] ↝* false (foldSingleton + churchAnd_falseAnything).
-- allConsFalseConsTrueNil (★): all [false,true] ↝* false — the FALSE-strict short-circuit (foldCons + churchAnd_-
-- falseAnything, NO tail reduction; dual to any's true-strict short-circuit which DOES reduce the tail).
-- allDistinguishesByContent: ¬ Conv (all [true]) (all [false]). anyAllDifferOnMixed (★): ¬ Conv (any [false,true])
-- (all [false,true]) — ∃ and ∀ are DISTINCT operations (∃→true, ∀→false on the same mixed list; else true≡false,
-- refuted #983). The quantifier-pair completion. No new de Bruijn reshape. Raw Step/Conv; no typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.allNil
#assert_no_axioms FX1Poly.Typed.allConsTrueNil
#assert_no_axioms FX1Poly.Typed.allConsFalseNil
#assert_no_axioms FX1Poly.Typed.allConsFalseConsTrueNil
#assert_no_axioms FX1Poly.Typed.allDistinguishesByContent
#assert_no_axioms FX1Poly.Typed.anyAllDifferOnMixed
-- CHURCH BOOLEAN COMPLEMENT LAWS (ChurchBooleanComplementLaws, CHURCH-BOOL-COMPLEMENT): the orthocomplementation
-- laws completing the Church booleans into a BOOLEAN ALGEBRA — law of NON-CONTRADICTION (b ∧ ¬b ↝* false) + law of
-- EXCLUDED MIDDLE (b ∨ ¬b ↝* true), at both booleans, computed in the term model. The bool analogue of #1031
-- (Church-numeral commutative-semiring laws). No new de Bruijn work — chains shipped negation (#1038) + AND/OR
-- (#1056) reductions via StepStar.appArgument / trans_compose. The proof SHAPES expose the dual short-circuit
-- structure: nonContradiction_true reduces ¬true first (and-true not strict); nonContradiction_false short-circuits
-- (and-false strict); excludedMiddle_true short-circuits (or-true strict); excludedMiddle_false reduces ¬false after
-- (or-false not strict). churchBooleanComplementLaws bundles all four. Raw Step; no typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.nonContradiction_true
#assert_no_axioms FX1Poly.Typed.nonContradiction_false
#assert_no_axioms FX1Poly.Typed.excludedMiddle_true
#assert_no_axioms FX1Poly.Typed.excludedMiddle_false
#assert_no_axioms FX1Poly.Typed.churchBooleanComplementLaws
-- CHURCH XOR (ChurchBoolXor, CHURCH-BOOL-XOR): the exclusive-or, completing the binary Boolean connectives {∧, ∨, ⊕}
-- and demonstrating the Boolean RING GF(2) (⊕ = addition, ∧ = multiplication). xor a b = (a ∨ b) ∧ ¬(a ∧ b),
-- defined from the shipped connectives — NO new λ / de Bruijn reshape (a meta-combination like churchListAny=fold or).
-- The 4-row truth table (false/true/true/false) chains shipped OR/AND/NOT reductions through StepStar.appFunction /
-- appArgument; xorSelfInverse (b ⊕ b ↝* false) is the GF(2) additive self-inverse x+x=0; xorFalseIdentity
-- (b ⊕ false ↝* b) is the additive unit x+0=x; xorDiffersFromAnd / xorDiffersFromOr show ⊕ is a genuinely NEW
-- connective (true⊕true ↝* false while true∧true / true∨true ↝* true), so {∧,∨,⊕} has three distinct members.
-- Conv discriminations via churchTrue_notConvertible_churchFalse (#983). Raw Step/Conv; no typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.xorTrueTrue
#assert_no_axioms FX1Poly.Typed.xorTrueFalse
#assert_no_axioms FX1Poly.Typed.xorFalseTrue
#assert_no_axioms FX1Poly.Typed.xorFalseFalse
#assert_no_axioms FX1Poly.Typed.xorSelfInverse
#assert_no_axioms FX1Poly.Typed.xorFalseIdentity
#assert_no_axioms FX1Poly.Typed.xorDiffersFromAnd
#assert_no_axioms FX1Poly.Typed.xorDiffersFromOr
-- CHURCH LIST FIRSTOR (ChurchListFirstOr, CHURCH-LIST-FIRSTOR): the head accessor — the first list op that PROJECTS
-- a stored ELEMENT out (returns data, not a derived boolean). firstOr d list = fold (λh.λrest. h) d list — the
-- cons-handler returns its FIRST bound argument (head) and DISCARDS the second (tail-fold). firstOrHandler_returnsHead
-- is the new handler shape (projection): β1 reshape is rfl (lift-on-head-index computes to weaken head), outer β cancels
-- the single weaken (forward rw at the hypothesis to avoid over-rewriting the free head). firstOrNil/ConsNil/ConsConsNil
-- compute via foldNil/Singleton/Cons; ConsConsNil is the HEAD-STRICT short-circuit (returns the head WITHOUT reducing
-- the tail). firstOrSeesHead: ¬Conv firstOr[true,x] firstOr[false,x] — separates by HEAD at equal length (where any/all
-- inspect all elements). firstOrDefaultIsFallback: the default fires on nil, a cons overrides it. Discriminations via
-- churchTrue_notConvertible_churchFalse (#983). Raw Step/Conv; no typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.firstOrHandlerInnerSubst
#assert_no_axioms FX1Poly.Typed.firstOrHandler_returnsHead
#assert_no_axioms FX1Poly.Typed.firstOrNil
#assert_no_axioms FX1Poly.Typed.firstOrConsNil
#assert_no_axioms FX1Poly.Typed.firstOrConsConsNil
#assert_no_axioms FX1Poly.Typed.firstOrSeesHead
#assert_no_axioms FX1Poly.Typed.firstOrDefaultIsFallback
-- CHURCH SUCC (ChurchSucc, CHURCH-SUCC): the Church successor churchSucc = λn.λA.λf.λx. f (n A f x) — the missing
-- successor operation on the shipped numerals (#1007/#1009), foundational for numeral-valued computations (a future
-- length : ChurchList → ChurchNat folds with succ). This increment ships the CONSTRUCTOR + value + first β-step:
-- churchSucc_isStepNormalForm (closed value, by decide); succ_step1_reshape (n-binder subst computes by rfl);
-- churchSucc_betaUnfold (churchSucc n ↝ λA.λf.λx. f ((weaken³ n) A f x), the single β exposing the successor
-- abstraction). The fully-applied iteration churchSucc n A f x ↝* f (n A f x) needs the weaken-tower cancellation
-- (weaken³ n → weaken² n → … across the 3 inner β-steps, NOT rfl) and is the next increment. Raw Step; zero-axiom.
#assert_no_axioms FX1Poly.Typed.churchSucc
#assert_no_axioms FX1Poly.Typed.succ_step1_reshape
#assert_no_axioms FX1Poly.Typed.churchSucc_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.churchSucc_betaUnfold
-- CHURCH SUCC APPLIES (ChurchSuccApplies, CHURCH-SUCC-APPLIES): the operational successor — the fully-applied 4-binder
-- reduction churchSucc n A f x ↝* f (n A f x), deferred from #1089. succ_step2/3/4_reshape are the per-binder β-contractum
-- reshapes: each unfolds subst0+body, `show`s the fully-distributed form (subst distributes over appCell/lamCell by rfl,
-- exposing the weaken-tower leaf), then rw's the cancellation lemmas (subst_lift_weaken / subst_lift_singleton_weaken_weaken
-- / weaken_subst_singleton) — the weaken-tower (weaken³ n → weaken² → weaken → ∅) collapses one level per binder.
-- churchSucc_applies chains the 4 β-steps (step1 = the shipped #1089 betaUnfold) lifted through the outer apps via
-- Step.cong .gen_app. churchSucc_iteratesOneMore: churchSucc (numeral d) A f x ↝* f^(d+1) x — succ genuinely implements
-- n↦n+1 on the numerals (via churchSucc_applies + the #1009 iteration). churchSuccZero_appliesToOne: depth-0 smoke. Raw
-- Step; no typing consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.succ_step2_reshape
#assert_no_axioms FX1Poly.Typed.succ_step3_reshape
#assert_no_axioms FX1Poly.Typed.succ_step4_reshape
#assert_no_axioms FX1Poly.Typed.churchSucc_applies
#assert_no_axioms FX1Poly.Typed.churchSucc_iteratesOneMore
#assert_no_axioms FX1Poly.Typed.churchSuccZero_appliesToOne

-- CHURCH LIST LENGTH + PARITY (ChurchListLength, CHURCH-LIST-LENGTH): the list-length fold and its
-- iteration-semantics faithfulness. churchListLength = fold (λhead.λacc. churchSucc acc) churchZero, so a
-- k-element list builds the successor-tower churchSucc^k churchZero (= numeral k). The two reshapes follow the
-- proven succ_step*_reshape idiom (unfold subst0 → show distributed → rw weaken-cancellations → trailing rfl on
-- the variable-leaf substs). lengthConsConsNil lifts the tail-fold through churchSucc· via appArgument.
-- succTowerOneParity/succTowerTwoParity apply a height-k tower to (motive, churchNot, churchTrue): odd height ↦
-- churchFalse, even ↦ churchTrue (the numeral ITERATES churchNot k times). lengthDistinguishesByParity: length
-- [h] and length [h,s], each applied to the parity probe, are non-Conv (false vs true) — length genuinely
-- separates length-parity, via the iteration semantics + #983 churchTrue ≢ churchFalse. Raw Step/Conv; no typing
-- consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.churchZero_applies
#assert_no_axioms FX1Poly.Typed.lengthConsHandlerInnerSubst
#assert_no_axioms FX1Poly.Typed.lengthConsHandlerOuterSubst
#assert_no_axioms FX1Poly.Typed.lengthConsHandler_reduces
#assert_no_axioms FX1Poly.Typed.lengthNil
#assert_no_axioms FX1Poly.Typed.lengthConsNil
#assert_no_axioms FX1Poly.Typed.lengthConsConsNil
