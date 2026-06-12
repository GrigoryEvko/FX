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
import FX1Poly.Typed.HasTypeDescPiSubstPair

/-! # FX1PolyAudit/AuditTypedCellShapeSubstrate — typed-layer zero-axiom gates: the cell builders and rename/subst/shift commutation substrate
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.TypingContext.lookup
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_zero
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_succ

/-! ### HasType engine — type-formation arms (var / conv / universe / Π / Σ) + IsType -/

#assert_no_axioms FX1Poly.Typed.universeCodeCell
#assert_no_axioms FX1Poly.Typed.emptyTypeCell
#assert_no_axioms FX1Poly.Typed.variableCell
#assert_no_axioms FX1Poly.Typed.piTyCodeCell
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell

/-! ### Typed renaming + weakening (the structural cartesian lift) -/

#assert_no_axioms FX1Poly.Typed.rename_variableCell
#assert_no_axioms FX1Poly.Typed.rename_universeCodeCell
#assert_no_axioms FX1Poly.Typed.rename_emptyTypeCell

/-! ### Typed substitution (the β-engine) — `subst0` preserves typing -/

#assert_no_axioms FX1Poly.Typed.subst_variableCell
#assert_no_axioms FX1Poly.Typed.subst_universeCodeCell
#assert_no_axioms FX1Poly.Typed.subst_emptyTypeCell
#assert_no_axioms FX1Poly.Typed.subst_singleton_renameWeaken_cancel
-- PURE STRUCTURAL UNIVERSE-CODE DICHOTOMY: every RawTerm either IS a universe code or provably is NOT one,
-- decided by head-generator inspection (DecidableEq Generator via by_cases, no Classical). The routing primitive
-- the totalBridge assembly (SN-027/#662) consumes: the term arms (TotalBridgeConclusion.var/.piElim) carry
-- a "classifier is not a universe code" hypothesis, discharged for the TERM case while the neutral-TYPE case
-- (type variable / type-family application — the level-flexibility-unsatisfiable subjects) routes to the pinned
-- reclassifier handler. Applied to context.lookup index resp. subst0 codomainCode argument.
#assert_no_axioms FX1Poly.Typed.RawTerm.isUniverseCodeOrNot
-- PURE STRUCTURAL VARIABLE DICHOTOMY: every RawTerm either IS a variable cell or provably is NOT, by
-- head-generator inspection (zero-axiom). The SECOND totalBridge conv-arm router (SN-027/#662): a non-variable
-- type-code reclassifier is level-flexible (re-derives at subjectLevel+1 via convWithLevelFlexibleReclassifier);
-- a variable reclassifier is pinned (validTypingBridgeConvPinnedReclassifier, needs contextLevels index =
-- subjectLevel+1). Separates flexible-former from pinned-variable where isUniverseCodeOrNot cannot.
#assert_no_axioms FX1Poly.Typed.RawTerm.isVariableOrNot
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_noStep_of_childrenNoStep

/-! ### Π-cell rename/subst commutations —
    `rename`/`subst` distribute over a `piTyCodeCell` (domain at shift `0`,
    codomain at shift `1` under `iterateLiftRaw _ 1`), both `rfl` via the
    canonical fold.  The typed-weakening / typed-substitution Π cases
    chain these with the `RawTermSubst0Commute` `iterateLiftRaw` lemmas. -/

#assert_no_axioms FX1Poly.Typed.rename_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_piTyCodeCell

/-! ### Rename lift-weaken commutation — the
    naturality square `lift ρ ∘ weaken = weaken ∘ ρ` at the term level, the
    binder-crossing crux the `piFormation` case of `renameRespectingContext`
    discharges its lifted context-condition with. -/

#assert_no_axioms FX1Poly.Typed.rename_lift_weaken_commute
#assert_no_axioms FX1Poly.Typed.subst_lift_weaken_commute

/-! ### Π-cell size measure — domain and
    codomain are `RawTerm.size`-smaller than the `piTyCodeCell` containing them.
    The `decreasing_by` obligations a well-founded recursive Π-formation decider
    discharges, sidestepping the `RawTerm`/`RawTermChildren` mutual
    `termination_by` boundary gap with a plain `Nat` measure. -/

#assert_no_axioms FX1Poly.Typed.size_lt_piTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_piTyCodeCell_codomain
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_noStep_of_childrenNoStep
#assert_no_axioms FX1Poly.Typed.rename_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_codomain
#assert_no_axioms FX1Poly.Typed.universeFormerOutput
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_binderShiftsNonEmpty
#assert_no_axioms FX1Poly.Core.StepChildrenSuccessor
#assert_no_axioms FX1Poly.Core.accStepChildrenSuccessor_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.weakenUnderBinding

/-! ### DEPENDENT-ELIMINATOR OUTPUT VALIDITY (`HasTypeDescApplication`).  polycell.md §11.8.5
    non-uniform seam: an eliminator's output type is motive-dependent (it instantiates the
    codomain at the eliminated value).  These two lemmas prove the SOUNDNESS HEART of the
    `app`/`snd` rules — that the instantiated codomain is a well-formed type — by composing
    three intrinsic bricks: validity (`classifierIsTypeDesc`), Π/Σ inversion-components, and
    the β-engine `substituteUnderBinding`, feeding the intrinsic substitution into a
    dependent-elimination soundness fact.  POSITIVE construction
    (not a degenerate SR/Conv-stability collapse): `piApplicationOutputIsType` —
    `f : Π A.B`, `a : A` ⊢ `B[a]` IsType; `sigmaProjectionOutputIsType` — the Σ mirror.
    `subst0 (universeCodeCell ..) argument ≡ universeCodeCell ..` by defeq (subst0 reducible +
    subst_universeCodeCell rfl) closes the `IsTypeDesc` witness.  Standalone lemmas, touching
    `HasTypeDesc` ctors not at all. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.piApplicationOutputIsType
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.sigmaProjectionOutputIsType

/-! ### The engine past formation + first non-vacuous subject reduction
    (`HasTypeDescPi`).  polycell.md §11.8.5: 0-FP is FREE BY CONSTRUCTION (intrinsic intro rules
    ⇒ empty fiber over the unsound).  `HasTypeDescPi` ADDITIVELY embeds the formation
    fragment (`ofFormation`) and adds Π-introduction (λ) + Π-elimination (app) + its own `conv`
    — the first engine that expresses β-redexes.  Additive: it leaves `HasTypeDesc`,
    `decidableOfWellFormed`, and the uniqueness proofs untouched (sidesteps the
    decidability/uniqueness cascade a direct `HasTypeDesc` extension would force); `HasTypeDesc`
    cannot type lamCell/appCell (no `typingRuleDescOf` row for gen_lam/gen_app), so `ofFormation`
    of a redex is impossible and the engine genuinely EXTENDS coverage.
    `betaCoherence_formationBody` is the first non-vacuous SR in the kernel: a β-redex
    `app(lam body) arg` and its β-reduct `subst0 body arg` BOTH type at `subst0 codomainCode arg`
    — redex by piElim∘piIntro, reduct by the intrinsic `substituteUnderBinding`.  Scope:
    preservation for component-derived redexes; fully-general inverted SR additionally needs
    Π-arm inversion + grown-engine substitution. -/
#assert_no_axioms FX1Poly.Typed.lamCell
#assert_no_axioms FX1Poly.Typed.appCell
-- η-COHERENCE for formation-component functions (HasTypeDescPiEtaCoherence.lean, PAR-2): the η-twin of
-- betaCoherence_formationBody. From the formation typings of D, C, and f : piTyCodeCell D C, BOTH the η-redex
-- etaLamSource f = λ. (weaken f @ var 0) and its η-reduct f type at the SAME piTyCodeCell D C. Forward build (no
-- inversion / grown strengthening): reduct via ofFormation; redex via piIntro over the formation-embedded D/C with
-- the body weaken f @ var 0 typed by piElim — the weakened function (weakenUnderBinding + rename_piTyCodeCell), the
-- newest var (HasTypeDesc.var + lookup_cons_zero), and the app's result classifier collapsed to C by THE η identity
-- subst0_iterateLiftWeaken_newestVar (the de Bruijn law that makes function η typecheck — composite subst∘rename is
-- pointwise the identity substitution). First step of the grown η-SR arc; fully-general inverted η-SR additionally
-- needs grown strengthening (not yet shipped).
#assert_no_axioms FX1Poly.Typed.RawTerm.subst0_iterateLiftWeaken_newestVar

/-! ### Grown-engine renaming/weakening (P6, the cartesian-lift leg) — `HasTypeDescPiWeakening`.
    polycell.md §11.8.5 P6 applied to the grown engine `HasTypeDescPi`: its cartesian-lift
    fibration leg.  Renaming PRESERVES formation-ness (introduces no eliminations), so the
    `ofFormation` arm delegates directly to `HasTypeDesc.renameRespectingContext` and
    re-wraps — no closure gap (term-substitution does not preserve formation-ness, which is why
    the grown engine carries the native `piFormation` / `genFormationPi` arms).  Self-recursive
    (not mutual): cross-call to the formation renamer on the opaque `formationTyped`; recursions
    on the strictly-smaller `HasTypeDescPi`
    sub-derivations ⇒ structural recursion w/o `termination_by`.  `piIntro` crosses one binder
    (one-binder context-condition via `rename_lift_weaken_commute`); `piElim`'s output commutes by
    `rename_subst0_commute`.  `weakenUnderBinding` is the `fun _ => rfl` corollary.  Additive:
    leaves HasTypeDesc/decidability/uniqueness untouched. -/
#assert_no_axioms FX1Poly.Typed.rename_lamCell
#assert_no_axioms FX1Poly.Typed.rename_appCell
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.weakenUnderBinding

/-! ### GROWN-ENGINE SUBSTITUTION — full leg (the β-engine "whiskering").
    `HasTypeDescPi.substRespectingContext` (mutual with `DescTelescopePi.substRespectingTelescope`)
    carries a GROWN derivation along ANY substitution whose substituents are `HasTypeDescPi`-typed at
    the substituted source bindings — the dual of the renaming `renameRespectingContext` (cartesian
    lift).  Substitution does NOT preserve formation-ness, so its `ofFormation` arm routes through the
    completed `HasTypeDesc.substIntoGrown` (returning a grown derivation) rather than a re-wrap; that
    keeps the recursion within the `HasTypeDescPi`/`DescTelescopePi` family (no cross-inductive
    boundary).  `subst_{lamCell,appCell}` are the rfl distribution bricks; `substContextCondition_cons`
    is the one-binder lifted grown substitution-condition the `piIntro` arm needs.  This is the
    substitution lemma typed β subject reduction consumes. -/
#assert_no_axioms FX1Poly.Typed.subst_lamCell
#assert_no_axioms FX1Poly.Typed.subst_appCell
-- CASCADE-FREE cross-former discrimination (ConvFormationFormerRigidity.lean): the TABLE-GENERIC rigidity —
-- distinct formation-table formers (any two generators with a typingRuleDescOf row) are non-Conv, proven WITHOUT
-- naming a generator (lifts formerCellStepIsChildCongruence/TG-1 through StepStar for head-stability, then
-- congrArg headGenerator on the shared common reduct). The PAYOFF: once a new formation row lands (the
-- gen_boolCode row of DI-1b, cubical/HIT/IR codes), that former AUTOMATICALLY gets all its cross-former
-- rule-outs from this one theorem — the canonicity rule-out substrate made cascade-free. listCode_not_conv_
-- optionCode = a concrete NEW discrimination (not in the per-pair files) as a by-free non-vacuity instance.
#assert_no_axioms FX1Poly.Typed.StepStar.formationFormerHeadStableGeneral
-- FLAT-TABLE twin (ConvFlatFormerRigidity.lean): the SAME cascade-free discrimination keyed on the FLAT table
-- (flatTypingRuleDescOf) for the binary non-dependent data formers product/sum/either/arrow/equiv (typed by the
-- standalone HasTypeDescFlat engine, NOT typingRuleDescOf). Lifts flatFormerCellStepIsChildCongruence instead of
-- formerCellStepIsChildCongruence. Together with the typingRuleDescOf version this gives complete cross-former
-- "no confusion" for every data type-code former — the SN-049 (pair/sum/either canonicity) rule-out substrate.
-- productCode_not_conv_sumCode = a concrete NEW discrimination (A × B is never A + B), by-free non-vacuity.
#assert_no_axioms FX1Poly.Typed.StepStar.flatFormationFormerHeadStableGeneral
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedex_betaStep
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedex_safety
-- EVALUATION DETERMINISM IN ACTION: the redex's UNIQUE normal form is exactly Type@0 (StepStar.single of the
-- β-step reaches it; closedHasUniqueNormalForm — OB-5 SN + raw confluence — forces uniqueness). The concrete
-- computation of an evaluation result through the determinism theorem, the one safety theorem the preceding
-- three witnesses did not exercise.
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedex_evaluation
-- CASCADE-FREE FORMER STEP-INVERSION (FormerStepInversionGeneric.lean, TG-1): a step out of any formation-rule
-- cell (typingRuleDescOf generator = some rule) is a child congruence, proven WITHOUT enumerating the formation
-- table — `cases step` with generator free (propext-clean), each of the 17 root-redex cases refuted because the
-- redex forces generator to a redex head (gen_app / gen_boolElim / ...) whose typingRuleDescOf = none (a
-- permanent table fact no future formation row disturbs). The table-invariant foundation of the cascade-free
-- former metatheory (TG-2 generic former SR + TG-3 cascade-free dispatcher build on it); zero-touch successor to
-- the enumerating former_step_inv.
#assert_no_axioms FX1Poly.Typed.formerCellStepIsChildCongruence
-- FORMATION LOOKUP-VALIDITY (WfContextDescLookup.lean): in a formation-well-formed context every variable's
-- type is a formation type (IsTypeDesc) in the full context — the var-arm engine that lets
-- classifierIsTypeDescNative read its variable case off WfContextDesc. Structural context induction +
-- HasTypeDesc.weakenUnderBinding (the universe code renames to itself). Formation mirror of
-- WfContextDescPi.lookupIsType.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContextDesc.lookupIsTypeDesc
-- GROWN LOOKUP-VALIDITY (WfContextDescPiLookup.lean, WFG-2): in a grown-well-formed context every variable's
-- type is a grown type (IsTypeDescPi). Structural context induction + grown weakening
-- IsTypeDescPi.weakenUnderBinding; the var-arm engine of grown classifier-validity over WfContextDescPi (the
-- master SR dispatcher threads WfContextDescPi, which extends at a grown piIntro binder).
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.lookupIsType
#assert_no_axioms FX1Poly.Typed.identityOnUniverse_noCertifiedCellDim0
#assert_no_axioms FX1Poly.Typed.typedDoesNotFactorThroughCertification
#assert_no_axioms FX1Poly.Typed.lamWithVariableAnnotation_certified
#assert_no_axioms FX1Poly.Typed.substitutedPiTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.substitutedSigmaTyCode_ne_universeCodeCell
-- LEVELED-CONTEXT LOOKUP-AS-TYPE: every entry of a leveled context is a HasTypeDescPi-type at a universe code,
-- in the FULL context (head + each tail entry weakened in via HasTypeDescPi.weakenUnderBinding; the classifier
-- universeCodeCell is rename-invariant). The substrate the term-FT recursor's var/conv arms read to classify
-- each looked-up context variable (supplies the reclassifierIsUniverse premise of the conv bridge arm). Clean
-- leveled-context recursor + propext-clean Fin split, like allLevelsPositive.
#assert_no_axioms FX1Poly.Typed.LeveledContext.lookupTyped
#assert_no_axioms FX1Poly.Typed.selfApplicationBody_noStep
-- Step is NON-DETERMINISTIC, yet the diamond closes (StepNonDeterministic): the concrete witness that raw
-- confluence #420 (Church-Rosser) is NOT vacuous. (λx.boolTrue) ((λy.y) unit) has two DISTINCT one-step reducts
-- — boolTrue (outerStep, head β discards the arg) and (λx.boolTrue) unit (innerStep, the uniform Step.cong rule
-- reducing the argument redex via StepChildren.there) — distinct at the root generator (gen_boolTrue vs gen_app,
-- refuted by Generator.noConfusion∘rootGenerator in outerReduct_ne_innerReduct). YET both →* boolTrue
-- (reachesCommon pair: outer is already normal, inner takes one more β). The headline packages it. This is the
-- complement to the SN/normalization pathologies above: confluence is the non-trivial fact that the genuinely
-- branching single-step relation always reconverges.
#assert_no_axioms FX1Poly.Typed.nondeterministicTerm_outerStep
#assert_no_axioms FX1Poly.Typed.nondeterministicTerm_innerStep
#assert_no_axioms FX1Poly.Typed.outerReduct_ne_innerReduct
#assert_no_axioms FX1Poly.Typed.outerReduct_reachesCommon
#assert_no_axioms FX1Poly.Typed.innerReduct_reachesCommon
#assert_no_axioms FX1Poly.Typed.stepIsNonDeterministicButDiamondCloses
#assert_no_axioms FX1Poly.Typed.ruleTableApplicationOutput_resolvesToUniverse
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables_atResolvedType
#assert_no_axioms FX1Poly.Typed.Step.appArgCong
-- CHURCH-ISZERO (#1055, TypedChurchNumeralIsZero): the term model COMPUTES the first PREDICATE on the Church
-- numerals — isZero, a ChurchNat → ChurchBool decision. churchIsZero = λn. n placeholder (λ_. churchFalse)
-- churchTrue feeds the numeral the constant-false step over the base churchTrue. constFalseStep_appReducesToFalse:
-- the const-false collapse — (λ_. churchFalse) arg ↝ churchFalse (weaken_subst_singleton, the body ignores the
-- argument). churchIsZeroBody_substitutes: the outer β-contractum, three weakened constants cancelled (mirrors
-- CHURCH-NOT). ★ churchIsZero_onZero: isZero (numeral 0) ↝* churchTrue (the empty iterate is the base). ★
-- churchIsZero_onSucc: isZero (numeral (k+1)) ↝* churchFalse for EVERY k — the iteration lemma (#1009) reduces
-- the numeral to (const churchFalse)^(k+1) churchTrue, whose OUTERMOST application collapses to churchFalse in one
-- β-step (inner iterate discarded). churchIsZero_discriminates: the two outputs are non-Conv (churchTrue ≢
-- churchFalse, #983), so the predicate genuinely separates zero from nonzero. Ships as a COMPUTATIONAL result, not
-- a typed one: a typed isZero : ChurchNat → ChurchBool would instantiate the numeral's A:Type@0 binder at
-- A := ChurchBool, but ChurchBool : Type@1 (one universe above), which the predicative non-cumulative engine
-- (UNIV-PREDICATIVE #1012) forbids — the impredicativity System-F Church recursion relies on and FX rejects. The
-- type arg is the inert branchMotivePlaceholder; the predicate is genuinely COMPUTED, only its predicatively-typed
-- packaging is unavailable. Zero-axiom: Step.beta/cong + StepStar.trans/trans_compose + Conv.fromStepStar; no
-- propext/Quot.sound/Classical/sorry/native_decide/omega.
#assert_no_axioms FX1Poly.Typed.constFalseStep_appReducesToFalse
-- the binder-extension key lemma: a renamed term equal to a variable cell WAS a variable cell (lookup
-- weakens its stored type by rename, so the cons-preservation constraint reduces through this inversion).
#assert_no_axioms FX1Poly.Typed.rename_eq_variableCell_inversion
-- the binder-extension PRESERVATION: a consistent stratification stays consistent across a cons (under the
-- local edge condition that a variable domain type sits one level above the fresh head), via the rename-
-- variable inversion + the rfl-closed levelCons_weaken computation over the propext-free Fin-position split.
#assert_no_axioms FX1Poly.Typed.levelCons_weaken
#assert_no_axioms FX1Poly.Typed.ConsistentStratification.cons
-- SN-027 refined-motive PRODUCERS (#656/#657): a type code is LEVEL-FLEXIBLE (valid as a universe member at
-- every positive level) because the ValidTyping formers produce it at ANY predLevel. IsLevelFlexibleTypeCode +
-- the three former arms (universeFormation immediate; pi/sigma given all-level domain + level-flexible codomain)
-- + the connector convWithLevelFlexibleReclassifier wiring a flexible reclassifier into the conv bridge. These
-- are the WITNESSES validTypingBridgeConvFromAllLevelReclassifier's reclassifierAllLevel premise consumes.
#assert_no_axioms FX1Poly.Typed.IsLevelFlexibleTypeCode

/-! ### FORMATION-ARM BRIDGE: membership at a universe-code classifier ⟺ strong normalization.
    A universe code is a normal leaf (`noStep_universeCode`), hence neutral, so the dependent
    reducibility relation assigns it the SN candidate and `IsReducibleMember (universeCodeCell ..) t ↔
    IsStronglyNormalizing t` (via the Core `IsReducibleMember.atNeutralClassifier`).  This is the
    fundamental theorem's formation/universe arm bridge between a well-formed type term and its SN. -/
#assert_no_axioms FX1Poly.Typed.universeCodeCell_noWeakHeadStep
-- Telescope REACH (DescTelescopeReach): a formation telescope forces its children's binderShifts to be the
-- cumulative sequence [depth, depth+1, ...] (structural recursion over the mutual telescope). Consequence:
-- the non-dependent [0,0] type-code formers (product/sum/either/arrow/equiv) are OUTSIDE genFormation's reach
-- (noFlatTwoChildTelescope / productCodeFormationTelescopeImpossible) — they need a flat-telescope
-- generalization, not a listCode-style row addition. cumulativeShifts_length via Nat induction; the [0,0]
-- refutation via plain List injection + Nat.noConfusion (no indexed-cases propext leak).
#assert_no_axioms FX1Poly.Typed.cumulativeShifts_length
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectIsNullaryValueCell
-- DATA-INTRO SR + SN METATHEORY (HasTypeDescDataIntroMetatheory, DI-4 substantive half). subjectHasNoStep =
-- the shared substrate: a data-intro subject blocks every Step (it is a bool value -> normal form, via
-- subjectIsBoolConstructor =def boolIsValue + boolIsValue_impliesStepNormalForm + isStepNormalForm_blocks_step).
-- subjectReduction = SR (vacuous: a value has no reduct). subjectStronglyNormalizing (★) = SN via
-- isStronglyNormalizing_of_noStep (a closed data-intro-typed term is a normal-form value — the canonicity fact).
-- classifierIsBoolTypeCell = the classifier twin of subjectIsBoolConstructor (Option.some.inj recovers the rule).
-- Weakening/subst are DEGENERATE here (closed variable-free subjects) -> folded into DI-2's open n-ary subjects.
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.classifierIsNullaryTypeCell

/-! ### TypeDirectedUnitReadback — the #481 η-long readback, unit + Π + recursive-spine fragment

The classifier flows TOP-DOWN: at `unitTypeCell` the readback is constantly `unitCell`; at a
literal Π over ANY λ it descends with the codomain classifier, emitting the CLASSIFIER's domain
(trust-the-classifier, brick 7 — outputs are annotation-canonical; soundness re-types the body
across the binder via `contextConversionExact` and routes the witness by `trans`); at a literal
Π over a NON-λ subject it η-EXPANDS (#360 — `λ(D, readback(app(weaken t, var₀)) at C)`, so η
and unit-η COMPOSE); at any other classifier it delegates to the MUTUAL recursive neutral-spine
readback
`readbackSpine` (the NbE `quoteNeutral`, brick 6): var-headed applications read the argument
back at the looked-up domain, app-headed function positions recurse into the head (this level's
argument deep-collapses — its classifier is a substituted code, the mapped soundness wall);
everywhere else and at fuel 0 the unconditionally sound deep collapse.
`readbackAtClassifier_congruent` is the typed soundness under the NbE presuppositions
(formation-wf context + subject grown-typed + classifier FORMATION-typed); the mutual
`readbackSpine_congruent` needs NO classifier hypothesis — the var arm recovers it from the wf
lookup, the app-headed arm needs only `invertApp` (the spine stays at the SAME context), so
spine soundness covers EVERY depth.  Decided through this ONE procedure: all five refutation
boundary pairs, THE η pair, the mixed η+unit pair, the 6th-boundary argument pair, and the
8th-boundary depth-2 spines.  Honest gaps: data-intro-typed subjects, Conv-not-literal Π
classifiers, Σ (#361), modal/cubical η (#363), former children (engine-gated).  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.asLamCell?
#assert_no_axioms FX1Poly.Typed.asLamCell?_sound
#assert_no_axioms FX1Poly.Typed.asAppCell?
#assert_no_axioms FX1Poly.Typed.asAppCell?_sound
#assert_no_axioms FX1Poly.Typed.asVarCell?
#assert_no_axioms FX1Poly.Typed.asVarCell?_sound
#assert_no_axioms FX1Poly.Typed.annotationPiCodes_oneStepApart
#assert_no_axioms FX1Poly.Typed.annotatedByRedexTyped
#assert_no_axioms FX1Poly.Typed.annotatedByLiteralTyped
#assert_no_axioms FX1Poly.Typed.annotationLambdas_oneStepApart
#assert_no_axioms FX1Poly.Typed.annotationPair_congruentlyEqual
#assert_no_axioms FX1Poly.Typed.asPiCode?_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.WfContextDesc.piCodeDetection_completeOnLookups
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.constNatZeroBranchProduces
#assert_no_axioms FX1Poly.Typed.copyNatBranch_substitutedReduct_eq
-- Native natElim computes binary ADDITION FAITHFULLY (NatElimFaithfulArithmetic): sharpens "computes to A
-- numeral" to the EXACT result — natElim(motive, numeral base, copyNatBranch, numeral n) ↝* numeral (base+n),
-- agreeing with the host's Nat addition. natNumeralCell is the reusable native numeral builder; the proof is
-- structural recursion on the scrutinee composing the Phase-Z SUBSTITUTING succ-iota (no β-step — the recursive
-- call lands in var 0 directly) with the natSuccArgument congruence (Nat.add_zero / Nat.add_succ are defeq).
#assert_no_axioms FX1Poly.Typed.natNumeralCell
#assert_no_axioms FX1Poly.Typed.natNumeralCell_isNumeral
#assert_no_axioms FX1Poly.Typed.natNumeralAt_zero_eq_natNumeralCell
-- ★ NatElimFaithfulMul (HON-13): native gen_natElim computes EXACT host Nat.mul, completing the recursor
-- faithfulness (Nat.add was natElimAddFaithful). mulNatBranch m = natElim(_, var 0, copyNatBranchAt,
-- numeralAt m) embeds the adder recursor in the two-binder succ branch (var 0 = the threaded accumulator);
-- mulBranchSubstitutedTarget names the inner adder the Phase-Z succ-iota substitution lands at. CONDITIONAL on
-- the mulStepReduces premise (the 2-variable subst-commutation through the embedded closed numeral — discharged
-- by the typed substPair lemma, tracked follow-up). natElimMulFaithful = structural recursion on n reusing
-- natElimAddFaithful as the per-step adder (m·n + m = m·(n+1) defeq via Nat.mul_succ).
-- Fin bounds use Nat.succ_pos _ (NOT omega, which leaks propext). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.copyNatBranchAt
#assert_no_axioms FX1Poly.Typed.copyNatBranchAt_zero
#assert_no_axioms FX1Poly.Typed.mulNatBranch
#assert_no_axioms FX1Poly.Typed.mulBranchSubstitutedTarget
-- ★ The typed 2-VARIABLE substitution lemma (HasTypeDescPiSubstPair): substPairUnderTwoBindings is
-- substRespectingContext instantiated at cons innerArg (singleton outerArg) — the Phase-Z substPair lemma the
-- natElim/natRec migration flagged; substPairNonDependent is the recursor-step shape (twice-weakened result
-- type, both weakenings cancel). mulNatBranch_substituted computes the 2-variable subst through the mul branch
-- (children by cons/singleton/lift var-equations, embedded numeral by natNumeralAt_subst), mulStepReduces_proved
-- discharges natElimMulFaithful's premise, and natElimMulFaithful.unconditional makes native-natElim-computes-
-- host-Nat.mul UNCONDITIONAL (closes the HON-13 conditional flag). The iota-instance reductTyped premise of
-- natElimSuccIotaComputesTyped stays honestly conditional: its inner substituent is the recursive natElimCell,
-- which the grown engine deliberately does not type — the union-engine follow-on. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substPairUnderTwoBindings
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substPairNonDependent
#assert_no_axioms FX1Poly.Typed.mulNatBranch_substituted
#assert_no_axioms FX1Poly.Typed.mulStepReduces_proved
#assert_no_axioms FX1Poly.Typed.natElimMulFaithful.unconditional
#assert_no_axioms FX1Poly.Typed.natElimMulFaithful.threeTimesTwoUnconditional
#assert_no_axioms FX1Poly.Typed.constNatZeroStep3Produces
#assert_no_axioms FX1Poly.Typed.lengthNatStepProduces
-- ★ VALUE-CASE eliminator HOST-FOLD faithfulness (ValueElimHostFold, HON-14): completes the faithfulness coverage
-- begun by the RECURSIVE eliminators (natElim=Nat.mul HON-13, listElim=List.length HON-12). Each non-recursive
-- eliminator, run on the raw cell of a HOST value, reduces to EXACTLY what the corresponding host eliminator
-- computes: boolElim ↝ cond (Bool.rec), fst/snd ↝ Prod.fst/Prod.snd, optionMatch ↝ Option.elim, eitherMatch ↝
-- Sum.elim, idJ ↝ Eq.rec-on-rfl. Each is `cases` on the host scrutinee then StepStar.single of the matching
-- Step.iota rule, whose reduct is the host fold's branch by rfl. The deepest "the cell truthfully encodes its
-- mathematical meaning" of the honesty arc — every native eliminator computes its named host fold. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.rawBoolCell
#assert_no_axioms FX1Poly.Typed.rawOptionCell
#assert_no_axioms FX1Poly.Typed.rawEitherCell
#assert_no_axioms FX1Poly.Typed.boolElimHostFold
#assert_no_axioms FX1Poly.Typed.fstHostFold
#assert_no_axioms FX1Poly.Typed.sndHostFold
#assert_no_axioms FX1Poly.Typed.optionMatchHostFold
#assert_no_axioms FX1Poly.Typed.eitherMatchHostFold
#assert_no_axioms FX1Poly.Typed.idJHostFold
#assert_no_axioms FX1Poly.Typed.boolElimHostFold.selectsThen
#assert_no_axioms FX1Poly.Typed.optionMatchHostFold.firesSome
-- ★ RECURSOR host-folds (RecursorHostFold): the LAST two of the ten data eliminators — natRec, idStrictRec —
-- compute their host folds, completing per-eliminator host-fold faithfulness to all ten (value-case six +
-- natElim=Nat.mul + listElim=List.length + these two). natRec on natZero/natSucc computes the host Nat.rec
-- defining clauses (base/successor); idStrictRec on refl computes the host strict Eq.rec base (twin of idJ).
-- Each is StepStar.single of the matching Step.iota rule. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.natRecCell
#assert_no_axioms FX1Poly.Typed.idStrictRecCell
#assert_no_axioms FX1Poly.Typed.natRecZeroHostFold
#assert_no_axioms FX1Poly.Typed.natRecSuccHostFold
#assert_no_axioms FX1Poly.Typed.idStrictRecHostFold
-- FLAT-ENGINE SUBJECT REDUCTION (#935, next increment): the flat twin of HasTypeDesc.subjectReduction.
-- flatFormerCellStepIsChildCongruence = the flat-former cell heads no root redex (18-arm cases keyed on
-- flatTypingRuleDescOf, every redex arm contradicted by some-rule ≠ none); FlatDescTelescope.subjectReduction
-- re-types the premise under stepped children (simpler than the cumulative one — flat cons doesn't extend the
-- context, so no convTelescope); HasTypeDescFlat.subjectReduction rebuilds flatFormation at the unchanged
-- classifier (a child step touches neither generator nor levels).
#assert_no_axioms FX1Poly.Typed.flatFormerCellStepIsChildCongruence
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.weakenUnderBinding
-- FLAT FORMER INVERSION + UNIQUENESS: the propext-free generic flat-former inversion (telescope + classifier
-- Conv). flatFormerBinderShifts = flat former arity [0,0]. inversionFormerWithConv aligns the generator via
-- congrArg headGenerator + subst BEFORE injection (cracked-wall idiom), avoiding the dependent-mkGen propext leak.
-- HasTypeDescFlat.uniquenessNative is the flat-engine typing-uniqueness headline: a clean free-index cases on the
-- first derivation exposes the .mkGen subject, the second derivation is inverted propext-free by
-- inversionFormerWithConv, and FlatDescTelescope.uniquenessAgree settles levels (and flag, via the two-child
-- telescope's nonempty level list) so both classifiers reduce to the same universe code.
#assert_no_axioms FX1Poly.Typed.flatFormerBinderShifts
#assert_no_axioms FX1Poly.Typed.consecutiveShifts
#assert_no_axioms FX1Poly.Core.boolTrueCell_isMember
#assert_no_axioms FX1Poly.Core.boolFalseCell_isMember
-- ELIMINATION canonicity (#672-free, SN-063 path): boolElim on a CANONICAL scrutinee COMPUTES to a branch.
-- StepStar.boolElimScrutinee = the scrutinee-position chain congruence (generic StepStar.congAt + Step.cong
-- (StepChildren.here ...) at the head of the 3-child spine). boolElimCanonicalScrutineeReducesToBranch = the
-- headline: the scrutinee reduces to true/false (boolClosedReducesToTrueOrFalse), the congruence carries that
-- under the boolElim, and the matching iota (iotaBoolTrue/iotaBoolFalse) selects the then/else branch
-- (StepStar.transLast). The elimination analog of closed-bool canonicity; no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.boolElimScrutinee
-- Sigma PROJECTION canonicity (#672-free, SN-058 path): fst/snd on a CANONICAL pair scrutinee PROJECT to the
-- components. StepStar.fstScrutinee/sndScrutinee = the unary scrutinee-position chain congruences (generic
-- StepStar.congAt + Step.cong (StepChildren.here ...) at the sole child). pairCanonicalScrutineeProjectsTo-
-- Components = the headline: the scrutinee reduces to pairCell first second (pairClosedReducesToValue), the
-- projection congruences carry that under fst/snd, and the matching iota (iotaFstPair/iotaSndPair) projects out
-- the components. The Sigma-projection analog of boolElim branch-selection; no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.fstScrutinee
#assert_no_axioms FX1Poly.Core.StepStar.sndScrutinee
-- IDENTITY-ELIMINATOR canonicity (#672-free, SN-068/069 path): idJ/idStrictRec on a CANONICAL refl WITNESS
-- COMPUTE to the base case. StepStar.idJWitness/idStrictRecWitness = the witness-position (second-child) chain
-- congruences (generic StepStar.congAt + Step.cong (StepChildren.there base (here ...)) reaching past the base
-- case into the witness child; headShift := 0 pins the [0,0]-spine). idJ/idStrictRecCanonicalWitnessReducesToBase
-- = the headline: the witness reduces to a refl (reflClosedReducesToValue), the witness congruence carries that
-- under the eliminator, and the matching iota (iotaIdJRefl/iotaIdStrictRecRefl) selects the base case. The last
-- non-growing eliminators (ι selects base from the witness); no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.idJWitness
#assert_no_axioms FX1Poly.Core.StepStar.idStrictRecWitness
-- NON-RECURSIVE data eliminators (#672-free, SN-065/066 path): optionMatch/eitherMatch on a CANONICAL scrutinee
-- COMPUTE to a branch. StepStar.optionMatchScrutinee/eitherMatchScrutinee = the head-child scrutinee congruences
-- (StepStar.congAt + Step.cong (here ...), as for boolElim). optionMatchCanonicalScrutineeReduces = none-branch
-- (scrutinee ->* none) or app someBranch payload (scrutinee ->* some payload); eitherMatchCanonicalScrutinee-
-- Reduces = app leftBranch/rightBranch payload (scrutinee ->* inl/inr payload). Option/Either are non-recursive,
-- so the iota fires once (no recursive sub-term) — completing the canonical-computation track for ALL
-- non-recursive eliminators (bool/sigma-proj/identity/option/either); only recursive nat/list need Tait. No
-- fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.optionMatchScrutinee
#assert_no_axioms FX1Poly.Core.StepStar.eitherMatchScrutinee
-- RECURSIVE eliminators, BASE CASE (#672-free, SN-061/062/064 base half): natElim/natRec on zero, listElim on
-- nil COMPUTE to the base branch. StepStar.natElimScrutinee/natRecScrutinee/listElimScrutinee = head-child
-- scrutinee congruences (as for boolElim). natElim/natRecZeroScrutineeReducesToBranch +
-- listElimNilScrutineeReducesToBranch = the headline: when the scrutinee reduces to the base constructor
-- (zero/nil), the congruence carries that under the eliminator and the base iota (iotaNatElimZero/iotaNatRecZero/
-- iotaListElimNil) selects the base branch. The recursive (succ/cons) step case GROWS (iota reappears the
-- eliminator on predecessor/tail) and needs full Tait; this is the clean base-case half. No fundamental theorem.
#assert_no_axioms FX1Poly.Core.StepStar.natElimScrutinee
#assert_no_axioms FX1Poly.Core.StepStar.natRecScrutinee
#assert_no_axioms FX1Poly.Core.StepStar.listElimScrutinee
#assert_no_axioms FX1Poly.Core.natElimZeroScrutineeReducesToBranch
#assert_no_axioms FX1Poly.Core.natRecZeroScrutineeReducesToBranch
#assert_no_axioms FX1Poly.Core.listElimNilScrutineeReducesToBranch
#assert_no_axioms FX1Poly.Core.noWeakHeadStep_of_isFlatDataCode

-- The K combinator `λx.λy.x : A → (B → A)` — the hardest concrete simply-typed term, where the inner body
-- CAPTURES the outer bound variable.  `subst0_lamCellVarOne_eq_lamWeaken` is the binder-crossing substitution
-- computation behind it (`subst0 (λy.var 1) arg = λy.weaken arg`), proven fold-`rfl`-free (no propext /
-- Quot.sound) with a Nat-arithmetic Fin bound (no omega).
#assert_no_axioms FX1Poly.Typed.subst0_lamCellVarOne_eq_lamWeaken

-- The ROOT-REDEX DISPATCH: `hasRootStepSource source = true → ∃ target, Step source target`, assembling all
-- 11 per-redex bricks via a generator case-split mirroring `hasRootStepSource`'s definition.  The missing
-- root ingredient for weak normalization (the Acc descent's step-extraction at a non-normal term).
#assert_no_axioms FX1Poly.Core.hasRootStepSource_exists_step

-- The COMPUTABLE root-redex firing FUNCTION + its soundness: `fireRootRedex generator payload children`
-- returns `some reduct` exactly on a root redex, exhibiting the reduct as a concrete RawTerm (vs the
-- existential `hasRootStepSource_exists_step`).  The reduct-supplier the weak-normalization normalizer
-- FUNCTION (#261/#480) needs to make `decidableOfNormalForms_of_isStronglyNormalizing` parameter-free.
-- Propext-clean over the 203-ctor table via DecidableEq dite-chains + ▸-casts + full spine destructure.
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedex
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedex_sound

-- COMPLETENESS of root-redex firing: fireRootRedex fires on EXACTLY the redexes hasRootStepSource detects
-- (the 11-generator dite-chains agree, via the RedexExtraction source-inversions + rfl firings).  The
-- contrapositive `fireRootRedex = none → hasRootStepSource = false` is the root half of structural normality
-- that reduceOnce completeness consumes.
#assert_no_axioms FX1Poly.Core.RawTerm.hasRootStepSource_imp_fireRootRedex_isSome
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedex_eq_none_imp_hasRootStepSource_false

-- One deterministic reduction step as a TOTAL FUNCTION + soundness: `reduceOnce` fires a root redex
-- (fireRootRedex) or descends the child spine to the first reducible child; `reduceOnce_sound` /
-- `reduceOnceSpine_sound` show every produced reduct is a genuine Step / StepChildren.  The descent engine
-- the WN normalizer FUNCTION (#261/#480) iterates along Acc StepSuccessor.
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_sound
#assert_no_axioms FX1Poly.Core.RawTermChildren.reduceOnceSpine_sound

-- COMPLETENESS of reduceOnce: it halts (returns none) EXACTLY at structural normal forms.  With soundness
-- this pins reduceOnce's halting set to isStepNormalForm.  reduceOnce_eq_none_iff_isStepNormalForm packages
-- the biconditional; not_isStepNormalForm_imp_reduceOnce_isSome is the descent guarantee (a non-normal term
-- genuinely reduces) the Acc StepSuccessor normalizer FUNCTION steps along.
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_complete
#assert_no_axioms FX1Poly.Core.RawTermChildren.reduceOnceSpine_complete
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.weakenUnderBinding

-- SIMPLY-TYPED SUBSTITUTION PRESERVATION — the SR arc's β-engine.  SimplyTypedTermLF survives any well-typed
-- substitution; the lam arm transports IsReducibleTypeExprLF premises via .subst and lifts the body IH with
-- the 0/succ split (var at 0, weakenUnderBinding at k+1).  substituteUnderBinding is the subst0 corollary
-- β-reduction cites: (λ.body) arg ↝ body[arg] preserves type.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.substRespectingContext
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.substituteUnderBinding
-- Candidate-bridge leaves: emptyTypeCell heads no weak-head step / no full Step (nullary gen_emptyCode leaf, no
-- β/ι, empty child spine); candidateIffEmptyCandidate is the empty-code shape inversion (a reducible type whose
-- code IS emptyTypeCell has candidate emptyTaitCandidate up to PointwiseIff) — the leaf deterministic's dataEmpty
-- arm consumes, twin of candidateIffStronglyNormalizing/candidateIffUniverse.
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_noStep
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_forwardStep
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_neutralInclusion_of_lt
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_backwardWeakHeadStep
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_forwardStep
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_neutralInclusion_of_lt
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_backwardWeakHeadStep
-- The DATA-morphism renaming category (FxBaseRenamingCategory.lean, SN-084) — the base the function-morphism
-- fxRenamingCategory above CANNOT be. fxRenamingCategory's morphisms are bare functions (Fin source -> Fin
-- target), so every downstream CwR equality (pullback commutes/universal, iso inverse laws) is a FUNCTION
-- equality needing funext (Quot.sound); the thin RMC escapes only by going degenerate (Prop-morphisms). This
-- file reifies a renaming as DATA: RenamingTo target source = the length-source vector of Fin target images, so
-- morphism equality is STRUCTURAL. All three category laws hold by induction over the vector (compose_assoc via
-- mapImages fusion + lookup_mapImages; identity_compose / compose_identity via the identity-lookup algebra), NO
-- funext -- so this base CAN host a zero-axiom RMC. lookup: the faithful bridge back to the function world
-- (RawRenaming); lookup_compose: lookup is a FUNCTOR (carries composition to function composition pointwise).
-- The propext trap (lookup-extensionality, a simultaneous two-renaming indexed match) is AVOIDED -- identity
-- _compose binds the cons subscope via @RenamingTo.cons _ source ... rather than matching the Nat index as
-- source+1. HONEST SCOPE: the underlying-category data-morphism base of fxBaseRMC; NOT yet the RMC (the
-- representable-map class + 3 CwR axioms, now structurally expressible, are the next rung, deferred). All
-- zero-axiom. _identity_eq / _compose_eq: the categorical identity/composition ARE the data-renaming ops (defeq).
#assert_no_axioms FX1Poly.Tier0.RenamingTo.lookup
#assert_no_axioms FX1Poly.Tier0.RenamingTo.mapImages_mapImages
#assert_no_axioms FX1Poly.Tier0.RenamingTo.lookup_mapImages
#assert_no_axioms FX1Poly.Tier0.RenamingTo.mapImages_congr
#assert_no_axioms FX1Poly.Tier0.RenamingTo.mapImages_id
#assert_no_axioms FX1Poly.Tier0.RenamingTo.compose_assoc
#assert_no_axioms FX1Poly.Tier0.RenamingTo.lookup_compose
#assert_no_axioms FX1Poly.Tier0.RenamingTo.identity_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingTo.identity_compose
#assert_no_axioms FX1Poly.Tier0.RenamingTo.compose_identity
-- The display / weakening renaming scope -> scope+1 (the data-morphism analogue of RawRenaming.weaken): shifts
-- every variable past the freshly-bound var 0, built as the shift of the identity (so it IS the successor
-- identity's tail, identity_succ_eq by rfl). weakening_lookup: its action is shiftImage (index -> index+1), via
-- lookup_mapImages + identity_lookup. The canonical context-PROJECTION morphism = the genuine display-map
-- representable candidate (not the degenerate iso class). Clean: rides on the shipped mapImages/identity algebra,
-- needs NO lookup-extensionality (which is the deferred propext-frontier crux for the RMC round-trip laws).
#assert_no_axioms FX1Poly.Tier0.RenamingTo.weakening
#assert_no_axioms FX1Poly.Tier0.RenamingTo.weakening_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingTo.identity_succ_eq
-- SN-055: the UNCONDITIONAL former-domain SR rebuild for a FORMATION codomain (completes the formation-codomain
-- former-domain case). {pi,sigma}FormationViaGenArm reassembles the former from the stepped domain + the
-- re-typed codomain (formationCodomainReTyping), at the canonical Type@(lmax domLevel codLevel). The dispatcher
-- converts to the former's classifier via the invertPiTyCode Conv. No grown context-conversion bundle.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormerStepDomainFormationCodomain
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerStepDomainFormationCodomain

-- SN-055 FORMATION-ENGINE subject reduction (HasTypeDescSubjectReduction.lean): the dispatcher's ofFormation
-- arm carries a HasTypeDesc premise (var/conv/universeFormation/genFormation), which must itself be SR-closed.
-- The formation engine types the Π/Σ-former CODES, whose Step is a domain/codomain congruence. A MUTUAL pair
-- mirroring convContext/convTelescope: HasTypeDesc.subjectReduction (var/universe normal via no_step_from_var/
-- _universeCode, conv recursive, genFormation via former_step_inv + the telescope SR) ⋈ DescTelescope.subject-
-- Reduction (here = head SR + convTelescope re-typing the tail under the stepped binding via convContext-
-- Condition_consStep; there = tail recursion). former_step_inv rules out root redexes generically over the
-- formation family (typingRuleDescOf_isPiOrSigma), so a future ≥1-child formation row extends with no cascade.
#assert_no_axioms FX1Poly.Typed.Step.no_step_from_universeCode
#assert_no_axioms FX1Poly.Typed.Step.no_step_from_emptyCode
#assert_no_axioms FX1Poly.Typed.former_step_inv
-- HONESTY: the formation fragment is NORMAL — subjectAdmitsNoStep is the genuinely content-bearing
-- characterization (every formation-typed subject admits no Step), making the SR above VACUOUSLY true.
-- childrenAdmitNoStep is the mutual telescope normality witness. subjectAdmitsNoStep is the tool the SN-055
-- dispatcher's ofFormation arm actually uses (absurd step via no-step), NOT the heavier vacuous subjectReduction.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectAdmitsNoStep
#assert_no_axioms FX1Poly.Typed.formationNormalSmoke_piCodeAdmitsNoStep

-- OB-6 (ContextValidityFails.lean): the WfContext hypothesis in open SN-043 is NECESSARY. A lamCell is never a
-- type (lamCell_isNotType, via subjectIsVariableOrTypeFormerCode + Generator.noConfusion head-mismatch), so
-- Γ = (.empty).cons (λx.x) is ill-formed; yet the var rule types var 0 in it
-- (wellTypedInIllFormedContext) — refuting HasTypeDescPi Γ t T → WfContext Γ (contextValidityPresuppositionFails).
-- The honest negative result: OB-5's WfContext qualifier is an irreducible presupposition, not a removable
-- artifact (the closed Γ=.empty instance consumed by canonicity/consistency is trivially well-formed).
#assert_no_axioms FX1Poly.Typed.lamCell_isNotType
#assert_no_axioms FX1Poly.Typed.wellTypedInIllFormedContext

-- Nullary-former formation (NullaryFormerFormation.lean): the engine-side CON-A2 (#809), parametric. The
-- empty type is a nullary type-former; a generator carrying the shared universeFormerOutput row with ZERO
-- children types as Type@0 through the SAME generic genFormationPi arm (no new arm; P13), because
-- lmaxAll [] = lzero (universeFormerOutput_nil). Instantiating at the future gen_emptyCode (binderShifts = [],
-- children := .childNil, premise := DescTelescopePi.nil, all rfl) gives ⊢ Empty : Type@0 — SN-050's formation
-- half (its NON-VACUITY), settled here; the residual is the substrate generator + candidate bridge (CON-A3).
#assert_no_axioms FX1Poly.Typed.universeFormerOutput_nil
#assert_no_axioms FX1Poly.Typed.lam_notTypedAtVariableCell
#assert_no_axioms FX1Poly.Typed.piTyCode_notTypedAtPiTyCode
#assert_no_axioms FX1Poly.Typed.sigmaTyCode_notTypedAtPiTyCode

-- GROWN-engine universe consistency (GrownUniverseConsistency.lean, SN-140 L1): the HasTypeDescPi parity twin of
-- the formation UniverseFormationStrictness corpus (self/above/below) plus a novel flag-rigidity probe. A universe
-- code Type@(e, flag) receives ONLY classifiers Conv to its strict predicative successor Type@(lsucc e, flag)
-- (inversionUniverseCode); universeCodeCell_inj_of_conv collapses that to level+flag equality, then the
-- predicativity guards refute the mis-classifications: no Type:Type (e = lsucc e, ne_lsucc_self — the §27.2
-- Girard-paradox rejection), no inflation (lsucc(lsucc e) = lsucc e), no deflation (e = lsucc (lsucc e),
-- ne_lsuccLsucc_self), flag rigidity (classifierFlag = subjectFlag from inj, refuting the disequality). The §11.8.2
-- universe-consistency guarantee at the engine the kernel metatheory runs on.
#assert_no_axioms FX1Poly.Typed.grownUniverseCode_notTypedAtSelf
#assert_no_axioms FX1Poly.Typed.grownUniverseCode_notTypedAboveSuccessor
#assert_no_axioms FX1Poly.Typed.grownUniverseCode_notTypedBelowSuccessor
#assert_no_axioms FX1Poly.Typed.grownUniverseCode_notTypedAtFlagMismatchedSuccessor
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_notInHeadFragment

-- Grown-engine canonical-forms boundary (HasTypeDescPiDataHeadUntyped.lean, the SR dispatcher's iota-vacuity
-- leg toward SN-055/#558). The grown engine types no data constructor and no data eliminator — it is the pure
-- Π/formation fragment. The smoke corpus cites the table-generic refutation
-- HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded (HasTypeDescPiRootGeneric, requires
-- typingRuleDescOf gen = none): every Step.iota* redex (.mkGen ELIM_GEN …) is refuted, discharging the iota
-- family vacuously. Instantiated on the real iota-redex heads across the eliminator shape classes (boolElim
-- branch-select / fst projection / natElim recursion / idJ path-induction) and on a data constructor (pair).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.boolElimCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fstCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.natElimCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.idJCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pairCellHasNoTyping
-- COMPLETED iota-redex-head corpus: the remaining data eliminators (snd projection / natRec+listElim recursion /
-- optionMatch+eitherMatch branch / idStrictRec strict path recursion) + the Empty TYPE-CODE cell gen_emptyCode
-- (typingRuleDescOf = none, CON-A1's deferred row). Every β+ι iota-redex head is now an EXPLICIT shipped
-- refutation. emptyTypeCellHasNoTyping additionally yields noConvReclassifierAtEmptyType — the conv arm of the
-- SN-050 consistency inversion (the residual is the piElim arm, the SR/model crux GrownCtxConv-5/CON-A3).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sndCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.natRecCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listElimCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.optionMatchCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.eitherMatchCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.idStrictRecCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.emptyTypeCellHasNoTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded

-- BOOL TYPE-CODE SUBSTRATE (BoolTypeCodeSubstrate.lean / HasType.lean, SN-047 prerequisite). gen_boolCode is the
-- bespoke nullary type-code generator filling the Bool-type gap (the kernel had VALUE gens gen_boolTrue/
-- gen_boolFalse but no TYPE code, like every ground datatype). boolTypeCell = mkGen gen_boolCode () childNil
-- mirrors emptyTypeCell (CON-A1). gen_boolCode_isNullaryTypeCode pins the metadata shape (arity 0, binderShifts
-- [], cellSort .type) the future Bool:Type@0 formation will consume; gen_boolCode_isAdmitted is the
-- SupportedGenerator witness. The serialization round-trip (toNat_injective/fromTag_toNat) + finite-polygraph
-- bound (toNat_lt over Fin 196) already re-verify gen_boolCode uniformly. typingRuleDescOf gen_boolCode = none
-- today (formation GTL-11-gated), so boolTypeCell is correctly not yet typed.
#assert_no_axioms FX1Poly.Typed.boolTypeCell
#assert_no_axioms FX1Poly.Typed.gen_boolCode_isNullaryTypeCode
#assert_no_axioms FX1Poly.Typed.gen_boolCode_isAdmitted

-- NAT TYPE-CODE SUBSTRATE (NatTypeCodeSubstrate.lean, SN-048/DI-3 prerequisite). gen_natCode is the bespoke
-- nullary type-code generator filling the Nat-type gap (the kernel had VALUE gens gen_natZero/gen_natSucc but no
-- TYPE code, like every ground datatype). natTypeCell = mkGen gen_natCode () childNil mirrors boolTypeCell /
-- emptyTypeCell. gen_natCode_isNullaryTypeCode pins the metadata shape (arity 0, binderShifts [], cellSort .type);
-- gen_natCode_isAdmitted is the SupportedGenerator witness. The serialization round-trip (toNat_injective/
-- fromTag_toNat) + finite-polygraph bound (toNat_lt over Fin 203) already re-verify gen_natCode uniformly.
-- baseTypeRuleDescOf gen_natCode = none today (Nat:Type@0 base-type formation deferred to keep the
-- baseTypeRuleDescOf two-way enumeration cascade-free); natTypeCell is a raw classifier for HasTypeDescNatIntro.
#assert_no_axioms FX1Poly.Typed.natTypeCell
#assert_no_axioms FX1Poly.Typed.gen_natCode_isNullaryTypeCode
#assert_no_axioms FX1Poly.Typed.gen_natCode_isAdmitted
-- IsTypeDescRigidity = the native rigidity + leaf characterization of formation type-hood, feeding the native
-- Decidable (IsTypeDesc Γ T) decision procedure.
-- hasNoStep = formation types are normal (read off subjectAdmitsNoStep); eq_of_isTypeDesc =
-- convertible formation types are equal (Conv.eq_of_noStep on the two normal endpoints);
-- ofUniverseCodeCell = a universe code is a formation type (universeFormation); variableCell_iff = a variable
-- cell is a type iff its lookup is a universe code (the ONE context-consulting leaf, over WfContextDesc).
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.hasNoStep
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.ofUniverseCodeCell
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.variableCell_iff_lookupIsUniverseCode
#assert_no_axioms FX1Poly.Typed.piIntroOutput
#assert_no_axioms FX1Poly.Typed.piElimOutput
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.cellUntypedWhenRolelessAndNonBespoke
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.boolTrueCellUntypedViaRole
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.natElimCellUntypedViaDecision
#assert_no_axioms FX1Poly.Typed.universeClassificationChain_twoStep_nonVacuous
-- Well-foundedness — the order-theoretic companion to acyclicity.  UniverseClassifies = the single-step
-- level-classification relation; universeClassifies_size_lt = each edge strictly increases LevelExpr.size;
-- grownUniverseClassificationIsWellFounded = WellFounded via Subrelation of InvImage Nat.lt size (no infinite
-- DESCENDING classification chain — distinct from acyclicity's no-cycle).  Together: strict well-founded order.
#assert_no_axioms FX1Poly.Typed.UniverseClassifies
#assert_no_axioms FX1Poly.Typed.universeClassifies_size_lt
#assert_no_axioms FX1Poly.Typed.grownUniverseClassificationIsWellFounded
#assert_no_axioms FX1Poly.Typed.universeClassifies_nonVacuous
#assert_no_axioms FX1Poly.Typed.polyCellSubstrate_isFxOriginal

-- §27.3 Layer-5 defense: the per-rule formal-review gate (provenance + positive + negative + metatheory +
-- fuzz + corpus = the six obligations, mapping onto the other four layers).  Two CONCRETE worked instances
-- (corrected Lam, universe formation) with each obligation ANCHORED (`…_<obligation> := @<shippedWitness>`)
-- to a real zero-axiom witness — re-certified zero-axiom by these gates — and `…ReviewGate_passes := rfl`.
-- The non-vacuity proof `incompleteReview_fails` shows the checker actually discriminates (a missing
-- obligation FAILS), so `passesReview = true` is a real certificate.  Completes the five-layer defense (L1-L5).
#assert_no_axioms FX1Poly.Typed.FormalReviewObligation
#assert_no_axioms FX1Poly.Typed.FormalReviewObligation.describe
#assert_no_axioms FX1Poly.Typed.FormalReviewGate
#assert_no_axioms FX1Poly.Typed.FormalReviewGate.isObligationSatisfied
-- TYPING RULES OUT NON-TERMINATION (TypedFragmentAcyclicity): the SN-043 contrapositive discharging the
-- English remark in UntypedOmegaNotStronglyNormalizing that "Ω is untypable". closedWellTypedTerm_notStepSelfLoop:
-- no closed well-typed term β-steps to itself — a self-loop makes the term non-accessible under the
-- one-step-successor relation (accessibleElementNotSelfRelated), contradicting closedStronglyNormalizing; typed
-- reduction is acyclic. ★ omegaCombinator_notClosedWellTyped: Ω has NO closed type — were it typed, SN-043 would
-- force it strongly normalizing, but it self-steps forever; so the typing rules genuinely REJECT the prototypical
-- divergence (untypability proven, not observed). typingRulesOutSelfLooping packages the contrast: a closed
-- β-self-looping untypable term (Ω) exists, while every closed well-typed term has no self-loop — typing is
-- exactly the separator. Reuses the Step t t defeq StepSuccessor t t identity (IsStronglyNormalizing = Acc Step).
#assert_no_axioms FX1Poly.Typed.closedWellTypedTerm_notStepSelfLoop
-- SYMBOLIC-S-RULE (SymbolicSCombinatorRule, #1024): the general S-combinator law S a b c ↝* (ac)(bc) for SYMBOLIC
-- a/b/c — closes the unmet half of #1016 (which shipped only concrete SKK=I; its docstring deferred the symbolic
-- S-rule because subst (lift (singleton b))(weaken² a) ≠ weaken a by rfl). Now ASSEMBLY via the #1023 double-weaken
-- substrate: combinatorS_reduces (★) chains 3 β-steps reusing shipped combinatorS/saTerm/sabTerm. β1 (x-discard →
-- saTerm) is Step.beta directly (rfl). β2 saTermBody_subst_b (saTerm→sabTerm) USES subst_lift_singleton_weaken_weaken
-- (#1023) for weaken²a→weaken a, via the show-push (subst over appCell/lamCell is DEFEQ) + rw + rfl idiom. β3
-- sabTermBody_subst_c via weaken_subst_singleton. DEMONSTRATES the de Bruijn substrate is complete (single+double
-- weaken). Zero-axiom (Step.beta + show/rw/rfl + StepStar.trans congruences).
#assert_no_axioms FX1Poly.Typed.saTermBody_subst_b
#assert_no_axioms FX1Poly.Typed.sabTermBody_subst_c
-- SYMBOLIC CHURCH SUMS (ChurchSumsGeneral, #1025): generalize #1019's case selection off the concrete combinatorI
-- to an ARBITRARY symbolic payload, unblocked by the #1023 double-weaken substrate. caseLeft_selectsLeftHandler_
-- general (★): ∀ payload l r, case (inl payload) l r ↝* l payload; caseRight twin; caseSelectsByTag_general bundle.
-- The ONLY change from #1019's concrete proof is the β1 contractum reshape (leftInjection_subst_handlerL /
-- rightInjection_subst_handlerL): the payload sits under TWO handler binders so it is weakened TWICE; substituting
-- the left handler collapses weaken²payload → weaken payload via subst_lift_singleton_weaken_weaken (#1023) +
-- show-push/rw/rfl — the step a concrete payload got by rfl. The rest mirrors #1019 (weaken_subst_singleton on both
-- handler and payload). SUBSUMES #1019's concrete theorems (instances at payload=combinatorI): the coproduct
-- encoding is faithful for arbitrary stored data. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.leftInjection_subst_handlerL
#assert_no_axioms FX1Poly.Typed.rightInjection_subst_handlerL
#assert_no_axioms FX1Poly.Typed.caseLeft_selectsLeftHandler_general
#assert_no_axioms FX1Poly.Typed.caseRight_selectsRightHandler_general
#assert_no_axioms FX1Poly.Typed.caseSelectsByTag_general
-- CHURCH LISTS (ChurchLists, CHURCH-LISTS): the first RECURSIVE / inductive Church (Boehm-Berarducci) data shape —
-- LISTS as their own right-fold. nil = λc.λn.n; cons h t = λc.λn. c h (t c n); fold c n list = list c n. Lists are
-- the first Church encoding past finite tagged unions (bool #981 / numerals #989 / products #1017 / coproducts #1019):
-- a list IS its parametric inductive eliminator, the recursive tail folded as nested polymorphic application
-- (structurally Church-SUCC carrying a payload). foldNil (★): fold c n nil ↝* n for ARBITRARY handlers — nil is the
-- Church-zero λf.λx.x carrying the fold, so the two β-contractions are the clean innermost-variable subst0
-- (one Step.cong .gen_app over the outer β, then the inner β; both subst0 contracta rfl-clean). churchNil_isValue /
-- churchCons_isValue: both encodings are gen_lam-headed λ-VALUES (closed weak-head-normal canonical inhabitants of
-- the encoded list type Π R.(A→R→R)→R→R). foldCons (★): the RECURSIVE cons-fold fold c n (cons h t) ↝* c h (t c n) —
-- folding a cons cell applies the cons-handler to the head AND the recursively-folded tail; the β1 reshape
-- churchCons_subst_consHandler weakens the cons-handler TWICE and collapses the two doubly-weakened stored values via
-- RawTerm.subst_lift_singleton_weaken_weaken (#1023) — the SAME double-weaken cancellation the symbolic Church-sum
-- payload (#1025) and the general S-rule (#1024) used; the second β cancels the single weakens. foldSingleton (★):
-- fold c n (cons h nil) ↝* c h n — the fold of a CONCRETE one-element list, the recursion bottoming out, composing
-- foldCons with foldNil (StepStar.appArgument-lifted through the folded-tail position). Raw Step throughout; no typing
-- derivation consulted. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.foldNil

/- Variable arm of grown strengthening (GrownStrengthening): the inverse of weakenUnderBinding for the
non-recursive (var) leaf — the base case of strengthenUnderBinding and first consumer of Conv.reflectWeaken
(#1167). strengthenVariableClassifier strips the weaken off a var's classifier Conv; strengthenVariableUnderBinding
re-types the var at the strengthened classifier given its validity. Toward grown η-contraction SR (#477/PAR-2). -/

#assert_no_axioms FX1Poly.Typed.lookupConsSuccEqWeaken
#assert_no_axioms FX1Poly.Typed.weakenedSubjectGrownTypedAtEscapingClassifier
#assert_no_axioms FX1Poly.Typed.escapingReclassifier_isOutsideWeakenImage
#assert_no_axioms FX1Poly.Typed.weakenedIdentityTypedAtVariableDomainPi
#assert_no_axioms FX1Poly.Typed.renameEqLamCellInversion
#assert_no_axioms FX1Poly.Typed.renameEqAppCellInversion
#assert_no_axioms FX1Poly.Typed.renameEqVariableCellInversion
#assert_no_axioms FX1Poly.Typed.renameEqUniverseCodeCellInversion

/- Plateau-master descent substrate (PlateauDescentSubstrate): the per-arm (size, normality)
descent obligations for the normal-subject size-recursive reflection — strict size bounds for the
recursion cells, the argument/body subterm-of-normal twins, and the generic mkGen child-normality
extraction (Bool-conjunct surgery; rfl-unfold beats the two-discriminant mutual match that dsimp
cannot reduce). -/

#assert_no_axioms FX1Poly.Typed.RawTerm.size_lt_lamCell_body
#assert_no_axioms FX1Poly.Typed.RawTerm.size_lt_appCell_function
#assert_no_axioms FX1Poly.Typed.RawTerm.size_lt_appCell_argument
#assert_no_axioms FX1Poly.Typed.appNormal_argumentNormal
#assert_no_axioms FX1Poly.Typed.lamNormal_bodyNormal

/- The NEUTRAL-REDUCT head residual HOLDS (NeutralReductResidualDischarge): a neutral is never a
λ (12-arm head discrimination), the whnf reduct is in-image and keeps the Π classifier by subject
reduction, the plateau pin-extraction pins it (the ∀-bound guarded residual frees the budget
guard), and the pinned-function core finishes with the original premise reflections.  One
λ-reduct residual now remains before the full piElim residual discharges. -/

#assert_no_axioms FX1Poly.Typed.IsNeutral.ne_lamCell

/- E2.7 MASTER (NormalUniverseClassificationUnique): two grown universe classifications of one
NORMAL subject agree on (level, flag) — budget-recursive 5-way root dispatch; the former arm's
flag agreement is anchored by the table-wide nonempty-binder-shifts fact.  Unconditional,
table-generic — the flag-negotiation keystone of the strengthening enrichment campaign. -/

#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_binderShiftsNonempty
#assert_no_axioms FX1Poly.Typed.RawRenaming.weaken_finInjective
#assert_no_axioms FX1Poly.Typed.RawTerm.reduceOnce_idTower_succ
#assert_no_axioms FX1Poly.Typed.RawTerm.reduceOnce_idTower_zero

/-! ### The nullary `unitCode` formation row — the flag-ignoring pinned output

`typingRuleDescOf` gains its first NULLARY row: `gen_unitCode` at the pinned
`nullaryFormerOutput` (`Type@0(standard)`, ignoring the empty level list and the unanchored
flag).  A childless former's telescope premise holds at EVERY flag, so a flag-USING output would
break uniqueness of typing; the pinned row restores it by output CONSTANCY
(`typingRuleDescOf_unitCode_outputConstant` + the PINNED classifier inversions on both engines).
The strong table-shape lemmas are rescoped to the >=1-child family (they now take a
`generator != gen_unitCode` hypothesis); the row-shape-agnostic interface
(`output_isUniverseCode` / `_renameStable` / `_substStable`) covers both shapes, and the
COMPUTABLE row-data accessor `formationOutputData` (+ its soundness equation) supplies the
Type-valued witnesses a decider needs (a Prop `∃` cannot eliminate into `Σ'`).  The
reducibility-FT arm for the nullary row is `IsReducibleMemberAt.unitFormerInUniverse` — no
telescope input, the inert-leaf membership. -/

#assert_no_axioms FX1Poly.Typed.nullaryFormerOutput
#assert_no_axioms FX1Poly.Typed.formationOutputData
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.pairCellHasNoDataIntroTyping
#assert_no_axioms FX1Poly.Typed.weakening_isZeroArm
#assert_no_axioms FX1Poly.Typed.substitution_isZeroArm
