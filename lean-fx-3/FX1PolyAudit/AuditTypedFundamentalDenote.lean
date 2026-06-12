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

/-! # FX1PolyAudit/AuditTypedFundamentalDenote — typed-layer zero-axiom gates: the denote-keyed reducibility fundamental theorem
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/


-- SN-003: the predicative well-founded MEASURE for classifier-level reducibility.  `denote_lt_lsucc` is the
-- strict decrease at the universe-decode step; the `lmax` bounds are the non-increasing former-component
-- descents; `variableCell_reducibleTypeAtZero` is the non-degenerate base (neutral types inhabit level 0,
-- unlike the SN-001 universe-code vacuity).
#assert_no_axioms FX1Poly.Typed.denote_lt_lsucc
#assert_no_axioms FX1Poly.Typed.denote_le_lmax_left
#assert_no_axioms FX1Poly.Typed.denote_le_lmax_right
-- The composed universe-domain-Pi measure step (#672 sub-step 3): a member of Type@e has level denote e
-- strictly below the dependent Pi's level lmax (lsucc e) levelC — the Adjedj recursion's well-founded
-- descent. Member level bound comes from ValidTyping's subjectLevel (the validity derivation), not bare
-- reducibility.
#assert_no_axioms FX1Poly.Typed.denote_lt_lmax_lsucc_left

-- DenoteKeyedReducibility (SN-006 foundation toward #672): the classifier-universe-level reducibility
-- relation. The universe arm decodes Type@e to the lower relation AT denote e (the fixed classifier level),
-- not ambient-fuel-minus-one — defeating SN-001's fuel-0 vacuity. The lower family is STRUCTURAL (not WF:
-- the WF .eq_def leaks Quot.sound), granting arbitrary-lower-level access at the structural predecessor.
-- universeMembership_levelIrrelevant is the headline: Type@e's candidate is the SAME decode-at-(denote e)
-- set at every ambient level > denote e — the level-irrelevance the fuel model could not deliver, true by
-- construction. universeCode_isReducibleAtDenote is the anti-vacuity (refutes RouteAObstruction's empty base).
#assert_no_axioms FX1Poly.Typed.universeDenotePredicate
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtDenote
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_eq_reducible
#assert_no_axioms FX1Poly.Typed.universeCode_isReducibleAtDenote
#assert_no_axioms FX1Poly.Typed.universeMembership_levelIrrelevant

-- DenoteKeyedReducibility CR machinery (#672 sub-step 1): shape inversions + determinism, ported from
-- StratifiedReducibleType. The only structural difference: the denote-keyed universe candidate depends on
-- levelExpr, so candidateIffUniverse/deterministic align it via universeCodeCell_inj (where the fuel version
-- used bare Iff.rfl). piTypeInversion decomposes a reducible Pi(Type@e)C — the decomposition the
-- universe-domain piArm of typeLevelIrrelevance consumes; deterministic aligns the domain/codomain candidates.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateAtWhnfReduct
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidatePiShape
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffUniverse
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffEmptyCandidate
-- The FLAT twin (CAN-6): root-keyed shape inversion — a reducible type whose root generator is a FLAT data
-- code came through the dedicated dataFlat arm; its candidate IS the pinned flat Tait candidate.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffFlatCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.deterministic
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.deterministic
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.piTypeInversion

-- DenoteKeyedReducibility forward closure + conversion-invariance (#672 sub-step 2a): ported from
-- StratifiedReducibleTypeForwardClosure/ConvInvariance. The reduction helpers (commuteWithStep,
-- weakHeadNormalRootStableAlongStepStar, piTyCode_decompose, noStep_universeCode) are relation-agnostic and
-- reused verbatim; only the reducibility constructors change. convTransfer is the membership form the conv
-- typing arm and the dependent-arrow CR3 argument-reduction case consume — the prerequisite for the arrow CR.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.whnfExpandClosure
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.forwardStepStar
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.forwardStepStar
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.convInvariant
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.convTransfer
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.convTransfer

-- DenoteKeyedReducibility CR-soundness (#672 sub-step 2b): every denote-keyed candidate is a Girard
-- reducibility candidate (CR1/CR2/CR3). The arrow CR is a verbatim port (CR3 via convTransfer); the
-- parametric isReducibilityCandidate reuses the fuel universeCandidateIsReducibilityCandidate at the DECODED
-- level via the defeq universeDenotePredicate env lowerAt levelExpr = universeReducibilityPredicate
-- (lowerAt (denote levelExpr env)). Interface legs are per-level (∀ lvl); the unconditional level-indexed
-- discharge carries the predicative level-bound subtlety, deferred to the piArm step.
#assert_no_axioms FX1Poly.Typed.isDependentArrowReducibleStepDenote_isReducibilityCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.isReducibilityCandidate

-- DenoteKeyedReducibility interface-leg discharge for denoteBelowFamily (#672 sub-step 3 prerequisite):
-- the per-level legs the candidate machinery consumes. forwardStep is unconditional (below the level via
-- coherence, above it vacuous since the family is empty); neutralInclusion holds for lvl < level only
-- (at/above, the family is empty and neutral-inclusion FAILS — SN-001 degeneracy re-keyed to denote; the
-- piArm satisfies the bound via denote e < level / denote_lt_lsucc). backwardWeakHeadStep is the THIRD leg
-- and is UNCONDITIONAL: unlike neutral-inclusion (an existence obligation, false on the empty family), a
-- backward-step leg is an implication whose premise is False above the bound, hence vacuous there and
-- whnfExpand below it — the leg the member weak-head β-expansion (denote lambda-arm engine) needs at its
-- universe arm, making that case bound-free.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.forwardStep
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.reducibleOfNeutral
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_eq_empty_of_ge
-- the denote-keyed semantic member predicate (member analogue of IsReducibleTypeAtDenote)
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtDenote
#assert_no_axioms FX1Poly.Typed.universeDomainPi_reducibleAtAllDenoteLevels
#assert_no_axioms FX1Poly.Typed.universeDomainPi_uniformCandidateAtAllDenoteLevels
#assert_no_axioms FX1Poly.Typed.universeDomainPi_memberStableAcrossDenoteLevels
-- universeLeafMemberStableAcrossDenoteLevels: the LEAF twin of the Π member-stability -- a reducible member of
-- Type@e at one level above denote e is a member at every level above it. The fixed decode-set candidate
-- (universeMembership_levelIrrelevant) is the same at both levels; determinism reconciles. Fills the gap left by
-- DenoteKeyedLevelIrrelevance (which has leaf member-stability only for neutral/uniform types, uniform across ALL
-- levels; the universe is uniform only ABOVE denote e). Choice-free (canonical candidate). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.universeLeafMemberStableAcrossDenoteLevels
-- totalises the universe-domain Π to ∀ level (the IsReducibleTypeAtAllDenoteLevels piArm shape): genuine
-- levels reuse reducibleAtAllDenoteLevels, low levels (≤ denote e env) vacuous via empty domain candidate.
#assert_no_axioms FX1Poly.Typed.universeDomainPi_reducibleAtEveryDenoteLevel

-- DenoteKeyedLevelIrrelevance (#672 toward the denote level-irrelevance induction): the denote analogue of the
-- fuel IsReducibleTypeAtAllLevels.ofReducibleTypeStep. IsReducibleTypeAtAllDenoteLevels = ∀ level,
-- IsReducibleTypeAtDenote env level typeCode. ofNeutral/ofUniverseCode/headExpand are the level-uniform leaves;
-- ofReducibleTypeStepDenote is the induction backbone discharging neutral/universe/whnfExpand/ofPointwiseIff and
-- isolating piType as the piArm hypothesis (whose impredicative universe-domain instance the fuel model could
-- not close but DenoteKeyedUniverseDomainPi does).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.ofNeutral
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote
-- the NON-universe half of the piArm: uniformDomainPi handles any domain with a single candidate uniform at
-- ALL levels (neutral/data/non-universe-former domains); neutralDomainPi is the witnessing neutral instance
-- (candidate IsStronglyNormalizing). Complements A1 (universe domain, uniform above denote e env).
#assert_no_axioms FX1Poly.Typed.uniformDomainPi_reducibleAtEveryDenoteLevel
#assert_no_axioms FX1Poly.Typed.neutralDomainPi_reducibleAtEveryDenoteLevel
-- member-level complement (toward the denote #672 member-extension): a member of a type reducible with one
-- all-level uniform candidate is level-stable (via determinism); neutral-type instance witnesses it. The
-- non-universe analogue of universeDomainPi_memberStableAcrossDenoteLevels (which holds only above denote e).
#assert_no_axioms FX1Poly.Typed.uniformType_memberStableAcrossDenoteLevels
#assert_no_axioms FX1Poly.Typed.neutralType_memberStableAcrossDenoteLevels
-- Member-stability lifted from leaf types to the Π FORMER: a uniform-domain Π's own candidate
-- (fun f => forall arg, domCand arg -> codCand arg (app f arg)) is itself level-uniform, so
-- uniformType_memberStableAcrossDenoteLevels applies. uniformDomainPiType_ + the neutral-domain witnessing
-- instance neutralDomainPiType_ extend the member-stable #672 fragment to dependent arrows over member-stable
-- domains -- the non-universe-domain case the cumulativity obstruction does NOT block.
#assert_no_axioms FX1Poly.Typed.uniformDomainPiType_memberStableAcrossDenoteLevels
#assert_no_axioms FX1Poly.Typed.neutralDomainPiType_memberStableAcrossDenoteLevels

-- DenoteKeyedReducibleEnv (route C toward the denote fundamental theorem): the denote analogue of
-- ReducibleEnvAt, riding on IsReducibleMemberAtDenote. def + var-projection + empty + binder-cons; the cons
-- proof is character-identical to ReducibleEnvAt.cons (env/level ride along the lookup/weaken rewrites).
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtDenote
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtDenote.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtDenote.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtDenote.cons

-- DenoteKeyedCanonicalMemberCandidate (route D Π-formation engine, the denote analogue of #490): the canonical
-- member-predicate IsReducibleMemberAtDenote env level typeCode is itself the type's own candidate. The
-- choice-free codomain extraction the denote FT's Π-formation arm consumes — turns the codomain IH's mere
-- EXISTENCE of a candidate into the FIXED canonical predicate, no Classical.choice. ofPointwiseIff (pointwise,
-- no funext) + deterministic; uniform in level (no cases-level split the fuel original needed).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.reducibleMemberCandidate
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtDenote.reducibleMemberCandidate

-- Member-transfer across weak-head reduction (the member-level analogues of SN-D1 head-expansion closure):
-- headExpand re-attaches the same candidate above a whnf step (whnfExpand ctor); weakHeadForward keeps the
-- candidate at the contractum (candidateAtWhnfReduct). whnfExpandDomainMemberStableToOuter is the whnfExpand
-- arm of the #752 dispatcher — member-stability transfers across a domain whnf step (forward to reduct, lift by
-- the contractum's stability, head-expand back), reducing the redex-domain case to the contractum's stability.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtDenote.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtDenote.weakHeadForward
#assert_no_axioms FX1Poly.Typed.whnfExpandDomainMemberStableToOuter

-- compositeDomainMemberStableToOuter (#752 — the RECURSIVE HEART, threshold-drift composite domains): Π dom cod
-- is member-stable to outerLevel from the components' all-levels both-directions member-stability (domainStable /
-- codomainStable, the recursion IHs). A function member at sourceLevel maps source-dom-members to
-- source-cod-members (piTypeInversion); an outer-dom argument is pulled back to source (domainStable
-- outer→source, candidate via deterministic), fed to the function's source property, and the codomain image
-- pushed forward to outerLevel (codomainStable source→outer, candidate via deterministic). The drift is absorbed
-- entirely into the components' member-stability — the Π former composes with NO extra threshold reasoning. The
-- recursion bottoms out at neutral/universe/whnf-redex leaves; only the universe leaves carry the threshold gate.
#assert_no_axioms FX1Poly.Typed.compositeDomainMemberStableToOuter

-- DenoteKeyedUniverseDomainPiArm (#752 — the universeCode arm of the ofReducibleTypeStepDenote piArm case-split):
-- the domain is a universe code Type@innerLevelExpr whose membership candidate DRIFTS (empty below the inner
-- decoded level, real above), so the neutral/uniform adapters cannot reach it. The two decode lemmas split the
-- lowerAt-keyed universe predicate universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr:
-- _aboveThreshold (inner < outer) decodes to "SN ∧ reducible-as-type at the inner level" via
-- denoteBelowFamily_eq_reducible; _empty (outer ≤ inner) refutes membership via denoteBelowFamily_eq_empty_of_ge.
-- universeDomainPiArmFromInductiveHypotheses then discharges the arm gated on the WELL-TYPED-guaranteed threshold
-- (denote innerLevelExpr env < outerLevel = the Π-formation level constraint Type@inner : Type@outer), assembling
-- IsReducibleTypeAtAllDenoteLevels PER OUTPUT LEVEL (so the codomain candidate may DRIFT — no member-stability):
-- above the inner level decode + transport to the backbone candidate + fire the codomain IH's canonical
-- member-predicate; at/below the inner level the domain is empty so the codomain obligation is vacuous. Remaining
-- #752 arms: composite/threshold-drift (piType) + the high-inner-universe case (unreachable for well-typed input).
#assert_no_axioms FX1Poly.Typed.universeDenotePredicate_belowFamily_aboveThreshold
#assert_no_axioms FX1Poly.Typed.universeDenotePredicate_belowFamily_empty
#assert_no_axioms FX1Poly.Typed.universeDomainPiArmFromInductiveHypotheses
-- universeDomainMemberStableToOuter: the universe-code instance of the unified piArm's memberStableToOuter,
-- gated on inner < outerLevel. A member at source forces inner < source (else empty), decodes to SN ∧
-- reducible-at-inner, the same predicate as the outerLevel candidate (also above inner) — so it transports.
#assert_no_axioms FX1Poly.Typed.universeDomainMemberStableToOuter

-- DenoteKeyedReducibilitySmoke (regression corpus, SN-149-flavored): the first CONCRETE denote-reducibility
-- witnesses — the two LEAF cases of the step functor. smoke_universeCode_isReducibleAtDenote: the universeCode
-- arm (a universe code reducible at EVERY level, the anti-vacuity refuting SN-001's empty fuel-0 base).
-- smoke_neutralVariable_isReducibleAtDenote: the neutral arm (a context variable, weak-head-normal non-Π
-- non-universe, reducible with the SN candidate; noWeakHeadStep from noStep_var via WeakHeadStep.toStep, the
-- root-generator inequalities via show-then-decide on the closed enum). The universe/neutral leaves of the
-- denote reducibility relation, guarding the load-bearing entry points against regression.
#assert_no_axioms FX1Poly.Typed.smoke_universeCode_isReducibleAtDenote
#assert_no_axioms FX1Poly.Typed.smoke_neutralVariable_isReducibleAtDenote
-- smoke_sigmaFormer: the neutral arm on a FORMER (not a leaf) — a Σ-type former is reducible-as-type
-- unconditionally (noWeakHeadStep via nomatch; no constraint on the children), concretely witnessing the EASY
-- half of the genFormationPi reducible-as-type ingredient (non-Π non-universe formers are reducible types; only
-- the Π case routes through the piType arm and constrains its children).
#assert_no_axioms FX1Poly.Typed.smoke_sigmaFormer_isReducibleAtDenote

-- SN-D5d (denote universe-member CR1 + Σ-from-child-members assembly): bridges the children's universe
-- MEMBERSHIPS (what the FT telescope IH supplies) to sigmaFormationMemberAtDenote's SN premises.
-- stronglyNormalizing_of_universeMemberAtDenote: a member of Type@e above threshold is SN (universe candidate
-- pinned via universeMembership_levelIrrelevant + ReducibleTypeAtDenote.deterministic — the threshold is the
-- fundamental #672 caveat). sigmaFormationFromChildMembersAtDenote: domain member + codomain member at var 0
-- ⟹ Σ universe membership (domain SN by CR1; codomain-under-binder SN by CR1 then openBodyOfConsSubst; the
-- denote analogue of the fuel sigmaFormerOfChildMembershipsAtRequiredLevel).
#assert_no_axioms FX1Poly.Typed.stronglyNormalizing_of_universeMemberAtDenote

-- SN-D5d (the genFormationPi Σ FT arm, premise-isolating like fundamentalPiIntroAtDenote): domain universe
-- membership (CR1-discharged to domain SN) + codomain under-binder SN, both ∀-substitution, ⟹ the Σ former's
-- FundamentalConclusionAtDenote at Type@levelExpr. The Σ case reduces to children SN (reducible-as-type is the
-- free neutral arm); the codomain SN is the deferred premise (its production needs var-0 mining at the weakened
-- scope = the Kripke-obstructed SN-040). The direct analogue of fundamentalPiIntroAtDenote for genFormationPi/Σ.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationSigmaAtDenote

-- SN-D5d (the genFormationPi Π FT arm, premise-isolating — the Π twin of the Σ arm, completing the 2-case
-- split): domain universe membership (CR1 → domain SN) + codomain under-binder SN + the Π former's
-- reducible-as-type at the decoded output level (the #752 threshold residual, isolated as a premise) ⟹ the Π
-- former's FundamentalConclusionAtDenote. Routes through fundamentalTypeFormerAtDenote; Π former SN is
-- piTyCode_isStronglyNormalizing_of_domain_codomain. Both genFormationPi branches are now premise-complete, the
-- two #672-family walls cleanly isolated: codomain SN (denote SN-040, shared) + Π reducible-as-type (#752).
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationPiAtDenote

-- POSITIVE complement to the obstruction (DenoteKeyedUniverseBoundedCumulativity): in the BOUNDED regime
-- (denote levelExpr env < ambient), the universe candidate is level-STABLE -- universeDenotePredicate reaches
-- lowerAt only at the fixed index denote e, which the below-family coherence (denoteBelowFamily_eq_reducible)
-- rewrites to the bound-independent ReducibleTypeAtDenote env (denote e). universeDenoteCandidate_boundIndependent:
-- the candidate agrees pointwise at two ambient levels both exceeding denote e. universeReducible_withLowerCandidate
-- _atHigher: cumulativity below the bound (same-candidate transport up via ofPointwiseIff). Together with the
-- obstruction witness this pins the EXACT cumulativity boundary (holds iff universe < ambient); the gap regime
-- is the sole residual = exactly what the bound-carrying refactor (#753) excludes by construction. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.universeDenoteCandidate_boundIndependent

-- closedTypeCodeStronglyNormalizingFromFundamentalAtDenote (SN-D6 type-code fragment): a CLOSED subject
-- classified by Type@levelExpr (decoded level < ambient) satisfying the denote FT conclusion at the empty context
-- is strongly normalizing. Composes closedMemberAtDenote (FT conclusion → closed universe membership) with the
-- shipped denote universe-member CR1 stronglyNormalizing_of_universeMemberAtDenote (bound-packaged by levelAbove).
-- The early-win type-code fragment of SN-D6 — subjects that ARE types, where denote CR1 is threshold-free (the
-- general-classifier CR1 carries the denoteBelowFamily neutral-inclusion bound the cumulativity obstruction pins).
-- Conditional only on the (still-blocked) FT conclusion; de-risks SN-D5 without the non-uniform genFormationPi residual.
#assert_no_axioms FX1Poly.Typed.closedTypeCodeStronglyNormalizingFromFundamentalAtDenote

-- SN-D5d (the SN-040-FREE codomain-member wiring — CORRECTS the ticks #18/#19 SN-040 claim): the codomain's
-- universe membership at `cons headTerm σ` (var0 → a domain member, σ tail UN-RENAMED) comes from the codomain
-- IH via ReducibleEnvAtDenote.cons — NO renaming-closure (SN-040). The `cons` (prepend) vs `lift` (weaken-rename)
-- distinction is the whole point. Consequence: the genFormationPi residual UNIFIES to #752 alone (the domain
-- member var0 routes through the A2 bridge = #752; there is NO separate SN-040 Kripke wall).
#assert_no_axioms FX1Poly.Typed.codomainMemberFromIH

-- DenoteKeyedMemberForwardClosed (CR2 for the denote relation, UNCONDITIONAL — first piece of the bounded-CR
-- decomposition toward B1'): every denote-reducible type's candidate is forward-closed under Step on members.
-- Uses only the lowerForwardStep leg (unconditional), never the bounded neutralInclusion. Π arm reduces to the
-- codomain CR2 (no domain candidacy ⟹ no bound); universe arm uses lowerForwardStep. Isolates the level bound
-- to CR1's Π-arm + CR3.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.memberForwardClosed

-- DenoteKeyedMemberWeakHeadExpansion: the inductive BACKBONE of the denote member weak-head expansion (the
-- lambda-arm engine toward SN-043/#672). One induction over ReducibleTypeStepDenote in the GENERAL form
-- (WeakHeadStep source reduct + SN source — the β-specific form breaks at the Π arm), discharging FOUR arms
-- intrinsically (neutral = SN source; universe = the unconditional backward leg; whnf/ofPointwiseIff = IH) and
-- isolating the fifth (piType = the application-SN-spine arm) as an explicit piArm hypothesis — the
-- ofReducibleTypeStepDenote discipline. The lambda FT arm instantiates with source = app (lam body) arg + SN
-- via appLam_isStronglyNormalizing_of_contractum; a proof of piArm alone completes the full member WHE.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.memberWeakHeadExpansionModuloPi

-- DenoteKeyedHeadExpansion (SN-D1): the SPINE-GENERAL head-expansion closure ported from the fuel layer
-- (StratifiedReducibleTypeHeadExpansion.lean:98) onto the denote relation — the lower-risk lambda-arm vehicle
-- (Route Y; spine absorbs the extra app arg via applySpineApp_append, so NO application-SN spine / NO piArm).
-- The parametric form takes a per-level lowerHeadExpand leg; the unconditional ReducibleTypeAtDenote corollary
-- discharges it via denoteBelowFamily_backwardWeakHeadStep on WeakHeadStep.betaSpine — bound-free (vacuous
-- above the bound). Feeds SN-D2 (abstractionMemberAtDenote via the generic DependentArrowCandidate.abstraction).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.headExpansionClosed
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.headExpansionClosed

-- DenoteKeyedAbstractionMember (SN-D2): the denote FT's Π-INTRODUCTION (λ) member arm, the introduction twin
-- of applicationMemberAtDenote. lam body is a denote-reducible MEMBER of Π domainCode codomainCode, assembled
-- in one anonymous constructor: the Π type is reducible with the dependent-arrow candidate via the piType ctor
-- (whose candidate is defeq to DependentArrowCandidate), and λ-membership is the generic
-- DependentArrowCandidate.abstraction fed SN-D1's ReducibleTypeAtDenote.headExpansionClosed for the codomain
-- head-expansion-closure premise. The domain CR1 (domainArgumentsSN) is an explicit premise, deferring the
-- bounded denote CR1 to BRICK 5; the FT supplies it at the ambient classifier level. Feeds SN-D3 (under-subst)
-- and the SN-D5 FT induction's Π-introduction case.
#assert_no_axioms FX1Poly.Typed.abstractionMemberAtDenote

-- DenoteKeyedAbstractionUnderSubst (SN-D3): the FT-shaped under-closing-substitution twin of SN-D2, the
-- introduction counterpart of applicationMemberUnderClosingSubstitution / piFormationUnderClosingSubstitution.
-- subst σ (Π A B) and subst σ (λ body) distribute definitionally (children crossing the binder get lift σ);
-- the codomain/body premises arrive in the FT IH shape (under cons argument σ) and bridge to
-- abstractionMemberAtDenote's subst0 … (lift σ) shape via RawTerm.subst_cons_eq_subst0_lift. The
-- codomainCandidate is pinned explicitly (existentially packaged in the conclusion). Feeds the SN-D5 FT
-- induction's Π-introduction case under the closing substitution.
#assert_no_axioms FX1Poly.Typed.abstractionMemberUnderClosingSubstitution

-- DenoteKeyedFundamentalMotive (SN-D4): the denote FT conclusion motive + the two LEAF member arms. The motive
-- FundamentalConclusionAtDenote uses a SINGLE uniform ambient level (not the per-variable contextLevels vector
-- the fuel route FundamentalConclusionLevelIndexed needed) — the denote relation's level-irrelevance lets one
-- ambient level carry the whole judgment, the binder cons threading the same level. fundamentalVarAtDenote =
-- ReducibleEnvAtDenote.lookupReducible (subst on a variable is the substitution lookup definitionally);
-- fundamentalUniverseFormationAtDenote = universeFormationMemberUnderClosingSubstitution (carries the levelAbove
-- side condition the FT discharges at a large-enough ambient level). The recursive arms (conv/piIntro/piElim/
-- genFormationPi) belong to the SN-D5 induction assembly.
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtDenote
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationAtDenote

-- DenoteKeyedFundamentalPiElim (SN-D5b): the denote FT's Π-elimination (application) dispatcher arm — the first
-- RECURSIVE-arm dispatcher (leaves shipped in SN-D4). Lowest-risk recursive arm: a direct composition of
-- applicationMemberUnderClosingSubstitution with the function + argument sub-conclusions at the SAME closing
-- substitution / environment / uniform ambient level — NO level-bridge (unlike the conv arm, which must extract
-- the target type's reducibility at the ambient level from a universe membership at the decoded level). Feeds
-- the SN-D5 HasTypeDescPi induction's piElim case.
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimAtDenote

-- DenoteKeyedFundamentalConv (SN-D5a): the denote FT's conversion dispatcher arm. The real content is
-- convMemberUnderClosingSubstitution (pushes Conv under σ, transports the member). SOLE RESIDUAL isolated as the
-- explicit reclassifierReducible premise = the target type's reducibility at the AMBIENT level — the single-level
-- motive's genuine obstruction: the reclassifier IH gives reducibility only at the DECODED level (universe
-- membership), and bridging to ambient is the general denote type-level level-irrelevance (A2). No conv-transport
-- produces it directly (reducibility candidates aren't backward-closed under arbitrary Step; convInvariant is
-- determinism-only at both layers). The wiring discharges the premise via the reclassifierTyped IH + the A2
-- universe-membership→ambient bridge (carrying denote levelExpr env < level). piIntro's domain hits the SAME
-- bridge; piElim sidesteps it.
#assert_no_axioms FX1Poly.Typed.fundamentalConvAtDenote

-- DenoteKeyedUniverseMembershipIntro (SN-D5d step (b)): the universe-membership INTRODUCTION — the converse of
-- the A2 decode bridge (#751). universeMembershipIntroAtDenote: a denote-reducible SN type AT its decoded level
-- is a denote-reducible MEMBER of its universe code Type@levelExpr at any higher ambient level. It IS the
-- headline universe candidate (universeMembership_levelIrrelevant, whose decode-set is SN ∧ reducible-at-decoded)
-- repackaged as an intro, no new induction; universeFormationMemberAtDenote is its closed-universe-code instance.
-- fundamentalTypeFormerAtDenote: the type-former FT arm (universeFormation/piFormation/genFormationPi) MODULO
-- route-A reducibility — the closed universe classifier is subst-fixed so the conclusion lands on the intro,
-- isolating the former's TYPE-reducibility (route A / the A2 composite-domain piArm #752) as the single premise,
-- the same isolation discipline fundamentalConvAtDenote uses.
#assert_no_axioms FX1Poly.Typed.universeMembershipIntroAtDenote
#assert_no_axioms FX1Poly.Typed.fundamentalTypeFormerAtDenote

-- DenoteKeyedNonDependentArrow (an unconditional slice of #752): the denote port of the fuel
-- nonDependentArrowOfAllLevelsDomain. A non-dependent arrow domainCode → codomainBase is reducible at ALL denote
-- levels from domain + base-codomain all-levels reducibility ALONE — NO domain-candidate uniformity, NO
-- member-extension, NO piArm. The weaken-cancellation subst0 (weaken codomainBase) arg = codomainBase collapses
-- the piType codomain obligation to the constant base fact, so the (possibly composite/drifting) domain candidate
-- is never consumed per-argument. universeDomainNonDependentArrow is the Type@e → codomainBase instance (reaches
-- past the universe-domain wall). The dependent composite-domain Π stays gated on #752.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllDenoteLevels.universeDomainNonDependentArrow

-- DenoteKeyedFundamentalPiIntro (SN-D5c): the denote FT's Π-introduction (λ) dispatcher arm — THE binder crux
-- (the case the per-level route walled on). Canonical-candidate move: domain + codomain candidates are the
-- canonical member predicate IsReducibleMemberAtDenote env level (subst …), so (a) the env-cons arg-membership
-- is direct (candidate = membership predicate) and (b) bodyReducible is direct (codomain candidate = body IH
-- target, no deterministic). Assembled via abstractionMemberUnderClosingSubstitution (SN-D3) + reducibleMemberCandidate
-- + ReducibleEnvAtDenote.cons. UNCONDITIONAL given the three caller premises: domain/codomain reducible-at-level
-- (= A2-bridge-applied IHs) + domain CR1; the body IH is direct. Feeds the SN-D5 induction's piIntro case.
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtDenote

-- DenoteKeyedClosedMember (route-E / SN-D6 precursor): closed-term reducibility from the empty-context denote FT
-- conclusion. Instantiate the FundamentalConclusionAtDenote at the empty context at the IDENTITY substitution +
-- ReducibleEnvAtDenote.empty, then cancel subst identity = id (RawTerm.subst_identity_apply) — yielding the closed
-- subject as a denote-reducible member of its closed classifier. Composed with denote CR1, this is the
-- wire-to-SN step for the closed-term SN headline (SN-043). Fed the eventual unconditional denote FT (#744).
#assert_no_axioms FX1Poly.Typed.closedMemberAtDenote

-- DenoteKeyedTelescopeReducible (SN-D5d first brick): the denote-keyed telescope-reducibility relation, the
-- return type the genFormationPi premise's future fundamentalTelescope companion produces. Single-level denote
-- analogue of the fuel TelescopeReducible (simpler: one ambient level, no +1 scope). nil = vacuous base; twoChild
-- = the Π/Σ-former unfolder (binderShifts [0,1] = consecutiveShifts 0 2). Starts the genFormationPi arm
-- infrastructure (#750); the cons recursion + the genFormationPi connection remain.
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtDenote
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtDenote.nil
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtDenote.twoChild

-- DenoteKeyedTelescopeFundamental (SN-D5d step 1): the telescope FT companion arms that BUILD
-- TelescopeReducibleAtDenote from the typed DescTelescopePi + per-child fundamentals — the denote analogues of
-- the fuel fundamentalTelescopeNilAtAll/fundamentalTelescopeConsAtAll (FundamentalAtAllTelescope), single-level
-- (no ∀ level over the head member). nil = True.intro at count 0; cons = the relation's cons conjunction
-- (head member from headFundamental σ reducibleEnv, subst_universeCodeCell cancelling subst on the closed code;
-- tail passed through). These are the DescTelescopePi.nil/.cons minor-premise bodies the eventual mutual FT
-- recursor discharges; the genFormationPi arm reads the produced telescope for its children's reducibility.
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeNilAtDenote
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtDenote

-- DenoteKeyedUniformReducible (#752 foundation): the uniform-candidate-above-threshold motive
-- UniformlyReducibleAboveDenote — the STRENGTHENING that breaks the piType circularity in the level-irrelevance
-- proof (the all-levels motive's per-level candidate varies; this fixes a single candidate above a threshold, so
-- the piType arm's domain IH supplies a uniform domain candidate that transfers the codomain gate across levels).
-- Three easy backbone arms: ofNeutral (threshold 0, SN candidate, level-independent ctor), ofUniverseCode
-- (threshold denote e, level-independent decode-set via universeMembership_levelIrrelevant), headExpand (rewrap
-- the contractum's uniform candidate via whnfExpand). PLUS the backbone induction ofReducibleTypeStepDenote —
-- a verbatim mirror of the all-levels IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote (same 5-arm
-- dispatch, level-independent uniform motive, piType isolated as the piArm hypothesis). REMAINING for #752: the
-- piArm discharge itself — deeper than one motive-swap (the codomain threshold-swap needs a "reducibility bounds
-- a type code's universe level" lemma; see the module header), then the projection to IsReducibleTypeAtAllDenoteLevels.
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofNeutral
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.headExpand
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofReducibleTypeStepDenote
-- Non-dependent arrow piArm (uniform motive): the UNCONDITIONAL slice of #752. The weaken-cancellation makes
-- the codomain constant in the argument, so the codomain threshold-swap vanishes (Π threshold = domThreshold +
-- codomainThreshold, NOT max — the Nat.le_max_* lemmas leak propext, so + with Nat.le_add_* is the clean route).
-- Correction recorded: the prior "reducibility bounds a type's universe level" idea is FALSE (Type@huge is a
-- reducible type at every level), so the DEPENDENT composite piArm needs a different technique, not a bound lemma.
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.nonDependentArrow
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.universeDomainNonDependentArrow
-- The consumable interface: uniform reducibility ⟹ is-a-reducible-type above the threshold (drops the candidate
-- to existence). The face the uniform backbone presents to a consumer (the A2 ambient-level bridge) once the
-- piArm lands. Weaker than IsReducibleTypeAtAllDenoteLevels (below-threshold reducibility is leaf-specific).
#assert_no_axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.isReducibleTypeAboveThreshold
#assert_no_axioms FX1Poly.Typed.denote_domainLevel_le_lmaxAll_pair
#assert_no_axioms FX1Poly.Typed.denote_codomainLevel_le_lmaxAll_pair
