import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.DataReducibilityCoverage
import FX1Poly.Core.DataTaitCandidate
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
import FX1Poly.Typed.ClosedDataCanonicity
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

/-! # Tools/AuditAll/AuditTyped
   — persistent per-declaration zero-axiom gate for the typed layer

The typed layer (polycell.md §11.8.5) is the dim-0 soundness stratum: the
`.context` / `.type` / `.term` cells that classify each other.  The native
`TypingContext` de Bruijn telescope is the `.context`-sort spine the `HasType`
engine consumes via the variable rule.

Every declaration here must elaborate without `propext`, `Classical.choice`,
`Quot.sound`, or `sorryAx` — so any future edit that introduces an axiom
dependency fails `lake build FX1PolyAudit` immediately.  The `lookup`
de Bruijn destructuring and `length_eq_scope` induction are the two places
a careless rewrite could pull `propext` through the match compiler; these
gates pin them shut.
-/

/-! ### TypingContext — native de Bruijn telescope + lookup + coherence -/

#assert_no_axioms FX1Poly.Typed.TypingContext
#assert_no_axioms FX1Poly.Typed.TypingContext.length
#assert_no_axioms FX1Poly.Typed.TypingContext.length_eq_scope
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_zero
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_succ

/-! ### HasType engine — type-formation arms (var / conv / universe / Π / Σ) + IsType -/

#assert_no_axioms FX1Poly.Typed.universeCodeCell
#assert_no_axioms FX1Poly.Typed.emptyTypeCell
#assert_no_axioms FX1Poly.Typed.variableCell
#assert_no_axioms FX1Poly.Typed.piTyCodeCell
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell

/-! ### Honesty — 0-false-positive probe (ill-typed cell has no derivation) -/

#assert_no_axioms FX1Poly.Typed.unitCell
#assert_no_axioms FX1Poly.Typed.RawTerm.headGenerator

/-! ### Typed renaming + weakening (the structural cartesian lift) -/

#assert_no_axioms FX1Poly.Typed.rename_variableCell
#assert_no_axioms FX1Poly.Typed.rename_universeCodeCell
#assert_no_axioms FX1Poly.Typed.rename_emptyTypeCell

/-! ### Typed substitution (the β-engine) — `subst0` preserves typing -/

#assert_no_axioms FX1Poly.Typed.subst_variableCell
#assert_no_axioms FX1Poly.Typed.subst_universeCodeCell
#assert_no_axioms FX1Poly.Typed.subst_emptyTypeCell
#assert_no_axioms FX1Poly.Typed.subst_singleton_renameWeaken_cancel

/-! ### Universe-code cell destructor — recovers
    `universeCodeCell e flag` from `headGenerator = gen_universeCode` via the
    `RawTermChildren.eq_childNil` brick; the raw destructor `Decidable IsType`
    needs to apply `HasType.universeFormation`. -/

#assert_no_axioms FX1Poly.Typed.eq_universeCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.eq_variableCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.headGenerator_universeCodeCell
#assert_no_axioms FX1Poly.Typed.headGenerator_variableCell
-- universe-code cell injectivity (no-Type-in-Type probe support): equal
-- universe codes have equal levels and flags, via `cases` on the cell equality
#assert_no_axioms FX1Poly.Typed.universeCodeCell_inj
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
-- UNIVERSE-CODE CONVERSION INJECTIVITY (no-Type-in-Type under conversion): two CONVERTIBLE universe codes have
-- equal levels and flags. Universe codes are step normal forms (noStep), so global confluence
-- (Conv.iff_normalForms_eq_of_confluence, the #420/#716 harvest, no SN premise) collapses Conv to syntactic
-- equality, then universeCodeCell_inj. The totalBridge conv arm reads this to align a universe-code
-- reclassifier's level with the classifier it was converted from (the conjunct-2-through-conv residual).
#assert_no_axioms FX1Poly.Typed.universeCodeCell_inj_of_conv
-- VARIABLE-CELL CONVERSION INJECTIVITY (variables are conv-rigid): two CONVERTIBLE variable cells share a de
-- Bruijn index. Same normal-form collapse (both are gen_var/childNil step normal forms → confluence reduces Conv
-- to syntactic equality → mkGen injectivity). The conv-arm dispatch fact the formation-engine totalBridge reads:
-- a variable-reclassifier whose subject's classifier is a convertible variable shares its index, so the looked-up
-- type IS the reclassifier and convVariableReclassifierOfStratified applies.
#assert_no_axioms FX1Poly.Typed.variableCell_inj_of_conv
-- A VARIABLE IS NEVER CONVERTIBLE TO A UNIVERSE CODE: both are step normal forms with distinct head generators
-- (gen_var vs gen_universeCode), so global confluence collapses any conversion to syntactic equality, refuted by
-- the head distinctness. The conjunct-2-vacuity fact the totalBridge conv-VARIABLE arm reads.
#assert_no_axioms FX1Poly.Typed.variableCell_not_conv_universeCodeCell

/-! ### Π-formation shape bricks — `piTyCodeCell`
    smart ctor + head-generator computation + the two-child destructor that
    the `piFormation` arm + the decider consume. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_piTyCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_noStep_of_childrenNoStep
-- `piTyCodeCell` is injective (domain/codomain recovered): the component extractor
-- the `piFormation` arm of `inversionPiCode` aligns the inducted arm's own
-- domain/codomain with the inversion target.  `cases` on the cell equality (the
-- propext-free substrate tactic), NOT `injection`.
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_inj

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
-- GTL-11 LANDED: the grown head-agnostic former-classifier inversion + the listCode piElim/empty refutations
-- (the grown twin of HasTypeDesc.inversionFormerWithConvGeneric); the one-child formation telescope level
-- projection (the DescTelescope sibling of DescTelescopePi.oneChildLevel) the formation vector-assembly arm uses.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.formerClassifierConvUniverseGeneric
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.listFormerNotTypedAtEmptyType
#assert_no_axioms FX1Poly.Typed.DescTelescope.oneChildLevel
-- GTL-13 part 1: the row-INDEPENDENT optionCode reducibility/shape substrate (the "reducibility-candidate
-- identification" half) — the one-child optionCode twins of the listCode shape reconstruction, the under-subst
-- universe-membership, the level-indexed telescope member, and the bounded genFormationPi recursor arm. They
-- land ahead of the typingRuleDescOf optionCode row (the formation row + ~18-site canonical-forms cascade follow).
#assert_no_axioms FX1Poly.Typed.eq_optionCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.optionCodeFormationUnderSubst
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.optionFormerFromTelescope
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationOptionFromTelescopeAtBoundedSucc
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
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_inj
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_noStep_of_childrenNoStep
#assert_no_axioms FX1Poly.Typed.rename_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_codomain

/-! ### ★ MOONSHOT CORE — the description-driven generic typing engine
    (`HasTypeDesc`, polycell.md §11.8.5 / §5.2: the Natural-Model display map
    `Tm ↠ Ty` realized as a data-driven cascade-free `gen` arm).  `HasTypeDesc`
    = var + conv + nullary `universeFormation` + ONE generic `genFormation` arm
    consuming a per-generator `TypingRuleDesc` (the `typingRuleDescOf` table),
    typing the whole dependent-type-former family via the mutual `DescTelescope`
    spine with output = `rule.outputType scope levels flag` (for the type-formers,
    `universeFormerOutput = universeCodeCell (lmaxAll levels) flag`).  The
    `outputType` field realizes the §11.8.5 "non-uniform output" seam (output is
    rule-DATA, not hardwired).
    The two reconstruction theorems witness Π AND Σ through the SAME arm (P13
    cascade-freedom: a new dependent former is one `typingRuleDescOf` row, ZERO
    new arms).  Propext-free `lmaxFold`/`lmaxAll` (no overlapping patterns) +
    `typingRuleDescOf` (nested `if` over DecidableEq, no 194-ctor wildcard);
    `TypingRuleDesc` is pure syntax (no HasTypeDesc → genFormation strictly
    positive); output classifier an explicit INDEX (Prop, P14). -/

#assert_no_axioms FX1Poly.Typed.lmaxFold
#assert_no_axioms FX1Poly.Typed.lmaxAll
#assert_no_axioms FX1Poly.Typed.universeFormerOutput
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
-- FLAG-UNIQUENESS substrate (GTL-09): the `levels ≠ []` guard of HasTypeDesc.uniquenessNative, made generic over
-- the formation generator. levels_length_eq_binderShifts is a structural telescope recursion (level list and
-- shift list have equal length); typingRuleDescOf_binderShiftsNonEmpty is the ≥1-child-family table fact
-- (pi/sigma both carry [0,1]) — extends by ONE by_cases row per ≥1-child data type code, breaks ONLY on a
-- nullary Empty former (CON-A1, the documented future branch); levels_ne_nil_of_isFormation is the combined
-- consumer-facing form. This retires the last per-former by_cases in the formation-family metatheory.
#assert_no_axioms FX1Poly.Typed.DescTelescope.levels_length_eq_binderShifts
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_binderShiftsNonEmpty
#assert_no_axioms FX1Poly.Typed.DescTelescope.levels_ne_nil_of_isFormation
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
#assert_no_axioms FX1Poly.Typed.DescTelescope
#assert_no_axioms FX1Poly.Typed.hasTypeDesc_piFormation_viaGenArm
#assert_no_axioms FX1Poly.Typed.hasTypeDesc_sigmaFormation_viaGenArm
-- DECIDABILITY (P11 0-FN) of the description engine.  `decidableOfWellFormed` is a native
-- formation decision procedure.  `Conv.decidableOfHasTypeDesc` decides Conv by SN: each classifier
-- is SN by the native `HasTypeDesc.classifierStronglyNormalizing`, fed to the parameter-free
-- `Conv.decidableOfStronglyNormalizing`.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormed
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfHasTypeDesc

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

/-! ### Intrinsic VALIDITY of the description engine (`HasTypeDescValidity`).
    `IsTypeDesc` = the intrinsic "inhabits a universe" over `HasTypeDesc`; it gives the
    description engine its own metatheory.  (Native formation validity lands as
    `HasTypeDesc.classifierIsTypeDescNative`, gated below.) -/
#assert_no_axioms FX1Poly.Typed.IsTypeDesc

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
#assert_no_axioms FX1Poly.Core.StepChildrenSuccessor
#assert_no_axioms FX1Poly.Core.accStepChildrenSuccessor_cons
#assert_no_axioms FX1Poly.Core.accStepChildrenSuccessor_of_allStronglyNormalizing
#assert_no_axioms FX1Poly.Core.formerCell_isStronglyNormalizing_of_accChildren
#assert_no_axioms FX1Poly.Typed.formerCellStronglyNormalizingOfChildren
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectStronglyNormalizingNative
#assert_no_axioms FX1Poly.Typed.DescTelescope.childrenStronglyNormalizingNative
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.Conv.trans_of_hasTypeDescMiddle

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
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedClassifierConvUniverseCode

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

/-! ### INVERSION (P8, FULL) for the description engine — premise telescope AND the
    classifier-`Conv` conjunct (`…WithConv`).  Wires typed `Conv.trans`
    into the description engine: `…WithConv` additionally concludes `Conv classifier
    (universeCodeCell (lmaxAll levels) flag)` — the cell's classifier converts to the
    canonical formation output.  This is the conjunct intrinsic UNIQUENESS (P7) and the
    typechecker's conv-check consume.  Three deltas over the premise half: a `WfContext`
    parameter (threaded as an OUTER argument — the term-mode `match` keeps the context
    index fixed, so it need not be reverted into the motive); the `conv` arm composes
    `Conv`s via `Conv.trans_of_typedMiddle`, the middle's validity from the native
    formation validity on the `conv` premise; the `genFormation` arm pins the `TypingRuleDesc`
    (`Option.some.inj`) so the output reduces to `universeCodeCell (lmaxAll …) …`, then
    `Conv.refl` closes the conjunct.  Both formers (Π + Σ). -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeWithConv
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeWithConv
-- Generic former-CLASSIFIER inversion (HasTypeDescInversion.lean): the WALL-FREE half of the generic
-- former inversion (GTL-08/10 down-payment). Generic over the formation generator (no concrete pi/sigma
-- pinning) — a typed formation cell's classifier converts to Type@(lmaxAll levels, flag). Sidesteps the
-- dependent-subst wall (the file header's documented blocker) by extracting the CLASSIFIER only: the
-- genFormation arm `obtain rfl`s the TypingRuleDesc (children-independent), NEVER substing the generator.
-- Empirically isolates the wall to the telescope-extraction (the residual hard half).
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionFormerClassifierGeneric
-- Generic former-TELESCOPE inversion (HasTypeDescFormerTelescopeInversion.lean): the wall-bearing half
-- of the generic former inversion — recover the children DescTelescope for ANY formation generator. The
-- documented dependent-subst wall (free generator vs arm generator) turned out NAVIGABLE in the
-- free-subject+thread-Eq shape: subst generatorAgree (the free-generator subst) SUCCEEDS, then injection
-- subjectEq + subst_vars aligns the children — the same propext-free idiom the per-former inversions use.
-- Unblocks HasTypeDescUniqueness (GTL-09) + the arity-bound reducibility arms.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionFormerTelescopeGeneric
-- Generic former inversion FULL (telescope + classifier Conv at consistent levels/flag), the generic
-- analogue of inversionPiCodeWithConvGeneral. Merges the classifier + telescope halves off the SAME
-- genFormation arm — the consistency uniquenessAgree-style consumers need. Zero-axiom (same cracked-wall
-- idiom). NOTE: HasTypeDescUniqueness can't yet consume it generically — its flag-uniqueness guard
-- (levels ≠ []) needs binderShifts ≠ [] (former has ≥1 child), NOT a clean cascade invariant (nullary
-- Empty violates it); kept per-former pending the nullary-former flag-uniqueness treatment.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionFormerWithConvGeneric

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
#assert_no_axioms FX1Poly.Typed.DescTelescope.renameRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.weakenUnderBinding

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
#assert_no_axioms FX1Poly.Typed.DescTelescope.substRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substituteUnderBinding

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaCoherence_formationBody
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaCoherence_formationFunction
-- TY-ETA-GROWN (#1033): generalize the forward η-coherence from formation-typed f (effectively only variables of
-- function type) to ANY grown-typed f — λ-terms, applications, Church numerals. etaExpansionPreservesTypingGrown
-- (★): well-formed grown context + f : piTyCode D C ⟹ etaLamSource f : piTyCode D C, via validity +
-- invertPiTyCode (grown domain/codomain) + grown weakenUnderBinding + rename_piTyCodeCell + the η identity +
-- piIntro/piElim. etaCoherenceGrown = the redex/reduct coherence pair. The forward half of grown η-SR (#477);
-- the inverted half still needs grown strengthening. Zero-axiom (same de Bruijn substrate as the formation twin).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaExpansionPreservesTypingGrown
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaCoherenceGrown
-- TY-ETA-COMPUTES (#1034): the OPERATIONAL content of η on top of forward η typing. etaLamSourceApplication (★):
-- (etaLamSource f) a ↝β f a for ANY scope/f/a — applying an η-expansion β-steps to applying the original (raw,
-- via subst0_etaLamSource_body's weaken/var-0 cancellations). etaExpansionTypedAndOperational bundles the static
-- (typing-preserved) and dynamic (application-preserved) halves into η-coherence. The two Church witnesses make it
-- concrete: η-expanding churchNumeralLambda n preserves BOTH its Church-Nat type (∘ #1007) AND its computed iterate
-- f^n x (∘ #1009, one leading admin β-step). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.subst0_etaLamSource_body
#assert_no_axioms FX1Poly.Typed.Step.etaLamSourceApplication
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaExpansionTypedAndOperational
#assert_no_axioms FX1Poly.Typed.etaExpandedChurchNumeral_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.etaExpandedChurchNumeral_appliedReducesToIterate

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
#assert_no_axioms FX1Poly.Typed.renameContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.weakenUnderBinding

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
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.genFormationToHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.renameRespectingTelescope

/-! ### GROWN-ENGINE SUBSTITUTION — `ofFormation` leg.  `HasTypeDesc.substIntoGrown` carries a
    formation derivation along a substitution whose substituents are `HasTypeDescPi`-typed, into the
    grown engine (a formation subject substituted by a grown term is no longer a formation term, so
    the result lands in `HasTypeDescPi`).  Its `genFormation` case rebuilds through the generic
    `genFormationPi` from a substituted grown spine (`DescTelescope.substIntoGrown` → `DescTelescopePi`)
    with no per-former child projection.  Mutual structural recursion on the formation derivation; the
    recursion stays within the `HasTypeDesc`/`DescTelescope` family, so no cross-inductive boundary. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substIntoGrown
#assert_no_axioms FX1Poly.Typed.DescTelescope.substIntoGrown

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
#assert_no_axioms FX1Poly.Typed.substContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substRespectingContext
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.substRespectingTelescope

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionSigmaCodeTelescopeGeneral
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

/-! ### Π/Σ-CODE `Conv` STRUCTURAL CHARACTERIZATION (injectivity + congruence), SN-FREE.
    `Conv (piTyCodeCell A B) (piTyCodeCell A' B') ↔ Conv A A' ∧ Conv B B'` (Σ dual).  Since `Conv` is
    joinability and `gen_piTyCode` is not a redex root, a Π-code's head is STABLE under reduction
    (`shapeStable_piTyCode`, via `Step.from_piTyCode`); two joinable Π-codes thus share a `piTyCodeCell`
    common reduct, and the children join componentwise — NO confluence/SN/`Conv.trans`.  The injectivity
    direction is the ingredient typed SR consumes to peel a conv-disguised Π-type; the iff is the
    decidable-`Conv` recursion for the dependent type-code formers. -/
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_inj
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_piTyCodeGeneral
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_piTyCode
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_sigmaTyCodeGeneral
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_iff
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_iff
-- Conv-to-former REDUCTION corollaries: a subject Conv to a Π/Σ-code StepStar-reduces to that former with
-- Conv-related components (the GrownCtxConv-5 / context-conversion ingredient that recovers an honest piTyCode shape
-- from a conv-disguised classifier; Join-unpack + shapeStable, SN-free).
#assert_no_axioms FX1Poly.Typed.Conv.reducesToPiTyCode
#assert_no_axioms FX1Poly.Typed.Conv.reducesToSigmaTyCode
-- FLAT (non-dependent, binary) twin: the same SN-free Conv structural characterization for the five flat
-- data type-code formers — arrow/product/sum/either/equiv (the [0,0]-binderShift formers HasTypeDescFlat
-- types). Both children at the SAME scope (no binder), so lighter than Π/Σ. Per former: head-stability +
-- cell injectivity + Conv-inj (the inversion ingredient) + Conv-cong + Conv-iff.
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_arrowCodeGeneral
#assert_no_axioms FX1Poly.Typed.arrowCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.arrowCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.arrowCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.arrowCode_iff
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_productCodeGeneral
#assert_no_axioms FX1Poly.Typed.productCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.productCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.productCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.productCode_iff
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_sumCodeGeneral
#assert_no_axioms FX1Poly.Typed.sumCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.sumCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.sumCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.sumCode_iff
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_eitherCodeGeneral
#assert_no_axioms FX1Poly.Typed.eitherCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.eitherCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.eitherCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.eitherCode_iff
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_equivCodeGeneral
#assert_no_axioms FX1Poly.Typed.equivCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.equivCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.equivCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.equivCode_iff
-- COMPLETING the Conv-injectivity arc over the type-code formers: the UNARY data formers list/option
-- (one child) and the TERNARY identity former id (type code + two endpoint terms). Same SN-free recipe
-- (head-stability via Step.from_<former> + StepStar.Join unpack + Conv.ofChildren). With the Π/Σ
-- (#865/866) and flat-binary (#947) files, every congruence-only type-code former now has Conv-inj/cong/iff.
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_listCodeGeneral
#assert_no_axioms FX1Poly.Typed.listCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.listCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.listCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.listCode_iff
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_optionCodeGeneral
#assert_no_axioms FX1Poly.Typed.optionCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.optionCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.optionCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.optionCode_iff
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_idCodeGeneral
#assert_no_axioms FX1Poly.Typed.idCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.idCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.idCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.idCode_iff

/-! ### TYPE-CODE DISJOINTNESS (rigidity), SN-FREE — distinct type formers are non-convertible.
    The companion to injectivity: together they give full type-code RIGIDITY (the canonicity
    ingredient — a Π-type is never a Σ-type, never a universe).  Same head-stability mechanism
    (`shapeStable` for Π/Σ, `StepStar.eq_of_noStep` + `noStep_universeCode` for the universe leaf): a
    shared common reduct's head is forced to two distinct generators, refuted by `Generator.noConfusion`. -/
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_not_universeCode
-- a former is never Conv-equal to a VARIABLE either (same shapeStable/noStep_var mechanism): the conv-arm
-- dispatch fact the formation-engine totalBridge reads for the vacuous case "a Π/Σ-code subject reclassified
-- to a type variable" (a former never converts to the variable, so that branch has no hypotheses).
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_variableCell
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_not_variableCell
-- emptyTypeCell is a FOURTH distinct type former (EmptyTypeCodeConvRigidity.lean): never Conv-equal to a
-- Π/Σ/universe code. Same SN-free mechanism, with Step.no_step_from_emptyCode (the empty code is a step
-- normal form) for the empty leg. The Conv-side companion to emptyHasNoClosedMember (#680): a closed value's
-- natural classifier (Π for a λ, a universe code for a former) is never Conv-equal to Empty — the consistency/
-- canonicity inversion ingredient (no closed value is typed at the empty type).
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_emptyTypeCode
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_not_emptyTypeCode
#assert_no_axioms FX1Poly.Typed.Conv.universeCode_not_emptyTypeCode
-- boolTypeCell is the data-type-code sibling (ConvBoolCodeRigidity.lean): never Conv-equal to a Π/Σ/universe
-- code. Same SN-free head-stability mechanism (boolTypeCell is a no-step LEAF, isStepNormalForm by rfl;
-- shapeStable_piTyCode/_sigmaTyCode + noStep_universeCode for the right legs; Generator.noConfusion on the
-- forced head equality). These ARE the CANON-1 (#1048) bool-canonicity rule-outs: a closed normal t:boolCode
-- has head in {lam,piTyCode,sigmaTyCode,universeCode,listCode,optionCode}, and uniqueness-of-typing forces
-- boolCode Conv to lam's classifier (a piTyCode) or a former's classifier (universeCode) — both refuted here.
#assert_no_axioms FX1Poly.Typed.Conv.boolTypeCell_not_piTyCode
#assert_no_axioms FX1Poly.Typed.Conv.boolTypeCell_not_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.boolTypeCell_not_universeCode
-- CASCADE-FREE cross-former discrimination (ConvFormationFormerRigidity.lean): the TABLE-GENERIC rigidity —
-- distinct formation-table formers (any two generators with a typingRuleDescOf row) are non-Conv, proven WITHOUT
-- naming a generator (lifts formerCellStepIsChildCongruence/TG-1 through StepStar for head-stability, then
-- congrArg headGenerator on the shared common reduct). The PAYOFF: once a new formation row lands (the
-- gen_boolCode row of DI-1b, cubical/HIT/IR codes), that former AUTOMATICALLY gets all its cross-former
-- rule-outs from this one theorem — the canonicity rule-out substrate made cascade-free. listCode_not_conv_
-- optionCode = a concrete NEW discrimination (not in the per-pair files) as a by-free non-vacuity instance.
#assert_no_axioms FX1Poly.Typed.StepStar.formationFormerHeadStableGeneral
#assert_no_axioms FX1Poly.Typed.Conv.formationFormerGeneratorEq
#assert_no_axioms FX1Poly.Typed.Conv.formationFormersNotConvOfDistinct
#assert_no_axioms FX1Poly.Typed.Conv.listCode_not_conv_optionCode
-- FLAT-TABLE twin (ConvFlatFormerRigidity.lean): the SAME cascade-free discrimination keyed on the FLAT table
-- (flatTypingRuleDescOf) for the binary non-dependent data formers product/sum/either/arrow/equiv (typed by the
-- standalone HasTypeDescFlat engine, NOT typingRuleDescOf). Lifts flatFormerCellStepIsChildCongruence instead of
-- formerCellStepIsChildCongruence. Together with the typingRuleDescOf version this gives complete cross-former
-- "no confusion" for every data type-code former — the SN-049 (pair/sum/either canonicity) rule-out substrate.
-- productCode_not_conv_sumCode = a concrete NEW discrimination (A × B is never A + B), by-free non-vacuity.
#assert_no_axioms FX1Poly.Typed.StepStar.flatFormationFormerHeadStableGeneral
#assert_no_axioms FX1Poly.Typed.Conv.flatFormationFormerGeneratorEq
#assert_no_axioms FX1Poly.Typed.Conv.flatFormationFormersNotConvOfDistinct
#assert_no_axioms FX1Poly.Typed.Conv.productCode_not_conv_sumCode
-- CROSS-TABLE discrimination (ConvCrossTableFormerRigidity.lean): completes the cross-former no-confusion —
-- a typingRuleDescOf-former (Π/Σ/list/option) is never Conv to a flatTypingRuleDescOf-former
-- (product/sum/either/arrow/equiv). NO disjointness helper needed: the LEFT uses formationFormerHeadStable
-- General, the RIGHT uses flatFormationFormerHeadStableGeneral, then per-instance g1 != g2 (Generator.no
-- Confusion). THIS is the load-bearing SN-049 rule-out: a closed normal t:productCode has head in
-- {lam,piTyCode,...} (all typingRuleDescOf-classified), and piTyCode_not_conv_productCode etc. refute each.
#assert_no_axioms FX1Poly.Typed.Conv.crossTableFormersNotConvOfDistinct
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_conv_productCode
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_not_conv_eitherCode
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
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectHeadIsFormerOrUniverse
-- FORMATION-ENGINE CONSISTENCY: no closed formation-engine term inhabits the empty type
-- (HasTypeDesc .empty t emptyTypeCell → False). Every classifier a closed formation derivation reaches has
-- head gen_universeCode (universeFormation / genFormation outputs) or — for a conv reclassifier — a Π/Σ/universe
-- head (subjectIsVariableOrFormerHead, variable disjunct killed by closedness); none is gen_emptyCode. The
-- FORMATION half of SN-050; no reconstruction, no value-inversion. Zero-axiom (recursor + Generator.noConfusion).
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.noClosedFormationTermAtEmptyType
-- PIELIM-KILLING TOOLKIT (PiTypeFunctionInversion.lean): the ingredients for the grown closed-canonical-forms
-- piElim case. eq_lamCell_of_headGenerator = the 4th head→shape reconstruction (λ companion to pi/sigma/
-- universe/var). The three *NotTypedAtPiType inversions = a type former / universe code is not a member of a
-- Π-type (its classifier is Conv a universe code, which a Π-code is not) — the Π-classifier analogue of the
-- *NotTypedAtEmptyType value inversions. Together they discharge every non-λ shape the app function can take.
#assert_no_axioms FX1Poly.Typed.eq_lamCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeCodeNotTypedAtPiType
-- GROWN CANONICAL FORMS (GrownCanonicalForms.lean): a closed NORMAL grown-typed term has head
-- gen_lam/gen_piTyCode/gen_sigmaTyCode/gen_universeCode (closedNormalSubjectHead, via the propext-free recursor;
-- piElim crux killed by appNormal_functionNormal + not_isStepNormalForm_beta_smoke + the *NotTypedAtPiType
-- inversions). noClosedNormalTermAtEmptyType = grown NORMAL-FORM consistency: no closed normal term inhabits
-- Empty (canonical forms + the *NotTypedAtEmptyType value inversions, NO SR). Full SN-050 adds SN (OB-5) + SR.
#assert_no_axioms FX1Poly.Typed.appNormal_functionNormal
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
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedex_betaStep
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedex_safety
-- EVALUATION DETERMINISM IN ACTION: the redex's UNIQUE normal form is exactly Type@0 (StepStar.single of the
-- β-step reaches it; closedHasUniqueNormalForm — OB-5 SN + raw confluence — forces uniqueness). The concrete
-- computation of an evaluation result through the determinism theorem, the one safety theorem the preceding
-- three witnesses did not exercise.
#assert_no_axioms FX1Poly.Typed.closedIdentityAppRedex_evaluation
-- SN-050 CONSISTENCY made concrete, gated on exactly SR-along-↝* (ConsistencyConditionalOnSubjectReduction.lean):
-- OB-5 (stronglyNormalizingOfWfContext) normalizes a closed t : EmptyType to a reachable normal form; the explicit
-- subjectReductionStar hypothesis carries the EmptyType classifier along the chain; noClosedNormalTermAtEmptyType
-- refutes the closed normal endpoint. The bounded SN model CANNOT discharge this (its emptyTypeCell candidate is
-- the coarse IsStronglyNormalizing via the neutral arm, NOT the empty candidate — CON-A3 needs a canonicity model),
-- so the syntactic route is the tractable one. subjectReductionStar = the iterated SN-055 master dispatcher
-- (SRD-1/SRD-3, blocked on WFG-3/the WfContext↔WfContextDescPi bundle); once it lands this is unconditional SN-050.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyOfSubjectReductionStar
-- CLOSED PROGRESS PER TYPE (GrownClosedProgressByClassifier.lean): the missing "closed + per-classifier +
-- progress" cell, read at the classifier. closedFunctionStepsOrIsLambda = a closed grown-typed term of Π type
-- STEPS or IS a λ (body extracted) — the operational form the function position of an application consumes, the
-- dependent analogue of the graded closedWellTypedProgress sharpened to the exact λ shape. closedTypeStepsOrIsFormer
-- = a closed grown-typed TYPE (universe classifier) STEPS or its head is a type FORMER (Π/Σ/universe/list/option
-- code), never a stuck λ. Both UNCONDITIONAL: the classifier is read only at the already-normal subject (via
-- closedNormalFunctionIsLambda / closedNormalTypeIsFormer), so no reduction step is typed — no SR, no GrownCtxConv-5 #842,
-- no §5; the non-normal case only asserts a step EXISTS. The per-classifier progress refinements of closedProgress.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedFunctionStepsOrIsLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeStepsOrIsFormer
-- EVALUATION DETERMINISM (GrownTypeSafety.lean): closedHasUniqueNormalForm = UNCONDITIONAL — a closed grown-typed
-- term has a UNIQUE normal form (OB-5 SN ⤳ exists_unique_normalForm_of_isStronglyNormalizing: existence by weak
-- normalization, uniqueness by raw confluence #420; NO SR), so evaluation is a well-defined single-valued total
-- function. closedTypeSafetyUniqueOfSubjectReductionStar = CONDITIONAL — that unique normal form is moreover a
-- canonical VALUE (closedNormalSubjectHead at the SR-typed normal form): the full "evaluates to THE canonical
-- value" statement, progress + preservation + confluence combined.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedHasUniqueNormalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyUniqueOfSubjectReductionStar
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
-- OPEN CANONICAL FORMS PER TYPE (GrownOpenCanonicalFormsByClassifier.lean, five-layer-defense L4 §27.3): the open
-- generalizations of closedNormalFunctionIsLambda / closedNormalTypeIsFormer, admitting the neutral disjunct.
-- openNormalFunctionIsLambdaOrNeutral = a normal grown-typed term at a Π type in ANY WfContext is a λ or a
-- Core.IsNeutral (the type-former heads refuted at a Π classifier by the *NotTypedAtPiType inversions).
-- openNormalTypeIsFormerOrNeutral = a normal grown-typed term at a universe in ANY WfContext is a type former or a
-- Core.IsNeutral (the λ head refuted by lam_notTypedAtUniverseCode). Exactly the type-directed NbE / η-long readback
-- dichotomy (TY-CONV-quote / η-M15 line). #672-independent — pure inversion, no SR, no SN.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openNormalFunctionIsLambdaOrNeutral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openNormalTypeIsFormerOrNeutral
-- OPEN PROGRESS PER TYPE (GrownOpenProgressByClassifier.lean): the eighth and last cell of the grown progress/
-- canonical-forms matrix {closed,open}×{general,per-classifier}×{canonical-forms,progress}. openFunctionStepsOrIsLambdaOrNeutral
-- = a grown-typed term of Π type in ANY WfContext STEPS or IS a λ or is Core.IsNeutral; openTypeStepsOrIsFormerOrNeutral
-- = a grown-typed TYPE (universe classifier) STEPS or has a type-former head or is Core.IsNeutral. The open
-- generalizations of the closed{Function,Type}Steps… twin (admitting the neutral leaf variables introduce). The
-- 3-way disjunction (steps ∨ canonical-at-classifier ∨ neutral) IS the type-directed η-long readback case split
-- (TY-CONV-quote / η-M15). UNCONDITIONAL: the classifier is read only at the already-normal subject (via the open
-- per-classifier canonical-forms lemmas), so no reduction step is typed — no SR, no GrownCtxConv-5 #842, no §5.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openFunctionStepsOrIsLambdaOrNeutral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeStepsOrIsFormerOrNeutral
-- OPEN TYPE SAFETY + DETERMINISM (GrownOpenTypeSafety.lean, five-layer-defense L4 §27.3): the open analogues of the
-- three GrownTypeSafety statements, resting on OB-5 open SN (stronglyNormalizingOfWfContext, any WfContext) + open
-- progress (openNormalSubjectCanonicalOrNeutral), with the neutral disjunct. openHasUniqueNormalForm = OPEN
-- EVALUATION DETERMINISM (unconditional — OB-5 SN any context ⤳ exists_unique_normalForm; NO SR, NO closedness):
-- evaluation of an open grown-typed term is a well-defined single-valued total function.
-- openTypeSafetyOfSubjectReductionStar / openTypeSafetyUniqueOfSubjectReductionStar = OPEN TYPE SAFETY (conditional
-- on SR-along-↝*): every open grown-typed term evaluates to a (unique) canonical-or-neutral normal form. Completes
-- the open metatheory triple (progress + canonical forms + safety). #672-independent (OB-5 is unconditional open SN).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openHasUniqueNormalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyOfSubjectReductionStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar
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
-- CASCADE-FREE FORMER STEP-INVERSION (FormerStepInversionGeneric.lean, TG-1): a step out of any formation-rule
-- cell (typingRuleDescOf generator = some rule) is a child congruence, proven WITHOUT enumerating the formation
-- table — `cases step` with generator free (propext-clean), each of the 17 root-redex cases refuted because the
-- redex forces generator to a redex head (gen_app / gen_boolElim / ...) whose typingRuleDescOf = none (a
-- permanent table fact no future formation row disturbs). The table-invariant foundation of the cascade-free
-- former metatheory (TG-2 generic former SR + TG-3 cascade-free dispatcher build on it); zero-touch successor to
-- the enumerating former_step_inv.
#assert_no_axioms FX1Poly.Typed.formerCellStepIsChildCongruence
-- CASCADE-FREE GENERIC FORMER SR (SubjectReductionAtFormerGeneric.lean, TG-2): ONE former subject-reduction arm
-- over typingRuleDescOf, replacing the piTyCode/sigmaTyCode-specific subjectReductionAtPiFormer/SigmaFormer. By
-- TG-1 a former's step is a child congruence; re-type the premise telescope (telescopeSR, the mutual-partner
-- DescTelescopePi SR whose here-case consumes grown context-conversion #814 pt2b) and reassemble via the generic
-- genFormationPi at the unchanged rule.outputType. No formation generator is named — a new formation row is
-- absorbed zero-touch. The master dispatcher (TG-3) routes its genFormationPi case through this one arm.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtFormerGeneric
-- FORMATION CONTEXT WELL-FORMEDNESS (WfContextDesc.lean): the IsTypeDesc-based context predicate. It stores
-- IsTypeDesc bindings, keeping lookups + extensions inside HasTypeDesc. Lighter than the grown WfContextDescPi
-- (formation IsTypeDesc < grown IsTypeDescPi).
#assert_no_axioms FX1Poly.Typed.WfContextDesc
#assert_no_axioms FX1Poly.Typed.WfContextDesc.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextDesc.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextDesc.headIsTypeDesc
#assert_no_axioms FX1Poly.Typed.WfContextDesc.cons
#assert_no_axioms FX1Poly.Typed.wfContextDesc_universeBinding
-- FORMATION LOOKUP-VALIDITY (WfContextDescLookup.lean): in a formation-well-formed context every variable's
-- type is a formation type (IsTypeDesc) in the full context — the var-arm engine that lets
-- classifierIsTypeDescNative read its variable case off WfContextDesc. Structural context induction +
-- HasTypeDesc.weakenUnderBinding (the universe code renames to itself). Formation mirror of
-- WfContextDescPi.lookupIsType.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContextDesc.lookupIsTypeDesc
-- FORMATION VALIDITY over WfContextDesc (WfContextDescValidity.lean): a HasTypeDesc-typed cell's classifier is a
-- formation type (IsTypeDesc), proved over WfContextDesc. The var arm reads WfContextDesc.lookupIsTypeDesc
-- directly. The canonical formation validity.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierIsTypeDescNative
-- FORMATION CLASSIFIER-SN over WfContextDesc (WfContextDescStronglyNormalizing.lean): the classifier of a
-- HasTypeDesc-typed cell is strongly normalizing, routed through classifierIsTypeDescNative then
-- IsTypeDesc.isStronglyNormalizing. A consumer of the native validity target.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierStronglyNormalizingNative
-- FORMATION UNIQUENESS (P7) over WfContextDesc (WfContextDescUniqueness.lean): a genuine MUTUAL recursion
-- uniquenessNative/uniquenessAgreeNative — the head child recurses into uniquenessNative itself and the rest
-- extends via WfContextDesc.cons whose IsTypeDesc binding IS the head typing; arms invert via the param-free
-- inversions. The canonical formation uniqueness.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.uniquenessNative
#assert_no_axioms FX1Poly.Typed.DescTelescope.uniquenessAgreeNative
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
-- GROWN LOOKUP-VALIDITY (WfContextDescPiLookup.lean, WFG-2): in a grown-well-formed context every variable's
-- type is a grown type (IsTypeDescPi). Structural context induction + grown weakening
-- IsTypeDescPi.weakenUnderBinding; the var-arm engine of grown classifier-validity over WfContextDescPi (the
-- master SR dispatcher threads WfContextDescPi, which extends at a grown piIntro binder).
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi.weakenUnderBinding
-- GROWN TYPE-STABILITY, substitution dual (WfContextDescPiLookup.lean): IsTypeDescPi survives single-
-- substitution (the subst dual of weakenUnderBinding), so a grown type in a cons-context becomes a grown type
-- in the prefix after substituting a typed argument. The universe-code witness is subst-invariant (same
-- definitional fact that makes IsType.substituteUnderBinding a 2-liner); completes the grown type-stability
-- pair (weaken + subst) the dependent Π-elimination output classifier needs.
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContextDescPi.lookupIsType
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
-- GROWN CLASSIFIER-VALIDITY, the grown-engine payoff (HasTypeDescPiClassifierValidity.lean, WFG-3): a grown-typed
-- subject's classifier is a grown type (IsTypeDescPi) under the EXTENDABLE WfContextDescPi — the leg the master SR
-- dispatcher (SN-055/TG-3) consumes (WfContext can't extend at a grown piIntro binder; WfContextDescPi can). The
-- piElim arm's Pi-code inversion is broken free of the WfContext entanglement by routing through the Conv-free,
-- WfContext-free formation inversion inversionPiCodeGeneral: this yields an UNCONDITIONAL grown Pi-code inversion
-- chain (Telescope/Components/piCodeInstantiationIsType, no well-formedness), so classifierIsTypeDescPi needs only
-- WfContextDescPi with no Conv.trans/HasType.classifierIsType obstruction.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeTelescopeUnconditional
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
-- GrownCtxConv-5 REDUCTION (PiElimUpToClassifierConv, VAL-1 #1039): the grown context-conversion piElim arm — the
-- entangled crux #842 — closes given EXACTLY ONE property, classifierRespectsConv (type-Conv-closure: IsTypeDescPi
-- respects Conv). piElimUpToClassifierConv rebuilds appCell fn arg from the mutual-IH re-typings (fn at a type
-- Conv to piTyCodeCell D C, arg at a type Conv to D) using ONLY shipped pieces: classifierIsTypeDescPi (validity,
-- unconditional) + classifierRespectsConv (the lone residual hypothesis) + two conv-rule re-ascriptions
-- (universe witnesses from the Pi-code's IsType + inversionPiCodeComponents) + piElim, landing at subst0 C arg
-- on the nose. So GrownCtxConv-5 = one lemma; the reflect (reducible-type -> typed) is the VAL-2 residual (the universe
-- candidate IS IsReducibleType, Conv-invariant via #537). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piElimUpToClassifierConv
-- GrownCtxConv-5-REFUTE (#1058, ClassifierRespectsConvRefuted): ★ classifierRespectsConv_isFalse — the VAL-1 GrownCtxConv-5
-- reduction target (classifierRespectsConv : IsType A → Conv A B → IsType B) is PROVABLY FALSE.
-- Counterexample: A = Type@0 (a type), B = (λ_.Type@0) Ω. B β-reduces to A (classifierConvCounterexampleRedex_
-- stepsToType: the body Type@0 discards Ω), so Conv A B; A isType (classifierConvCounterexampleType_isType, via
-- universe-formation); but B is NOT a type (classifierConvCounterexampleRedex_notType: invertApp would type the
-- discarded argument Ω, contradicting omegaCombinator_notClosedWellTyped #958). So VAL-2 as planned is impossible.
-- DEEP FINDING: grown typing requires EVERY subterm typed (even a discarded argument), so IsTypeDescPi is NOT
-- Conv-invariant. REDIRECT: the real piElim arm keeps the SOURCE fn:piTyCode D C derivation (D,C genuinely typed
-- by validity) and context-converts that formation (GrownCtxConv-4), NOT the lossy Conv-to-piTyCode. Zero-axiom: Step.beta
-- + invertApp + omega-untypable + universeFormation + Conv.fromStepStar.
#assert_no_axioms FX1Poly.Typed.classifierConvCounterexampleRedex_stepsToType
#assert_no_axioms FX1Poly.Typed.classifierConvCounterexampleType_isType
#assert_no_axioms FX1Poly.Typed.classifierConvCounterexampleRedex_notType
#assert_no_axioms FX1Poly.Typed.classifierRespectsConv_isFalse
-- reclassifyArgumentToFunctionDomain: the first consumer — re-type an argument (Conv to the function's domain) at
-- the domain itself, with functionDomainIsType supplying the conv rule's universe witness. The argument-retyping
-- step of the grown β / context-conversion piElim arms (toward GrownCtxConv-5/SN-055).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.reclassifyArgumentToFunctionDomain
-- FUNCTION-SPACE SR ARMS over the GROWN well-formedness (HasTypeDescPiSubjectReductionDescPi.lean, toward SN-055):
-- the WfContextDescPi twins of betaSubjectReduction + subjectReductionPiElimArm, now that the grown
-- classifierIsTypeDescPi (WFG-3) is available. Each is a one-site swap (the lone WfContext use = the
-- classifier-validity call; all else is well-formedness-free). With the already-WfContext-free
-- subjectReductionPiIntroArm, the dispatcher's function-space arms all thread WfContextDescPi (which DOES extend
-- at a grown piIntro binder); the remaining dispatcher residual is the former arms' codomainReTyping (the
-- separate grown context-conversion / GrownCtxConv bundle).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaSubjectReductionDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionPiElimArmDescPi
-- MASTER SR DISPATCHER for the grown engine, conditional on the grown telescope SR (SRD-1 / SN-055,
-- HasTypeDescPiSubjectReduction.lean): inducts on the grown derivation threading the EXTENDABLE WfContextDescPi.
-- ofFormation is VACUOUS (subjectAdmitsNoStep: formation subjects are normal), conv recurses, piIntro/piElim use
-- the shipped function-space arms with children SR obtained recursively (extending well-formedness at the λ
-- binder via WfContextDescPi.cons + the domain's IsTypeDescPi), genFormationPi decomposes via former_step_inv +
-- the telescopeSR hypothesis. The telescopeSR hypothesis = the grown telescope SR (DescTelescopePi.subjectReduction,
-- gated on grown context-conversion / GrownCtxConv #838-843) is the LONE residual; SRD-2 (#845) discharges it for the
-- unconditional master SR. Mirrors the UB-SD conditional-package discipline (#664).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionOfGrownTelescopeSR
-- MASTER SR ⋈ GROWN TELESCOPE SR mutual pair (HasTypeDescPiSubjectReductionMutual.lean, SRD-2/SRD-4): DISCHARGES
-- SRD-1's telescopeSR hypothesis by proving the grown telescope SR as the mutual companion of the dispatcher, so
-- the WHOLE grown SR metatheory is now conditional on the SAME ONE lemma as the grown context-conversion — the
-- piElim crux (GrownCtxConv-5). The telescope here/cons arm re-types the tail under the stepped head via the grown telescope
-- context-conversion convTelescopeOfPiElimArm (carrying the piElim arm). Arg order (telescope BEFORE wellFormed) is
-- required for Lean mutual-recursion implicit inference. Discharging the piElim arm ⟹ unconditional SN-055.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionOfPiElimArm
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.subjectReductionOfPiElimArm
-- ITERATED SR + ★ SN-050 CONSISTENCY, both conditional on EXACTLY the single piElim crux
-- (ConsistencyOfPiElimArm.lean, SRD-3 #846 + CON-A5wire #848 / SN-050 #553 / #812). subjectReductionStarOfPiElimArm
-- iterates the single-step master SR along a StepStar chain (structural recursion: refl unchanged, trans re-types
-- the one-step reduct then recurses under the same well-formedness — classifier+context invariant under reduction).
-- consistencyOfPiElimArm instantiates the iterated SR at the empty context (WfContextDescPi.emptyIsWellFormed) to
-- supply the SR-along-↝* hypothesis of consistencyOfSubjectReductionStarToEmptyType — so grown consistency is now
-- conditional on the SAME ONE lemma (piElim) as the master SR and context-conversion: Milestone-A consistency is one
-- lemma away. The BFT bounded model CANNOT prove this (its emptyTypeCell candidate is the coarse IsStronglyNormalizing
-- neutral arm); the syntactic SR-to-normal-form route is the tractable one.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionStarOfPiElimArm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.consistencyOfPiElimArm
-- ★ SN-050 UNCONDITIONAL (EmptyTypeConsistencyUnconditional.lean): emptyTypeConsistency DROPS the piElim/SR
-- conditionality above. Once emptyTypeCellHasNoTyping (the data-head boundary, last commit) existed, grown
-- VALIDITY (classifierIsTypeDescPi, WFG-3) closes consistency in two lines: t : emptyTypeCell forces
-- emptyTypeCell : universe (validity), refuted by emptyTypeCellHasNoTyping. Honest scope: the current engine,
-- where emptyTypeCell is not yet a substantive type (typingRuleDescOf gen_emptyCode = none); the
-- canonicity-grounded consistency for a formation-row Empty (CON-A3) is independent + future.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.emptyTypeConsistency

/-! ### REDUCIBLE CLOSING-SUBSTITUTION ENVIRONMENT (the #425 fundamental-theorem environment).
    `ReducibleEnv context γ` says `γ` sends every context variable to an `IsReducibleMember` of its
    looked-up (γ-closed) type — the ∀-form makes the fundamental theorem's `var` case
    `lookupReducible`, and the dependent membership re-substitutes each variable's type.  `empty` is the
    closed-term base; `cons` is the
    Π-introduction binder extension, its weakened lookups cancelled by `RawTerm.weaken_subst_cons`. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnv
#assert_no_axioms FX1Poly.Typed.ReducibleEnv.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnv.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnv.cons

/-! ### LEVEL-INDEXED REDUCIBLE ENVIRONMENT (the conv-closing stratified port of the above).
    `ReducibleEnvAt level context γ` rides on `IsReducibleMemberAt level` instead of `IsReducibleMember`:
    its universe arm carries each type variable's candidate ONE LEVEL DOWN, closing the conv-invariance
    gap the pure-SN `ReducibleEnv` leaves open at a type variable `x : Type@k`.  The `level` is inert
    through the `cons` binder rewrites (they touch only the looked-up type and substituted term), so the
    `empty` / `cons` / `lookupReducible` proofs port character-identically.  This is the environment the
    fundamental theorem over `HasTypeDescPi` actually consumes. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.cons

/-! ### ∀-LEVEL (Kripke) reducible environment — the off-by-one resolution for the dependent fundamental
    theorem's `var` arm.  A fixed-level `ReducibleEnvAt (predLevel+1)` cannot close `var` at a TYPE variable:
    the binder steps deposit each binding at the level its classifier supplies (`predLevel` after
    `tarskiDecode`), the universe candidate changes per fuel level (no monotonic cast), so `var`'s demanded
    `predLevel+1` never matches.  `ReducibleEnvAtAllLevels` certifies every variable at ALL positive levels
    (`∀ level, ReducibleEnvAt (level+1) …`) so `var` instantiates the family at the conclusion level.  Binder
    extension additionally needs the fresh semantic argument at all positive levels; the explicit
    all-positive argument bridges below isolate that remaining condition. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.cons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.toVecPositive
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.ofVecPositiveFamily
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consHeadToEnvAtPositive
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consHeadToVecPositive
-- consVariableOfAllLevelType: the GENERAL variable binder-extension -- the all-level env extends through a
-- variable binder whenever the binding type is reducible AS A TYPE at every positive level (head discharged by
-- IsReducibleMemberAt.variable). consTypeVariable is its universe-code instance (all-level type reducibility
-- automatic via IsReducibleTypeAt.universeCode). Surmounts the binder wall for arbitrary all-level binding types.
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consVariableOfAllLevelType
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consTypeVariable
#assert_no_axioms FX1Poly.Typed.reducibleEnvAtAllLevels_oneTypeVariable
-- SN-009 VERIFIED 2026-06-02 (no rebuild): the universe-code / closed env cons is shipped + gated.
-- consTypeVariable (ReducibleEnvAtAllLevels.lean:173-185) extends the all-level env through a Type@e binding —
-- the fresh variable inhabits Type@e reducibly at EVERY level via IsReducibleTypeAt.universeCode (level-
-- polymorphic), routed through consVariableOfAllLevelType + IsReducibleMemberAt.variable; the fixed-level form is
-- ReducibleEnvVec.cons (gated ~1459). The SMOKE reducibleEnvAtAllLevels_oneTypeVariable (gated just above) builds an
-- all-level env for the one-entry context [Type@e] from empty by one consTypeVariable. No denote-keyed variant:
-- per SN-008, denote-keying is instantiation of the abstract level, not a new cons (do NOT duplicate).
-- SN-010/011/012 VERIFIED 2026-06-02 (no rebuild; the env-cons/lookup family, all gated above):
--  · SN-010 consTypeVariable — the type-variable binder extension (detailed in the SN-009 note above; its
--    non-vacuity witness reducibleEnvAtAllLevels_oneTypeVariable is gated above).
--  · SN-011 consVariableOfAllLevelType — the GENERAL binder extension for ANY all-levels-reducible binding type
--    (premise typeAllLevel : ∀ level, IsReducibleTypeAt (level+1) bindingType; head discharged by
--    IsReducibleMemberAt.variable); consTypeVariable is its universe-code instance, consHeadToVecPositive
--    (gated above) the mixed-level bridge.
--  · SN-012 ReducibleEnvVec.lookupReducible — yields IsReducibleMemberAt (levels index) (subst σ (lookup index))
--    (σ index): the variable's reducible membership at its OWN env level levels index (= contextLevels index),
--    the off-by-one-FREE leg the var FT arm consumes; ReducibleEnvAtAllLevels.lookupReducible (gated above) is
--    the all-levels form.
-- No denote-keyed variants built: instantiation of the abstract level, not a rebuild (SN-008 discipline).

/-! ### PROOF-RELEVANT ∀-LEVEL ENVIRONMENT with positive type-candidate companions.  This strengthens the
    all-level environment with the binder-facing fact that every substituted lookup type has the
    all-positive member predicate as a candidate at every positive fuel level.  The `cons` operation is the
    key checked bookkeeping step: old variables use the tail companion after the weakening/substitution
    cancellation, and variable zero uses the explicit head-type companion. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.toAllLevels
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.lookupPositiveCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.consFromPositiveTypeCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.lookupMemberExtendsToAllPositive

/-! ### PROOF-RELEVANT ∀-LEVEL ENVIRONMENT with type-value candidate companions.  The previous strengthened
    environment records candidates for looked-up BINDING TYPES.  The two-part dependent fundamental theorem
    also needs the type-variable payload: when the substituted lookup classifier is a universe code, the
    substituted VARIABLE VALUE itself must carry positive-fuel all-positive candidates.  The universe test is
    stated after substitution so `cons` is stable by `weaken_subst_cons`, avoiding a false syntactic
    rename-reflection assumption. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.toPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.toAllLevels
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.lookupPositiveCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.lookupTypeValuePositiveCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons

/-! ### Dependent fundamental theorem — bundled type-value candidate motive.  This strengthens the
    positive-candidate arm layer by carrying the conditional type-variable payload in the theorem motive
    itself: if a substituted classifier is a universe code, the substituted subject must expose the
    all-positive member predicate as a positive-fuel candidate.  The bundled validity shape prevents later
    binder/type-variable arms from trying to recover this payload by false level irrelevance. -/
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.TypeValueCandidateConclusionWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates.memberConclusion
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates.typeValueCandidateConclusion
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.toTypeValueCandidateConclusion
#assert_no_axioms FX1Poly.Typed.TypeValueCandidateConclusionWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
#assert_no_axioms FX1Poly.Typed.TypeValueCandidateConclusionWithTypeValueCandidates.ofSubstitutedClassifierNeUniverse
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.consEnvWithTypeValueCandidate
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllPositiveUniverseMembers
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllReducibleTypesAtAllLevels
#assert_no_axioms FX1Poly.Typed.HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllPositiveUniverseMembers.toAllReducibleTypesAtAllLevels
#assert_no_axioms FX1Poly.Typed.hasTypeValueCandidatesForAllPositiveUniverseMembers_iff_allReducibleTypesAtAllLevels
#assert_no_axioms FX1Poly.Typed.hasTypeValueCandidatesForAllReducibleTypesAtAllLevels_iff_positiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.reducibleTypeAtExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes.toAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes.reducibleTypeAtExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toTypeValueCandidateConclusionOfUniverseMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toTypeValueCandidateConclusionOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toValidityOfUniverseMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toValidityOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalVarWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateVarLookupWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.typeValueCandidateVarWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalVarValidityWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalConvWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalConvValidityWithTypeValueCandidatesFromTargetTypeValuePremise
#assert_no_axioms FX1Poly.Typed.fundamentalConvValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesFromResultTypeValuePremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.substitutedPiTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.substitutedSigmaTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithTypeValueCandidatesFromTypedArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromTypedArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.positiveCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.typeValueCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationWithTypeValueCandidatesFromPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.positiveCandidateSigmaTypeWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.typeValueCandidateSigmaTypeWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility

/-! ### Dependent fundamental theorem — proof-relevant positive-candidate environment arm layer.  This is
    the recursor-facing strengthened motive: ordinary all-level membership plus positive type-candidate
    companions for looked-up binding types.  The non-binder arms project to the ordinary all-level layer; the
    lambda arm is the binder-critical proof that a decoded domain argument can be strengthened to
    all-positive membership, extending the strengthened environment before running the codomain/body
    recursive premises. -/
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.consEnv
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.toPositiveTypeCandidateEnv
#assert_no_axioms FX1Poly.Typed.fundamentalVarWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithPositiveTypeCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.fundamentalConvWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateVarWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateSigmaTypeWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidatePiTypeWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithPositiveTypeCandidatesFromPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithPositiveTypeCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithPositiveTypeCandidatesFromUniverseDomain

/-! ### Dependent fundamental theorem — the NON-telescope arms over the ∀-level environment.  `var` (the arm
    the ∀-level env unblocks: closes by instantiating the all-levels family at the conclusion
    level, off-by-one-free), `universeFormation` (`Type@e : Type@(lsucc e)`), and `conv` (reclassifier IH one
    level up → `tarskiDecode` → `castAlongConvUnderSubst`) all close with zero axioms over
    `ReducibleEnvAtAllLevels`, validating the env on the leaf/conv fragment.  The `genFormation` / `piIntro`
    binder companions use the per-variable-level bridge for the fresh argument; their non-recursive packaging
    gates pin them shut. -/
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalConvAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtDispatchLevelsAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtDispatchLevelsAtAll
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeNilAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAll
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtAll
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAtAllPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromMemberPremises
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.atAllPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.atLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofWeakHeadReduct
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.ofWeakHeadReduct
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtWeakHeadExpansion
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.domainOfPiType
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.codomainOfPiTypeAtAllPositiveArgument
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.universeCode_iff
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.ofMemberExtensionAtPositiveLevel
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.atPositiveLevelsOfMemberExtension
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveOfAllPositiveCandidate
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.ofNeutralClassifier
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtNeutralClassifier
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piTypeAtPositiveLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtPiType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piTypeUnderSubst
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piTypeUnderSubstAtPositiveLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtPositivePiType
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtPiTypeOfComponentMemberExtensions
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.domainDataOfStronglyNormalizingPiType
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.codomainDataOfStronglyNormalizingPiTypeAtAllPositiveArgument
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.sigmaType
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtSigmaType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.sigmaTypeUnderSubst
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.piType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.sigmaType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.universeCodeOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtUniverseCodeOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.universeCodeHasNoMemberAtZero
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.notSuccUniverseCodeAtZero
-- typeVariableHasAllPositiveCandidate: a type variable AS A TYPE has the all-positive candidate (neutral
-- classifier via ofNeutralClassifier + WeakHeadStep.not_from_var) -- candidate-side complement of
-- typeVariableAllLevelMember. piBetweenTypeVariablesHasAllPositiveCandidate: a Π with a type-VARIABLE domain
-- (Π(x:A).A, A = var 0) has a candidate -- the FIRST former with a variable domain, beyond the ∀-level-domain
-- limitation of fundamentalPiFormationLevelIndexed (the genuinely-dependent former still needs the recursor).
#assert_no_axioms FX1Poly.Typed.typeVariableHasAllPositiveCandidate
#assert_no_axioms FX1Poly.Typed.piBetweenTypeVariablesHasAllPositiveCandidate
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.notSuccUniverseCode
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.piType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.sigmaType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.universeCodeOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromAllPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromPositiveDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromAllLevelHeadCandidateCompanion
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasPositiveCandidateOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consArgumentAtPositiveMemberLevelOfHeadFundamental
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.consArgumentAtPositiveMemberLevelOfHeadFundamental
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_hasPositiveCandidateOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromPositiveMemberExtensionAndZeroMemberTail
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromPositiveDomainCandidateAndBaseLevelPremise
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromPositiveDomainCandidateAndBaseLevelPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAllFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAllFromPositiveDomainCandidate

-- Canonical per-level candidate companion extracted from an all-level `T : Type@u` fundamental result.  This
-- is weaker than the all-positive candidate discipline and avoids assuming stratified level-irrelevance.
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateUnderAllLevelSubstitution
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateAtPositiveLevelsUnderSubstitution
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateUnderAllLevelSubstitution.atPositiveLevels
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateUnderSubstitution
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateAtPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtVector
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtVectorMatchingLevel
#assert_no_axioms FX1Poly.Typed.fundamentalConclusionAtAllOfVector
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromVectorPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAllFromVectorPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtAllFromVectorPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromVectorPremise
#assert_no_axioms FX1Poly.Typed.positiveUniformLevels
#assert_no_axioms FX1Poly.Typed.positiveUniformLevels_eq
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalConclusionAtAllOfUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAllFromUniformVectorPremise
#assert_no_axioms FX1Poly.Typed.IsTelescopeReducibleAtVector
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalVectorFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalAtAllFromFormation
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromFormation
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

-- DECOUPLED-subjectLevel FT CONCLUSION (#496 — the var-level wall resolution).  IsFundamentalConclusionAtVector
-- fixes the conclusion at a uniform predLevel+1 decoupled from the env's per-variable levels, so var (reducible
-- only at its own level contextLevels index) is unprovable for arbitrary vectors; uniform-vector handles var but
-- not the dependent binder (codomain one rung lower via tarskiDecode). FundamentalConclusionLevelIndexed
-- concludes at a SEPARATE subjectLevel = the subject's level, so var = lookupReducible directly (off-by-one-free),
-- and the level-preserving arms (universeFormation, piElim — application is uniform-level via applicationUnderSubst)
-- thread it unchanged. The level-CHANGING arms now ALSO land: conv carries the tarskiDecode +1 (reclassifier run
-- one level up, decoded down to a reducible type, then castAlongConvUnderSubst); piIntro (the dependent binder, the
-- crux that walled the FT) is uniform-level via abstractionCanonicalUnderSubst with the bound arg deposited at
-- predLevel+1 via levelCons (positive level needed for CR1 on the domain candidate). genFormation (the dependent
-- type-former telescope) + the HasTypeDescPi.rec assembly with consistency hypotheses are the remaining Route-2 work.
-- SN-013 VERIFIED + GATED 2026-06-02: FundamentalConclusionLevelIndexed is the DECOUPLED-subjectLevel FT motive
-- (FundamentalLevelIndexed.lean:60) — ∀ closing σ, ReducibleEnvVec contextLevels context σ → IsReducibleMemberAt
-- subjectLevel (subst σ classifier) (subst σ subject) — with subjectLevel a SEPARATE Nat (fuel/depth, NOT denote)
-- from the env's contextLevels vector; that decoupling lets var conclude at its OWN level and the binder thread the
-- codomain one rung lower.
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionLevelIndexed
-- SN-014..020 VERIFIED 2026-06-02 (no rebuild): the seven fundamental*LevelIndexed arms that discharge the motive
-- (assembled by ValidTyping.fundamental) are each gated immediately below — var (own-level direct
-- ReducibleEnvVec.lookupReducible, off-by-one-free), universeFormation, conv (tarskiDecode +1), piIntro (binder via
-- levelCons at predLevel+1), piElim (uniform level), piFormation + sigmaFormation (∀-head-level-quantified former
-- membership). No denote-keyed motive/arm variants: instantiation of the abstract level, not a rebuild (SN-008).
#assert_no_axioms FX1Poly.Typed.fundamentalVarLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalConvLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroLevelIndexed
-- The dependent type-FORMER arms (the level-indexed twins of PiFormerMembership): the Π/Σ type-code
-- cell is a reducible universe member, from its children's QUANTIFIED-over-head-level fundamentals.
-- These are the membership dispatch the generic genFormation/genFormationPi arm calls; the remaining
-- Route-2 work is the DescTelescope(Pi) inversion feeding these the domain/codomain fundamentals + the
-- HasTypeDescPi.rec assembly.
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationLevelIndexed
-- The GENERIC genFormation/genFormationPi former arm: dispatches piTyCode/sigmaTyCode, inverts the two-child
-- spine, reads the FormerChildrenReducible bundle off the level-indexed telescope IH. The level-indexed twin
-- of fundamentalVectorFromFormation's genFormationPi arm — the FORMER half of the recursor assembly. Remaining:
-- the motive threading subjectLevel/contextLevels + the telescope motive_2 producing telescopeFundamental.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationFormerLevelIndexed
-- CLOSED-TERM HANDOFF (#497/#498): at the empty context the per-variable-level env is vacuous
-- (ReducibleEnvVec.empty), so a level-indexed fundamental conclusion specializes to closed reducibility
-- under any closing substitution, and via CR1 (positive level) + the empty-renaming SN reflection to closed
-- strong normalization. Conditional on the level-indexed fundamental conclusion for the closed term (an
-- explicit argument, as the committed *FromFormation handoffs are conditional on the formation premise);
-- unconditional once the HasTypeDescPi.rec level-indexed assembly supplies that conclusion.
#assert_no_axioms FX1Poly.Typed.closedSubjectReducibleFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.closedSubjectStronglyNormalizingFromLevelIndexed
-- Closed-type twin: a closed type code (given its type-FT) is a reducible TYPE at its level under any closing
-- substitution, via ReducibleEnvVec.empty. The handoff a closed-former canonicity argument consumes.
#assert_no_axioms FX1Poly.Typed.closedTypeReducibleFromTypeFundamental
-- BRIDGE to the committed vector machinery: IsFundamentalConclusionAtVector ≡ the level-indexed conclusion
-- at every (envLevels, predLevel+1). Makes precise why var fails at vector (forces predLevel+1 for the var's
-- env-fixed level) and lets vector-proved grown arms be read as level-indexed conclusions (toLevelIndexed).
#assert_no_axioms FX1Poly.Typed.isFundamentalConclusionAtVector_iff_forall_levelIndexed
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtVector.toLevelIndexed
-- TYPE-FT (the type half of the mutual fundamental theorem): the formation type-subjects (universe code +
-- Pi/Sigma formers) are reducible TYPES (ReducibleTypeAt, not just members) at their level, via tarskiDecode
-- of the shipped term-FT arms. This is the ReducibleTypeAt form the conv arm consumes for its classifier;
-- the type-variable case + context-validity threading remain for the full mutual relation.
-- The GENERIC type-FT bridge: type-FT = tarskiDecode ∘ term-FT. Collapses the type half of the mutual FT
-- into a projection of the term FT (no separate induction); the three former type-FT lemmas below route
-- through it. The recursor's conv arm draws its reclassifier's type validity from the reclassifier's term IH.
#assert_no_axioms FX1Poly.Typed.typeFundamentalOfTermFundamental
#assert_no_axioms FX1Poly.Typed.universeCodeIsTypeFundamentalLevelIndexed
#assert_no_axioms FX1Poly.Typed.piFormerIsTypeFundamentalLevelIndexed
#assert_no_axioms FX1Poly.Typed.sigmaFormerIsTypeFundamentalLevelIndexed
-- type-FT var case: a type variable (looked-up type a universe code, env level positive) is a reducible TYPE
-- at its env level, via tarskiDecode of the env's membership. Completes the type-FT for all formation
-- type-subjects (universe code + Pi/Sigma formers + var) modulo conv (mutual with the term FT).
#assert_no_axioms FX1Poly.Typed.varIsTypeFundamentalLevelIndexed
-- LEVELED VALID CONTEXT (the validity-context structure for the term-FT recursor motive): context is a
-- telescope of types each typed at a universe code, contextLevels recording each entry's positive membership
-- level via levelCons. allLevelsPositive (induction on the inductive; propext-clean Fin split) is the
-- positivity invariant the recursor relies on (CR1 + conv tarskiDecode one-up both need positive levels).
#assert_no_axioms FX1Poly.Typed.LeveledContext.allLevelsPositive
-- LEVELED-CONTEXT LOOKUP-AS-TYPE: every entry of a leveled context is a HasTypeDescPi-type at a universe code,
-- in the FULL context (head + each tail entry weakened in via HasTypeDescPi.weakenUnderBinding; the classifier
-- universeCodeCell is rename-invariant). The substrate the term-FT recursor's var/conv arms read to classify
-- each looked-up context variable (supplies the reclassifierIsUniverse premise of the conv bridge arm). Clean
-- leveled-context recursor + propext-clean Fin split, like allLevelsPositive.
#assert_no_axioms FX1Poly.Typed.LeveledContext.lookupTyped
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
#assert_no_axioms FX1Poly.Typed.omegaCombinator_betaSelfStep
#assert_no_axioms FX1Poly.Typed.omegaCombinator_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.selfApplicationBody_noStep
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
#assert_no_axioms FX1Poly.Typed.discardedBody_isNormalForm
#assert_no_axioms FX1Poly.Typed.discardingApplicationOnOmega_argumentSelfLoop
#assert_no_axioms FX1Poly.Typed.discardingApplicationOnOmega_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.weaklyNormalizingDoesNotImplyStronglyNormalizing
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
-- Conv VALUE NON-DEGENERACY (ConvValueDiscrimination): the contrapositive of Conv.eq_of_noStep — distinct closed
-- normal-form values are NOT convertible. normalLeavesNotConvertibleOfDistinctRoot: two no-step terms with
-- distinct head generators ⟹ ¬Conv (Conv.eq_of_noStep collapses Conv→Eq, congrArg rootGenerator refutes).
-- boolTrue ≢ boolFalse + boolTrue ≢ unit concretely; convIsNonDegenerate (★ ∃ a b, ¬Conv a b) is the value-
-- discrimination sanity property canonicity rests on (if Conv collapsed values, every type would be inhabited
-- and the theory inconsistent). Distinct from Conv-INJECTIVITY (#947/948, same-head decomposition).
#assert_no_axioms FX1Poly.Typed.normalLeavesNotConvertibleOfDistinctRoot
#assert_no_axioms FX1Poly.Typed.boolTrueValue_notConvertible_boolFalseValue
#assert_no_axioms FX1Poly.Typed.boolTrueValue_notConvertible_unitValue
#assert_no_axioms FX1Poly.Typed.convIsNonDegenerate
-- Conv on the NORMAL FRAGMENT is DECIDABLE and the decider EXECUTES (ConvValueDiscrimination, constructive
-- companion to the non-degeneracy facts): convDecidableOfBothNoStep packages the ConvNormalForm seed as an
-- actual Decidable (decidable_of_iff (left=right) ∘ Conv.iff_eq_of_noStep, over the propext-free DecidableEq
-- RawTerm — no normalizer). The convDecider_* equations are `@decide … = true/false` by rfl: the decider RUNS
-- and computes the right boolean (Conv boolTrue boolTrue → true; boolTrue/boolFalse, boolTrue/unit → false). No
-- native_decide; the evaluations reduce over the structural DecidableEq.
#assert_no_axioms FX1Poly.Typed.convDecidableOfBothNoStep
#assert_no_axioms FX1Poly.Typed.convDecider_boolTrueValue_self_isTrue
#assert_no_axioms FX1Poly.Typed.convDecider_boolTrueValue_boolFalseValue_isFalse
#assert_no_axioms FX1Poly.Typed.convDecider_boolTrueValue_unitValue_isFalse
-- Concrete HasTypeDescPi TYPING-ENGINE derivations of λ-terms (TypedLambdaDerivations): the first concrete
-- witnesses of the actual typing judgment HasTypeDescPi for honest λ-abstractions (the closed-SN smokes go
-- through the FT/reducibility layer's fundamentalPiIntroLevelIndexed, NOT the typing engine). identityOn
-- Universe: λ(x:Type@e).x : Π(Type@e).Type@e via piIntro + var (through ofFormation) — the var-lookup classifier
-- rename-weaken Type@e is defeq Type@e (nullary leaf). constantTypeLambda: λ(x:Type@e).Type@e : Π(Type@e).
-- Type@(e+1) via piIntro with a universeFormation body. stronglyNormalizing feeds the concrete identity
-- derivation through SN-043 (closedStronglyNormalizing) — the typing→SN pipeline on a concrete closed program.
#assert_no_axioms FX1Poly.Typed.identityOnUniverse_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.constantTypeLambda_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.identityOnUniverse_stronglyNormalizing
-- The ELIMINATION (application) form + concrete subject reduction (TypedLambdaDerivations, extending the
-- piIntro derivations above): identityApplicationOnUniverseCode applies the identity at Type@(e+1) to the
-- universe code Type@e (which inhabits Type@(e+1) by universeFormation — no data-code machinery), typed by
-- piElim; the result-type subst0 Type@(e+1) Type@e is defeq Type@(e+1) (constant codomain ignores the arg).
-- identityApplication_subjectReduction: the redex β-reduces to its argument Type@e and BOTH redex and reduct
-- type at the SAME Type@(e+1) — concrete subject reduction on an honest piElim derivation.
#assert_no_axioms FX1Poly.Typed.identityApplicationOnUniverseCode_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.identityApplicationOnUniverseCode_betaReducesToArgument
#assert_no_axioms FX1Poly.Typed.identityApplication_subjectReduction
-- THE POLYMORPHIC IDENTITY (TypedLambdaDerivations capstone): λ(A:Type@0).λ(x:A).x : Π(A:Type@0).Π(x:A).A —
-- the canonical dependently-typed term, typed by the grown engine via NESTED piIntro with a type-VARIABLE inner
-- domain. dependentArrowOverTypeVariable is the genuine Π-FORMATION with VARIABLE children (genFormationPi + a
-- DescTelescopePi typing var0/var1 each at Type@0 by the var rule; cumulative-lookup classifiers defeq Type@0).
-- stronglyNormalizing feeds it through SN-043. Tactic-mode refine threads the profile/contexts via goal-driven
-- unification (term-mode re-introduces TypingContext.empty with fresh profile metavars).
#assert_no_axioms FX1Poly.Typed.dependentArrowOverTypeVariable_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentity_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentity_stronglyNormalizing
-- DEPENDENT TYPE-INSTANTIATION (TypedLambdaDerivations): applying a polymorphic function to a type. The level-0
-- poly-id CANNOT be applied to a closed arg (no closed inhabitant of Type@0 in the formation-only engine), so the
-- LEVEL-1 twin Λ(A:Type@1).λ(x:A).x (same term, domain climbs to Type@1) is instantiated at the closed Type@0
-- (Type@0:Type@1 by universe formation). polymorphicIdentityInstantiatedAtTypeZero: piElim gives Π(x:Type@0).
-- Type@0 — the result-type subst0 (Π(x:A).A) Type@0 computes by defeq to Π(x:Type@0).Type@0, the dependent
-- codomain genuinely specializing (the FIRST application witness whose codomain depends on the argument, vs the
-- ID-TOWER's constant codomain). betaReducesToIdentity: the redex β-reduces to the monomorphic identity λx.x
-- (subst0 leaves the A-free inner lambda unchanged, defeq). subjectReduction: redex + reduct type at the SAME
-- Π(x:Type@0).Type@0 (the reduct via identityOnUniverse at lzero). stronglyNormalizing via SN-043. All zero-axiom
-- (direct constructor applications + defeq subst0; the level-1 twins mirror the level-0 derivations with lsucc
-- bumps).
#assert_no_axioms FX1Poly.Typed.dependentArrowOverTypeVariableAtLevelOne_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityAtLevelOne_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiatedAtTypeZero_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiation_betaReducesToIdentity
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiation_subjectReduction
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiation_stronglyNormalizing
-- CURRIED 2-ARGUMENT application (TypedLambdaDerivations): parametric polymorphism in action. The single
-- instantiation above stops at the type-application (Type@0 has no closed inhabitant to apply to); climbing ONE
-- more universe, the LEVEL-2 poly-id Λ(A:Type@2).λ(x:A).x instantiated at Type@1 gives the identity on Type@1
-- (Π(x:Type@1).Type@1), which DOES accept the closed value Type@0:Type@1. polymorphicIdentityAppliedToTypeOne
-- ThenTypeZero: the nested piElim (ΛA.λx.x)(Type@1)(Type@0):Type@1 — first arg instantiates the polymorphic A,
-- second arg is the actual value; outer piElim result subst0 Type@1 Type@0 is defeq Type@1. twoArgReducesToType
-- Zero: 2-step StepStar to Type@0 — a CONGRUENCE step (Step.cong .gen_app + StepChildren.here) contracting the
-- inner type-application under the outer function position, then the outer β. subjectReduction: redex + reduct
-- both type at the SAME Type@1 (reduct Type@0:Type@1 by universe formation). stronglyNormalizing via SN-043. All
-- zero-axiom (constructor applications + defeq subst0 + the growingReductionSequence congruence template). The
-- level-2 twins (dependentArrowOverTypeVariableAtLevelTwo, polymorphicIdentityAtLevelTwo) climb the firing-80
-- recipe once more (lzero -> lzero.lsucc.lsucc in domain positions).
#assert_no_axioms FX1Poly.Typed.dependentArrowOverTypeVariableAtLevelTwo_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityAtLevelTwo_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiatedAtTypeOne_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityAppliedToTypeOneThenTypeZero_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityTwoArgReducesToTypeZero
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityTwoArg_subjectReduction
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityTwoArg_stronglyNormalizing
-- Σ-FORMATION in the typing engine: the generic genFormationPi arm types a dependent PAIR type, not
-- only Π. The reducibility layer already had Σ formation (fundamentalSigmaFormationLevelIndexed); these
-- are the first in the TYPING judgment (HasTypeDescPi). genFormationPiTypesBothPiAndSigmaFormers bundles
-- Π and Σ at one identical context+classifier — the conjuncts differ only in the head former, i.e. only
-- in the Generator argument to the same arm: the cascade-free typing thesis, a former is a table row.
#assert_no_axioms FX1Poly.Typed.dependentPairTypeOverTypeVariable_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.closedDependentPairType_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.closedDependentPairType_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.genFormationPiTypesBothPiAndSigmaFormers
-- INTRODUCTION + ELIMINATION rule TABLES drive a concrete term: the identity application
-- (λ(x:Type@(e+1)).x)(Type@e) typed end-to-end through hasTypeDescPi_piIntro_viaIntroDesc (the intro
-- table) composed with hasTypeDescPi_piElim_viaElimDesc (the elim table). Output is the elim rule-DATA
-- output piElimOutput, resolving (rfl) to Type@(e+1) = the explicit-engine classifier; SN via SN-043.
-- Completes the formation/intro/elim cascade-free-typing demonstration trio (Σ-formation is above).
#assert_no_axioms FX1Poly.Typed.identityLambdaViaIntroTable
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables
#assert_no_axioms FX1Poly.Typed.ruleTableApplicationOutput_resolvesToUniverse
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables_atResolvedType
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables_stronglyNormalizing
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
#assert_no_axioms FX1Poly.Typed.lamCell_isStepNormalForm
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
#assert_no_axioms FX1Poly.Typed.Step.appArgCong
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
-- FIRST LANE CROSSING: the FT-derived SN results discharge the SN-fragment conversion decider
-- (Conv.decidableOfStronglyNormalizing — normalize each, compare NF), yielding UNCONDITIONAL decidable Conv
-- for concrete closed terms (β-redex vs reduct, β-redex vs identity). The general bridge is conditional on the
-- FT conclusion (becomes unconditional with the recursor). betaRedexConvertsToReduct is the non-vacuity witness
-- (the redex really converts to its reduct). Concrete realization of raw decidable Conv (#267 / #503).
#assert_no_axioms FX1Poly.Typed.closedConvDecidableFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.decidableConvBetaRedexAndReduct
#assert_no_axioms FX1Poly.Typed.decidableConvBetaRedexAndIdentity
#assert_no_axioms FX1Poly.Typed.betaRedexConvertsToReduct
-- EXTRACTION twin of the decision lane: from the FT-derived closed SN, the normalizer EXTRACTS the canonical
-- normal form (closedNormalFormFromLevelIndexed) with its metatheory — converts to it, it is normal, and NF
-- equality is a COMPLETE conversion invariant (closedConv_iff_normalForm_eq). The cherries are PROVEN (not
-- just decidable): the closed β-redex normalizes to its reduct Type@e; the closed identity is its own NF.
#assert_no_axioms FX1Poly.Typed.closedNormalFormFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.closedNormalForm_conv
#assert_no_axioms FX1Poly.Typed.closedNormalForm_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.closedConv_iff_normalForm_eq
#assert_no_axioms FX1Poly.Typed.closedBetaRedexNormalForm_eq
#assert_no_axioms FX1Poly.Typed.closedIdentityNormalForm_eq
-- NEGATIVE non-vacuity capstone: closed normal terms convert IFF syntactically equal
-- (closedNormalConv_iff_syntacticEq, the isStepNormalForm-stated rigidity), so distinct head generators are
-- PROVABLY non-convertible. Complements betaRedexConvertsToReduct (positive) — the decidable-Conv lane
-- decides both convertible AND non-convertible closed pairs. Unconditional (no FT/SN — just normality).
#assert_no_axioms FX1Poly.Typed.closedNormalConv_iff_syntacticEq
#assert_no_axioms FX1Poly.Typed.closedUniverseCode_not_conv_identity
#assert_no_axioms FX1Poly.Typed.closedUniverseCode_not_conv_piCode
#assert_no_axioms FX1Poly.Typed.closedIdentity_not_conv_piCode
-- LEG-2 RECURSOR (ValidTyping.lean): the level-annotated typing (Abel validity-derivation-indexed relation),
-- now spanning var/universeFormation/conv/piIntro/piElim/piFormation/sigmaFormation — the leaf+conv core, the
-- COMPUTATIONAL core (λ-introduction + application, where β-redexes live), AND the Π/Σ TYPE-former core. var/conv
-- level coordination resolved BY CONSTRUCTION (var at contextLevels index; conv's reclassifier at subjectLevel+1;
-- piIntro's body under levelCons at predLevel+1, codes at predLevel+1+1; piElim shares subjectLevel; the formers
-- carry ∀-level-quantified domain children — a type code's universe membership is fuel-polymorphic — which the
-- recursor lifts to ∀-quantified IHs feeding fundamentalPiFormationLevelIndexed/…Sigma…). So ValidTyping.fundamental
-- is a CLEAN single induction (ValidTyping.rec) threading the seven shipped level-indexed arms.
-- closedStronglyNormalizing = SN-for-well-typed (core, closed) via the recursor; validTyping_identity… shows the
-- closed identity λx.x lands SN through piIntro; validTyping_{pi,sigma}BetweenUniverses… show closed Π/Σ codes land
-- SN through the former arms. REMAINING for full SN: the GENERIC genFormation arm (table-driven former over an
-- arbitrary telescope, of which Π/Σ are instances) + the HasTypeDescPi→ValidTyping leveling bridge.
-- SN-007 VERIFIED 2026-06-02 (no rebuild): ValidTyping IS the per-binder-leveled validity context — its index is
-- the ABSTRACT (Fin scope → Nat) contextLevels + Nat subjectLevel (depth/fuel levels, NOT denote(LevelExpr)); all
-- seven claimed arms (var/universeFormation/conv/piIntro/piElim/piFormation/sigmaFormation) are present; the var arm
-- produces subjectLevel := contextLevels index by construction (the off-by-one dodge, SN-024); fundamental is PROVED
-- (clean ValidTyping.rec induction) + gated below; it is the consumer the SN-022 bridge composes with. No
-- classifier-universe-level (denote-keyed) variant is built: SN-004 is GO but the fuel-level bridge (SN-022) is not
-- yet shown insufficient, so a variant would be premature duplication (task discipline: do NOT duplicate ValidTyping).
-- SN-021 LANDED 2026-06-02: ValidTyping now also carries the GENERIC table-driven `genFormationPi` ctor (over
-- typingRuleDescOf — Π/Σ as instances), so the leveled relation has cascade-free former coverage matching
-- HasTypeDescPi. The ctor is NON-recursive in ValidTyping (carries DescTelescopePi + the telescopeFundamental
-- reducibility premise — faithful for an Abel VALIDITY relation), so it needed no mutual refactor; the fundamental
-- arm is a one-liner to fundamentalGenFormationFormerLevelIndexed (real former-membership work). Both gates below
-- now cover the extended inductive + theorem zero-axiom (the genFormationPi arm's axiom-cleanliness is checked
-- transitively by the .fundamental gate).
#assert_no_axioms FX1Poly.Typed.ValidTyping
#assert_no_axioms FX1Poly.Typed.ValidTyping.fundamental
-- SN-022 (LevelingBridge.lean): the leveling bridge HasTypeDescPi → ∃ contextLevels subjectLevel, ValidTyping …
-- — var/conv/universeFormation arms. var + universeFormation are UNCONDITIONAL leaves (direct ValidTyping ctor
-- applications; var concludes at subjectLevel := contextLevels index, the SN-024 off-by-one dodge); conv is the
-- coordinated-input wrapper (cross-sub-derivation level coordination is the inductive assembly's job, SN-027).
-- Composed with the PROVEN ValidTyping.fundamental ⟹ unconditional dependent reducibility/SN. Binder/former
-- arms = SN-023.
#assert_no_axioms FX1Poly.Typed.validTypingBridgeVar
#assert_no_axioms FX1Poly.Typed.validTypingBridgeUniverseFormation
#assert_no_axioms FX1Poly.Typed.validTypingBridgeConv
-- SN-023 (LevelingBridge.lean): the binder + former bridge arms — each mirrors the matching ValidTyping ctor's
-- level discipline (piIntro: codes at predLevel+1+1, body at predLevel+1 under levelCons; piElim: shared level;
-- piFormation/sigmaFormation: the ∀-aboveLevel domain premise SN-025 produces; genFormationPi: the SN-021 ctor).
-- Per-arm TARGET SHAPES given coordinated inputs; the cross-IH coordination + ∀-aboveLevel production is the
-- inductive assembly SN-027 (ValidTyping is NOT level-weakenable — var pins its level — so coordination is the
-- deferred crux, not arm-local).
#assert_no_axioms FX1Poly.Typed.validTypingBridgePiIntro
#assert_no_axioms FX1Poly.Typed.validTypingBridgePiElim
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
-- SN-027 (LevelingBridge.lean, COMPOSE step): hasTypeDescPiReducibleFromTotalBridge composes the TOTAL leveling
-- bridge (HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping … (predLevel+1) …) with the PROVEN
-- ValidTyping.substReducible ⟹ every HasTypeDescPi-typed subject is reducible under every closing reducible env.
-- The total bridge is an explicit HYPOTHESIS here (mirroring the conditional fundamentalAtAllFromFormation): the
-- residual crux is the total-bridge INDUCTION that assembles the SN-022..025 per-arm blocks under a consistent
-- contextLevels + coordinates IH levels + inverts ofFormation/HasTypeDesc + routes type-variable domains through
-- the reducibility all-levels machinery — the formation-FT obstruction both routes share. Composition done; the
-- unconditional discharge is the in-progress remainder of SN-027.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPiReducibleFromTotalBridge
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
-- SN-027 (refined-motive coordination): validTypingBridgeConvFromAllLevelReclassifier discharges the conv arm's
-- LEVEL alignment — the existential ∃-shape can't force aligned levels, but a REFINED MOTIVE giving type-code
-- subjects an ∀-level conclusion does: conv needs the reclassifier at subjectLevel+1, which is just the
-- subjectLevel-instance of the all-level reclassifier IH. Supersedes the pre-aligned validTypingBridgeConv
-- (SN-022). Type variables (var-pinned) are the sole non-level-flexible type code → reducibility route (SN-025).
#assert_no_axioms FX1Poly.Typed.validTypingBridgeConvFromAllLevelReclassifier
-- SN-027 (the type-variable conv arm, refined-motive wall RESOLVED): validTypingBridgeConvPinnedReclassifier —
-- a type-variable reclassifier is NOT level-flexible, but ValidTyping.conv only needs it at subjectLevel+1, and
-- a type variable var index IS valid there at its PINNED level contextLevels index PROVIDED the leveling is
-- consistent (contextLevels index = subjectLevel+1, the leveling discipline). So the refined-motive blockage was
-- an over-demanding motive (flexibility for ALL universe-classified subjects), not a real obstruction: the
-- type-variable conv case closes inside ValidTyping under level-consistency, NOT via the reducibility detour.
#assert_no_axioms FX1Poly.Typed.validTypingBridgeConvPinnedReclassifier
-- SN-027 #662 leveling-bridge invariant (ConsistentStratification.lean): the STATIC level-inference
-- invariant a totalBridge contextLevels must satisfy for the conv-pinned arm above — a binding whose type
-- is a type variable sits one level below it — plus its two acyclicity consequences (strictly-below the
-- type-variable edge; no binding is its own type). The binder-extension preservation + full assembly are
-- the subsequent multi-fire #662 steps.
#assert_no_axioms FX1Poly.Typed.ConsistentStratification
#assert_no_axioms FX1Poly.Typed.consistentStratification_empty
#assert_no_axioms FX1Poly.Typed.ConsistentStratification.strictlyBelowType
#assert_no_axioms FX1Poly.Typed.ConsistentStratification.noSelfType
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
#assert_no_axioms FX1Poly.Typed.universeFormation_isLevelFlexible
#assert_no_axioms FX1Poly.Typed.piFormation_isLevelFlexible
#assert_no_axioms FX1Poly.Typed.sigmaFormation_isLevelFlexible
#assert_no_axioms FX1Poly.Typed.ValidTyping.convWithLevelFlexibleReclassifier
-- SN-027 the TOTAL-BRIDGE MOTIVE (#655, ValidTypingRefinedMotive.lean): TotalBridgeConclusion = single-level
-- validity ∧ (NON-VARIABLE subject whose classifier is CONVERTIBLE to a universe code ⟹ level-flexible). The
-- IH-strengthening induction motive that forces the conv/piElim level coordination the bare ∃-shape can't. Two
-- design points: the non-variable guard (∀ index, subject ≠ variableCell index) — a type variable is pinned by
-- ValidTyping.var, cannot be flexible; and the CONVERTIBILITY guard (Conv classifier (Type@e f), not syntactic =)
-- so conjunct-2 propagates through conv by Conv.trans. var arm: conjunct-2 vacuous (subject IS a variable).
-- universeFormation arm: flexibility via universeFormation_isLevelFlexible, convertibility guard met by
-- universeCodeCell_inj_of_conv. RawTerm.isVariableOrNot routes the conv arm onto the guard.
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.var
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.universeFormation
-- the CONV arm (non-variable reclassifier) of the revised motive. The convertibility guard (Conv classifier
-- (Type@e f), not syntactic =) lets conjunct-2 propagate through conv by Conv.trans; conjunct-1 reclassifies
-- via convWithLevelFlexibleReclassifier (the non-variable reclassifier is level-flexible from its own conjunct-2
-- at Conv.refl). The variable-reclassifier case routes to validTypingBridgeConvPinnedReclassifier (the leveling
-- eq) via RawTerm.isVariableOrNot.
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.convNonVariableReclassifier
-- the conv arm VARIABLE-reclassifier twin (ValidTypingConvArm.lean): conjunct-1 via validTypingBridgeConvPinnedReclassifier
-- (consuming the leveling eq contextLevels index = subjectLevel + 1, the one residual the assembly's leveling
-- discipline supplies); conjunct-2 vacuous (a variable reclassifier is not conv to a universe code). Routed by
-- isVariableOrNot. This COMPLETES the conv arm modulo the leveling equation.
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.convVariableReclassifier
-- the BASE CASE of the level synthesis (ValidTypingConvArm.lean): the conv-variable arm for a FRESHLY-BOUND type
-- variable ⟨0,_⟩ under a binder (contextLevels = levelCons (predLevel+1) tailLevels). The leveling eq
-- contextLevels ⟨0,_⟩ = subjectLevel+1 is discharged BY rfl (levelCons's ⟨0,_⟩ branch = predLevel+1, subject at
-- predLevel) — NO hypothesis. A binder pins its variable's level, so the coordination is automatic; this is where
-- the assembly's level synthesis bottoms out (deeper variables thread the eq through the levelCons tail).
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.convBoundVariableReclassifier
-- the DEEPER tower step (#662): a subject var termIndex whose looked-up type IS the reclassifier type-variable
-- (lookup termIndex = variableCell index, the x:A:Type tower). The leveling eq contextLevels index =
-- contextLevels termIndex + 1 is discharged by the ConsistentStratification invariant at that looked-up edge —
-- this is where the assembly's synthesized level vector pays off (no per-derivation hypothesis).
#assert_no_axioms FX1Poly.Typed.TotalBridgeConclusion.convVariableReclassifierOfStratified
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
-- (An earlier syntactic-equality-guarded motive iteration that the var-arm wall killed, and its arm cluster, were
-- deleted; the convertibility-guarded TotalBridgeConclusion above is the canonical motive. genFormationPi's
-- TotalBridgeConclusion arm + the HasTypeDescPi.rec assembly are the #662 residual.)
-- SN-027 the VARIABLE-LEVEL-PINNING INVERSION + the type-variable obstruction (#662 diagnosis,
-- ValidTypingVariableLevelPinned.lean): validTypingVariableLevelPinned proves a ValidTyping derivation of subject
-- variableCell index has level = contextLevels index (var pins, conv preserves, all other ctors have a distinct
-- head generator; genFormationPi forced to gen_var contradicts typingRuleDescOf gen_var = none). The corollary
-- typeVariableNotLevelFlexible turns it into the WALL: a type variable cannot satisfy the refined motive's
-- conjunct-2 (forall level) — at contextLevels index it would force contextLevels index + 1 = contextLevels index.
-- This PINS that the dependent assembly's neutral type-codes (var-at-universe + the piElim type-family case) do NOT
-- go through ValidTyping all-level flexibility; they route through the reducibility env at the single
-- conv-coordinated level. The shipped refined-motive arms stay correct for the FORMER + value-subject cases.
#assert_no_axioms FX1Poly.Typed.validTypingVariableLevelPinned
#assert_no_axioms FX1Poly.Typed.typeVariableNotLevelFlexible
-- SN-027 the KRIPKE-ROUTE REDUCTION (#674, FormationEngineFundamentalReduction.lean): given the wall pinned above,
-- the assembly PIVOTS to the Kripke route (SN-026) where neutral type-codes route through ReducibleEnvAtAllLevels
-- (reducibility, NOT ValidTyping levels). The grown-engine recursor HasTypeDescPi.fundamentalAtAllFromFormation is
-- ALREADY proven conditional on the formation-engine FT (HasTypeDesc -> IsFundamentalConclusionAtVector). This
-- theorem WIRES that single hypothesis to the all-level FT INTERFACE HasTypeDescPiAllLevelFundamentalTheorem, which
-- is consumed by ~10 downstream SN/canonicity/consistency theorems. So SN-027's sole
-- residual is now the 4-arm formation-engine FT (#674: var via the all-level env, not pinning; universe/genFormation
-- formers; conv via Conv-invariance of reducibility) — the var arm is dischargeable here, no level-pinning wall.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental
-- SN-027 #674 the formation-engine FT, arm by arm (FormationEngineFundamental.lean). First arm:
-- universeFormation. Type@e is a reducible member of Type@(lsucc e) at every positive level — the universe code
-- is closed so subst is identity (subst_universeCodeCell) and membership is IsReducibleMemberAt.universeFormation
-- (SN-037), independent of the env-level vector. Remaining arms for formationFundamental: var (via the env lookup,
-- ReducibleEnvVec.lookupReducible — NOT the ValidTyping pinning), conv (Conv-invariance of reducibility SN-034),
-- genFormation (the generic former telescope). Then assemble the 4-arm induction => discharge SN-027 + the ~10
-- downstream theorems via HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental (shipped).
#assert_no_axioms FX1Poly.Typed.formationFundamentalUniverseFormationArm
-- #674 conv arm: formationFundamentalConvArm (binary helper over the 2 sub-derivation IHs + converts). Level-
-- PRESERVING (no mismatch): reclassifier IH one level up, tarskiDecode to a reducible type, castAlongConvUnderSubst
-- (SN-034) transports the subject's membership across the conversion. Residual: var (the genuine hard arm — the
-- AtVector arbitrary-level conclusion vs the env's stored-level lookup, probed mismatch; needs extendsToAllPositive
-- under a classifier condition) + genFormation (the former telescope helper).
#assert_no_axioms FX1Poly.Typed.formationFundamentalConvArm
-- #674 var arm, RESIDUAL ISOLATED: formationFundamentalVarArmOfAllPositiveMember. IsReducibleMemberAt level T t =
-- exists candidate, ReducibleTypeAt level T candidate AND candidate t — so ALL level-dependence is in
-- ReducibleTypeAt level T, whose cross-positive-level extension IS the universe-domain-Pi fixpoint (#672). The var
-- arm reduces EXACTLY to: the variable's substituted member at ALL positive levels (.atLevel reads it at
-- predLevel+1). ReducibleEnvVec gives only ONE level, so discharging allPositiveMember per variable = #672 = the
-- ACTUAL SN-027/SN-043 gate. BOTH the ValidTyping route (ValidTypingVariableLevelPinned) and this Kripke route
-- bottom out at the SAME variable obstruction. Residual: genFormation arm (former telescope, tractable like conv)
-- + the #672 fixpoint discharge.
#assert_no_axioms FX1Poly.Typed.formationFundamentalVarArmOfAllPositiveMember
-- genFormation arm (#672-INDEPENDENT, level-preserving): formationFundamentalGenFormationArm. The generic former
-- (Pi/Sigma via universeFormerOutput) over a fundamentally-reducible child telescope is a reducible member of its
-- output universe at every positive conclusion level. A thin forall-envLevels/predLevel wrapper over the shipped
-- fundamentalGenFormationFormerLevelIndexed: IsFundamentalConclusionAtVector unfolds to
-- forall envLevels predLevel, FundamentalConclusionLevelIndexed envLevels (predLevel+1) ..., so instantiate +
-- apply. Universe-former output is level-flexible (toPiMember/toSigmaMember build membership at the requested
-- predLevel+1) so NO #672 extension. The complete assembly formationFundamentalVectorOfAllVariablesPositive
-- already inlines the equivalent former logic over DescTelescope; this is the independently-reviewable NAMED arm
-- at the grown-telescope DescTelescopePi vector shape, completing the file's arm-by-arm set.
#assert_no_axioms FX1Poly.Typed.formationFundamentalGenFormationArm
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
-- OPEN-CONTEXT HANDOFFS (ValidTyping.lean): the UNCONDITIONAL open twins of the ClosedLevelIndexed handoffs.
-- The closed handoffs take the level-indexed fundamental conclusion as a HYPOTHESIS; over ValidTyping the
-- fundamental IS proved (ValidTyping.fundamental), so substReducible (open reducibility under any reducible env)
-- + substStronglyNormalizing (open SN via CR1) are unconditional and hold in ANY context. openVariable… is the
-- first SN witness for a NON-closed subject (a free var closed by a reducible substitution), exercising the open
-- handoff with a genuine reducible env (Fin 1 split refuted structurally, no omega).
#assert_no_axioms FX1Poly.Typed.ValidTyping.substReducible
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.fundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.substitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.closedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.toTypeValueCandidateValidityOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toReducibilityAndStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.hasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem_iff_typeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.allLevelFundamentalTheoremFromFormationVector
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValueReducibilityAndStrongNormalizationTheoremFromFormationVectorAndAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValueReducibilityAndStrongNormalizationTheoremFromFormationVectorAndPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
-- SN-046 typed Newman bridge + general typed decidable Conv, CONDITIONAL on the one typed-SN interface
-- (HasTypeDescPiConditionalConfluence.lean). HasTypeDescPiStronglyNormalizes = the named typed-SN hypothesis
-- (= SN-043, gate #672). subjectConfluenceOfStronglyNormalizes = Newman confined to the SN fragment
-- (StepStar.confluence_of_localJoin_and_accessible on the hypothesis-supplied SN witness; raw global confluence
-- false-by-Omega is never used). decidableOfHasTypeDescPiStronglyNormalizes = general typed Conv decidable via
-- the parameter-free SN-fragment decider (Conv.decidableOfStronglyNormalizing), subsuming decidableOfIsType
-- (TYPES-only) to ARBITRARY well-typed terms. All zero-axiom (Acc-recursion + instDecidableEqRawTerm). Once #672
-- lands and feeds HasTypeDescPi.subjectStronglyNormalizingFromFormation, the hypothesis discharges and these go
-- unconditional in one step.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiStronglyNormalizes
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectConfluenceOfStronglyNormalizes
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfHasTypeDescPiStronglyNormalizes
-- SN-046/NbE-soundness: Conv.iff_normalize_eq_of_hasTypeDescPiStronglyNormalizes = the SEMANTIC characterization
-- for the typed fragment (Conv ↔ normalize-equality), the Path-A NbE headline (Conv ↔ quote∘eval eq) modulo the
-- one typed-SN hypothesis. The decidability theorem above is decidable_of_iff over this. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.Conv.iff_normalize_eq_of_hasTypeDescPiStronglyNormalizes
-- WEAK NORMALIZATION leg of the conditional package: subjectWeaklyNormalizesOfStronglyNormalizes — typed-SN ⟹
-- every well-typed subject reaches a normal form (RawTerm.normalize on the hypothesis-supplied SN witness;
-- normalize_reducesTo + normalize_isStepNormalForm). Completes typed-SN ⟹ {confluence, decidable Conv,
-- Conv=normalize-eq, WN}. Zero-axiom (Acc-recursion).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectWeaklyNormalizesOfStronglyNormalizes
-- CANONICAL-FORMS HEADLINE (conditional on typed-SN): uniqueNormalFormOfStronglyNormalizes — every well-typed
-- subject has a UNIQUE normal form. Existence = weak normalization; uniqueness = confluence + normal-form
-- rigidity (two NFs reached from one subject join, and a NF reached by a chain IS the chain start, so the join
-- apex collapses both onto one term). The typed fragment is a normalizing rewriting system with a unique
-- canonical representative. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.uniqueNormalFormOfStronglyNormalizes
-- RELEASE-READINESS CONSOLIDATION (#664, Thrust-C de-risking): convergencePackageModuloStronglyNormalizes bundles
-- the THREE propositional normalization consequences of the single typed-SN hypothesis into one auditable
-- statement: (1) weak normalization, (2) per-subject confluence (typed Newman bridge SN-046), (3) unique normal
-- form. Termination (the hypothesis) + WN + confluence = convergence; conjunct 3 is the headline. NOT new
-- metatheory — each conjunct is the corresponding shipped conditional theorem applied to the one hypothesis; the
-- value is the single discharge point. Decidable Conv + Conv=normalize-eq are the companion gated results (their
-- conclusions thread the SN witness into normalize, so they stay standalone in HasTypeDescPiConditionalConfluence).
-- Unconditional in one step once #672 lands. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convergencePackageModuloStronglyNormalizes

/-! ### PER-VARIABLE-LEVEL reducible environment (the Kripke refinement for the dependent fundamental
    theorem).  `ReducibleEnvAt`'s single global level cannot serve a context that mixes variables at
    different typing-tower rungs (each rung sits one fuel higher via `tarskiDecode`, and upward
    level-cumulativity is false).  `ReducibleEnvVec` indexes each variable by its OWN tower level via a
    `Fin scope → Nat` vector; `levelCons` is the propext-free fresh-level cons. -/
-- SN-008 VERIFIED 2026-06-02 (no rebuild): ReducibleEnvVec IS the per-variable-level reducible closing
-- environment — `def ReducibleEnvVec (levels : Fin scope → Nat) context substitution := ∀ index,
-- IsReducibleMemberAt (levels index) (subst substitution (context.lookup index)) (substitution index)` — its
-- per-variable level is the ABSTRACT (Fin scope → Nat) vector (fuel/depth, NOT denote(LevelExpr)); empty/cons/
-- lookupReducible are proved + gated below, and the all-levels Kripke variant ReducibleEnvAtAllLevels (+9 members)
-- is gated above (lines ~943-956). A denote-keyed env is the INSTANTIATION levels := fun i => denote(classifierOf i)
-- env — NO new relation (the SN-002 "instantiation, not rebuild" finding) — so NO variant is built: it would
-- duplicate the shipped env (task discipline forbids duplication).
#assert_no_axioms FX1Poly.Typed.levelCons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.cons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.typeVariableReducible
-- typeVariableAllLevelMember: a SYNTACTIC type variable (type = universe code) is a reducible member of its
-- universe at EVERY positive level (universe codes are level-poly types; vars inhabit any reducible type).
-- Records that the dependent-former DOMAIN obstruction is the per-variable-level ENV pinning, not an intrinsic
-- single-level limitation of variables — an all-level env for type-variable entries would discharge it.
#assert_no_axioms FX1Poly.Typed.typeVariableAllLevelMember

/-! ### SEMANTIC TYPING RULES UNDER A CLOSING SUBSTITUTION (the fundamental theorem's arm bodies).
    The Girard-Tait fundamental theorem over `HasTypeDescPi` is a thin induction whose arms dispatch to
    these substitution-closed semantic rules.  `applicationUnderSubst` is the `piElim` arm: it lifts the
    raw `IsReducibleMemberAt.application` through the β-substitution commutation
    `RawTerm.subst0_subst_commute` (which lines up `subst γ (subst0 codomainCode argument)` with the
    dependent output of the substituted pieces), at a FIXED `level` (elimination introduces no universe
    nesting).  Future arms (conv / piIntro / formation) append here. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.applicationUnderSubst

/-! ### CONV ARM under a closing substitution.  Transports membership across the substituted conversion
    (`Conv.subst`) via the shipped `castAlongConv`; the target type-reducibility is supplied by the
    fundamental theorem via `tarskiDecode` of the `reclassifier : Type@e` premise's IH at `level + 1`. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.castAlongConvUnderSubst

/-! ### NON-DEPENDENT (simply-typed) Π-INTRODUCTION arm under a closing substitution.  Lifts the raw
    `abstractionNonDependent` (the choice-free no-large-elim piIntro) through the cell-substitution
    commutations: `subst_lamCell`/`subst_piTyCodeCell` (rfl) + `subst_lift_weaken_commute` (the codomain
    weakening commutes out through the binder lift).  The binder arm of the simply-typed fundamental
    theorem. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.abstractionNonDependentUnderSubst

/-! ### DEPENDENT Π-introduction + both Π-formation arms under a closing substitution.  The dependent
    `piIntro` (`abstractionUnderSubst`) and `Π`-formation (`piTypeUnderSubst`) twins lift the raw
    `abstraction` / `piType` through the rfl cell-substitutions (dependent codomain stays in the extended
    scope — no weakening-commutation); the simple-arrow formation (`arrowTypeUnderSubst`) lifts
    `arrowType` through the same `typeEq` re-expression as the non-dependent `piIntro` arm.  Choice-free as
    semantic rules (the per-argument candidate is given); the dependent arms are the full-FT (large
    elimination) introduction/formation rules. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.abstractionUnderSubst
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAt.arrowTypeUnderSubst
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAt.piTypeUnderSubst

/-! ### CHOICE-FREE dependent Π formation + introduction under a closing substitution (the Path-A
    fundamental-theorem binder arms).  The canonical-codomain twins of `piTypeUnderSubst` /
    `abstractionUnderSubst`: they feed the FIXED `fun arg => IsReducibleMemberAt level (subst0 (subst
    (lift γ) cod) arg)` codomain and discharge the per-argument codomain premise from mere EXISTENCE via
    the Core engine `reducibleMemberCandidate` — no candidate is chosen, so the choice wall the dependent
    fundamental theorem hit at `piIntro`/`piType` is dissolved. -/
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAt.piTypeCanonicalUnderSubst
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.abstractionCanonicalUnderSubst

/-! ### genFormationPi former weak-head-normality — the `genFormationPi` arm's WHN obligation.
    `typingRuleDescOf` is `some` only for `gen_piTyCode` / `gen_sigmaTyCode` (the dependent type-formers),
    both weak-head normal, so the fundamental theorem's generic formation arm discharges the
    `reducibleOfWeakHeadNormalFormer` weak-head-normality hypothesis with no per-former proof at the
    induction site. -/
#assert_no_axioms FX1Poly.Typed.formationGenerator_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormationUnderSubst
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormationUnderSubst
-- GTL-11 spike GO (proven by construction): the listCode data-former universe-membership under a closing
-- substitution, the one-child twin of sigmaFormationUnderSubst via the arity-generic dataFormerInUniverse.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.listCodeFormationUnderSubst
-- GTL-11 level-indexed reassembly: the listCode former-membership FROM the one-child telescope (the
-- level-indexed twin of the bounded fundamentalGenFormationListFromTelescopeAtBoundedSucc; CR1 element-SN +
-- listCodeFormationUnderSubst). Makes the FundamentalLevelIndexed + vector arms one-line calls.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.listFormerFromTelescope

-- Root-classification corollaries: a formation-typed subject's root generator is neither lam nor app. The
-- table-generic family in HasTypeDescPiRootGeneric (subjectRootGeneratorGeneric /
-- closedSubjectRootGeneratorGeneric, gated below) drives these ne_lam/ne_app corollaries, so a new formation
-- row extends them with no change.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_lam
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_app
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeApplication

/-! ### FORMATION-ARM BRIDGE: membership at a universe-code classifier ⟺ strong normalization.
    A universe code is a normal leaf (`noStep_universeCode`), hence neutral, so the dependent
    reducibility relation assigns it the SN candidate and `IsReducibleMember (universeCodeCell ..) t ↔
    IsStronglyNormalizing t` (via the Core `IsReducibleMember.atNeutralClassifier`).  This is the
    fundamental theorem's formation/universe arm bridge between a well-formed type term and its SN. -/
#assert_no_axioms FX1Poly.Typed.universeCodeCell_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.IsReducibleMember.atUniverseCode
#assert_no_axioms FX1Poly.Typed.DescTelescope.consInversion
#assert_no_axioms FX1Poly.Typed.DescTelescope.twoChildLevels
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
-- Telescope REACH (DescTelescopeReach): a formation telescope forces its children's binderShifts to be the
-- cumulative sequence [depth, depth+1, ...] (structural recursion over the mutual telescope). Consequence:
-- the non-dependent [0,0] type-code formers (product/sum/either/arrow/equiv) are OUTSIDE genFormation's reach
-- (noFlatTwoChildTelescope / productCodeFormationTelescopeImpossible) — they need a flat-telescope
-- generalization, not a listCode-style row addition. cumulativeShifts_length via Nat induction; the [0,0]
-- refutation via plain List injection + Nat.noConfusion (no indexed-cases propext leak).
#assert_no_axioms FX1Poly.Typed.cumulativeShifts_length
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
-- FLAT-FORMER TYPING (HasTypeDescFlat): the #934 CAPABILITY — the non-dependent [0,0] type-code formers now TYPE
-- via a STANDALONE judgment (mirrors the grown HasTypeDescPi; NOT a HasTypeDesc mutual-block arm, so zero
-- cascade). flatTypingRuleDescOf table (product/sum/either/arrow/equiv → universeFormerOutput); the partition
-- fact (typingRuleDescOf_productCode_none: product is NOT cumulative); flatTypingRuleDescOf_outputIsUniverseFormer
-- metadata; HasTypeDescFlat inductive; productFlatFormationSmoke = product (Type@0)(Type@0) : Type@(lmax 1 1).
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_productCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_productCode_none
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_outputIsUniverseFormer
#assert_no_axioms FX1Poly.Typed.productFlatFormationSmoke
-- DATA-INTRO ENGINE (HasTypeDescDataIntro, DI-1): the standalone data-CONSTRUCTOR typing judgment, FLAT pattern
-- (references nothing of HasTypeDescPi in the nullary arm; a NEW relation, so the grown engine's data-head-
-- untyped refutations stay true — boolTrue is still untyped in HasTypeDescPi). Nullary arm + dataIntroNullary
-- RuleDescOf table (boolTrue/boolFalse -> boolCode); the constructors the grown engine PROVES untyped now have a
-- typing in the dedicated judgment. boolTrueTyped/boolFalseTyped = the two closed bool canonical members; the
-- partition witness typingRuleDescOf_boolTrue_none documents that ONLY this engine types boolTrue (it is a VALUE,
-- not a type-former). First brick toward non-vacuous bool canonicity (link-4, CANON-1). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_boolTrue
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_boolFalse
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.boolTrueTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.boolFalseTyped
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_boolTrue_none
-- DATA-INTRO INVERSION + BOOL CANONICAL FORMS (HasTypeDescDataIntroInversion, DI-1/DI-4 inversion slice). The
-- twin of HasTypeDescFlatInversion: inversion = single-arm cases (nullaryIntro context is the auto-index, binds 5);
-- dataIntroNullaryRuleDescOf_isBoolConstructor = the table holds exactly boolTrue/boolFalse. subjectIsBoolConstructor
-- (★) = the closed-canonical-forms content CANON-1 (link-4) consumes: a data-intro-typed subject IS boolTrueCell or
-- boolFalseCell (combined with SN+SR -> closed t:boolCode reduces to a bool value). Cell normalization: cases payload
-- (Unit -> ()) + cases children (RawTermChildren [] -> childNil), rfl each branch. Refines as DI-2/DI-3 add ctors.
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.inversion
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_isBoolConstructor
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectIsBoolConstructor
-- DATA-INTRO SR + SN METATHEORY (HasTypeDescDataIntroMetatheory, DI-4 substantive half). subjectHasNoStep =
-- the shared substrate: a data-intro subject blocks every Step (it is a bool value -> normal form, via
-- subjectIsBoolConstructor =def boolIsValue + boolIsValue_impliesStepNormalForm + isStepNormalForm_blocks_step).
-- subjectReduction = SR (vacuous: a value has no reduct). subjectStronglyNormalizing (★) = SN via
-- isStronglyNormalizing_of_noStep (a closed data-intro-typed term is a normal-form value — the canonicity fact).
-- classifierIsBoolTypeCell = the classifier twin of subjectIsBoolConstructor (Option.some.inj recovers the rule).
-- Weakening/subst are DEGENERATE here (closed variable-free subjects) -> folded into DI-2's open n-ary subjects.
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.classifierIsBoolTypeCell
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.boolCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.emptyCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.natCodeTyped
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_boolCode_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_emptyCode_none
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_natCode_none
-- BASE-TYPE METATHEORY (HasTypeDescBaseTypeMetatheory, #1062 / DI-1b-meta): inversion + determinism + SR/SN,
-- the DI-4 analogue for the type-FORMER judgment. ★ classifierDetermined = the PROOF the flag-pinning design
-- works (two derivations of one subject reach the SAME classifier — not just Conv, EQUAL — the determinism a
-- free flag would have broken); a propext-free corollary of classifierIsType0 (each pins Type@0 independently,
-- no cases-on-both / mkGen-index unification). subjectIsBaseTypeCode = closed forms (boolTypeCell/emptyTypeCell).
-- subjectHasNoStep/StronglyNormalizing = type codes are no-step normal-form leaves (isStepNormalForm by rfl).
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.inversion
#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_isBoolEmptyOrNatCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.subjectIsBaseTypeCode
#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_outputIsType0
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.classifierIsType0
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.classifierDetermined
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.subjectStronglyNormalizing
-- STANDALONE-ENGINE CANONICITY (StandaloneEngineCanonicity, CANON-1 increment): combined closed-canonical-forms
-- over the two NON-grown engines (data-intro values + base-type codes). ★ standaloneBoolCanonicalForms = a
-- subject typed at boolTypeCell by EITHER engine is boolTrue/boolFalse (data-intro gives it; base-type is ruled
-- out since its classifier is Type@0 != boolCode, via classifierIsType0 + headGenerator/Generator.noConfusion).
-- standaloneEmptyUninhabited = nothing typed at emptyTypeCell by either engine (standalone half of SN-050).
-- dataIntroAndBaseTypeSubjectsDisjoint = the value layer and type layer never type the same term (disjoint heads).
-- The grown disjunct (HasTypeDescPi at boolCode via conv/piElim) is the remaining CANON-1 residual. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.standaloneBoolCanonicalForms
#assert_no_axioms FX1Poly.Typed.standaloneEmptyUninhabited
#assert_no_axioms FX1Poly.Typed.dataIntroAndBaseTypeSubjectsDisjoint
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtBoolType
#assert_no_axioms FX1Poly.Typed.closedNormalBoolCanonicalForms
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
-- ★ MILESTONE-A VALUE-LAYER SPINE: the three now-unconditional soundness pillars of the grown typed kernel
-- bundled as ONE record — SN-043 (every closed grown-typed term is SN), SN-050 (no closed grown inhabitant
-- of emptyType), SN-047 value-layer (a closed bool reduces to boolTrue/boolFalse). Each field is the shipped
-- unconditional theorem at the empty context; zero-axiom. Honest scope: eliminator-layer canonicity (CANON-1)
-- and the joint-decidability apex (O-NORM) remain the named open frontier (see the file docstring).
#assert_no_axioms FX1Poly.Typed.milestoneAValueLayerSpineHolds
-- ★ MILESTONE-A ELIMINATOR-LAYER SPINE: discharges the eliminator-layer frontier the VALUE-layer spine deferred.
-- Five fields, one per data eliminator, each a shipped unconditional computing-canonicity theorem: bool
-- (boolElimValueCanonicity, value-branch engine, one ι-step), nat (natElimCopyComputesToNumeral, RECURSIVE
-- IH-threaded copy fold), list (listElimLengthComputesToNumeral, RECURSIVE length fold), option/either
-- (closedOption/EitherMatchIntoBoolComputes, firing-64 typed match-into-bool). Every closed well-formed
-- eliminator instance reduces to a canonical value; zero-axiom. Honest scope: this is the per-eliminator
-- computing layer, NOT a unified eliminator:dataType judgment (the combined intro/elim table-residency, whose
-- formation/grown half GTL-18/20 is shipped, data-elim half open). Advances #556/#1138.
#assert_no_axioms FX1Poly.Typed.eliminatorLayerCanonicitySpineHolds
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
#assert_no_axioms FX1Poly.Typed.dataCanonicityFromGrownRigidity
#assert_no_axioms FX1Poly.Typed.boolCanonicityViaGrownRigidity
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedGrownTermAtSigmaType
-- ★ SN-048: CLOSED NAT CANONICITY (ClosedNatCanonicity, the first per-type instance of the generic grown-rigidity
-- packaging, unblocked by DI-3's gen_natCode + HasTypeDescNatIntro). IsNatNumeral = the recursive value predicate
-- (natZero, or natSucc of a numeral — Nat has infinitely many, unlike bool's two). subjectIsNatNumeral = every
-- nat-intro-typed subject IS a numeral (two-arm induction, no reduction — nat-intro terms are already values).
-- Conv.natTypeCell_not_{piTyCode,sigmaTyCode,universeCode} = the cross-former rigidities (no-step-leaf +
-- shapeStable/noStep + noConfusion, mirror of the bool rigidities). ★ closedNatCanonicalForms = SN-048: a closed
-- term typed at natTypeCell by the nat-intro OR grown engine reduces to a numeral (standalone arm =
-- standaloneNatCanonicalForms; grown arm derived via noClosedGrownTermAtDataClassifier). natOne = non-vacuity
-- (succ 0 canonical). The recursive natElim-computing canonicity (#1138) is the follow-on. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.subjectIsNatNumeral
#assert_no_axioms FX1Poly.Typed.standaloneNatCanonicalForms
#assert_no_axioms FX1Poly.Typed.Conv.natTypeCell_not_piTyCode
#assert_no_axioms FX1Poly.Typed.Conv.natTypeCell_not_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.natTypeCell_not_universeCode
#assert_no_axioms FX1Poly.Typed.closedNatCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedNatCanonicalForms.natOne
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
#assert_no_axioms FX1Poly.Typed.closedOptionCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedOptionCanonicalForms.smoke
#assert_no_axioms FX1Poly.Typed.closedListCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedListCanonicalForms.smoke
#assert_no_axioms FX1Poly.Typed.closedProductCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedProductCanonicalForms.smoke
#assert_no_axioms FX1Poly.Typed.closedEitherCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedEitherCanonicalForms.smoke
-- ELIMINATOR-ENGINE CLOSED-NORMAL VACUITY (BoolElimClosedNormalForms, the first concrete piece of #1138): the
-- bool ELIMINATOR engine (HasTypeDescBoolElim, the 4th engine) contributes a VACUOUS disjunct to closed-normal
-- canonical forms — a closed eliminator on a closed VALUE scrutinee always ι-fires, so it is never normal.
-- ★ noClosedNormalBoolElim = the eliminator vacuity (classifier-agnostic): scrutinee is data-intro-typed at
-- boolCode ⟹ boolTrue/boolFalse (standaloneBoolCanonicalForms) ⟹ boolElim is an ι-redex ⟹ `cases normal` refutes
-- (NF checker computes false on the head redex). ★ closedNormalBoolCanonicalFormsWithElim = the FOUR-engine
-- closed-normal bool canonical forms, extending closedNormalBoolCanonicalForms (#1064, 3 engines) with the
-- eliminator as the vacuous 4th disjunct. The arbitrary-subject 4-engine upgrade (combined SN/SR) is the #1138
-- follow-on. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescBoolElim.noClosedNormalBoolElim
#assert_no_axioms FX1Poly.Typed.closedNormalBoolCanonicalFormsWithElim
-- MATCH-ENGINE CLOSED-NORMAL VACUITY (MatchClosedNormalForms): the option/either MATCH eliminator engines
-- (HasTypeDescOptionMatch / HasTypeDescEitherMatch) are likewise VACUOUS disjuncts — a closed match on a closed
-- constructor scrutinee always ι-fires, so it is never normal. Same structural argument as the bool case:
-- scrutinee is option/either-intro-typed ⟹ a constructor (subjectIsOptionConstructor / subjectIsEitherInjection)
-- ⟹ the match is a ι-redex ⟹ `cases normal` refutes. Extends the per-classifier eliminator rule-out from bool
-- to the match family. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionMatch.noClosedNormalOptionMatch
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherMatch.noClosedNormalEitherMatch
-- ARBITRARY-SUBJECT 4-ENGINE BOOL CANONICITY (BoolElimArbitrarySubjectCanonicity): upgrades the closed-normal
-- 4-engine forms OFF the `normal` hypothesis. ★ KEY: the bool-elim engine's branches are GROWN-typed and the
-- grown engine has no closed boolCode inhabitant, so a closed boolElim AT boolTypeCell is impossible by inverting
-- to a branch + noClosedGrownTermAtBoolType — NO SN/SR. ★ noClosedBoolElimAtBoolType = the eliminator vacuity at
-- boolCode (arbitrary subject). ★ closedBoolCanonicalFormsWithElim = the 4-engine arbitrary-subject bool canonicity
-- (DataIntro∨BaseType∨Pi∨BoolElim ⟹ ↝* boolTrue/boolFalse). HONEST FINDING: the current eliminator requires
-- grown branches so it cannot type boolElim b true false : Bool (data-value branches) — eliminator-computing
-- canonicity AT a data type is VACUOUS for it; the non-vacuous version needs a stronger combined intro/elim engine
-- (deferred #1138 / GTL table-residency). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescBoolElim.noClosedBoolElimAtBoolType
#assert_no_axioms FX1Poly.Typed.closedBoolCanonicalFormsWithElim
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
#assert_no_axioms FX1Poly.Typed.boolElimValueCanonicity
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
#assert_no_axioms FX1Poly.Typed.constNatZeroStepProduces
#assert_no_axioms FX1Poly.Typed.natElimConstZeroComputesToNumeral
#assert_no_axioms FX1Poly.Typed.copyNatStepProduces
#assert_no_axioms FX1Poly.Typed.natElimCopyComputesToNumeral
#assert_no_axioms FX1Poly.Typed.natElimCopyComputesToNumeral.two
-- Native natElim computes binary ADDITION FAITHFULLY (NatElimFaithfulArithmetic): sharpens "computes to A
-- numeral" to the EXACT result — natElim(numeral n, numeral m, copyStep) ↝* numeral (m+n), agreeing with the
-- host's Nat addition. natNumeralCell is the reusable native numeral builder; the proof is structural recursion
-- on the scrutinee composing ι-steps + the copy-step β-pair (Nat.add_zero / Nat.add_succ for the arithmetic).
#assert_no_axioms FX1Poly.Typed.natNumeralCell
#assert_no_axioms FX1Poly.Typed.natNumeralCell_isNumeral
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
#assert_no_axioms FX1Poly.Typed.natNumeralAt_zero_eq_natNumeralCell
-- ★ NatElimFaithfulMul (HON-13 closed): native gen_natElim computes EXACT host Nat.mul, completing the recursor
-- faithfulness (Nat.add was natElimAddFaithful). mulNatStep m = lam.lam.natElim(numeralM, r, copyStep) embeds a
-- recursor in the step branch; mulStepFires lands the inner adder via the two β-reductions, consuming the
-- natNumeralAt_subst crack (each Step.beta gives the raw subst0 body arg; firstEq/secondEq rewrite it — the
-- pretty reduct cannot be asserted directly on the stuck symbolic numeral). natElimMulFaithful = structural
-- recursion on n reusing natElimAddFaithful as the per-step adder (m·n + m = m·(n+1) defeq via Nat.mul_succ).
-- Fin bounds use Nat.succ_pos _ (NOT omega, which leaks propext). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.copyNatStepAt
#assert_no_axioms FX1Poly.Typed.copyNatStepAt_zero
#assert_no_axioms FX1Poly.Typed.mulNatStep
#assert_no_axioms FX1Poly.Typed.mulStepFires
#assert_no_axioms FX1Poly.Typed.natElimMulFaithful
#assert_no_axioms FX1Poly.Typed.natElimMulFaithful.threeTimesTwo
-- ★ HON-5 NEGATIVE soundness of the honest static-typing classifier: a head hasSomeTypingRule reports RESERVED
-- (= false) is typed by NO engine. Grown leg = the propext-free bridge hasSomeTypingRule_false_imp_isUntypableHead
-- (peels the 24-disjunct || chain via orEqFalse_left/rightFalse, reduces typingRoleOf via if_neg, discharges with
-- decide_eq_true) feeding the shipped isUntypableHead_sound; the 14 standalone legs consume each engine's shipped
-- subjectIs… inversion + Bool.noConfusion (Flat keys on a symbolic generator, so collapses the chain via
-- Bool.or_true/true_or). reservedHeadUntypedByEveryEngine bundles all 15. Turns hasSomeTypingRule = false from a
-- Bool into a TRUTHFUL "statically reserved" verdict.
#assert_no_axioms FX1Poly.Typed.orEqFalse_leftFalse
#assert_no_axioms FX1Poly.Typed.orEqFalse_rightFalse
#assert_no_axioms FX1Poly.Typed.notEqTrue_ofEqFalse
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_false_imp_isUntypableHead
#assert_no_axioms FX1Poly.Typed.grownReservedUntyped
#assert_no_axioms FX1Poly.Typed.flatReservedUntyped
#assert_no_axioms FX1Poly.Typed.baseTypeReservedUntyped
#assert_no_axioms FX1Poly.Typed.dataIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.natIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.idIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.optionIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.eitherIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.pairIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.listIntroReservedUntyped
#assert_no_axioms FX1Poly.Typed.boolElimReservedUntyped
#assert_no_axioms FX1Poly.Typed.idElimReservedUntyped
#assert_no_axioms FX1Poly.Typed.optionMatchReservedUntyped
#assert_no_axioms FX1Poly.Typed.eitherMatchReservedUntyped
#assert_no_axioms FX1Poly.Typed.sigmaProjectionReservedUntyped
#assert_no_axioms FX1Poly.Typed.reservedHeadUntypedByEveryEngine
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
#assert_no_axioms FX1Poly.Typed.constNatZeroStep3Produces
#assert_no_axioms FX1Poly.Typed.listElimConstZeroComputesToNumeral
#assert_no_axioms FX1Poly.Typed.lengthNatStepProduces
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
-- ★ SEMANTIC-TIER soundness (SemanticTierSoundness): the unified live/reserved ledger's RESERVED verdict is
-- TRUTHFUL. semanticTier g = .reserved decomposes (semanticTier_reserved_imp_both_false) into BOTH classifier
-- Bools false — were the || true the tier if would yield .live, refuted by SemanticTier.noConfusion — feeding
-- the HON-5 static leg (reserved ⟹ untyped by every engine; grown representative + full-15 bundle) and the
-- HON-6 operational leg (reserved ⟹ no root redex). semanticTierReservedSound is the headline: a reserved
-- generator is semantically dead (grown-untyped AND operationally inert). The soundness that makes the honest
-- 197-generator partition a VERIFIED ledger, not an unchecked Bool. Zero-axiom (cases on the || + if_pos + the
-- shipped HON-5/HON-6 legs).
#assert_no_axioms FX1Poly.Typed.semanticTier_reserved_imp_both_false
#assert_no_axioms FX1Poly.Typed.reservedTierOperationallyInert
#assert_no_axioms FX1Poly.Typed.reservedTierUntypedByGrownEngine
#assert_no_axioms FX1Poly.Typed.reservedTierUntypedByEveryEngine
#assert_no_axioms FX1Poly.Typed.semanticTierReservedSound
-- ★ CLASSIFIER REFINEMENT (ClassifierRefinement): the full-union static classifier hasSomeTypingRule STRICTLY
-- refines the grown-only untypability decision isUntypableHead. Refinement (union-reserved ⟹ grown-untypable =
-- the HON-5 bridge) + containment (grown-typable ⟹ union-typed, Bool-contrapositive) + STRICT witness
-- (gen_boolTrue: grown-untypable yet union-typed, since the standalone HasTypeDescDataIntro engine types it).
-- The union's typed-set strictly contains the grown-typable set — the standalone data engines genuinely EXTEND
-- typability beyond the grown core, so the honest 197-table classifier is not the grown decision in disguise.
-- Zero-axiom (cite HON-5 bridge + cases/rw/Bool.noConfusion + ⟨rfl, rfl⟩ witness).
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_refines_isUntypableHead
#assert_no_axioms FX1Poly.Typed.grownTypable_imp_unionTyped
#assert_no_axioms FX1Poly.Typed.boolTrue_grownUntypableButUnionTyped
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRuleStrictlyRefinesUntypableHead
-- ★ THE HONESTY-ARC CAPSTONE (GeneratorHonestyLedger): one machine-checked ledger bundling the arc's four
-- pillars over the 197-generator table — SOUNDNESS (reserved ⟹ semantically dead, via semanticTierReservedSound),
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
-- PAIR INTRODUCTION (HasTypeDescPairIntro, DI-2): the standalone n-ary data-constructor judgment typing the Σ
-- VALUE pair(a,b) : product(A,B) from grown components a:A, b:B — the first non-vacuous Σ-value the kernel types
-- (cascade-free, mirroring HasTypeDescBaseType, NOT an arm of HasTypeDescDataIntro/HasTypeDescPi). pairOfUniverse
-- CodesTyped = the smoke pair(Type@0,Type@0) : product(Type@1,Type@1). subjectIsPair/classifierIsProduct = the
-- SR-free closed-forms inversions (subject is a pairCell, classifier a productTypeCell). The SR/SN quartet is the
-- GrownCtxConv-5-entangled deferral (pair steps when a component steps → consumes grown master SR / #842).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPairIntro.pairOfUniverseCodesTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescPairIntro.subjectIsPair
#assert_no_axioms FX1Poly.Typed.HasTypeDescPairIntro.classifierIsProduct
-- EITHER INTRODUCTION (HasTypeDescEitherIntro, DI-2 sum half): the standalone coproduct judgment typing the sum
-- VALUES eitherInl(a) / eitherInr(b) : either(A,B) — each arm has ONE value premise + ONE type-formedness premise
-- for the un-injected (free) component (the asymmetry vs pair, whose two components are both value-pinned).
-- eitherInl/InrOfUniverseCodeTyped = the smokes eitherInl/Inr(Type@0) : either(Type@1,Type@1). subjectIsEither
-- Injection/classifierIsEither = the SR-free closed-forms inversions (subject is an inl/inr cell, classifier an
-- eitherTypeCell). Completes the DI-2 "pair / eitherInl / eitherInr" value-typing scope (SR quartet GrownCtxConv-5-deferred).
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherIntro.eitherInlOfUniverseCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherIntro.eitherInrOfUniverseCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherIntro.subjectIsEitherInjection
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherIntro.classifierIsEither
-- OPTION INTRODUCTION (HasTypeDescOptionIntro, DI-2c): the standalone option judgment typing the option VALUES
-- optionNone / optionSome(a) : option(A). The optionNone arm carries a type-formedness premise for the FREE
-- element type A (the None asymmetry — None carries no payload, exactly like eitherInl's free un-injected side);
-- the optionSome arm a value premise a:A that PINS A. The scrutinee-typing prerequisite for the option ELIMINATOR
-- (DI-5c, next). optionNone/SomeOfUniverseCodeTyped = the smokes optionNone:option(Type@0) /
-- optionSome(Type@0):option(Type@1). subjectIsOptionConstructor/classifierIsOption = the SR-free closed-forms
-- inversions (subject is a none/some cell, classifier an optionTypeCell). SR quartet GrownCtxConv-5-deferred.
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionIntro.optionNoneOfUniverseCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionIntro.optionSomeOfUniverseCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionIntro.subjectIsOptionConstructor
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionIntro.classifierIsOption
-- Σ/COPRODUCT CANONICAL FORMS (ProductEitherCanonicalForms, the DI-2 payoff): NON-VACUOUS closed-normal
-- canonicity for product/either types, unconditional (no GrownCtxConv-5/§5). NEW rigidity Conv.product/eitherCode_not_
-- universeCode (flat-former twin of boolTypeCell_not_universeCode, via shapeStable + universe leaf + noConfusion)
-- + Conv.piTyCode_not_conv_eitherCode (cross-table). noClosedNormalTermAtProduct/EitherType = CANON-1c rule-out
-- instances (grown engine inhabits no product/either type — Σ/coproduct formation but no introduction). ★ closed
-- NormalProduct/EitherCanonicalForms = a closed-normal term at product/either by the intro engine OR grown is a
-- pairCell / eitherInl-or-Inr cell. The non-vacuous Σ/coproduct canonicity (values exist via DI-2a/b + every
-- closed-normal inhabitant is one). Full canonicity (all closed terms) still needs the master SR / #842.
#assert_no_axioms FX1Poly.Typed.Conv.productCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.eitherCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_conv_eitherCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtProductType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtEitherType
#assert_no_axioms FX1Poly.Typed.closedNormalProductCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedNormalEitherCanonicalForms
-- OPTION CANONICAL FORMS (OptionCanonicalForms, the DI-2c payoff): NON-VACUOUS closed-normal option canonical
-- forms — a closed-normal term typed at option(A) by the option-intro engine OR the grown engine is optionNone /
-- optionSome. Unlike product/either (FLAT-table codes), gen_optionCode is a FORMATION-table former (typingRuleDescOf,
-- via GTL-13) — like boolCode/sigmaTyCode — so the rule-outs use the FORMATION substrate: optionCode_not_universeCode
-- = the new head-stable(shapeStable_optionCodeGeneral)-vs-leaf(universe) rigidity (one-child twin of productCode_not_
-- universeCode); optionCode_not_piTyCode = the within-formation-table rigidity (formationFormersNotConvOfDistinct,
-- gen_optionCode≠gen_piTyCode). noClosedNormalTermAtOptionType = the CANON-1c grown rule-out instance.
-- closedNormalOptionCanonicalForms = the headline (option-intro disjunct via subjectIsOptionConstructor, grown ruled
-- out). Completes the option data story (intro DI-2c + elim DI-5c + canon). Full canonicity needs master SR / #842.
#assert_no_axioms FX1Poly.Typed.Conv.optionCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.optionCode_not_piTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtOptionType
#assert_no_axioms FX1Poly.Typed.closedNormalOptionCanonicalForms
-- BOOL ELIMINATOR + TYPED ι-COMPUTATION (HasTypeDescBoolElim, DI-5 first brick): the kernel's data story from
-- INTRODUCTION to ELIMINATION. The standalone non-dependent boolElim judgment (boolElim(s,t,e):C from scrutinee
-- s:boolCode via data-intro + branches t,e:C via grown). boolElimOfUniverseCodesTyped = the smoke boolElim(boolTrue,
-- Type@0,Type@0):Type@1. subjectIsBoolElim = free-index inversion. ★ boolElimTrue/FalseIotaComputesTyped = the
-- TYPED ι-COMPUTATION: a typed boolElim on a value ι-reduces (Step.iotaBoolTrue/False) to the typed branch — the
-- eliminator COMPUTES and PRESERVES TYPING (constructor-side, so SR-free + propext-free; full SR is the GrownCtxConv-5-gated
-- branch-congruence deferral). Advances DI-5 #1047 (boolElim brick).
#assert_no_axioms FX1Poly.Typed.HasTypeDescBoolElim.boolElimOfUniverseCodesTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescBoolElim.subjectIsBoolElim
#assert_no_axioms FX1Poly.Typed.boolElimTrueIotaComputesTyped
#assert_no_axioms FX1Poly.Typed.boolElimFalseIotaComputesTyped
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherMatch.subjectIsEitherMatch
#assert_no_axioms FX1Poly.Typed.eitherMatchInlIotaComputesTyped
#assert_no_axioms FX1Poly.Typed.eitherMatchInrIotaComputesTyped
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionMatch.subjectIsOptionMatch
#assert_no_axioms FX1Poly.Typed.optionMatchNoneIotaComputesTyped
#assert_no_axioms FX1Poly.Typed.optionMatchSomeIotaComputesTyped
-- Σ-PROJECTION ELIMINATOR + the THIRD ι shape (HasTypeDescSigmaProjection, DI-5d): completes the Σ/pair data story
-- (intro DI-2a + canon DI-2-canon + this elim). fst/snd carry the CONTENT-PROJECTION ι (fst(pair(a,b)) ↝ a;
-- snd(pair(a,b)) ↝ b) — the reduct is a CHILD of the SCRUTINEE, not a branch (boolElim) nor a handler-applied-to-
-- payload (eitherMatch). The SIMPLEST typed ι: the reduct's typing IS one of the pair's component typings directly
-- (no branch, no piElim, no subst0). The 2-arm judgment (scrutinee:product(A,B) via the pair-intro engine → fst:A /
-- snd:B). fstOfUniverseCodesTyped = the smoke fst(pair(Type@0,Type@0)):Type@1. subjectIsSigmaProjection = free-index
-- inversion. ★ fst/sndProjectionIotaComputesTyped = the typed content-projection ι. Constructor-side, SR-free +
-- propext-free (full scrutinee-congruence SR GrownCtxConv-5-deferred). All THREE non-recursive ι shapes now typed-and-
-- computing across the data eliminators. Advances DI-5 #1047 / SN-058 (#446, Σ projections).
#assert_no_axioms FX1Poly.Typed.HasTypeDescSigmaProjection.fstOfUniverseCodesTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescSigmaProjection.subjectIsSigmaProjection
#assert_no_axioms FX1Poly.Typed.fstProjectionIotaComputesTyped
#assert_no_axioms FX1Poly.Typed.sndProjectionIotaComputesTyped
-- IDENTITY DATA STORY (HasTypeDescIdIntro DI-2d + HasTypeDescIdElim DI-5e): reflexivity intro + idJ eliminator.
-- INTRO: refl(x):Id(A,x,x) is the PINNED reflexive intro (witness x:A pins A and BOTH endpoints, which are EQUAL).
-- reflOfUniverseCodeTyped = the smoke refl(Type@0):Id(Type@1,Type@0,Type@0). subjectIsRefl + classifierIsReflexiveId
-- = the SR-free inversions (subject is a reflCell, classifier a REFLEXIVE idTypeCell — both endpoints same term).
-- ELIM: the substrate's gen_idJ is the SIMPLIFIED two-child J (idJ(baseCase,witness), motive in the profile layer);
-- on refl its ι SELECTS the base case (idJ(b,refl(x)) ↝ b, Step.iotaIdJRefl) — the BRANCH-SELECTION shape (the
-- boolElim shape reused on identity). idJOfUniverseCodesTyped = the smoke idJ(Type@0,refl(Type@0)):Type@1.
-- subjectIsIdJ = free-index inversion. ★ idJReflIotaComputesTyped = the typed branch-selection ι (reduct IS the
-- base case, typed verbatim). Constructor-side → SR-free + propext-free (full witness-congruence SR GrownCtxConv-5-deferred).
-- Completes the identity data story (intro + elim). Advances DI-5 #1047 / SN-067/068 (#450, refl + idJ).
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdIntro.reflOfUniverseCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdIntro.subjectIsRefl
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdIntro.classifierIsReflexiveId
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdElim.idJOfUniverseCodesTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdElim.subjectIsIdJ
#assert_no_axioms FX1Poly.Typed.idJReflIotaComputesTyped
-- LIST INTRODUCTION (HasTypeDescListIntro, DI-2e): the FIRST RECURSIVE data constructor. nil:List(A) is the
-- NULLARY-free arm (free element type A, type-formedness premise, like optionNone); cons(h,t):List(A) is the
-- RECURSIVE arm — head h:A (pins A) + tail t:List(A) typed BY THE SAME judgment (the first self-referential
-- standalone data-intro arm, strictly positive). listNilOfUniverseCodeTyped = nil:List(Type@0).
-- listConsOfUniverseCodesTyped = the one-element list cons(Type@0,nil):List(Type@1) EXERCISING the recursive arm
-- (tail nil typed by the same engine). subjectIsListConstructor/classifierIsList = the SR-free closed-forms
-- inversions (subject is a nil/cons cell, classifier a listTypeCell). The scrutinee-typing prerequisite for the
-- list ELIMINATOR (listElim, the first RECURSIVE eliminator, a future brick). SR quartet GrownCtxConv-5-deferred.
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.listNilOfUniverseCodeTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.listConsOfUniverseCodesTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.subjectIsListConstructor
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.classifierIsList
-- NAT INTRODUCTION (HasTypeDescNatIntro, DI-3): the nat constructors at the nat type code natTypeCell. natZero:Nat
-- is the NULLARY arm with NO premise (Nat is a closed ground type, simpler than listNil's free element type);
-- natSucc(p):Nat is the RECURSIVE arm — predecessor p:Nat typed BY THE SAME judgment (strictly positive, the nat
-- twin of listConsIntro). natZeroTyped = 0:Nat; natOneTyped = succ 0:Nat (EXERCISING the recursive arm);
-- natTwoTyped = succ(succ 0):Nat (recursion nested twice). subjectIsNatConstructor/classifierIsNat = the SR-free
-- closed-forms inversions (subject a natZero/natSucc cell, classifier natTypeCell). Cascade-free standalone
-- judgment using natTypeCell as a RAW classifier (no Nat:Type@0 base-type-formation dependency). The
-- scrutinee-typing prerequisite for the nat ELIMINATORS (natElim/natRec) + nat canonicity (SN-048). SR quartet
-- engine-separation-deferred (#1078).
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.natZeroTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.natOneTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.natTwoTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.subjectIsNatConstructor
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.classifierIsNat
-- LIST CANONICAL FORMS (ListCanonicalForms, the DI-2e payoff): NON-VACUOUS closed-normal list canonical forms — a
-- closed-normal term typed at List(A) by the list-intro engine OR the grown engine is nil/cons. Like option/bool
-- (and unlike product/either FLAT-table codes), gen_listCode is a FORMATION-table former (typingRuleDescOf, GTL-11),
-- so the rule-outs use the FORMATION substrate: listCode_not_universeCode = head-stable(shapeStable_listCodeGeneral)-
-- vs-leaf(universe) rigidity (one-child twin of optionCode_not_universeCode); listCode_not_piTyCode = the within-
-- formation-table rigidity (formationFormersNotConvOfDistinct, gen_listCode≠gen_piTyCode). noClosedNormalTermAtList
-- Type = the CANON-1c grown rule-out instance. closedNormalListCanonicalForms = the headline (list-intro disjunct
-- via subjectIsListConstructor, grown ruled out). NOTE: the list ELIMINATOR (listElim) typed-ι is GrownCtxConv-5-class blocked
-- — its cons-ι reduct app(app(app(consBranch,h),t), listElim(t,...)) applies consBranch to the TAIL t (a list value)
-- and the RECURSIVE listElim (elim-engine-typed), NEITHER grown-typed, so piElim can't type them (recursive
-- eliminators are engine-separation-blocked, unlike the non-recursive ones). Full canonicity needs master SR / #842.
#assert_no_axioms FX1Poly.Typed.Conv.listCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.listCode_not_piTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtListType
#assert_no_axioms FX1Poly.Typed.closedNormalListCanonicalForms
-- IDENTITY CANONICAL FORMS (IdCanonicalForms, the DI-2d/5e payoff): NON-VACUOUS closed-normal identity canonical
-- forms — a closed-normal term typed at Id(A,left,right) by the id-intro engine OR the grown engine is a refl. THE
-- NOVEL RIGIDITY ROUTE: gen_idCode is NOT in typingRuleDescOf and CANNOT be (universeFormerOutput types every child
-- as a universe code, but idCode's children [typeCode,left,right] have left/right as TERMS not types), so the within-
-- formation-table rigidity (formationFormersNotConvOfDistinct) does NOT apply. idCode_not_universeCode = head-stable
-- (shapeStable_idCodeGeneral, 3-child) vs leaf(universe); idCode_not_piTyCode = the TWO-HEAD-STABLE route (BOTH idCode
-- and piTyCode head-stable → shared reduct carries both heads → noConfusion — the cleaner primitive needing no table
-- membership, vs the data-canon files' formationFormersNotConvOfDistinct). noClosedNormalTermAtIdType = CANON-1c grown
-- rule-out. closedNormalIdCanonicalForms = the headline (id-intro disjunct via subjectIsRefl, grown ruled out); stated
-- for a GENERAL idTypeCell (rigidities+subjectIsRefl endpoint-agnostic), refl populates only the reflexive left=right.
#assert_no_axioms FX1Poly.Typed.Conv.idCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.idCode_not_piTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noClosedNormalTermAtIdType
#assert_no_axioms FX1Poly.Typed.closedNormalIdCanonicalForms
-- FLAT-ENGINE INVERSION (#935, first increment): the flat twin of HasTypeDesc.inversionListCode. inversion =
-- generic single-arm cases recovering the flatFormation fields; inversionProductCodeComponents projects the
-- two-child flat telescope (twoChildComponents) to recover both child typings + pins the classifier shape to
-- Type@(lmax [firstLevel,secondLevel]) via the gen_productCode row.
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.inversion
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.inversionProductCodeComponents
-- FLAT-ENGINE SUBJECT REDUCTION (#935, next increment): the flat twin of HasTypeDesc.subjectReduction.
-- flatFormerCellStepIsChildCongruence = the flat-former cell heads no root redex (18-arm cases keyed on
-- flatTypingRuleDescOf, every redex arm contradicted by some-rule ≠ none); FlatDescTelescope.subjectReduction
-- re-types the premise under stepped children (simpler than the cumulative one — flat cons doesn't extend the
-- context, so no convTelescope); HasTypeDescFlat.subjectReduction rebuilds flatFormation at the unchanged
-- classifier (a child step touches neither generator nor levels).
#assert_no_axioms FX1Poly.Typed.flatFormerCellStepIsChildCongruence
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.subjectReduction
-- FLAT-FORMER FAMILY COMPLETION (#935): the other four flat formers (sum/either/arrow/equiv) TYPE — each a row
-- lemma (rfl) + a formation smoke (the children + premise are former-agnostic, only the generator/row differ),
-- completing the five-former flat-formation corpus alongside the existing productFlatFormationSmoke.
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_sumCode
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_eitherCode
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_arrowCode
#assert_no_axioms FX1Poly.Typed.flatTypingRuleDescOf_equivCode
#assert_no_axioms FX1Poly.Typed.sumFlatFormationSmoke
#assert_no_axioms FX1Poly.Typed.eitherFlatFormationSmoke
#assert_no_axioms FX1Poly.Typed.arrowFlatFormationSmoke
#assert_no_axioms FX1Poly.Typed.equivFlatFormationSmoke
-- FLAT-ENGINE STRONG NORMALIZATION (#935, next increment): the flat twin of
-- HasTypeDesc.subjectStronglyNormalizingNative. flatFormerCellStronglyNormalizingOfChildren reuses the GENERIC
-- Core accessibility substrate (formerCell_isStronglyNormalizing_of_accChildren) with the firing-45 congruence-
-- only inversion swapped in; FlatDescTelescope.childrenStronglyNormalizing is a plain (non-mutual) structural
-- recursion calling HasTypeDesc.subjectStronglyNormalizingNative on each head; HasTypeDescFlat.subjectStronglyNormalizing
-- is the headline; the five closed witnesses show each flat former TYPES and is SN.
#assert_no_axioms FX1Poly.Typed.flatFormerCellStronglyNormalizingOfChildren
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.childrenStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.subjectStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.productFlatTypeStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.sumFlatTypeStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.eitherFlatTypeStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.arrowFlatTypeStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.equivFlatTypeStronglyNormalizing
-- FLAT-ENGINE WEAKENING (#937, P6 structural metatheory): the flat twin of HasTypeDescWeakening. The two flat
-- former-table helpers (flatFormationRuleImpliesNotVariable / flatFormationRuleIsUniverseFormer) mirror the
-- cumulative formationRule* helpers. FlatDescTelescope.renameRespectingTelescope is LIGHTER than the cumulative
-- one (flat cons doesn't extend the context, so NO iterateLiftRaw — tail recurses with the SAME context-condition);
-- HasTypeDescFlat.renameRespectingContext reuses it + reconstructs the cell table-generically; weakenUnderBinding
-- instantiates at RawRenaming.weaken (context-condition fun _ => rfl).
#assert_no_axioms FX1Poly.Typed.flatFormationRuleImpliesNotVariable
#assert_no_axioms FX1Poly.Typed.flatFormationRuleIsUniverseFormer
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.renameRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.weakenUnderBinding
-- FLAT-ENGINE SUBSTITUTION (#938, P6 β-engine): the flat twin of HasTypeDescSubstitution, completing the flat
-- structural-metatheory quartet (SR/SN/weakening/substitution). FlatDescTelescope.substRespectingTelescope is
-- DRAMATICALLY lighter than the cumulative one — flat cons doesn't extend the context, so NO iterateLiftRaw, NO
-- 0/successor split, NO weakenUnderBinding (the tail recurses with the SAME substitution-condition);
-- HasTypeDescFlat.substRespectingContext reuses it + reconstructs the cell table-generically;
-- substituteUnderBinding is the subst0 β-corollary (ambient singleton split, mirrors the cumulative proof).
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.substRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.substRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.substituteUnderBinding
-- FLAT-ENGINE VALIDITY + TELESCOPE AGREEMENT (#939): formation-engine-parity properties.
-- classifierIsTypeDescNative = flat regularity (UNCONDITIONAL — flat has no var arm, classifier always a universe
-- code; lighter than the formation twin which needs WfContextDesc). FlatDescTelescope.uniquenessAgree = two flat
-- telescopes over equal children agree on levels/flag (the uniqueness substrate; flat rest-recursion keeps the
-- SAME context, no WfContextDesc.cons). The uniqueness headline itself is DEFERRED (propext via dependent mkGen
-- second-derivation injection — needs a propext-free flat inversionFormerWithConv analogue).
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.classifierIsTypeDescNative
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.uniquenessAgree
-- FLAT FORMER INVERSION + UNIQUENESS: the propext-free generic flat-former inversion (telescope + classifier
-- Conv). flatFormerBinderShifts = flat former arity [0,0]. inversionFormerWithConv aligns the generator via
-- congrArg headGenerator + subst BEFORE injection (cracked-wall idiom), avoiding the dependent-mkGen propext leak.
-- HasTypeDescFlat.uniquenessNative is the flat-engine typing-uniqueness headline: a clean free-index cases on the
-- first derivation exposes the .mkGen subject, the second derivation is inverted propext-free by
-- inversionFormerWithConv, and FlatDescTelescope.uniquenessAgree settles levels (and flag, via the two-child
-- telescope's nonempty level list) so both classifiers reduce to the same universe code.
#assert_no_axioms FX1Poly.Typed.flatFormerBinderShifts
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.inversionFormerWithConv
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.uniquenessNative
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.consInversion
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.twoChildLevels
-- GTL-11 substrate: the one-child [0] analogue (data type-code formers listCode / optionCode) — same
-- single-live-cons-then-nil discipline, no propext / Quot.sound; feeds the FT data-former branch.
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.oneChildLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormerOfChildMembershipsAtRequiredLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormerOfChildMemberships
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormerOfChildMemberships
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toDispatchLevels
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toPiMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.toPiMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toSigmaMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.toSigmaMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.ofTelescopeReducible
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.ofTelescopeReducible
#assert_no_axioms FX1Poly.Typed.consecutiveShifts
#assert_no_axioms FX1Poly.Typed.TelescopeReducible
#assert_no_axioms FX1Poly.Typed.Generator.gen_piTyCode_binderShifts_eq
#assert_no_axioms FX1Poly.Typed.Generator.gen_sigmaTyCode_binderShifts_eq
-- GTL-11: the one-child listCode binderShifts = consecutiveShifts 0 1 bridge for the FT data-former branch.
#assert_no_axioms FX1Poly.Typed.Generator.gen_listCode_binderShifts_eq

-- Universe-domain member-extension reduction: the cons-arm's last hard case (the type-polymorphic binder
-- `Π (A : Type@e). …`) is EXACTLY type-level positive level-irrelevance — the membership/SN layer stripped
-- off via the Tarski universe decode/encode, exposing the pure type-level lift the level-congruence
-- inductive step (`ReducibleTypeStep.existsCongr`) is built to thread.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
#assert_no_axioms FX1Poly.Typed.universeDomainMemberExtension_ofTypeLevelIrrelevance
#assert_no_axioms FX1Poly.Typed.typeLevelIrrelevance_ofUniverseDomainMemberExtension

-- Non-Π type leaves are reducible at ALL levels UNCONDITIONALLY (candidate `IsStronglyNormalizing` /
-- per-level universe candidate), discharging the type-level-irrelevance obligation for every cons-arm
-- universe-domain argument except a Π-TYPE argument — the sole remaining cons-arm gap, now isolated.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberNonPiNonUniverseArgument
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUniverseCodeArgument

-- Level-irrelevance INDUCTION over the whole reducibility derivation: every `ReducibleTypeStep` arm but
-- `piType` discharged unconditionally (redex via `headExpand` — extending the non-Π discharge to
-- redex-carrying args — neutral/universe via the leaves, congruence via the IH).  The entire type-level
-- level-irrelevance obstruction is reduced to ONE hypothesis, the `piArm` (Π-former case).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofReducibleTypeStep
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofReducibleAtLevel

-- The `piArm` CLOSES for a neutral / data-former domain: such a domain's reducible-type candidate is
-- `IsStronglyNormalizing` at EVERY level, so the domain-candidate level-mismatch dissolves and the Π type
-- rebuilds at every level (canonical codomain candidate, choice-free).  Level-irrelevance now holds
-- unconditionally for every Π type whose domain is neutral / a data former — residual gap: Π- or
-- universe-rooted domains.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberPiNeutralDomainArgument
-- First concrete all-levels witness for a DEPENDENT Π with a non-universe (type-variable / neutral) domain —
-- validates the neutral-domain piArm discharger end-to-end; the universe-domain Π remains the open fixpoint.
#assert_no_axioms FX1Poly.Typed.allLevelsReducible_piOverNeutralVariableDomain

-- SN-001: the fuel-0 universe-vacuity obstruction, pinned as committed theorems.  A universe-DOMAIN Π is
-- VACUOUSLY reducible at fuel 0 for EVERY codomain (its fuel-0 candidate is the trivial `fun _ => True`),
-- so fuel-0 reducibility carries no information and the all-levels / member-extension route (Route A)
-- cannot bootstrap past the degenerate 0↔1 base.  Formal input for the SN-002+ classifier-level pivot.
#assert_no_axioms FX1Poly.Typed.universeDomainPiVacuouslyReducibleAtZero
#assert_no_axioms FX1Poly.Typed.universeDomainPiTrivialCandidateAtZero

-- SN-002 spike: the reducibility level CAN be re-keyed to the classifier universe level `denote(LevelExpr)`
-- — `Type@e` is a reducible member at its DENOTED classifier level `denote(lsucc e)`, the `lsucc → +1`
-- alignment matching the shipped tarskiDecode discipline by definitional equality.  Setup verdict: GO;
-- the make-or-break universe-DOMAIN Π-formation case is deferred to SN-004.
#assert_no_axioms FX1Poly.Typed.universeCode_reducibleMemberAtClassifierLevel

-- SN-003: the predicative well-founded MEASURE for classifier-level reducibility.  `denote_lt_lsucc` is the
-- strict decrease at the universe-decode step; the `lmax` bounds are the non-increasing former-component
-- descents; `variableCell_reducibleTypeAtZero` is the non-degenerate base (neutral types inhabit level 0,
-- unlike the SN-001 universe-code vacuity).
#assert_no_axioms FX1Poly.Typed.denote_lt_lsucc
#assert_no_axioms FX1Poly.Typed.denote_le_lmax_left
#assert_no_axioms FX1Poly.Typed.denote_le_lmax_right
#assert_no_axioms FX1Poly.Typed.variableCell_reducibleTypeAtZero
-- The composed universe-domain-Pi measure step (#672 sub-step 3): a member of Type@e has level denote e
-- strictly below the dependent Pi's level lmax (lsucc e) levelC — the Adjedj recursion's well-founded
-- descent. Member level bound comes from ValidTyping's subjectLevel (the validity derivation), not bare
-- reducibility.
#assert_no_axioms FX1Poly.Typed.denote_lt_lmax_lsucc_left

-- SN-004 (make-or-break): the universe-DOMAIN Π former CLOSES at classifier-level semantics.  Constant
-- codomain is shipped (universeDomainNonDependentArrow); the dependent case reduces to domain
-- member-extension (piTypeOfDomainMemberExtension), supplied by the SN-003 denote-WF recursion — the fuel-0
-- wall does NOT reappear.  VERDICT: GO (Route B viable).  Concrete witness:
#assert_no_axioms FX1Poly.Typed.universeDomainPi_reducibleAllLevels

-- SN-005 (decision gate, GO locked 2026-06-02): SN strategy = classifier-level validity route PRIMARY,
-- BKS sconing independent-second, Makkai word-equality cross-check.  The certificate anchors the GO rationale
-- as a checked object — the SAME universe-domain Π former is genuinely all-levels reducible (live model,
-- SN-004) yet only VACUOUSLY fuel-0 reducible with the trivial candidate (dead model, SN-001).
#assert_no_axioms FX1Poly.Typed.lockedStrategyGoCertificate

-- SN-006 (contingency spec, fallback-only): the Adjedj derivation-indexed LogRel.  Key finding: `HasTypeDescPi`
-- is Prop-valued, so a Nat derivation-size is BLOCKED (no large elim from Prop); the fallback is Prop-motive
-- structural recursion on the derivation (same scheme as ValidTyping.fundamental, impredicativity-robust).
-- The marker is the fallback's deferred TARGET statement (= the primary SN goal), a checked Prop, no obligation.
#assert_no_axioms FX1Poly.Typed.DerivationIndexedStrongNormalizationFallback

-- Member-side leaf (dual of the type leaves): membership in a neutral / data-former classifier is
-- `IsStronglyNormalizing` (level-independent), so a one-level member extends to all positive levels — the
-- cons-arm `headMemberExtendsToAllPositive` premise for a neutral-domain former.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
#assert_no_axioms FX1Poly.Typed.headMemberExtendsToAllPositive_ofNeutralClassifier

-- ASSEMBLY: the formation-FT telescope-cons (binder) arm CLOSES for a neutral / data-former domain — the
-- member-side leaf composed with the all-positive-argument cons companion.  The binder arm that has carried
-- the lone all-level-assembly `sorry` is discharged for every non-type-polymorphic former, given only the
-- tail recursion (supplied by the FT's own IH).
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllNeutralDomain

-- ASSEMBLY: the same binder arm CLOSES for a weak-head-reducible domain — the member-side `whnfExpand` arm
-- (this iteration) composed with the all-positive-argument cons companion.  Sibling of the neutral-domain
-- lemma; chaining the two covers every former whose substituted domain weak-head-normalises to neutral/data.
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllWhnfDomain

-- The Π `piType` arm of type-level level-irrelevance, generalized from a neutral domain to ANY domain that
-- admits MEMBER-EXTENSION: the domain-candidate level-mismatch dissolves under domain member-extension
-- (rebuild with the domain's fixed canonical member-predicate).  The type leg of the mutual type+member
-- irrelevance — residual obstruction now purely member-side (member-extension for Π/universe domains).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension

-- The MEMBER leg of the Π `piType` arm: a positive-level Π member extends to all positive levels via the
-- application chain (domain member-ext → `application` → codomain member-ext), run entirely at positive
-- levels (the degenerate fuel-0 base untouched).  With the type leg, the full `piType` arm of mutual
-- type+member level-irrelevance is reduced to domain+codomain member-extension.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtension

-- The TIGHT primary form: the domain/codomain member-extension premises need only hold from POSITIVE source
-- levels (the proof never invokes them at the degenerate fuel-0), and the all-source-level
-- `piTypeMemberExtension` is now the trivial weakening that delegates to it.  This tightening is what lets the
-- member-extension family ASSEMBLE over nested non-dependent arrows (a sub-arrow supplies only positive-source
-- member-extension, which now suffices to feed the enclosing arrow).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtensionPositive

-- The member-side `whnfExpand` arm of mutual type+member level-irrelevance: member-extension lifts backward
-- across one weak-head step of the classifier (peel the member to the shared-candidate contractum, strengthen
-- by the contractum's member-extension, head-expand back).  With `ofNeutralClassifier` this completes the
-- member-side arm family for the non-Π / non-universe cases — the structurally-recursive part.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand

-- The CONVERSION arm of the member-extension family: member-extension transports across an arbitrary kernel
-- `Conv` of the classifier (target reducible at all positive levels), via the single-level `castAlongConv` /
-- `ReducibleTypeAt.convTransfer`.  More flexible than the single-step whnfExpand arm; the conv arm of the
-- strengthened formation-FT motive.  `castAlongConvOfAllLevels` is the all-levels-target convenience form.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.castAlongConv
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.castAlongConvOfAllLevels

-- CR1 for the all-positive member family: every all-positive member is strongly normalizing (read at the
-- bottom positive fuel via `atLevel 0`, then single-level CR1).  The SN bridge the strong-normalization /
-- canonicity corollaries consume once a binder/telescope arm strengthens a one-level member to all-positive.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.stronglyNormalizing

-- Member-extension for a NON-DEPENDENT arrow `A → B`: the dependent `piTypeMemberExtension`'s argument-indexed
-- codomain hypotheses collapse to the CONSTANT base-codomain facts via weaken-cancellation
-- (`subst0 (weaken B) arg = B`).  The member-side twin of `formerChildrenReducibleNonDependentAtAll`; the
-- premise-(2) recursion step for the simply-typed fragment (no dependent-Π codomain growth).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.nonDependentArrow

-- TYPE-side twin: all-levels type reducibility for a non-dependent arrow `A → B`.  The dependent
-- `piTypeOfDomainMemberExtension`'s argument-indexed codomain premise collapses to the constant base-codomain
-- all-levels fact via weaken-cancellation.  With the member-side twin this is the full non-dependent-arrow
-- reducibility pair — the simply-typed step where the dependent-Π codomain-growth obstruction is absent.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.nonDependentArrow

-- TYPE-side crack past the universe-domain wall: a non-dependent arrow is all-levels reducible from domain +
-- codomain all-levels reducibility ALONE — NO domain member-extension (the codomain candidate is constant in
-- the argument when the codomain is `weaken`-ed, so the argument membership is never consumed).  This reaches
-- a non-dependent arrow over a UNIVERSE domain (`Type@e → B`), which the member-extension-requiring
-- `nonDependentArrow` cannot — only the dependent and member legs of a universe domain stay open.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.universeDomainNonDependentArrow

-- ASSEMBLY CAPSTONE: the universe member-extension principle (open in general at the fuel-0 universe wall) is
-- proved UNCONDITIONALLY for the FIRST-ORDER simply-typed fragment — types built from neutral/data leaves and
-- non-dependent arrows with neutral DOMAINS (curried first-order functions over base types).  This is the
-- classic Tait reducibility result realized on FX's stratified Tarski substrate: the first non-trivial
-- fragment where the reducibility machinery closes end-to-end, assembling the neutral-leaf, non-dependent-
-- arrow (type + positive-source member), and ofNeutralClassifier arms by induction on a 2-ctor witness.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.nonDependentArrowPositive
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.reducibleAndMemberExtension

-- Smart constructors making the first-order fragment CONSTRUCTIBLE for concrete types (via the
-- canonical-form weak-head-normality lemmas), plus the end-to-end corollary that a variable type is
-- reducible-at-all-levels and member-extending — a closed demonstration that the Tait machinery applies
-- concretely, not merely to an abstract fragment.
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofVariable
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofSigmaTyCode
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.arrowOfVariableDomain
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.variableReducibleAndMemberExtension

-- The general neutral-leaf principle: every neutral type (variable / neutral application / projection /
-- stuck eliminator) is first-order simply-typed, lifting the leaf class from bare variables to the full
-- Tait neutral family.  Backed by the Core `IsNeutral.rootGenerator_ne_piTyCode` / `…_ne_universeCode`
-- root-disequality lemmas (swept by `#audit_namespace FX1Poly.Core`).  The end-to-end corollary exercises
-- reducibility + member-extension on a NON-variable neutral type (a type-family application `f a`).
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofNeutral
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofNeutralApplication
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.neutralApplicationReducibleAndMemberExtension
-- NO CLOSED NEUTRAL (closed-canonical-forms precursor for canonicity SN-047/049 + consistency SN-050).
-- IsNeutral.elimEmptyScope: a neutral term forces an inhabitant of Fin scope — every arm but `var` recurses on a
-- same-scope neutral premise, so threading the (Fin scope → False) emptiness witness down the spine refutes the
-- head variable; stated scope-polymorphically to keep the induction motive index-clean. IsNeutral.noClosed:
-- specialize to scope 0 (Fin 0 empty via elim0) — no RawTerm 0 is neutral, so a CLOSED normal form is an
-- introduction form, never a stuck eliminator. Pure structural induction over the 12-arm IsNeutral; #672-free.
#assert_no_axioms FX1Poly.Core.IsNeutral.elimEmptyScope
#assert_no_axioms FX1Poly.Core.IsNeutral.noClosed
-- DATA-CANONICITY FOUNDATION: CanonicalFormsPredicate isValue = SN ∧ (neutral ∨ reduces-to-value), the sharper
-- canonicity-bearing candidate (vs the bare SN candidate the model gives data leaves). Generic over the value
-- predicate (bool→true/false, Empty→empty pred, nat→zero/succ). CR1 (stronglyNormalizing) = first conjunct; CR3
-- (neutralExpansion) = Acc.intro over reducts' SN + Or.inl (shipped SN-candidate CR3 pattern); containsVariable
-- via vacuous CR3. CR2 DEFERRED (needs IsNeutral-closed-under-Step + per-term confluence) — so this is the
-- honest 2-of-3 foundation, NOT yet a full IsReducibilityCandidate. #672-free. Toward SN-063/047.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.stronglyNormalizing
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.neutralExpansion
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.containsVariable
-- The full CR3 neutral leaf (generalizes containsVariable past the vacuous variable case): a STRONGLY-
-- NORMALIZING NEUTRAL term is a member of every canonical-forms candidate, by well-founded recursion on its SN
-- accessibility (reducts stay neutral via closedUnderStep, are SN-smaller, hence members by IH; neutralExpansion
-- lifts). The reducibility leaf any neutral-eliminator (stuck app/fst/boolElim over a neutral head) member
-- argument consumes; isValue-agnostic.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral
-- CR2 NOW DISCHARGED (was deferred last tick): closedUnderStep — a member's reduct stays a member, the disjunct
-- preserved by neutralClosedUnderStep (neutral case) or per-term confluence + value rigidity (reduces-to-value
-- case: value is an NF, confluence_of_localJoin_and_accessible joins the reduct with the value-chain,
-- eq_of_noStep collapses the apex onto the value). isReducibilityCandidate = the FULL CR1+CR2+CR3 bundle: the
-- canonical-forms predicate IS a Girard reducibility candidate given the two data facts (IsNeutral closed under
-- Step + data values are normal). Per-term confluence only (no global-confluence assumption). #672-free; the
-- honest unconditional foundation for data canonicity (SN-063 bool reducibility / SN-047 bool canonicity).
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.closedUnderStep
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.isReducibilityCandidate
-- NEUTRAL OBLIGATION NOW DISCHARGED: the `neutralClosedUnderStep` argument is exactly the unconditional
-- `IsNeutral.closedUnderStep` (NeutralStepClosure.lean), so a data type need only supply that its values are
-- normal forms (trivial for constructors) to obtain its reducibility candidate.
#assert_no_axioms FX1Poly.Core.CanonicalFormsPredicate.isReducibilityCandidateOfValuesNormal
-- FIRST CONCRETE DATA CANDIDATE — bool (SN-063 data core), unconditional + zero-axiom: boolIsValue := the
-- true/false constructor cells; boolIsValue values are structural normal forms (isStepNormalFormBool computes
-- to true); the candidate is isReducibilityCandidateOfValuesNormal at boolIsValue (CR1+CR2+CR3, neutral half
-- via IsNeutral.closedUnderStep); both canonical inhabitants are members (Acc.intro over no_step_from_bool*).
#assert_no_axioms FX1Poly.Core.boolIsValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.boolCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.boolTrueCell_isMember
#assert_no_axioms FX1Poly.Core.boolFalseCell_isMember
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
-- ELIMINATION canonicity (#672-free, SN-063 path): boolElim on a CANONICAL scrutinee COMPUTES to a branch.
-- StepStar.boolElimScrutinee = the scrutinee-position chain congruence (generic StepStar.congAt + Step.cong
-- (StepChildren.here ...) at the head of the 3-child spine). boolElimCanonicalScrutineeReducesToBranch = the
-- headline: the scrutinee reduces to true/false (boolClosedReducesToTrueOrFalse), the congruence carries that
-- under the boolElim, and the matching iota (iotaBoolTrue/iotaBoolFalse) selects the then/else branch
-- (StepStar.transLast). The elimination analog of closed-bool canonicity; no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.boolElimScrutinee
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
-- Sigma PROJECTION canonicity (#672-free, SN-058 path): fst/snd on a CANONICAL pair scrutinee PROJECT to the
-- components. StepStar.fstScrutinee/sndScrutinee = the unary scrutinee-position chain congruences (generic
-- StepStar.congAt + Step.cong (StepChildren.here ...) at the sole child). pairCanonicalScrutineeProjectsTo-
-- Components = the headline: the scrutinee reduces to pairCell first second (pairClosedReducesToValue), the
-- projection congruences carry that under fst/snd, and the matching iota (iotaFstPair/iotaSndPair) projects out
-- the components. The Sigma-projection analog of boolElim branch-selection; no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.fstScrutinee
#assert_no_axioms FX1Poly.Core.StepStar.sndScrutinee
#assert_no_axioms FX1Poly.Core.pairCanonicalScrutineeProjectsToComponents
-- IDENTITY-ELIMINATOR canonicity (#672-free, SN-068/069 path): idJ/idStrictRec on a CANONICAL refl WITNESS
-- COMPUTE to the base case. StepStar.idJWitness/idStrictRecWitness = the witness-position (second-child) chain
-- congruences (generic StepStar.congAt + Step.cong (StepChildren.there base (here ...)) reaching past the base
-- case into the witness child; headShift := 0 pins the [0,0]-spine). idJ/idStrictRecCanonicalWitnessReducesToBase
-- = the headline: the witness reduces to a refl (reflClosedReducesToValue), the witness congruence carries that
-- under the eliminator, and the matching iota (iotaIdJRefl/iotaIdStrictRecRefl) selects the base case. The last
-- non-growing eliminators (ι selects base from the witness); no fundamental theorem used.
#assert_no_axioms FX1Poly.Core.StepStar.idJWitness
#assert_no_axioms FX1Poly.Core.StepStar.idStrictRecWitness
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
-- unit + identity(refl) canonicity via sconing: the last two data types join the generic witness (SN-049 Unit,
-- SN-059/067 identity introduction), completing data-canonicity-via-sconing coverage to ALL data axes. Thin
-- isValue specializations (isUnitValue / isReflValue); #672-free extraction, conditional only on the per-type
-- fundamental (NOT typed SN), so genuinely unblocked.
#assert_no_axioms FX1Poly.Core.unitCanonicityViaSconing
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
-- RECURSIVE data candidate — Nat (SN-060/062): IsNatValue is the inductive numeral predicate; numerals are
-- structural normal forms by induction (a natSucc cell is normal iff its predecessor is); the candidate is
-- isReducibilityCandidateOfValuesNormal at IsNatValue; every numeral is a member (memberOfValue); a closed
-- member reduces to a numeral (closedReducesToValue). Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isNatValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.natCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.isNatValue_isMember
#assert_no_axioms FX1Poly.Core.natClosedReducesToValue
-- BINARY data candidate — Σ pairs (SN-057/059): isPairValue := a pairCell with both components normal; a
-- pair of normals is a structural normal form (the two-child spine recursion); the candidate is
-- isReducibilityCandidateOfValuesNormal at isPairValue; a normal pair is a member (memberOfValue); a closed
-- member reduces to a pair (closedReducesToValue). Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isPairValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.pairCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.pairValue_isMember
#assert_no_axioms FX1Poly.Core.pairClosedReducesToValue
-- NULLARY single-constructor data candidate — Unit, the last SN-049 data type (Sum = Either, already
-- shipped). isUnitValue := (term = unitCell); the unit cell is a structural normal form (rfl); the candidate
-- is isReducibilityCandidateOfValuesNormal at isUnitValue; the unit cell is a member (Acc over
-- no_step_from_unit); a closed member reduces to a value and, by unit's uniqueness, to THE unit cell.
-- Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isUnitValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.unitCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.unitCell_isMember
#assert_no_axioms FX1Poly.Core.unitClosedReducesToValue
#assert_no_axioms FX1Poly.Core.unitClosedReducesToUnitCell
-- MODAL layer data candidate — modIntro (SN-073 data core): the modal box is a single unary constructor
-- (option-some shape); isModIntroValue := modIntro of a normal payload; value-normality is the one-child
-- spine; candidate via isReducibilityCandidateOfValuesNormal; a normal box is a member (memberOfValue); a
-- closed member reduces to a modIntro. Over β+ι Step (raw modal η is a separate relation). #672-free.
#assert_no_axioms FX1Poly.Core.isModIntroValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.modIntroCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.modIntroValue_isMember
#assert_no_axioms FX1Poly.Core.modIntroClosedReducesToValue
-- EMPTY type / CONSISTENCY core (SN-050/053): emptyIsValue := False (no value constructors); the candidate is
-- the SN neutral terms (isReducibilityCandidateOfValuesNormal with vacuous value-normality); a CLOSED member
-- is impossible (closedReducesToValue yields a False-satisfying value). The #672-free structural heart of "no
-- closed proof of Empty"; only the membership half (closed well-typed Empty term is a member) awaits the FT.
#assert_no_axioms FX1Poly.Core.emptyCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.emptyHasNoClosedMember
-- HEAD-EXPANSION-CLOSED empty Tait candidate (the candidate-bridge empty candidate): SN ∧ every reachable
-- normal form is neutral. Unlike CanonicalFormsPredicate emptyIsValue (members must be neutral THEMSELVES),
-- this is head-expansion-closed (a β-redex inherits membership from its contractum, via per-term confluence) —
-- so it serves as a Π codomain candidate across the whole fundamental theorem (a λ into Empty is reducible).
-- It is a reducibility candidate (CR1/CR2/CR3) and has no closed member (a closed reachable normal form would
-- be neutral, but closed neutrals don't exist) — the consistency core for the candidate-bridge model.
#assert_no_axioms FX1Poly.Core.emptyTaitCandidate.noClosedMember
#assert_no_axioms FX1Poly.Core.emptyTaitCandidate_isReducibilityCandidate
#assert_no_axioms FX1Poly.Core.emptyTaitCandidate_headExpansionClosed
#assert_no_axioms FX1Poly.Core.emptyTaitCandidate_memberWeakHeadExpansion
-- The GENERIC head-expansion-closed data Tait candidate (dataTaitCandidate isValue), generalizing
-- emptyTaitCandidate from the empty value set to ANY data value predicate ("SN AND every reachable normal
-- form is a value or neutral").  It is a reducibility candidate (CR1/CR2/CR3) and head-expansion-closed
-- (so it serves as a Π codomain candidate across the fundamental theorem) for every isValue; a CLOSED
-- member reduces to a VALUE (closedReducesToValue) — the candidate-bridge-ready data-canonicity payload
-- each data type code (bool/nat/…) instantiates exactly as emptyTypeCell instantiates emptyTaitCandidate.
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.stronglyNormalizing
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.closedUnderStep
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.neutralExpansion
#assert_no_axioms FX1Poly.Core.dataTaitCandidate_isReducibilityCandidate
#assert_no_axioms FX1Poly.Core.dataTaitCandidate_headExpansionClosed
#assert_no_axioms FX1Poly.Core.dataTaitCandidate_memberWeakHeadExpansion
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.closedReducesToValue
#assert_no_axioms FX1Poly.Core.dataTaitCandidate.memberOfValue
#assert_no_axioms FX1Poly.Core.dataTaitCandidate_false_iff_emptyTaitCandidate
-- The bool instance (the SN-047 payload shape): a closed member of the bool Tait candidate reduces to
-- boolTrue or boolFalse — closed bool canonicity, candidate-bridge-ready.
#assert_no_axioms FX1Poly.Core.boolTaitCandidate_isReducibilityCandidate
#assert_no_axioms FX1Poly.Core.boolTaitCandidate_headExpansionClosed
#assert_no_axioms FX1Poly.Core.closedBoolTaitReducesToValue
-- RICHEST data candidate — List (SN-064): IsListValue inductive combines nullary nil + binary-recursive cons
-- (head normal like pair, tail recursive like Nat); list values are normal forms by induction; the candidate
-- is isReducibilityCandidateOfValuesNormal at IsListValue; every list value is a member (memberOfValue); a
-- closed member reduces to a list constructor (closedReducesToValue). Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isListValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.listCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.isListValue_isMember
#assert_no_axioms FX1Poly.Core.listClosedReducesToValue
-- OPTION data candidate (SN-065): isOptionValue := none | some payload (payload normal) — nullary + unary,
-- no recursion; option values are normal forms; the candidate is isReducibilityCandidateOfValuesNormal at
-- isOptionValue; every option value is a member (memberOfValue); a closed member reduces to none/some.
#assert_no_axioms FX1Poly.Core.isOptionValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.optionCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.isOptionValue_isMember
#assert_no_axioms FX1Poly.Core.optionClosedReducesToValue
-- EITHER (sum) data candidate (SN-066): isEitherValue := inl payload | inr payload (payload normal) — two
-- unary tagged arms; either values are normal forms; the candidate is isReducibilityCandidateOfValuesNormal
-- at isEitherValue; every either value is a member (memberOfValue); a closed member reduces to inl/inr.
-- Completes the tagged-union extraction family (option + either).
#assert_no_axioms FX1Poly.Core.isEitherValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.eitherCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.isEitherValue_isMember
#assert_no_axioms FX1Poly.Core.eitherClosedReducesToValue
-- IDENTITY refl data candidate (SN-067): isReflValue := refl witness (witness normal) — the single unary
-- introduction of the identity type; refl values are normal forms; the candidate is
-- isReducibilityCandidateOfValuesNormal at isReflValue; every refl value is a member (memberOfValue); a closed
-- member reduces to a refl. Completes the data-introduction extraction family.
#assert_no_axioms FX1Poly.Core.isReflValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.reflCanonicalFormsCandidate
#assert_no_axioms FX1Poly.Core.isReflValue_isMember
#assert_no_axioms FX1Poly.Core.reflClosedReducesToValue

-- FULL HIGHER-ORDER simply-typed fragment: the certified Tait fragment extended from first-order to the whole
-- simply-typed lambda calculus over neutral/data base types — arrows closed on BOTH domain and codomain (an
-- arrow domain `(A → B) → C` recurses, NOT blocked).  The arrow-domain recursion is unblocked precisely by the
-- member-extension-free type-side arrow `nonDependentArrowOfAllLevelsDomain` (the IH supplies only
-- positive-source member-extension, which the member-side `nonDependentArrowPositive` accepts).  Corrects the
-- first-order file's docstring claim that higher-order domains hit the fuel-0 wall — only UNIVERSE domains do.
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.reducibleAndMemberExtension
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.ofFirstOrder
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.ofNeutral
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.higherOrderArrow
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.higherOrderArrowReducibleAndMemberExtension
-- #672 STLC discharge (operational form): IsSimplyTyped.positiveMemberExtension — for ANY simply-typed type,
-- a member at one positive level extends to all positive levels, the exact operational shape of
-- HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes (#672) restricted to the predicative STLC
-- fragment. This is the simply-typed dispatch arm of the eventual #672 assembly, discharged in full generality
-- (no SN / all-levels hypothesis — both are CONCLUSIONS of simply-typedness). Residual = universe-domain +
-- dependent-codomain (the impredicative / WHN-under-subst core).
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.positiveMemberExtension

-- TERM-level reducibility of the simply-typed fragment: the term-formation rules (abstraction / application)
-- made concrete + the SN payoff on a REDUCING term.  `lambdaNeutralArrow` / `applicationNonDependentArrow`
-- are the candidate-free piIntro/piElim specializations; `polymorphicIdentity` is `λx.x : A→A`; and
-- `polymorphicIdentityRedexStronglyNormalizing` proves the β-redex `(λx.x) y` strongly normalizes — strong
-- normalization of an actually-reducing term (CR1 on a non-normal form), the genuine Tait payoff.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.lambdaNeutralArrow
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.applicationNonDependentArrow
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.polymorphicIdentity
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityRedexStronglyNormalizing

-- HIGHER-ORDER term reducibility: `lambdaNeutralDomain` generalizes the abstraction rule from a neutral
-- codomain to ANY reducible codomain (candidate = the codomain's own member-predicate, so the body condition
-- is "body lands as a member" — the form functions-returning-functions and the FT λ arm need).
-- `constantIdentity` demonstrates it on an ARROW codomain: `λx.(λy.y) : A → (B → B)`.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.lambdaNeutralDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.constantIdentity

-- The K combinator `λx.λy.x : A → (B → A)` — the hardest concrete simply-typed term, where the inner body
-- CAPTURES the outer bound variable.  `subst0_lamCellVarOne_eq_lamWeaken` is the binder-crossing substitution
-- computation behind it (`subst0 (λy.var 1) arg = λy.weaken arg`), proven fold-`rfl`-free (no propext /
-- Quot.sound) with a Nat-arithmetic Fin bound (no omega).
#assert_no_axioms FX1Poly.Typed.subst0_lamCellVarOne_eq_lamWeaken
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.kCombinator

-- Abstraction rule-family completion: `lambdaLeafDomain` is the maximally-general form — a LEAF domain
-- (weak-head-normal, non-Π, non-universe: data formers, not only neutrals) + any reducible codomain — matching
-- the `IsSimplyTyped.leaf` class and subsuming `lambdaNeutralArrow` / `lambdaNeutralDomain`.  `sigmaIdentity`
-- (`λx.x : (Σ A. B) → (Σ A. B)`) is the identity over a Σ-code DATA-FORMER base type, reachable only via it.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.lambdaLeafDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaIdentity

-- The FT crux that sidesteps the universe wall: a type-VARIABLE domain (a context binding `α : Type@e`) is a
-- reducible TYPE under a reducible environment, read off the environment via the universe-membership decode
-- (`universeMembership_iff`).  The wall blocks TYPE abstraction (`λA:Type.…`), not term abstraction over type
-- variables — so the simply-typed fundamental theorem is NOT wall-blocked, only awaiting the judgment+env
-- assembly.
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.typeVariableReducible

-- The TYPE-LEVEL half of the simply-typed fundamental theorem.  `IsSimplyTypedTypeExpr` classifies the pure
-- STLC type expressions over a context (type variable bound at a universe, or non-dependent arrow of such), and
-- `reducibleAtAllLevels` proves every one substitutes to an all-levels reducible type under an all-levels
-- reducible closing environment.  The type-variable arm reads reducibility off the environment (sidestepping
-- the universe wall via `typeVariableReducible`); the arrow arm is `nonDependentArrowOfAllLevelsDomain` on the
-- induction hypotheses.  This is the domain/codomain reducibility the term FT's λ-introduction arm consumes.
#assert_no_axioms FX1Poly.Typed.IsSimplyTypedTypeExpr
#assert_no_axioms FX1Poly.Typed.IsSimplyTypedTypeExpr.reducibleAtAllLevels

-- The simply-typed lambda arm of the LEVEL-FREE term fundamental theorem: the non-dependent specialization
-- of the dependent `abstractionUnderSubst`, pre-cancelling the codomain weakening
-- (`subst0 (subst (lift σ) (weaken codomainBase)) arg = subst σ codomainBase`).  The simply-typed term FT
-- assembles over the level-free layer (not the stratified one): level-free `ReducibleEnv.cons` extends from
-- a single `IsReducibleMember`, so the lam binder needs no all-levels argument — the stratified universe wall
-- is structurally absent for a non-dependent codomain.
#assert_no_axioms FX1Poly.Typed.IsReducibleMember.abstractionNonDependentUnderSubst

-- The domain supplier for the level-free simply-typed term FT: the non-dependent arrow type builder
-- (`ReducibleType.nonDependentArrow`, level-free twin of the stratified `IsReducibleTypeAtAllLevels.nonDependentArrow`),
-- the directly-reducible type-expression class (`IsReducibleTypeExprLF` = universe codes + non-dependent
-- arrows; no type-variable leaves, which decode only to SN level-free), and the supplier proper
-- (`reducibleUnderSubst`) — every such expression substitutes to a directly-reducible level-free type, the
-- domain reducibility the lam arm consumes.
#assert_no_axioms FX1Poly.Typed.ReducibleType.nonDependentArrow
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF.reducibleUnderSubst

-- THE LEVEL-FREE SIMPLY-TYPED TERM FUNDAMENTAL THEOREM (#502): the well-scoped term judgment
-- `SimplyTypedTermLF` (var/app/lam) + `reducibleUnderSubst` (every simply-typed term, closed by a reducible
-- substitution, is a reducible member of its type — var→lookupReducible, app→applicationUnderSubst,
-- lam→abstractionNonDependentUnderSubst fed reducibleUnderSubst) + the strong-normalization corollaries.
-- `stronglyNormalizingClosed` is the tangible payoff: every closed simply-typed term strongly normalizes
-- (SN-for-well-typed on the wall-free simply-typed fragment).
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reducibleUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reducibleClosed
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingClosed

-- CHURCH-ROSSER + NORMAL-FORM UNIQUENESS for simply-typed terms: the SN result fed the per-term Newman bridge
-- (`confluence_of_localJoin_and_accessible`) gives confluence (`reductsJoinUnderSubst`), and `eq_of_noStep`
-- gives normal-form uniqueness (`normalFormUnique{UnderSubst,Closed}`) — the foundation for deciding conversion
-- on the simply-typed fragment.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reductsJoinUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormUniqueUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormUniqueClosed

-- INHABITATION CORPUS for the simply-typed term FT (the fundamental theorem is non-vacuous): concrete
-- `SimplyTypedTermLF` derivations of the polymorphic identity at a universe base type and at an arrow type,
-- with their strong normalization as fundamental-theorem corollaries.  Simply-typed analogue of TY-honesty.
#assert_no_axioms FX1Poly.Typed.identityIsSimplyTyped
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

-- The ROOT-REDEX DISPATCH: `hasRootStepSource source = true → ∃ target, Step source target`, assembling all
-- 11 per-redex bricks via a generator case-split mirroring `hasRootStepSource`'s definition.  The missing
-- root ingredient for weak normalization (the Acc descent's step-extraction at a non-normal term).
#assert_no_axioms FX1Poly.Core.hasRootStepSource_exists_step

-- The COMPUTABLE root-redex firing FUNCTION + its soundness: `fireRootRedex generator payload children`
-- returns `some reduct` exactly on a root redex, exhibiting the reduct as a concrete RawTerm (vs the
-- existential `hasRootStepSource_exists_step`).  The reduct-supplier the weak-normalization normalizer
-- FUNCTION (#261/#480) needs to make `decidableOfNormalForms_of_isStronglyNormalizing` parameter-free.
-- Propext-clean over the 194-ctor table via DecidableEq dite-chains + ▸-casts + full spine destructure.
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
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_eq_none_iff_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.not_isStepNormalForm_imp_reduceOnce_isSome

-- THE NORMALIZER FUNCTION + its correctness, and the parameter-free SN-fragment decidable Conv it unlocks.
-- normalize iterates reduceOnce along Acc StepSuccessor (Acc.rec — the descent shrinks the accessibility
-- proof, not the term); normalize_reducesTo / normalize_isStepNormalForm are its soundness/normality.
-- Conv.decidableOfStronglyNormalizing: two SN terms → Decidable (Conv ..), no NF witnesses / Normalizer /
-- global confluence.  The culmination of the WN grind (#503) — raw redex detection to a real decider.
#assert_no_axioms FX1Poly.Core.RawTerm.normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_reducesTo
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_isStepNormalForm
#assert_no_axioms FX1Poly.Core.Conv.decidableOfStronglyNormalizing
-- Conv.iff_normalize_eq_of_isStronglyNormalizing: the SEMANTIC NbE soundness+completeness iff — two SN terms
-- convert IFF RawTerm.normalize maps them to the SAME term (the explicit biconditional decidableOfStronglyNorm-
-- alizing is decidable_of_iff over). Sharper than iff_normalForms_eq (NFs as opaque args): RHS is a literal
-- RawTerm equality via the actual normalizer.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalize_eq_of_isStronglyNormalizing

-- NORMALIZER METATHEORY: fixed-point-at-NF, idempotence, term↔NF conversion, and the headline
-- normalize_eq_iff_conv (two terms convert iff their normal forms coincide — the normal form is a complete
-- conversion invariant on the SN fragment, the explicit biconditional behind decidableOfStronglyNormalizing).
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_eq_self_of_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_idempotent
#assert_no_axioms FX1Poly.Core.RawTerm.conv_normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_eq_iff_conv

-- DECIDABLE CONV ON THE SIMPLY-TYPED FRAGMENT WITH SN DISCHARGED.  Composing the normalizer's
-- decidableOfStronglyNormalizing with the simply-typed fundamental theorem's stronglyNormalizing* — typing
-- alone decides convertibility (no SN hypothesis), joining the FT (#502) and WN-normalizer (#503) lines.
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedUnderSubst
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedClosed

-- SN REFLECTED BY SUBSTITUTION: SN of `subst σ term` ⇒ SN of bare `term` (Acc reflected along `subst σ` via
-- Step.subst + Subrelation.accessible ∘ InvImage.accessible).  This pulls the FT's SN-of-substituted back to
-- SN-of-bare, removing the closing-substitution wart: decidableOfSimplyTypedBareClosed decides conversion of
-- the BARE closed terms themselves — the cleanest "simply-typed fragment has decidable conversion".
#assert_no_axioms FX1Poly.Core.StepStar.stronglyNormalizing_of_subst
#assert_no_axioms FX1Poly.Typed.emptyClosingSubst
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedBareClosed

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
-- WfContextDefensibleKernel + wfContextDefensibleKernel (#484): the SN-043 WIDENING of the floor from the
-- simply-typed fragment to EVERY well-formed context. SN proven (stronglyNormalizingOfWfContextDesc) + Conv
-- decidable (decidableOfWellTypedInWfContextDesc) with the WF presupposition alone, NO SN and NO SR hypothesis
-- (the milestone-ledger correction: SR is not a decidability ingredient; the joint canonicity apex stays open).
#assert_no_axioms FX1Poly.Typed.WfContextDefensibleKernel
#assert_no_axioms FX1Poly.Typed.wfContextDefensibleKernel

-- CANONICAL NORMAL FORM for closed simply-typed terms — the NORMALIZE companion to the bare-closed DECIDE.
-- stronglyNormalizingBare: bare SN (the sole use site of stronglyNormalizing_of_subst); normalForm: the
-- computable RawTerm 0; conv_normalForm / normalForm_isStepNormalForm: term ↝* its NF and NF is normal;
-- normalForm_eq_self_of_isStepNormalForm: no spurious rewriting on a normal input; conv_iff_normalForm_eq:
-- two terms convert IFF their NFs coincide (the canonical NF is a complete conversion invariant — the
-- explicit characterization behind decidableOfSimplyTypedBareClosed).
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingBare
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.conv_normalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_eq_self_of_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.conv_iff_normalForm_eq

-- REDUCER SMOKE CORPUS — the WN-grind reducer COMPUTES on concrete closed terms (each `by rfl`, no decide).
-- Demonstrates non-vacuity of reduceOnce / fireRootRedex / isStepNormalFormBool: β fires with the right
-- reduct (identity + binder-ignoring bodies), the reducer halts on normal forms, a two-step normalization
-- trace reaches `unit`, the detector agrees, and the root engine fires directly.  The 8 theorem gates
-- transitively certify the 5 fixture defs are axiom-free too.
#assert_no_axioms FX1Poly.Typed.reduceOnce_betaIdentity_fires
#assert_no_axioms FX1Poly.Typed.reduceOnce_betaConstant_fires
#assert_no_axioms FX1Poly.Typed.reduceOnce_identityLambda_halts
#assert_no_axioms FX1Poly.Typed.reduceOnce_unit_halts
#assert_no_axioms FX1Poly.Typed.reduceOnce_nestedRedex_fires
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_betaRedex_false
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_identityLambda_true
#assert_no_axioms FX1Poly.Typed.fireRootRedex_betaIdentity_fires

-- SIMPLY-TYPED GENERATION (INVERSION) LEMMAS — the "extract the premises" foundation of subject reduction.
-- SimplyTypedTermLF has no conv arm, so inversions conclude EQUALITIES: a variable's type IS its lookup, an
-- application's type IS the function's arrow codomain, a lambda's type IS a Π-code over a weakened codomain.
-- Proven by the cell-index inversion recipe (generalize subject + thread Eq + headGenerator/noConfusion +
-- injection past the mkGen/childCons index-eqs).  SR-β consumes inversionApplication then inversionLambda.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionVariable
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionApplication
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionLambda

-- REDUCIBLE TYPE-EXPR CLOSURE under renaming and substitution — the SR arc's type-side substrate.  The
-- lam rule of SimplyTypedTermLF carries IsReducibleTypeExprLF premises on domain/codomain; the (downstream)
-- renaming/substitution-preservation lemmas transport those premises across the action via these closure
-- lemmas (universe-code leaves are action-invariant; arrows thread *_lift_weaken_commute through the codomain).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF.subst
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF.rename

-- SIMPLY-TYPED RENAMING PRESERVATION — the SR arc's term-side substrate.  SimplyTypedTermLF survives any
-- context-respecting renaming (var/app/lam, no conv arm); the lam arm transports its IsReducibleTypeExprLF
-- premises via IsReducibleTypeExprLF.rename and lifts the body IH via renameContextCondition_cons.
-- weakenUnderBinding is the one-fresh-binder corollary the substitution lemma's binder-lift consumes.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.weakenUnderBinding

-- SIMPLY-TYPED SUBSTITUTION PRESERVATION — the SR arc's β-engine.  SimplyTypedTermLF survives any well-typed
-- substitution; the lam arm transports IsReducibleTypeExprLF premises via .subst and lifts the body IH with
-- the 0/succ split (var at 0, weakenUnderBinding at k+1).  substituteUnderBinding is the subst0 corollary
-- β-reduction cites: (λ.body) arg ↝ body[arg] preserves type.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.substRespectingContext
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.substituteUnderBinding

-- SUBJECT REDUCTION + TYPE-PRESERVING NORMALIZATION — the SR arc CULMINATION.  Reduction preserves typing
-- (single-step inverts Step per shape via StepInversion: var refuted, app = β/cong-fn/cong-arg with the
-- β-engine substituteUnderBinding + weaken_subst_singleton, lam = cong-body); multi-step iterates it; and
-- normalForm_typed (the gold payoff) threads the normalizer's reduction chain through SR* so the canonical
-- normal form of a closed simply-typed term is itself simply-typed at the same type.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.subjectReduction
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.subjectReductionStar
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_typed

-- CANONICITY (PROGRESS) — the classic STLC capstone, completing the simply-typed metatheory.  Closed normal
-- forms are lambdas: a LnNeutral term (var-headed app spine) is impossible at scope 0, the canonicalSplit
-- inducts on typing (β-redex case killed by Step.beta + blocks_step, child-normality via cong), and
-- normalFormIsLambda composes it with type-preserving normalization — every closed simply-typed term
-- normalizes to a lambda.
#assert_no_axioms FX1Poly.Typed.lnNeutral_scopeZero_absurd
#assert_no_axioms FX1Poly.Typed.isStepNormalForm_appCell_function
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.canonicalSplit
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.closedNormalIsLambda
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormIsLambda

-- INHABITATION / CONSISTENCY — the final theorem of the simply-typed metatheory.  Every closed simply-typed
-- term has an arrow type (canonicity says its NF is a lambda, type-preserving normalization keeps the type,
-- lambda inversion makes the type an arrow); hence universe codes are uninhabited by closed terms (arrow vs
-- universe-code head generators differ) — the fragment's consistency.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.closedTermHasArrowType
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.noClosedTermAtUniverseCode

-- CONV EQUIVALENCE PACKAGE (#421) — convertibility is a DECIDABLE EQUIVALENCE RELATION on closed simply-
-- typed terms.  Raw Conv.refl/sym are unconditional but Conv.trans needs Church-Rosser for the chains
-- leaving the shared middle term, which at the raw layer requires that middle term to be strongly
-- normalizing (raw Step is NOT globally SN).  On the simply-typed fragment the fundamental theorem supplies
-- exactly that SN, so conv_trans (= trans_of_middle_accessible ∘ stronglyNormalizingBare) holds; bundled
-- with refl/sym it gives convertsTo_equivalence, and decidableOfSimplyTypedBareClosed makes it decidable.
-- This is the honest locus where the Conv equivalence structure becomes provable — the unconditional raw
-- Conv.trans remains genuinely unavailable.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.conv_trans
#assert_no_axioms FX1Poly.Typed.SimplyTypedClosedTerm.convertsTo_equivalence
#assert_no_axioms FX1Poly.Typed.SimplyTypedClosedTerm.decidableConvertsTo

-- The PRODUCTIVE MIRROR of `isStepNormalForm_blocks_step`: a non-normal term genuinely reduces, with the
-- reduct exhibited.  Mutual term + child-spine halves.  Combines the root-redex dispatch (root conjunct) with
-- a structural recursion into the child spine (`Step.cong` / `StepChildren.here` / `StepChildren.there`).
-- The step-extraction the `Acc StepSuccessor` weak-normalization descent calls at every non-normal node.
#assert_no_axioms FX1Poly.Core.exists_step_of_not_isStepNormalForm
#assert_no_axioms FX1Poly.Core.exists_stepChildren_of_not_areStepNormalForms

-- WEAK NORMALIZATION: a strongly-normalizing term reaches a structural normal form, with the reduction
-- chain produced by descending the `Acc StepSuccessor` witness and extracting a real Step at every
-- non-normal node.  The StepStar-existence half of normalization (uniqueness comes from confluence) —
-- the strongly-normalizing-fragment door to decidable Conv (#267) and the WHNF normalizer (#374).
#assert_no_axioms FX1Poly.Core.exists_normalForm_of_isStronglyNormalizing

-- NORMAL-FORM UNIQUENESS: confluence forces two normal reducts of one SN term to coincide, so the SN
-- fragment has a UNIQUE normal form (existence from WN + this uniqueness clause).  The "the normal form"
-- handle a normalizer function realizes and SN-fragment decidable Conv (#267) rests on.
#assert_no_axioms FX1Poly.Core.normalForm_unique
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
#assert_no_axioms FX1Poly.Core.IsReducibilityCandidate.respectsPointwiseIff
#assert_no_axioms FX1Poly.Core.IsReducibilityCandidate.containsVariable

-- The NEUTRAL ARM of the #672 fuel-stability gate. For a weak-head-normal non-Pi non-universe type code
-- reducible at every fuel level, the stratified candidate is level-independent (= IsStronglyNormalizing via
-- candidateIffStronglyNormalizing), so membership at one positive fuel implies SN implies membership at all
-- positive fuels. This is a genuine non-vacuous sub-case of HasPositiveMemberExtensionForStronglyNormalizing
-- AllLevelTypes; the universe / Pi arms (where the candidate moves with the fuel) remain the open crux (#672).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember

-- The Pi TYPE-saturation reassembly arm of #672 (inverse of domainOfPiType / codomainOfPiTypeAtAllPositive
-- Argument): from domain all-positive + domain-member fuel-stability + codomain all-positive (per all-positive
-- arg), the Pi type is reducible at all positive fuels. Choice-free via reducibleMemberCandidate. A conditional
-- inductive step matching the existing arm style (the component fuel-stabilities are the recursion's sub-term
-- IHs); the well-founded recursion tie-up remains the open crux (#672).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.ofPiType

-- First genuinely DEPENDENT Pi fuel-stability arm: a Pi over a neutral/data domain. Both domain legs of the
-- Pi reassembly (#718) / Pi member-extension (piTypeMemberExtensionPositive) discharge unconditionally for a
-- neutral/data domain (domain all-levels via ofWeakHeadNormalNonPiNonUniverse; domain-member fuel-stability
-- via the #717 neutral arm ofNeutralTypeMember), isolating the residual to the CODOMAIN alone. The codomain
-- genuinely varies with the argument (unlike the simply-typed non-dependent arrow), so this strictly extends
-- the closed surface past the simply-typed fragment. The universe-domain case remains the open crux (#672).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.dependentPiMemberExtensionOverNeutralDomain

-- First FULLY UNCONDITIONAL dependent Pi arm + concrete closed witness: when the codomain INSTANTIATIONS
-- subst0 cod arg are also neutral/data (for every arg), the codomain leg discharges too (via the neutral leaf
-- + #717), so the dependent Pi is reducible / member-extending with NO reducibility hypothesis. The headline
-- concreteDependentPi exhibits Pi (x : A). P x (A, P free type/family variables) reducible end-to-end with
-- ZERO hypotheses — the first genuinely dependent type closed through the stratified reducibility model.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.dependentPiOverNeutralDomainNeutralCodomain
#assert_no_axioms FX1Poly.Typed.concreteDependentPi_isReducibleType

-- The DEPENDENT analogue of IsFirstOrderSimplyTyped: an inductive fragment (neutral/data leaves + dependent Pi
-- over neutral domains with recursively-fragment codomain instantiations) + one fundamental theorem. Captures
-- curried dependent functions Pi(x:A).Pi(y:B x).C x y over neutral/data base types. reducibleAndMemberExtension
-- is the #672 fuel-stability gate proven for this fragment; the all-levels dependentPiOverNeutralDomain feeds
-- its member leg; typeFamilyApplication is the concrete Pi(x:A).P x fragment member. Universe-domain Pi open.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain
#assert_no_axioms FX1Poly.Typed.IsNeutralDomainDependentlyTyped.reducibleAndMemberExtension
#assert_no_axioms FX1Poly.Typed.IsNeutralDomainDependentlyTyped.ofNeutral
#assert_no_axioms FX1Poly.Typed.IsNeutralDomainDependentlyTyped.typeFamilyApplication

-- The dependent-neutral fragment STRICTLY CONTAINS the first-order simply-typed fragment: a non-dependent
-- arrow is the constant-codomain degenerate dependent Pi (weaken_subst_singleton cancels the substitution).
-- The corollary re-derives first-order reducibility+member-extension through the dependent fragment's single
-- fundamental theorem — one FT covering both fragments. Higher-order simply-typed (arrow domains) is NOT
-- subsumed (needs domain member-extension at fuel 0, deferred with the universe-domain crux of #672).
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.toNeutralDomainDependentlyTyped
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.reducibleAndMemberExtensionViaDependentFragment

-- Cumulativity SN-072: reducibility respects Type@e ⊆ Type@(lsucc e). In the fuel-stratified model the
-- universe candidate is LevelExpr/flag-independent (meta-fuel decoupled from object levels; the hierarchy
-- discipline lives in HasType, not the semantic model), so universe membership is level-label-IRRELEVANT
-- (a two-way equivalence) and cumulativity is its named corollary (single-level + all-positive). Honest scope:
-- this is cumulativity in the coarse model; per-LevelExpr cumulativity awaits the LevelExpr-matching refinement.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.universeCumulativity
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.universeCumulativity

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
-- Candidate-bridge leaves: emptyTypeCell heads no weak-head step / no full Step (nullary gen_emptyCode leaf, no
-- β/ι, empty child spine); candidateIffEmptyCandidate is the empty-code shape inversion (a reducible type whose
-- code IS emptyTypeCell has candidate emptyTaitCandidate up to PointwiseIff) — the leaf deterministic's dataEmpty
-- arm consumes, twin of candidateIffStronglyNormalizing/candidateIffUniverse.
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_noStep
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffEmptyCandidate
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
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_forwardStep
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_neutralInclusion_of_lt
#assert_no_axioms FX1Poly.Typed.denoteBelowFamily_backwardWeakHeadStep
-- the denote-keyed semantic member predicate (member analogue of IsReducibleTypeAtDenote)
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtDenote

-- DenoteKeyedUniverseDomainPi (#672 toward the non-fuel piArm): the denote model closes the universe-domain
-- Π that the external-fuel level-irrelevance induction (ReducibleTypeAtAllLevelsInduction.piArm) provably
-- could not. candidate_levelStable is the conceptual heart — one fixed candidate is Type@e's candidate at
-- every ambient level above denote e env (the negation of the fuel "candidates at successive levels differ"
-- obstruction). reducibleAtAllDenoteLevels assembles the dependent universe-domain Π Π(Type@e).C uniformly
-- across all those levels with one codomain candidate, since the level-stable domain candidate discharges the
-- piType constructor at every level simultaneously (no across-level member-extension circularity).
-- uniformCandidateAtAllDenoteLevels pulls the candidate existential outside the level quantifier (∃cand,∀level)
-- and memberStableAcrossDenoteLevels is the #672-shaped payoff: a member at one level above denote e env is a
-- member at every such level, via the uniform candidate + ReducibleTypeAtDenote.deterministic.
#assert_no_axioms FX1Poly.Typed.universeDomainCandidate_levelStable
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

-- DenoteKeyedCanonicalMemberCandidate (route D Π-formation engine, the denote analogue of #490): the canonical
-- member-predicate IsReducibleMemberAtDenote env level typeCode is itself the type's own candidate. The
-- choice-free codomain extraction the denote FT's Π-formation arm consumes — turns the codomain IH's mere
-- EXISTENCE of a candidate into the FIXED canonical predicate, no Classical.choice. ofPointwiseIff (pointwise,
-- no funext) + deterministic; uniform in level (no cases-level split the fuel original needed).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtDenote.reducibleMemberCandidate
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtDenote.reducibleMemberCandidate

-- DenoteKeyedPiFormationFromExistence (route D Π-formation arm, the route-D-friendly piArm): the denote
-- Π-formation arm that takes the codomain IH as mere EXISTENCE (IsReducibleTypeAtAllDenoteLevels) rather than a
-- chosen candidate, extracting the per-level candidate choice-freely via the canonical-member-candidate engine.
-- uniformDomainPi covers any level-stable-candidate domain; neutralDomainPi is the witnessing instance (type
-- variables / stuck applications — the common FT case). The domain-membership gating matches because the domain
-- candidate is uniform across levels. No Classical.choice.
#assert_no_axioms FX1Poly.Typed.uniformDomainPi_reducibleFromCodomainExistence
#assert_no_axioms FX1Poly.Typed.neutralDomainPi_reducibleFromCodomainExistence
-- universeDomainPi_reducibleFromCodomainExistence: the impredicative case — Π(X:Type@e).C[X] reducible from
-- codomain existence over universe members. Threshold split (Nat.lt_or_ge, choice-free): above denote e the
-- below-family = the relation at denote e (universe membership IS the codomain gate); at/below it's empty
-- (codomain vacuous). Completes the from-existence piArm family across all domain shapes.
#assert_no_axioms FX1Poly.Typed.universeDomainPi_reducibleFromCodomainExistence

-- DenoteKeyedGeneralDomainPiArm (#752 residual isolation): the GENERAL domain piArm modulo domain
-- member-stability. The backbone's domain IH gives a candidate PER LEVEL (drift allowed); the piType assembly
-- needs them collapsed, which IS domain member-stability (a denote-reducible member at one level is a member at
-- every level). generalDomainPi_reducibleFromMemberStability takes the per-level domain reducibility + member-
-- stability + codomain existence and produces the Π at every level — strictly generalizing the uniform piArm
-- (its member-stable-by-a-uniform-candidate instance via determinism), reaching member-stable COMPOSITE domains
-- (Nat → Nat). Construction: canonical member-predicate as domain/codomain candidate (reducibleMemberCandidate),
-- member-stability lifting per-level domain membership to the all-level gate. The remaining #752 residual is now
-- precisely the THRESHOLD-DRIFT domains (composite domains with sub-threshold universe codes, member-stability
-- fails below threshold), needing the threshold-split.
#assert_no_axioms FX1Poly.Typed.generalDomainPi_reducibleFromMemberStability

-- DenoteKeyedGeneralDomainPiArm adapters (#752 — the uniform/neutral arms of the ofReducibleTypeStepDenote
-- piArm case-split): the backbone piArm supplies its codomain IH as an EXISTENTIAL-candidate all-level
-- reducibility keyed on the step's domainCandidate; the shipped uniform/neutral instances consume a CONCRETE
-- per-level codomain candidate. uniformDomainPiArmFromInductiveHypotheses bridges the two for a uniform domain
-- candidate, routing through generalDomainPi_reducibleFromMemberStability with member-stability from
-- uniformType_memberStableAcrossDenoteLevels and the codomain-IH candidate reconciled via determinism at level 0
-- (choice-free). neutralDomainPiArmFromInductiveHypotheses is its weak-head-normal non-Π non-universe instance,
-- in exactly the shape the backbone supplies its premises. Remaining piArm arms: universe-code + composite.
#assert_no_axioms FX1Poly.Typed.uniformDomainPiArmFromInductiveHypotheses
#assert_no_axioms FX1Poly.Typed.neutralDomainPiArmFromInductiveHypotheses

-- DenoteKeyedGeneralDomainPiArm UNIFIED piArm (#752): the bridge invokes ofReducibleTypeStepDenote at
-- lowerAt = denoteBelowFamily env outerLevel, so the backbone's domain step IS (definitionally) ReducibleType
-- AtDenote env outerLevel. piArmFromMemberStabilityToOuterLevel collapses the whole 5-arm cases-domainReducible
-- split to ONE hypothesis — member-stability of the domain TO the fixed outerLevel — with codomain existence
-- derived automatically by determinism against domainReducible (no codomainExistence premise, no per-shape
-- casing). Strictly more usable than generalDomainPi_reducibleFromMemberStability (only stability-to-outerLevel,
-- not to-every-level). Per output level: (domainAllLevel level).reducibleMemberCandidate as domain candidate,
-- memberStableToOuter lifts the member to outerLevel, determinism pins domainCandidate, codomain IH fires. The
-- residual is now exactly memberStableToOuter (neutral/uniform always; universe above threshold; composite open).
#assert_no_axioms FX1Poly.Typed.piArmFromMemberStabilityToOuterLevel

-- The concrete memberStableToOuter INSTANCES the unified piArm consumes. neutralDomainMemberStableToOuter:
-- fixed-target specialization of neutralType_memberStableAcrossDenoteLevels (neutral candidate = SN, uniform).
#assert_no_axioms FX1Poly.Typed.neutralDomainMemberStableToOuter

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
-- universeCodeNotAllLevelsMemberStable (#672 RESIDUAL BOUNDARY, §27.2-style negative witness): a universe code
-- Type@inner is NOT all-levels member-stable — var index is a reducible member just above the inner level (SN +
-- neutral reducible) but the candidate at level 0 is empty. So a composite domain with a universe-code COMPONENT
-- canNOT satisfy compositeDomainMemberStableToOuter's all-levels component-stability premise; threshold-drift
-- composites are the open #672 residual, NOT closed by the member-stability route.
#assert_no_axioms FX1Poly.Typed.universeCodeNotAllLevelsMemberStable

-- DenoteKeyedSingleLevelPi (the #672 REFRAME — drift-free single-level toolkit): the all-levels piArm (#752)
-- over-generalizes to low levels where composite-universe domains are vacuously inhabited (the drift,
-- universeCodeNotAllLevelsMemberStable). But genFormationPi's piReducibleAsType needs the Π reducible-as-type at
-- ONE level (the decoded output level, above thresholds). piReducibleAtLevelFromComponents assembles it directly
-- via the piType arm + canonical member-predicates (single level ⟹ no member-stability, no drift).
-- universeMemberReducibleAsTypeAtDecodedLevel is the A2 bridge's prefix: a universe member is reducible-as-type
-- at the decoded level directly (no all-levels lift, no piArm) — drift-free for ANY typeCode.
#assert_no_axioms FX1Poly.Typed.piReducibleAtLevelFromComponents
#assert_no_axioms FX1Poly.Typed.universeMemberReducibleAsTypeAtDecodedLevel

-- DenoteKeyedUniformPiCandidate (#752 — composite member-stability, the recursive step): a Π over uniform-
-- candidate components has a SINGLE uniform candidate, because the piType candidate
-- (fun f => ∀ arg, domCand arg → codCand arg (f arg)) is level-INDEPENDENT when its components are. So uniform
-- candidacy composes up the Π/Σ-former spine from leaf types (the leaf member-stability lemmas covered only a
-- single uniform candidate / neutral types). uniformDomainPi_hasUniformCandidate: Π reducible at every level
-- with the fixed candidate (one piType per level). uniformDomainPi_memberStable: hence member-stable
-- (uniformType_memberStableAcrossDenoteLevels on it). This is what lets the shipped uniform piArm /
-- generalDomainPi reach composite (uniform-component) domains (Nat → Nat). The remaining residual is precisely
-- the THRESHOLD-DRIFT domains (composite domains with sub-threshold universe codes — candidate varies, NOT
-- uniform), needing the threshold-split.
#assert_no_axioms FX1Poly.Typed.uniformDomainPi_hasUniformCandidate
#assert_no_axioms FX1Poly.Typed.uniformDomainPi_memberStable

-- DenoteKeyedUniformPiAboveThreshold (#752 — the threshold-drift composite handler): the ABOVE-THRESHOLD twins
-- of the uniform-composite lemmas, for composites CONTAINING universe codes (Type@0 → Type@0) whose components
-- are uniform only ABOVE the inner codes' decoded level (universeMembership_levelIrrelevant gives the fixed
-- candidate there). The all-level reducibility such composites would need is unachievable (the Π fails below
-- threshold), but the FT never needs it — a former's components live in universes strictly below the former's,
-- so the former's decoded level sits above every component threshold, exactly this regime.
-- uniformType_memberStableAboveThreshold: bounded leaf member-stability. uniformDomainPi_hasUniformCandidate-
-- AboveThreshold: Π reducible with the fixed candidate above threshold (one piType per above-threshold level).
-- uniformDomainPi_memberStableAboveThreshold: composite member-stability above threshold.
#assert_no_axioms FX1Poly.Typed.uniformType_memberStableAboveThreshold
#assert_no_axioms FX1Poly.Typed.uniformDomainPi_hasUniformCandidateAboveThreshold
#assert_no_axioms FX1Poly.Typed.uniformDomainPi_memberStableAboveThreshold

-- DenoteKeyedPiFormerAtLevel (#752 — the single-level route's foundational primitive): the FT genFormationPi
-- arm needs the former reducible at its DECODED level (a SINGLE level), not all levels (the all-level backbone
-- is unachievable for threshold-drift composite-domain Π and unneeded — a former's decoded level sits above all
-- component thresholds). piFormerReducibleAtLevel: Π reducible at level L from domain reducible at L + codomain
-- reducible at L per L-member, choice-free via reducibleMemberCandidate (one piType at one level, NO all-level /
-- member-stability / threshold machinery). universeDomainPiFormerReducibleAtLevel: the impredicative case
-- Π(X:Type@e).C[X] becomes TRIVIAL at a single level — Type@e is reducible at EVERY level
-- (universeCode_isReducibleAtDenote), so NO threshold-split (contrast the all-level
-- universeDomainPi_reducibleFromCodomainExistence). The single-level route sidesteps the impredicative
-- obstruction entirely.
#assert_no_axioms FX1Poly.Typed.piFormerReducibleAtLevel
#assert_no_axioms FX1Poly.Typed.universeDomainPiFormerReducibleAtLevel
-- neutralDomainPiFormerReducibleAtLevel: the neutral/type-variable-domain instance (the common FT case
-- Π(x:X).C[x] with X a context type variable) — neutral domains are reducible at every level (the neutral arm,
-- free lift), so piFormerReducibleAtLevel applies directly. With the universe instance this covers the FREE-LIFT
-- domain shapes; threshold-drift composites lift via the above-threshold uniform candidate (shipped) as the
-- domain premise. Completes the genFormationPi piArm INGREDIENTS; only the telescope/recursor wiring remains.
#assert_no_axioms FX1Poly.Typed.neutralDomainPiFormerReducibleAtLevel

-- DenoteKeyedReducibleTypeLevelLift (#752/#744 — the genFormationPi child-LIFT engine): the SINGLE-level
-- reducibility lift backbone. A former's telescope children arrive reducible at THEIR decoded levels (strictly
-- lower than the former's); lifting them to the former's level is genFormationPi's central move.
-- reducibleTypeLevelLift: from a ReducibleTypeStepDenote env lowerAt step produce reducibility at one fixed
-- highLevel — four constructive arms (whnfExpand head-expands the lifted reduct; neutral free; universeCode via
-- universeCode_isReducibleAtDenote, reducible at EVERY level; ofPointwiseIff inherits) with the piType arm
-- isolated as piArmLift. Contrast the all-level IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote whose
-- piArm is unachievable for threshold-drift composite-domain Π (fails below threshold); the single fixed highLevel
-- makes piArmLift the TRACTABLE member-stability bridge (above threshold, via the shipped
-- uniformDomainPi_memberStableAboveThreshold) rather than the unachievable all-level gate. The route correction
-- for #752 crystallised into reusable infrastructure.
#assert_no_axioms FX1Poly.Typed.reducibleTypeLevelLift

-- DenoteKeyedPiArmDischarge (#752/#744 — discharging reducibleTypeLevelLift's piArmLift, case by case): the
-- lift isolates the piType arm as a hypothesis dischargeable per domain shape (neutral / universe / composite).
-- neutralDomainPiArmLift: the NEUTRAL-domain case. The domain is reducible at highLevel for free (the neutral
-- constructor's SN candidate references neither lowerAt nor the level); the member-stability bridge from the
-- canonical highLevel member-predicate back to the lower domainCandidate pivots through
-- candidateIffStronglyNormalizing at BOTH levels (member → IsStronglyNormalizing → domainCandidate, the fully
-- level-irrelevant SN pivot). The first of the three piArmLift shape cases; with the universe and composite
-- cases it makes the single-level child-lift unconditional on a neutral spine.
#assert_no_axioms FX1Poly.Typed.neutralDomainPiArmLift
-- universeDomainPiArmLift: the UNIVERSE-domain case (2/3), ABOVE THRESHOLD. For a universe-code domain Type@e,
-- the Π is reducible at highLevel PROVIDED denote e < lowLevel AND denote e < highLevel: domain reducible at
-- highLevel for free (universeDomainPiFormerReducibleAtLevel), and the member bridge pins both candidates to the
-- universe predicate (candidateIffUniverse) then collapses both below-family predicates to the fixed
-- decode-at-(denote e) set via coherence (denoteBelowFamily_eq_reducible — applicable exactly by the two
-- thresholds). The thresholds are ESSENTIAL: below its decoded level a universe code's member candidate is
-- IsStronglyNormalizing ∧ False (EMPTY — the index runs off denoteBelowFamily's end), the threshold-drift
-- obstruction sharpest. So the universe case is NOT unconditionally free (contrast neutral); the genFormationPi
-- context supplies the thresholds (components live strictly below the former's level).
#assert_no_axioms FX1Poly.Typed.universeDomainPiArmLift
-- aboveThresholdDomainPiArmLift: the GENERAL shape-independent engine. For ANY domain reducible with one fixed
-- candidate at every above-threshold level, the Π is reducible at highLevel — the member bridge is just
-- ReducibleTypeAtDenote.deterministic at the SINGLE highLevel (both the member's candidate and the uniform
-- candidate live there, so no cross-level transport). Subsumes the universe/neutral cases and is the form the
-- composite case needs; the lift's piArmLift already supplies the domain reducible at highLevel, so the only
-- residual is determinism-pinning the member's candidate to domainCandidate.
#assert_no_axioms FX1Poly.Typed.aboveThresholdDomainPiArmLift
-- compositeDomainPiArmLift: the COMPOSITE-domain case (3/3), ABOVE THRESHOLD. The domain is itself Π inner over
-- components uniform above threshold, so it has a fixed piType candidate there
-- (uniformDomainPi_hasUniformCandidateAboveThreshold) and feeds the general engine. This is the lone deep
-- #672/SN-001 obstruction (Type@0 → Type@0, candidate drifts below threshold) closed ABOVE threshold — all the
-- genFormationPi arm needs (the former's decoded level sits above its components' thresholds). With neutral and
-- universe it discharges piArmLift on every domain shape.
#assert_no_axioms FX1Poly.Typed.compositeDomainPiArmLift
-- universeDomainPiFormerViaEngine: the universe-domain former re-derived THROUGH the general engine, feeding
-- universeMembership_levelIrrelevant as domainUniform (threshold = denote levelExpr env). Validates the engine
-- subsumes the universe case AND exposes the codomain key in the CLEAN fixed-predicate form (SN ∧ reducible at
-- the decoded level) — the form the genFormationPi assembly prefers (the telescope's universe-membership intro
-- supplies exactly the decoded-level membership). Only side-condition: denote levelExpr env < highLevel.
#assert_no_axioms FX1Poly.Typed.universeDomainPiFormerViaEngine

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

-- sigmaFormationMemberAtDenote (SN-D5d, the Σ case of the genFormationPi denote-FT arm; denote analogue of the
-- fuel IsReducibleMemberAt.sigmaFormationUnderSubst): under a closing substitution, Σ domain. codomain is a
-- denote-reducible MEMBER of its universe Type@levelExpr given its substituted children are SN. The FIRST
-- genFormationPi denote-FT arm closing FULLY (both conjuncts), unconditional — the Σ case carries NO threshold
-- hypothesis exactly because its reducible-as-type half is the FREE neutral arm (smoke_sigmaFormer); SN via the
-- two-child former-SN, packaged by universeMembershipIntroAtDenote. typingRuleDescOf is some only for {Π, Σ},
-- so this + the Π piType arm (the #752 threshold residual) cover the whole 2-case genFormationPi split.
#assert_no_axioms FX1Poly.Typed.sigmaFormationMemberAtDenote

-- SN-D5d (denote universe-member CR1 + Σ-from-child-members assembly): bridges the children's universe
-- MEMBERSHIPS (what the FT telescope IH supplies) to sigmaFormationMemberAtDenote's SN premises.
-- stronglyNormalizing_of_universeMemberAtDenote: a member of Type@e above threshold is SN (universe candidate
-- pinned via universeMembership_levelIrrelevant + ReducibleTypeAtDenote.deterministic — the threshold is the
-- fundamental #672 caveat). sigmaFormationFromChildMembersAtDenote: domain member + codomain member at var 0
-- ⟹ Σ universe membership (domain SN by CR1; codomain-under-binder SN by CR1 then openBodyOfConsSubst; the
-- denote analogue of the fuel sigmaFormerOfChildMembershipsAtRequiredLevel).
#assert_no_axioms FX1Poly.Typed.stronglyNormalizing_of_universeMemberAtDenote
#assert_no_axioms FX1Poly.Typed.sigmaFormationFromChildMembersAtDenote

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

-- piReducibleAsTypeFromComponentReducibility (the #672 reframe applied): discharges the genFormationPi arm's
-- piReducibleAsType premise from the children's reducibility AT THE DECODED OUTPUT LEVEL (the primitive form the
-- FT recursion supplies) — domain via universeMemberReducibleAsTypeAtDecodedLevel, codomain under the var-0
-- extended env (subst0 (subst (lift σ) codomain) arg). Routes through the drift-free single-level
-- piReducibleAtLevelFromComponents after subst_piTyCodeCell. SINGLE level (decoded, above thresholds) ⟹ no
-- all-levels drift; sidesteps the #752 all-levels piArm for the genFormationPi reducible-as-type half.
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromComponentReducibility

-- piReducibleAsTypeFromUniformLevelMember (fully-uniform genFormationPi reducible-as-type, lift-free): for the
-- Π whose domain AND codomain are classified at the SAME universe levelExpr as the Π's own output
-- (levelExpr = lmaxAll [levelExpr, levelExpr]), the piReducibleAsType premise is discharged from the children's
-- raw universe-MEMBERSHIPS (the natural FT output) with NO cumulativity lift: each member of Type@levelExpr
-- decodes to a reducible TYPE at denote levelExpr env directly (universeMemberReducibleAsTypeAtDecodedLevel,
-- decoded level = the Π's level), fed to the connector. The non-uniform cases (levelExpr strictly above one
-- child's universe) need the level-bounded TYPE-reducibility cumulativity (the documented multi-lemma residual).
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniformLevelMember

-- piReducibleAsTypeFromUniverseDomainCodomainReducibility (the NON-uniform DOMAIN twin, anti-vacuity sidestep):
-- when the Π domain is a literal universe code Type@domainLevel (the type-of-type-families shape), the domain is
-- reducible-as-type at the Π's decoded output level FOR FREE via universeCode_isReducibleAtDenote (anti-vacuity,
-- EVERY level) — NO cumulativity even when denote domainLevel env < denote levelExpr env (the non-uniform case
-- piReducibleAsTypeFromUniformLevelMember cannot reach). The #752/#753 obstruction bites only the universe MEMBER
-- candidate (vacuous below its decoded level), never universe-code TYPE reducibility; residual isolated to codomain.
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniverseDomainCodomainReducibility

-- piReducibleAsTypeFromUniverseCodeComponents (BOTH children universe codes — Π (A:Type@a). Type@b): the
-- constant-codomain type-family former's piReducibleAsType is discharged UNCONDITIONALLY (no hypotheses) — both
-- children anti-vacuously reducible at the output level, codomain a CLOSED universe code unchanged by subst/subst0.
-- Closes the NON-uniform a ≠ b case entirely via anti-vacuity — the type-half witness that the obstruction is a
-- member-candidate phenomenon, not a type-reducibility one.
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniverseCodeComponents

-- fundamentalGenFormationPiUniverseUniverse (the FIRST fully-closed genFormationPi denote FT arm): the complete
-- FundamentalConclusionAtDenote for the type-of-type-families former Π (A:Type@a). Type@b, all three premises of
-- fundamentalGenFormationPiAtDenote discharged UNCONDITIONALLY — domainMember via universeFormationMemberUnder-
-- ClosingSubstitution (Type@a member of Type@(lsucc a)), codomainSN via noStep_universeCode, piReducibleAsType via
-- piReducibleAsTypeFromUniverseCodeComponents. The Π analogue of the already-closed Σ arm; advances SN-D5d (#750).
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationPiUniverseUniverse

-- fundamentalGenFormationSigmaUniverseUniverse (the Σ twin, completing the universe-universe former PAIR): the
-- complete FundamentalConclusionAtDenote for Σ (A:Type@a). Type@b, both premises of fundamentalGenFormationSigmaAt-
-- Denote discharged UNCONDITIONALLY — domainMember via universeFormationMemberUnderClosingSubstitution, codomainSN
-- via noStep_universeCode. NO piReducibleAsType premise (Σ uses its free neutral candidate) — so even shorter than
-- the Π twin, documenting the genuine Σ-free / Π-via-#752-discharge asymmetry. Both formers over universes now closed.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationSigmaUniverseUniverse

-- gapUniverseDomainPiVacuouslyReducibleAtLowLevel (the cumulativity-obstruction WITNESS): at lowLevel ≤
-- denote gapLevel env, Type@gapLevel has the EMPTY member candidate (denoteBelowFamily empty at index ≥
-- lowLevel), so Π(Type@gapLevel) codomain is reducible-as-type at lowLevel for ANY codomain (vacuous codomain
-- obligation). Low-level reducibility of a gap-universe-domain Π is codomain-BLIND ⟹ cannot be lifted to a
-- higher level where the domain gains members. Pins WHY the non-uniform genFormationPi piReducibleAsType is
-- model-obstructed (semantic reducibility does NOT bound universes — universeCode_isReducibleAtDenote fires at
-- every level), so it needs a bound-carrying model OR stays a carried premise (conditional/fragment milestone).
#assert_no_axioms FX1Poly.Typed.gapUniverseDomainPiVacuouslyReducibleAtLowLevel

-- #753 / SN-D5e BOUND-CARRYING RELATION (DenoteKeyedBoundedReducibility) — the genuine resolution of the
-- obstruction above. ReducibleTypeStepBounded GATES the universeCode arm on denote levelExpr env < bound, so
-- high-universe codes are EXCLUDED from low bounds by construction (universe-label-AWARE, unlike the label-blind
-- ReducibleTypeStepDenote). denoteBelowFamilyBounded keeps the structural (non-WF) recursion ⟹ Quot.sound-free.
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_eq_reducible
-- THE PAYOFF: cumulativity is FREE in the gated relation (the property the label-blind model CANNOT prove). A
-- bounded-reducibility derivation lifts from bound to any higherBound ≥ bound with the SAME candidate — universeCode
-- arm re-fires (its gate denote e < higherBound guaranteed by denote e < bound ≤ higherBound) reconciled via
-- ofPointwiseIff (funext-free), every other arm by IH. The keystone the genFormationPi piArm needs.
#assert_no_axioms FX1Poly.Typed.stepBounded_cumulative
#assert_no_axioms FX1Poly.Typed.isReducibleBounded_cumulative
-- THE FORGET BRIDGE (bounded ⊆ denote): a bounded-reducibility derivation IS a denote derivation (drop the gate),
-- so ALL ReducibleTypeStepDenote metatheory (determinism, candidate-shapes, forward-closure, convTransfer, the
-- CR1/2/3 bundle) transfers to the bounded relation WITHOUT re-porting. The leverage lemma for the rest of #753.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.toReducibleTypeStepDenote
-- First fruits of the bridge: determinism transferred (the canonical-candidate reconciliation the bounded FT needs).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.deterministic
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.deterministic
-- THE UNCONDITIONAL CR1/CR2/CR3 BUNDLE for the bounded relation. Forward-closure must PRODUCE a bounded
-- (gate-preserving) derivation, so it does NOT transfer through the forget bridge -- it is a direct port
-- (universeCode is a step normal form, gate carried vacuously). The reducibility-candidate bundle is also a
-- direct induction, but here the gate PAYS OFF: at the universeCode arm belowBound : denote e < bound supplies
-- the level bound neutral-inclusion needs, so the FAMILY-level ReducibleTypeAtBounded.isReducibilityCandidate is
-- UNCONDITIONAL -- no predicative caveat (the property the label-blind ReducibleTypeAtDenote could not get).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.whnfExpandClosure
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.forwardStepStar
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.forwardStep
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.reducibleOfNeutral
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_eq_empty_of_ge
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_forwardStep
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_neutralInclusion_of_lt
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.isReducibilityCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.isReducibilityCandidate
-- THE BOUNDED FT FOUNDATIONAL LAYER (DenoteKeyedBoundedReducibleEnv): the bound-carrying member predicate +
-- closing-substitution environment the bounded fundamental theorem consumes. Character-identical to the denote
-- env (DenoteKeyedReducibleEnv) with bound riding where level rode; cons is the Fin-position split + the
-- weakening cancellation. The env the bounded FT uses to discharge the non-uniform genFormationPi piReducibleAsType
-- that the denote relation leaves model-obstructed (DenoteKeyedCumulativityObstruction).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtBounded
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtBounded
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtBounded.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtBounded.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtBounded.cons
-- THE BOUNDED FT MOTIVE + LEAF ARMS (DenoteKeyedBoundedFundamentalMotive): the bound-carrying analogue of
-- FundamentalConclusionAtDenote + var/universeFormation, built over the label-AWARE ReducibleTypeAtBounded. The
-- universe-membership machinery (isReducibleAtBounded / membership level-irrelevance) threads the universeCode gate;
-- the universeFormation arm's new gate vs denote is denote e < denote (lsucc e) (denote_lt_lsucc). This is where the
-- bounded FT begins replacing the denote FT, whose non-uniform genFormationPi arm is model-obstructed.
#assert_no_axioms FX1Poly.Typed.universeCode_isReducibleAtBounded
#assert_no_axioms FX1Poly.Typed.universeMembershipBounded_levelIrrelevant
#assert_no_axioms FX1Poly.Typed.universeFormationMemberAtBounded
#assert_no_axioms FX1Poly.Typed.universeFormationMemberUnderClosingSubstitutionBounded
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtBounded
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtBounded
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationAtBounded
-- THE BOUNDED FT CONV ARM (DenoteKeyedBoundedConvArm): the bound-carrying analogue of the denote conv member arm +
-- FT arm. convTransfer is a ~3-line FORGET-BRIDGE transfer (bounded forgets to denote at the same lowerAt, and
-- ReducibleTypeStepDenote.convTransfer is lowerAt-parametric) — the canonical economy the forget bridge provides for
-- facts-about-candidates. The FT arm is premise-isolating (carries the A2 ambient-bound reducibility premise).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.convTransfer
#assert_no_axioms FX1Poly.Typed.memberConvAtBounded
#assert_no_axioms FX1Poly.Typed.convMemberUnderClosingSubstitutionBounded
#assert_no_axioms FX1Poly.Typed.fundamentalConvAtBounded
-- THE BOUNDED FT PI-ELIM ARM (DenoteKeyedBoundedPiElimArm): the bound-carrying application member + FT arm. Unlike
-- the conv arm, the application member's OUTPUT carries a BOUNDED codomain derivation the forget bridge cannot
-- recover, so candidatePiShape is a DIRECT 5-arm induction port (the derivation-producing side of the dichotomy);
-- ReducibleTypeAtBounded.deterministic (bridge-transferred) supplies the argument-candidate alignment.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.candidatePiShape
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.piTypeInversion
#assert_no_axioms FX1Poly.Typed.applicationMemberAtBounded
#assert_no_axioms FX1Poly.Typed.applicationMemberUnderClosingSubstitutionBounded
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimAtBounded
-- THE BOUNDED FT PI-INTRO ARM (DenoteKeyedBoundedPiIntroArm) — THE BINDER CRUX. The headline: headExpansionClosed
-- is a FORGET-BRIDGE transfer (HeadExpansionClosed candidate is a FACT; ReducibleTypeStepDenote.headExpansionClosed
-- is lowerAt-parametric) fed the bounded leg denoteBelowFamilyBounded_backwardWeakHeadStep (verbatim by-cases port).
-- reducibleMemberCandidate (the choice-free canonical predicate) makes the binder env-cons coordination direct;
-- abstractionMemberAtBounded via DependentArrowCandidate.abstraction; the arm threads ReducibleEnvAtBounded.cons.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.reducibleMemberCandidate
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtBounded.reducibleMemberCandidate
#assert_no_axioms FX1Poly.Typed.denoteBelowFamilyBounded_backwardWeakHeadStep
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.headExpansionClosed
#assert_no_axioms FX1Poly.Typed.abstractionMemberAtBounded
#assert_no_axioms FX1Poly.Typed.abstractionMemberUnderClosingSubstitutionBounded
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtBounded
-- THE BOUNDED FORMER ENGINE (DenoteKeyedBoundedFormerEngine): the universe-membership INTRODUCTION + type-former
-- arm + universe-member SN projection that the bounded universeFormation / genFormationPi arms route through. All
-- three route through the SHIPPED universeMembershipBounded_levelIrrelevant; fundamentalTypeFormerAtBounded isolates
-- the former's type-reducibility (route A) as the single premise — the residual that, in the BOUNDED relation,
-- closes via free cumulativity (stepBounded_cumulative) where the denote relation is model-obstructed.
#assert_no_axioms FX1Poly.Typed.universeMembershipIntroAtBounded
#assert_no_axioms FX1Poly.Typed.fundamentalTypeFormerAtBounded
#assert_no_axioms FX1Poly.Typed.stronglyNormalizing_of_universeMemberAtBounded
-- THE BOUNDED GENFORMATIONPI ARM SKELETON (DenoteKeyedBoundedGenFormationPiArm): the single-level Π toolkit + the
-- premise-isolating arm. piReducibleAtLevelFromComponentsBounded (piType + canonical member-predicate codomain),
-- universeMemberReducibleAsTypeAtDecodedLevelBounded (.2-projection twin of the universe-member SN), the connector,
-- and fundamentalGenFormationPiAtBounded (routes through the former engine; Π-former SN relation-agnostic). The
-- non-uniform piReducibleAsType — model-obstructed in denote — closes via free cumulativity (the next brick).
#assert_no_axioms FX1Poly.Typed.piReducibleAtLevelFromComponentsBounded
#assert_no_axioms FX1Poly.Typed.universeMemberReducibleAsTypeAtDecodedLevelBounded
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromComponentReducibilityBounded
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationPiAtBounded

-- THE PAYOFF (DenoteKeyedBoundedGenFormationPiDischarge): the bound-carrying piReducibleAsType DISCHARGE variants.
-- piReducibleAsTypeFromNonUniformLevelMemberBounded closes the model-obstructed non-uniform case (a child classified
-- STRICTLY below the Π output universe) via isReducibleBounded_cumulative -- the free bounded cumulativity decode-
-- then-lift the denote relation cannot do (DenoteKeyedCumulativityObstruction). Uniform is its Nat.le_refl instance.
-- The universe-code variants discharge anti-vacuously via the GATED universeCode_isReducibleAtBounded (strict-below
-- hypotheses). fundamentalGenFormationPiUniverseUniverseAtBounded = the FIRST fully-discharged bounded genFormationPi
-- arm (Π (A : Type@a). Type@b), all three premises of fundamentalGenFormationPiAtBounded closed.
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromNonUniformLevelMemberBounded
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniformLevelMemberBounded
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniverseDomainCodomainReducibilityBounded
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniverseCodeComponentsBounded
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationPiUniverseUniverseAtBounded

-- THE A2 BRIDGE + WIRED CONV ARM (DenoteKeyedBoundedAssemblyBridge): toward the bounded grown-FT assembly. The
-- recursor arms extract a reducible-TYPE-at-bound from a universe-MEMBERSHIP IH -- now a clean cumulativity
-- composition (universeMemberReducibleAsTypeAtDecodedLevelBounded then isReducibleBounded_cumulative via Nat.le_of_lt).
-- reducibleTypeAtBoundUnderSubstFromMembershipBounded is the under-subst wrapper; fundamentalConvArmBounded wires the
-- conv recursor arm (fundamentalConvAtBounded composed with the bridge). The piIntro arm additionally needs member->SN
-- (CR1) at arbitrary scope, blocked by ReducibleTypeAtBounded.isReducibilityCandidate being at scope+1 -- the next residual.
#assert_no_axioms FX1Poly.Typed.reducibleTypeAtBoundFromUniverseMemberBounded
#assert_no_axioms FX1Poly.Typed.reducibleTypeAtBoundUnderSubstFromMembershipBounded
#assert_no_axioms FX1Poly.Typed.fundamentalConvArmBounded

-- Bounded CR1 in member form at the non-empty closing scope (scope+1) -- the piIntro arm's domainArgumentsSN discharge.
-- The bounded reducibility-candidate bundle is at scope+1 (arrow-CR1 var-0 inhabitant), exactly the scope the FT closes
-- into; arbitrary-scope member-SN is structurally blocked (the same var-0 wall in denote too -- denote escapes by keying
-- CR1 on a positive fuel LEVEL, scope-general). The wired piIntro arm consumes this once its motive closes into scope+1.
#assert_no_axioms FX1Poly.Typed.stronglyNormalizing_of_memberAtBoundedSucc

-- THE +1-CLOSING MOTIVE + the piIntro arm with domainArgumentsSN AUTO-DISCHARGED. The grown-FT assembly must close
-- into a non-empty scope targetScope+1 so the binder arm reads member->SN via the scope+1 bounded CR1. FundamentalConcl
-- usionAtBoundedSucc is that motive; .toSucc lifts the shipped arbitrary-scope arms (var/conv/universeFormation/piElim/
-- genFormationPi -- no binder) into it for free; fundamentalPiIntroAtBoundedSucc is the last binder-specific arm, its
-- domainArgumentsSN premise ELIMINATED (discharged internally by stronglyNormalizing_of_memberAtBoundedSucc at the +1 scope).
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtBounded.toSucc
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtBoundedSucc

-- The +1-closing conv + piElim recursor arms (+ the +1 A2 bridge). Mechanical mirrors of the shipped arbitrary-scope
-- arms at the targetScope+1 substitution -- the member-level lemmas (convMember.../applicationMember...) are scope-
-- parametric. With fundamentalPiIntroAtBoundedSucc, the grown-FT arms conv/piIntro/piElim are now all +1-available;
-- only the genFormationPi +1-arm + the formation FT + the HasTypeDescPi.rec dispatch remain.
#assert_no_axioms FX1Poly.Typed.reducibleTypeAtBoundUnderSubstFromMembershipBoundedSucc
#assert_no_axioms FX1Poly.Typed.fundamentalConvArmBoundedSucc
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimAtBoundedSucc

-- The +1-closing former engine + genFormationPi arm. Mirrors of fundamentalTypeFormerAtBounded / fundamentalGenForm
-- ationPiAtBounded over the +1 motive (universeMembershipIntroAtBounded + piTyCode SN are scope-parametric/relation-
-- agnostic). With these, ALL FIVE grown-FT arms (conv/piIntro/piElim/genFormationPi + ofFormation premise) are now
-- +1-available; only the HasTypeDescPi.rec dispatch (motive_2 telescope + bound-exceeds-levels threading) + the
-- formation FT remain before the SN-043 wire.
#assert_no_axioms FX1Poly.Typed.fundamentalTypeFormerAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationPiAtBoundedSucc

-- GATE EXTRACTION -- dissolves the bound-threading. The bounded universeCode arm carries belowBound (denote levelExpr
-- env < bound) as a gate; read backwards, a bound-reducible universe code FORCES that gate. So each grown-FT recursor
-- arm recovers its belowBound LOCALLY from a sub-derivation's reducibility (intro the closing substitution, apply the
-- universe-typing IH, extract) -- NO global "bound exceeds every level in subject" invariant needed. The spine is a
-- 5-arm induction (candidatePiShape style): universeCode carries it, whnfExpand/neutral/piType impossible, ofPointwiseIff recurses.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepBounded.belowBoundOfUniverseCodeShape
#assert_no_axioms FX1Poly.Typed.universeCodeReducibleAtBounded_belowBound

-- POSITIVE complement to the obstruction (DenoteKeyedUniverseBoundedCumulativity): in the BOUNDED regime
-- (denote levelExpr env < ambient), the universe candidate is level-STABLE -- universeDenotePredicate reaches
-- lowerAt only at the fixed index denote e, which the below-family coherence (denoteBelowFamily_eq_reducible)
-- rewrites to the bound-independent ReducibleTypeAtDenote env (denote e). universeDenoteCandidate_boundIndependent:
-- the candidate agrees pointwise at two ambient levels both exceeding denote e. universeReducible_withLowerCandidate
-- _atHigher: cumulativity below the bound (same-candidate transport up via ofPointwiseIff). Together with the
-- obstruction witness this pins the EXACT cumulativity boundary (holds iff universe < ambient); the gap regime
-- is the sole residual = exactly what the bound-carrying refactor (#753) excludes by construction. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.universeDenoteCandidate_boundIndependent
#assert_no_axioms FX1Poly.Typed.universeReducible_withLowerCandidate_atHigher

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

-- DenoteKeyedConvMember (the denote FT's conversion member arm): a denote-reducible member of typeLeft, with
-- Conv typeLeft typeRight + typeRight denote-reducible, is a denote-reducible member of typeRight (via the
-- shipped convTransfer). convMemberUnderClosingSubstitution is the FT-shaped form: pushes the raw conversion
-- under the closing substitution via Conv.subst, then transports. The conversion typing rule, member level.
#assert_no_axioms FX1Poly.Typed.memberConvAtDenote
#assert_no_axioms FX1Poly.Typed.convMemberUnderClosingSubstitution

-- DenoteKeyedMemberForwardClosed (CR2 for the denote relation, UNCONDITIONAL — first piece of the bounded-CR
-- decomposition toward B1'): every denote-reducible type's candidate is forward-closed under Step on members.
-- Uses only the lowerForwardStep leg (unconditional), never the bounded neutralInclusion. Π arm reduces to the
-- codomain CR2 (no domain candidacy ⟹ no bound); universe arm uses lowerForwardStep. Isolates the level bound
-- to CR1's Π-arm + CR3.
#assert_no_axioms FX1Poly.Typed.ReducibleTypeStepDenote.memberForwardClosed

-- DenoteKeyedUniverseMemberBetaExpansion (the UNIVERSE arm of the denote member weak-head β-expansion / the
-- lambda-arm engine toward SN-043/#672): the β-redex app (lam body) arg is a member of the denote universe
-- candidate given its contractum subst0 body arg is. SN conjunct via appLam_isStronglyNormalizing_of_contractum
-- (last tick's neutral arm); the ∃c, lowerAt(denote e) · c conjunct via the lower backward-weak-head-step leg
-- on WeakHeadStep.beta — discharged UNCONDITIONALLY for denoteBelowFamily (backward-step is an implication
-- vacuous above the bound, not the bounded neutral-inclusion existence). So this arm is BOUND-FREE; the level
-- bound is confined to the remaining Π/spine arm (application-SN).
#assert_no_axioms FX1Poly.Typed.universeMemberBetaExpansionAtDenote

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

-- DenoteKeyedAmbientLevelBridge (SN-D5-A2bridge): the single shared deep ingredient of the denote FT's
-- conv/piIntro arms. universeMemberReducibleAtLevel turns a universe MEMBERSHIP at the ambient level into the
-- type's REDUCIBILITY at the ambient level (given denote levelExpr env < level). Real content: candidateIffUniverse
-- unpacking → universeDenotePredicate ∃-conjunct → denoteBelowFamily_eq_reducible (decoded-level reducibility) →
-- ofReducibleTypeStepDenote lift to all levels → project to level. Parametric over EXACTLY the
-- ofReducibleTypeStepDenote composite-domain piArm (at the decoded level's below-family) — the lone deep A2
-- residual = the denote restatement of #672. Consolidates: conv (SN-D5a) + piIntro (SN-D5c) BOTH reduce through
-- this bridge to that one piArm.
#assert_no_axioms FX1Poly.Typed.universeMemberReducibleAtLevel

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
-- SN-D7 (#746): MEMBER strong-normalization for the universe-domain Π fragment over the denote relation
-- (DenoteKeyedUniverseDomainPiMemberSN.lean). The TYPE-level half (universeDomainPi_reducibleAtEveryDenoteLevel
-- + member-stability) supplies the type-level half; this adds the MEMBER-SN payoff. The early win that
-- de-risks SN-D5: it sidesteps the cumulativity obstruction (DenoteKeyedCumulativityObstruction) entirely by
-- fixing ONE ambient level strictly above denote e — no across-level transport — where the Type@e universe
-- candidate is a genuine reducibility candidate (the bounded denoteBelowFamily legs hold via denote e < level)
-- and the shipped denote dependent-arrow CR1 lifts it to the whole Π. universeDomainPiCandidateIsReducibility-
-- Candidate: the dependent-arrow candidate is a Girard CR (domain inhabitant supplied concretely as Type@0).
-- universeDomainPiMemberStronglyNormalizing: a reducible member of Π(X:Type@e).C[X] is SN via that CR's
-- stronglyNormalizing field + ReducibleTypeAtDenote.deterministic. Isolates the residual SN-043 obstruction to
-- ESTABLISHING the codomain reducibility uniformly across levels — no member of the fragment is the obstacle.
#assert_no_axioms FX1Poly.Typed.universeDomainPiCandidateIsReducibilityCandidate
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
-- General-reducibility NORMALIZATION sconing extraction (SN-094 / SN-110 at the logical-predicate level,
-- ReducibilityNormalizationViaSconing.lean). reducibilityScone (SconingWitness) extracts strong normalization;
-- DataMetatheoryViaSconing (#696) bundles SN + reduces-to-value for the DATA axis. Neither delivers the genuine
-- WEAK-NORMALIZATION metatheorem (term reaches a structural normal form). This file adds it at the GENERAL
-- reducibility-candidate level (any IsReducibilityCandidate, any scope): the SECOND concrete sconing witness,
-- whose extraction composes CR1 (candidate => SN) with exists_normalForm_of_isStronglyNormalizing (SN => reaches
-- NF, WeakNormalization.lean). reachesStepNormalForm: the WN predicate. reducibilityNormalizationScone: the
-- normalization sconing witness. normalizationViaSconing: well-typed => reaches NF. ReducibilityMetatheory +
-- reducibilityMetatheoryViaSconing: ONE fundamental => BOTH strong + weak normalization, the general-reducibility
-- "sconing is enough" demonstration (SN-110), strictly beyond DataMetatheory's SN-only. Parametric in the
-- fundamental obligation (honest: gated on SN-043 for the full kernel, discharged on proven fragments); does NOT
-- flip the Tier-0 categorical NormalizationExtraction ledger flag. All zero-axiom.
#assert_no_axioms FX1Poly.Core.reachesStepNormalForm
#assert_no_axioms FX1Poly.Core.reducibilityNormalizationScone
#assert_no_axioms FX1Poly.Core.normalizationViaSconing
#assert_no_axioms FX1Poly.Core.reducibilityMetatheoryViaSconing
-- Decidable conversion from a reducibility candidate + the full-metatheory capstone (the decidability FX wants
-- most, ReducibilityConversionViaSconing.lean). ReducibilityNormalizationViaSconing extracts SN + weak
-- normalization from a candidate; DECIDABLE CONVERSION (the Milestone-A core) is the next free extraction: CR1
-- makes both sides SN, and Conv.decidableOfStronglyNormalizing (Normalize.lean) decides Conv by normalizing each
-- side and comparing -- no global confluence. conversionDecidableViaSconing: the decidability extraction.
-- conversionIffNormalizeEqViaSconing: the semantic NbE characterization (Conv = normalize-equality).
-- ReducibilityFullMetatheory + reducibilityFullMetatheoryViaSconing: ONE fundamental => SN + weak normalization
-- + decidable conversion, the general-reducibility decidable-metatheory capstone (Type-valued: conversion is
-- decision DATA). Parametric in the fundamental (gated on SN-043 for the full kernel, discharged on fragments);
-- NOT the BKS parametricity leg (that needs a binary relation). All zero-axiom.
#assert_no_axioms FX1Poly.Core.conversionDecidableViaSconing
#assert_no_axioms FX1Poly.Core.conversionIffNormalizeEqViaSconing
#assert_no_axioms FX1Poly.Core.reducibilityFullMetatheoryViaSconing
-- First CONCRETE UNCONDITIONAL instantiation of the metatheory capstone (SimplyTypedMetatheoryViaSconing.lean):
-- the closed simply-typed fragment's full decidable metatheory via the sconing route. reducibilityFullMetatheory
-- ViaSconing is parametric in (candidate, fundamental); this exhibits a real inhabitant with NO SN-043 dep:
-- candidate = the SN reducibility candidate (isStronglyNormalizing_isReducibilityCandidate); fundamental = the
-- unconditional simply-typed SN theorem simplyTypedBareClosedStronglyNormalizing (Milestone-A0 floor). Genuine +
-- non-circular: fundamental is "closed simply-typed => SN" (isWellTyped != candidate), then the capstone carries
-- SN => {reaches NF, decidable Conv}. IsClosedSimplyTyped: well-typedness as a bare RawTerm 0 predicate.
-- simplyTypedFullMetatheoryViaSconing: the capstone instance (SN + WN + decidable Conv, unconditional).
-- simplyTypedReachesNormalForm: the WN headline for the fragment (genuinely new). simplyTypedConversionDecidable
-- ViaSconing: decidable Conv via the sconing route (cross-checks the direct Conv.decidableOfSimplyTypedBareClosed).
-- All zero-axiom. Proves the metatheory capstone is inhabited, not a vacuous interface.
#assert_no_axioms FX1Poly.Typed.IsClosedSimplyTyped
#assert_no_axioms FX1Poly.Typed.simplyTypedFullMetatheoryViaSconing
#assert_no_axioms FX1Poly.Typed.simplyTypedReachesNormalForm
#assert_no_axioms FX1Poly.Typed.simplyTypedConversionDecidableViaSconing
-- First concrete RawCategory instance for FX (FxRenamingCategory.lean, toward SN-083/084 fxBaseRMC). The Tier-0
-- categorical interfaces (RawCategory / RepresentableMapCategory / GlobalSections / SconingObject) are
-- obligation-shape interfaces; fxRenamingCategory builds the first concrete FX inhabitant: the
-- renaming (thinning) category, objects = scopes (Nat), morphisms = positional renamings (RawRenaming = Fin
-- source -> Fin target). All three category laws hold definitionally (function-comp associativity + definitional
-- eta), so it is a genuine complete category, not a stub. HONEST SCOPE: this is the renaming/thinning base (the
-- variable-reindexing category NbE presheaf models live over), the underlying-category first piece of fxBaseRMC;
-- the full RepresentableMapCategory additionally needs term substitutions as morphisms + a representable-map
-- class with the 3 CwR axioms (pullback-universal-property in particular), deferred. fxRenamingCategory_identity
-- _eq / _compose_eq: the categorical identity/composition ARE the renaming identity/composition (defeq samples).
-- All zero-axiom (no funext -- renaming function-equality would pull Quot.sound).
#assert_no_axioms FX1Poly.Tier0.fxRenamingCategory
#assert_no_axioms FX1Poly.Tier0.fxRenamingCategory_identity_eq
#assert_no_axioms FX1Poly.Tier0.fxRenamingCategory_compose_eq
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
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingCategory
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingCategory_identity_eq
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingCategory_compose_eq
-- The EXTENSIONAL data-morphism renaming category (FxBaseRenamingVecCategory.lean, SN-084) — the base that
-- finally proves lookup-extensionality, the lemma RenamingTo above had to AVOID. Same morphism content (a
-- length-source tuple of Fin target images), but reified as a PRODUCT recursion (RenamingVec target 0 = PUnit,
-- ... (source+1) = Fin target x ...) instead of an indexed inductive. Products have DEFINITIONAL eta, so ext
-- (two vectors with equal lookups are equal) falls out of a structural induction with NO impossible-case eqn
-- lemmas and NO propext -- the exact lemma RenamingTo could not prove, and the lemma the CwR pullback's universal
-- property needs (conclude morphism equality from pointwise-equal lookups). With ext the three category laws go
-- DIRECTLY pointwise (compose_assoc via a lookup_compose calc chain; identity_compose/_identity via
-- lookup_compose + identity_lookup), no mapImages fusion. weakening_unique: the display map is UNIQUELY
-- characterized by its action (ext-powered, unstatable over RenamingTo) -- the shape the CwR representable-map
-- axioms need. faithful: ext at the category level (lookup determines the morphism; the reification is faithful).
-- ADDITIVE: RenamingTo / fxBaseRenamingCategory retained untouched; RenamingVec is the strictly-more-capable
-- sibling carrying the extensional content. HONEST SCOPE: the extensional underlying-category base of fxBaseRMC;
-- the pullback rung (now POSSIBLE here, unlike over RenamingTo) + the 3 CwR axioms are the next task. All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.RenamingVec.lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.lookup_zero
#assert_no_axioms FX1Poly.Tier0.RenamingVec.lookup_succ
#assert_no_axioms FX1Poly.Tier0.RenamingVec.ext
#assert_no_axioms FX1Poly.Tier0.RenamingVec.lookup_mapImages
#assert_no_axioms FX1Poly.Tier0.RenamingVec.lookup_compose
#assert_no_axioms FX1Poly.Tier0.RenamingVec.identity_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.compose_assoc
#assert_no_axioms FX1Poly.Tier0.RenamingVec.identity_compose
#assert_no_axioms FX1Poly.Tier0.RenamingVec.compose_identity
#assert_no_axioms FX1Poly.Tier0.RenamingVec.weakening_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.identity_succ_eq
#assert_no_axioms FX1Poly.Tier0.RenamingVec.weakening_unique
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecCategory
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecCategory_identity_eq
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecCategory_compose_eq
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecCategory_faithful
-- The categorical isomorphisms of the EXTENSIONAL renaming base (FxBaseRenamingVecIsomorphism.lean, SN-085) — the
-- iso-class CwR-axiom CONTENT. isomorphismOfLookupInverse is the ext-powered iso constructor: forward + backward +
-- two pointwise round-trips ⟹ IsIsomorphism, the inverse laws (morphism equalities) discharged by RenamingVec.ext
-- (over the function base this would need funext/Quot.sound; over RenamingTo it leaks propext — so this is the
-- direct payoff of the extensional base). swapTwo/_involutive/IsIsomorphism: a concrete NON-IDENTITY iso (var-0/1
-- swap on scope 2, self-inverse) — non-vacuity (the iso class ⊋ {identity}), Fin 2 matched structurally (no
-- Fin.cases). IsCategoricalIsomorphism + _identity/_compose/_pullback: the THREE iso-class CwR-axiom contents
-- (contains identity, closed under composition via generic IsIsomorphism.comp, closed under pullback via generic
-- pullbackAlong with identity right-projection), Nonempty witnesses extracted by Prop-matching (no Classical).
-- HONEST SCOPE: this is the CwR-axiom CONTENT, not yet the RepresentableMapCategory RECORD — that needs a
-- MorphismClass whose memberDecidable decides Nonempty (IsIsomorphism ...) = whether a RenamingVec is a finite
-- bijection, a separate Init-only propext-risky Fin-combinatorics sub-problem, the ONLY remaining piece. The iso
-- class is the right representable class precisely because its pullbacks exist GENERICALLY (pullbackAlong). All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isomorphismOfLookupInverse
#assert_no_axioms FX1Poly.Tier0.RenamingVec.swapTwo
#assert_no_axioms FX1Poly.Tier0.RenamingVec.swapTwo_involutive
#assert_no_axioms FX1Poly.Tier0.RenamingVec.swapTwoIsIsomorphism
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isCategoricalIsomorphism_identity
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isCategoricalIsomorphism_compose
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isCategoricalIsomorphism_pullback
-- Reification ≅ function-space bijection + decidable equality for RenamingVec (FxBaseRenamingVecTabulate.lean,
-- SN-085a substrate). tabulate = the constructive companion to lookup (build a RenamingVec from an image function);
-- tabulate_lookup (lookup∘tabulate=id) + tabulate_lookup_self (tabulate∘lookup=id via ext) exhibit RenamingVec
-- target source ≅ (Fin source → Fin target). decEq + instance = structural zero-axiom DecidableEq (head via
-- Nat.decEq on .val + Fin.eq_of_val_eq, dodging Fin.decEq/Fin.cases propext). These are the foundation the
-- finite-bijectivity iso-decider (#914) builds on: the candidate inverse of an iso is tabulate of its preimage
-- function, the round-trip checks are RenamingVec equalities decided by the instance. All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tabulate
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tabulate_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tabulate_lookup_self
#assert_no_axioms FX1Poly.Tier0.RenamingVec.decEq
#assert_no_axioms FX1Poly.Tier0.instDecidableEqRenamingVec
-- The preimage search over a RenamingVec (FxBaseRenamingVecPreimage.lean, SN-085a search core toward #914's
-- memberDecidable). findPreimage walks the product structure for the first position whose image = targetIndex
-- (reconstructed as a Fin source), none if unhit; the candidate inverse of an iso is tabulate of this preimage
-- function. findPreimage_succ_eq = the rfl reduction equation (so proofs avoid unfold). findPreimage_some =
-- SOUNDNESS (found position maps to the target ⟹ candidate is a right-inverse section). findPreimage_none =
-- COMPLETENESS (none ⟹ target unhit ⟹ the decider's not-surjective isFalse branch, since an iso's inverse would
-- supply a preimage). Head compared by Nat.decEq match (not if/by_cases = Classical); proofs case on it + a
-- computed reduced equation (no unfold/simp), nomatch for impossible Options, Fin index split structurally (no
-- Fin.cases). All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.RenamingVec.findPreimage
#assert_no_axioms FX1Poly.Tier0.RenamingVec.findPreimage_succ_eq
#assert_no_axioms FX1Poly.Tier0.RenamingVec.findPreimage_some
#assert_no_axioms FX1Poly.Tier0.RenamingVec.findPreimage_none
-- The Option-valued tabulate (FxBaseRenamingVecTryTabulate.lean, SN-085a candidate-inverse core toward #914).
-- tryTabulate (imageOf : Fin length → Option (Fin target)) : Option (RenamingVec target length) succeeds iff
-- every image is some; composed with findPreimage it builds the candidate inverse (some backward iff surjective).
-- tryTabulate_succ_eq = rfl reduction. tryTabulate_lookup = SOUNDNESS (success ⟹ every image agrees with the
-- built vector's lookup ⟹ candidate is a right-inverse SECTION). tryTabulate_none = COMPLETENESS (failure ⟹ some
-- image was none ⟹ the not-surjective isFalse branch). Reasoned propext-clean via rw [succ_eq] at h; split at h
-- (split REDUCES the matcher where rw won't), case h_1/h_2 for naming, Option.map_none/_some rfl-lemmas, nomatch
-- for impossible Options, Fin index split structurally. All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate_succ_eq
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate_lookup
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryTabulate_none
-- ★ THE COMPLETE RepresentableMapCategory over the extensional renaming base (FxBaseRenamingVecRMC.lean,
-- SN-085a/SN-085/SN-084, closes #210/#914). The finite-bijectivity decider, PIGEONHOLE-FREE: tryInverse :=
-- tryTabulate ∘ findPreimage (some backward iff surjective); tryInverse_rightInverse(_composed) = the candidate is
-- a RIGHT inverse by construction; tryInverse_none_notSurjective = failure exhibits an unhit index;
-- isIsomorphism_inverse_rightInverse = extract the pointwise inverse from an IsIsomorphism witness;
-- tryInverse_unique = INVERSE UNIQUENESS by pure function-algebra (backward = backward∘id = backward∘(forward∘g) =
-- (backward∘forward)∘g = id∘g = g — NO cardinality); decideIsCategoricalIsomorphism = the decider (none ⟹ isFalse
-- via a hypothetical iso's preimage; some ⟹ decEq the left inverse, isTrue ⟹ isomorphismOfLookupInverse, isFalse ⟹
-- inverse-uniqueness). fxBaseRenamingVecRepresentableMaps = the MorphismClass; fxBaseRenamingVecRMC = THE record
-- (3 CwR axioms wired to isCategoricalIsomorphism_{pullback,identity,compose}). First genuine non-degenerate
-- data-morphism extensional CwR for FX. All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryInverse
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryInverse_rightInverse
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryInverse_rightInverse_composed
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryInverse_none_notSurjective
#assert_no_axioms FX1Poly.Tier0.RenamingVec.isIsomorphism_inverse_rightInverse
#assert_no_axioms FX1Poly.Tier0.RenamingVec.tryInverse_unique
#assert_no_axioms FX1Poly.Tier0.RenamingVec.decideIsCategoricalIsomorphism
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecRepresentableMaps
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecRMC
-- The GlobalSections instance over the extensional renaming base (FxBaseRenamingVecGlobalSections.lean, SN-089,
-- #592). The canonical global-sections functor is the REPRESENTABLE presheaf Hom(-, T): sections X = Morphism X T,
-- sectionMap = precomposition, functoriality = the category's identity/assoc laws. GlobalSections.representable =
-- this presheaf over ANY RawCategory (mapsIdentity = identityLeft, mapsComposition = composeAssoc), reusable for
-- any future CwR base. In the renaming category the terminal object is scope 1 (Hom(X,1) singleton — every source
-- var maps to var 0; scope 0 is NOT terminal, Hom(X,0) empty for X>0): finOneIsZero = Fin 1 subsingleton by
-- structural index split (no Fin.cases); fxBaseRenamingVecScopeOneTerminal = terminality via RenamingVec.ext +
-- finOneIsZero; fxBaseRenamingVecGlobalSections = the instance at scope 1; the subsingleton smoke = "exactly one
-- closed renaming into the terminal". Honest scope: the standard representable-at-terminal global-sections shape
-- (the structural prerequisite the SconingObject/SconingPreservation ladder parameterizes over); NOT a
-- non-vacuous canonicity-extracting realization presheaf (that needs a term-carrying CwR base, SN-086/088). All
-- zero-axiom (no funext, no Fin.cases, (1:Nat) ascription fixes the Object-projection OfNat).
#assert_no_axioms FX1Poly.Tier0.GlobalSections.representable
#assert_no_axioms FX1Poly.Tier0.finOneIsZero
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecScopeOneTerminal
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecGlobalSections
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecGlobalSections_terminal_subsingleton
-- The concrete SconingPreservation instance over the extensional renaming base
-- (FxBaseRenamingVecSconingPreservation.lean, SN-090, #593). The first concrete BKS SconingPreservation witness
-- for a genuine FX CwR (fxBaseRenamingVecRMC). liftsRepresentable = the REINDEXING lift: for f : A ⟶ B, the
-- source sconing object (A, Γ(B), sectionMap f) reindexes tautological-B along f, target = tautological-B (id),
-- semantic map = id, gluing square = rfl (uniform over ALL base morphisms — the representability hypothesis is
-- unused, a strengthening). liftsPullbacks = the tautological object over square.pullbackObject
-- (projectsToPullback = rfl). Honest scope: existence-level preservation witness (SconingPreservation carries
-- only projectsToPullback, no inter-lift coherence, so it's inhabitable over any (RMC, GlobalSections) — the
-- content is realizing it correctly over the FX renaming base); the canonicity/normalization/parametricity
-- TRANSFER strength lives in the extraction records' laws (SN-093..096), and this file deliberately does NOT
-- advance fxSconingConstructionLevel (it tracks the full FX base; renaming is a precursor). Zero-axiom: structure
-- population over sectionMap (SN-089) + SconingObject.tautological + two rfl laws, no funext.
#assert_no_axioms FX1Poly.Tier0.fxBaseRenamingVecSconingPreservation
-- The EXTENSIONAL substitution representation (FxBaseSubstVec.lean) — the FIRST brick of the TERM-CARRYING CwR
-- base (the contexts-and-substitutions category the sconing ladder SN-086/088/091/093-096 needs; the renaming
-- base carries no term content). RawTermSubst source target := Fin source → RawTerm target is FUNCTION-typed, so
-- its morphism extensionality (∀i, s1 i = s2 i → s1 = s2) IS funext (leaks Quot.sound) — the EXACT trap the
-- RenamingVec arc solved for renamings. SubstVec is the substitution analogue: same length-source tuple but of
-- RawTerm target payloads, PRODUCT-recursive (PUnit / RawTerm × SubstVec), so ext falls out via definitional
-- product eta with NO funext. SubstVec + lookup (+zero/succ) + ext (THE lemma RawTermSubst can't get zero-axiom) +
-- tabulate (build from a function) + lookup_tabulate (function round-trips, pointwise to avoid funext) +
-- tabulate_lookup (vec round-trips via ext, zero-axiom) + toRawTermSubst bridge (+ round-trip) exhibiting
-- SubstVec ≅ RawTermSubst. SUBSTRATE only — the substitution CATEGORY (identity/compose/laws) + RMC + sconing
-- instances are LATER bricks of this multi-firing arc. All zero-axiom (RenamingVec port, Prod.ext + structural
-- induction, no funext).
#assert_no_axioms FX1Poly.Tier0.SubstVec
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_zero
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_succ
#assert_no_axioms FX1Poly.Tier0.SubstVec.ext
#assert_no_axioms FX1Poly.Tier0.SubstVec.tabulate
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_tabulate
#assert_no_axioms FX1Poly.Tier0.SubstVec.tabulate_lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.toRawTermSubst
#assert_no_axioms FX1Poly.Tier0.SubstVec.toRawTermSubst_tabulate
-- The TERM-CARRYING RawCategory of contexts-and-substitutions (FxBaseSubstCategory.lean, brick 2 of the
-- term-carrying CwR arc). Lifts the function-level RawTermSubst algebra onto SubstVec via lookup/ext and assembles
-- fxBaseSubstCategory : RawCategory (objects = scopes, morphisms source⟶target = SubstVec target source carrying
-- real RawTerm content — unlike the renaming base's variable reindexings). SubstVec.identity(+identity_lookup) +
-- compose(+lookup_compose, the genuine subst action: subst secondVec into firstVec's image) + the 3 category laws
-- via ext: identity_compose (LEFT id = subst-of-var rfl, needs explicit rfl after the reducible-only rw),
-- compose_identity (RIGHT id via subst_pointwise bridging identity.toRawTermSubst≐RawTermSubst.identity +
-- subst_identity_apply), compose_assoc (the shipped RawTerm.subst_compose subst-then-subst law + subst_pointwise).
-- fxBaseSubstCategory + _identity_eq/_compose_eq defeq-sample bridges (the shape the sconing ladder consumes).
-- Honest scope: the underlying TERM-carrying RawCategory; the representable-map class + CwR axioms + sconing
-- instances over THIS base are later bricks. All zero-axiom (tabulate/lookup_tabulate + shipped subst lemmas, NO
-- funext — the whole point of SubstVec).
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity_lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity_compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose_identity
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose_assoc
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory_identity_eq
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory_compose_eq
-- The display / weakening substitution (FxBaseSubstWeakening.lean, brick 3 of the term-carrying CwR arc). The
-- first distinguished morphism the comprehension structure needs: SubstVec.weakening scope : SubstVec (scope+1)
-- scope, the substitution scope⟶scope+1 sending each variable i to the term var(i+1) (past the freshly-bound
-- variable 0) — the term-carrying analogue of RenamingVec.weakening. weakening_lookup (the shifted-var term, via
-- lookup_tabulate) + weakening_lookup_eq_rename (lookup agrees with the weakening RENAMING on a variable) +
-- weakening_unique (uniquely characterized by its action, via ext). weakening_subst_eq_rename is the DEEP
-- coherence: the weakening SUBSTITUTION acts on EVERY term as the weakening renaming (subst weakening = rename
-- weaken on the whole term algebra, not merely on variable lookups) — via subst_identity_apply +
-- rename_subst_commute (folding rename into weaken.thenSubst identity) + subst_pointwise against weakening_lookup.
-- Honest scope: the display map ITSELF + its renaming coherence; the cons comprehension + the universal property
-- (β/weakening cancellation) are the next brick. All zero-axiom (no funext).
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_lookup_eq_rename
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_unique
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_subst_eq_rename
-- The context-extension / comprehension structure (FxBaseSubstComprehension.lean, brick 4 of the term-carrying
-- CwR arc). The dual of the display map: SubstVec.cons headTerm tailVec : SubstVec target (source+1) extends a
-- substitution with a head term (literally the product pair) — the morphism source+1⟶target sending the fresh
-- variable 0 to headTerm and i+1 to tailVec i; the extensional analogue of RawTermSubst.cons. cons_lookup_zero
-- (v-law, head recovery, rfl) + cons_lookup_succ (tail recovery, rfl). weakening_compose_cons is the p-law /
-- comprehension β-cancellation: weakening.compose (cons head tail) = tail (the display map projects the extended
-- context onto its base) — via ext + lookup_compose + weakening_lookup + subst-of-var rfl. cons_unique is the
-- comprehension UNIVERSAL PROPERTY: the extension is the UNIQUE morphism whose display-projection is the tail and
-- whose zeroth lookup is the head (ext + projecting projectsToTail at each succ position). cons_toRawTermSubst:
-- SubstVec.cons IS RawTermSubst.cons pointwise (the β-engine's binder-extension). All zero-axiom (no funext).
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_lookup_zero
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_lookup_succ
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_cons
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_toRawTermSubst
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_unique
-- The single-substitution / β-contraction section (FxBaseSubstSingleton.lean, brick 5 of the term-carrying CwR
-- arc). The most important INSTANCE of comprehension: SubstVec.singleton rawArg := cons rawArg (identity scope) :
-- SubstVec scope (scope+1), the morphism scope+1⟶scope sending fresh var 0 to rawArg and shifting the rest down —
-- EXACTLY the substitution canonical β-reduction runs (app (lam body) arg ↝ subst0 body arg). singleton_lookup_zero
-- (head = arg, rfl). weakening_compose_singleton is the genuine CwF content: the β-contraction is a SECTION of the
-- display map (weakening.compose (singleton arg) = identity, the SUBSTVEC-4 p-law at the identity tail).
-- singleton_toRawTermSubst: the categorical singleton IS RawTermSubst.singleton pointwise (match: head rfl, tail
-- identity_lookup). subst_singleton_eq_subst0 is THE operational β bridge: subst via the categorical singleton =
-- RawTerm.subst0 (the de Bruijn β-reduct the Step relation references), via subst_pointwise (subst0 @[reducible] =
-- subst singleton). All zero-axiom (no funext). [Full fxBaseSubstRMC deferred: subst-iso decider is multi-step;
-- term base has NO terminal object so its GlobalSections differs from the renaming base — see file docstring.]
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton_lookup_zero
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton_toRawTermSubst
#assert_no_axioms FX1Poly.Tier0.SubstVec.subst_singleton_eq_subst0
-- The closed-terms GlobalSections over the term base (FxBaseSubstGlobalSections.lean, brick 6 of the term-carrying
-- CwR arc). The renaming base's GlobalSections (SN-089) is Hom(-, 1) at the TERMINAL object — a subsingleton, NOT
-- a closed-terms functor (the renaming category has no term content). The subst category has NO terminal object
-- (SubstVec target X never a singleton for X≥1) but HAS an INITIAL object scope 0, so the canonical functor is the
-- representable Hom(-, 0): sections X = Morphism X 0 = SubstVec 0 X = the X closed terms closing an X-var context.
-- fxBaseSubstGlobalSections (= GlobalSections.representable at scope 0, reusing the generic def) +
-- sections_eq (sections X = SubstVec 0 X, rfl). closedTermAsSection/sectionAsClosedTerm + the two round-trips
-- (rfl, via cons_lookup_zero + product/PUnit eta) = the iso sections 1 ≅ RawTerm 0 (global elements ARE closed
-- terms). closedTermAsSection_injective = the NON-VACUITY witness: the closed-terms presheaf faithfully embeds
-- RawTerm 0 (contrast the renaming base's subsingleton-at-terminal) — the FIRST canonicity-relevant GlobalSections
-- for FX. All zero-axiom. [Section index 1 on the concrete SubstVec 0 1 to dodge OfNat-on-Object.]
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstGlobalSections
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstGlobalSections_sections_eq
#assert_no_axioms FX1Poly.Tier0.closedTermAsSection
#assert_no_axioms FX1Poly.Tier0.sectionAsClosedTerm
#assert_no_axioms FX1Poly.Tier0.sectionAsClosedTerm_closedTermAsSection
#assert_no_axioms FX1Poly.Tier0.closedTermAsSection_sectionAsClosedTerm
#assert_no_axioms FX1Poly.Tier0.closedTermAsSection_injective
-- The first non-trivial sconing OBJECT over the term base (FxBaseSubstScone.lean, brick 7 of the term-carrying CwR
-- arc). SconingObject (InternalSconing.lean) needs only a GlobalSections (the RMC-gated parts are
-- SconingLift/SconingPreservation), so it's buildable over the term base NOW. fxBaseSubstClosedTermScone glues the
-- closed terms RawTerm 0 onto the global sections of the single-variable context via the SUBSTVEC-6 iso
-- closedTermAsSection (a genuine syntactic-term realization, NOT the tautological id the renaming base was limited
-- to) — the first sconing object for FX whose semantic domain is a real term type realized into real closed-term
-- sections. _realizationInjective = FAITHFUL (non-degenerate, via closedTermAsSection_injective).
-- closedTermSconeToTautological/tautologicalToClosedTermScone = mutually-inverse SconingMorphisms to/from the
-- tautological scone at scope 1, exhibiting the closed-term scone as the RawTerm 0-presentation of the canonical
-- global-sections scone (commutes via mapsIdentity; reverse first rw's the round-trip). [comp=identity NOT proved:
-- SconingMorphism eq compares semanticMaps as functions = funext-leaks-Quot.sound; the SUBSTVEC-6 round-trips
-- witness mutual-inverseness pointwise instead.] All zero-axiom. Section index 1 = (1 : Nat) ascription.
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstClosedTermScone
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstClosedTermScone_realizationInjective
#assert_no_axioms FX1Poly.Tier0.closedTermSconeToTautological
#assert_no_axioms FX1Poly.Tier0.tautologicalToClosedTermScone
-- The Path-A witness → Tier-0 categorical scone bridge (FxBaseSubstWitnessScone.lean, brick 8). FX has TWO sconing
-- framings: CONCRETE (Core/SconingWitness.lean — a SconingWitness isWellTyped isCanonical = the Path-A logical
-- relation: computable predicate + fundamental obligation + extraction obligation, whose composite is canonicity;
-- reducibilityScone builds one from a reducibility candidate) and ABSTRACT (Tier0/InternalSconing.lean — the
-- categorical SconingObject). witnessScone bridges them: ANY closed-scope SconingWitness induces a Tier-0
-- SconingObject over the term base, semantic domain = the COMPUTABLE (hence canonical) subset { t : RawTerm 0 //
-- witness.computable t }, realization = closedTermAsSection∘Subtype.val. The FIRST predicate-carrying Tier-0 scone
-- (SUBSTVEC-7's carried bare RawTerm 0). _realizationInjective (FAITHFUL, via Subtype.ext+closedTermAsSection_injective)
-- + _semanticIsCanonical (the semantic domain consists of CANONICAL closed terms, = witness.extraction applied to
-- .property — the categorical scone CARRIES the canonicity content) + witnessSconeToClosedTermScone (embeds into
-- fxBaseSubstClosedTermScone via Subtype.val, commutes by mapsIdentity = SUB-scone). The term-base instance of the
-- "sconing is enough" thesis (SN-110): the reducibility witness IS a categorical sconing object. All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.witnessScone
#assert_no_axioms FX1Poly.Tier0.witnessScone_realizationInjective
#assert_no_axioms FX1Poly.Tier0.witnessScone_semanticIsCanonical
#assert_no_axioms FX1Poly.Tier0.witnessSconeToClosedTermScone
-- Concrete data-canonicity scones over the term base (FxBaseSubstConcreteScone.lean, brick 9, capstone of the
-- term-carrying CwR arc). Grounds the SUBSTVEC-8 generic witnessScone bridge in the shipped data-reducibility
-- candidates (DataReducibilityCoverage.lean, SN-082): each candidate becomes a reducibilityScone (SN-092, identity
-- fundamental — candidate membership IS the well-typed predicate, the honest "candidate member ⟹ SN" witness via
-- CR1) and witnessScone lifts it to a concrete predicate-carrying categorical scone. boolValueScone = the scone
-- whose semantic domain is the BOOL-canonical closed terms (CanonicalFormsPredicate boolIsValue); its
-- _semanticIsStronglyNormalizing (the domain is SN closed terms, via witnessScone_semanticIsCanonical = CR1) +
-- _inhabited (NON-VACUITY: boolTrueCell is a member, so not an empty predicate). emptyValueScone = the CONSISTENCY
-- scone whose semantic domain is the EMPTY-canonical closed terms; its _semanticIsUninhabited (the domain is EMPTY,
-- via emptyFamilyCandidateHasNoClosedMember = the categorical consistency core, a non-trivial sconing object whose
-- semantic domain is the genuine bottom). The term-base categorical analog of the Core track's bool-canonicity /
-- consistency-via-sconing. Honest scope: identity fundamental (isWellTyped := candidate), NOT HasTypeDescPi typing;
-- IsStronglyNormalizing lives in FX1Poly.Core.StepStar. All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.boolValueScone
#assert_no_axioms FX1Poly.Tier0.boolValueScone_semanticIsStronglyNormalizing
#assert_no_axioms FX1Poly.Tier0.boolValueScone_inhabited
#assert_no_axioms FX1Poly.Tier0.emptyValueScone
#assert_no_axioms FX1Poly.Tier0.emptyValueScone_semanticIsUninhabited
-- Generic categorical isomorphism infrastructure for the CwR axioms (IsomorphismCategorical.lean, toward
-- SN-084/085). For the smallest valid representable-map class -- the isomorphisms -- the three CwR axioms reduce
-- to three BASE-INDEPENDENT generic facts (hold in any RawCategory, reusable whether fxBaseRMC ends up over the
-- renaming or the substitution category): isomorphismsRepresentable (trivial), closedUnderComposition (<= comp),
-- closedUnderPullback (<= pullbackAlong). IsIsomorphism.identity: the identity is an iso. IsIsomorphism.comp:
-- isos compose ((f.g)^-1 = g^-1.f^-1). IsIsomorphism.pullbackAlong: the pullback of an iso f along any g is the
-- square (apex = dom g, right proj = identity, left proj = g.f^-1) with its universal property -- right proj is
-- the identity (an iso, hence representable). All pure equational reasoning through the RawCategory law fields +
-- the IsIsomorphism inverse laws; NO funext (morphism extensionality would pull Quot.sound). All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.IsIsomorphism.identity
#assert_no_axioms FX1Poly.Tier0.IsIsomorphism.comp
#assert_no_axioms FX1Poly.Tier0.IsIsomorphism.pullbackAlong
-- The FIRST concrete zero-axiom RepresentableMapCategory for FX (FxThinScopeRMC.lean, SN-084/085). The renaming
-- category's FUNCTION morphisms can't host a zero-axiom RMC -- every CwR equality (pullback commutes/universal,
-- iso inverse laws) is a function equality needing funext (Quot.sound). Escape: a THIN (preorder) base, where a
-- morphism a->b is a Prop-proof PLift(a<=b), so proof irrelevance (definitional, NOT an axiom) makes every
-- morphism equality free (rfl). thinScopeCategory: the scope-inclusion preorder (objects = scopes Nat, morphism
-- = a<=b). thinScopeRepresentableMaps: the equal-scope (iso) class, decidable via Nat.decEq. thinScopeRMC: all 3
-- CwR axioms genuine -- closedUnderPullback via the MEET (pullbacks in a poset are meets; greatest common
-- sub-scope + universal property), isomorphismsRepresentable via antisymmetry, closedUnderComposition via
-- transitivity. meetScopes + its 4 facts: a propext-free structural min (core Nat.min leaks propext) proved by
-- Nat induction over the clean le primitives. Honest scope: the degenerate THIN instance, establishing the
-- Tier-0 interface is inhabitable; NOT the full renaming/substitution CwR (that needs data morphisms). All
-- zero-axiom (no funext, no Nat.min).
#assert_no_axioms FX1Poly.Tier0.meetScopes
#assert_no_axioms FX1Poly.Tier0.meetScopes_le_left
#assert_no_axioms FX1Poly.Tier0.meetScopes_le_right
#assert_no_axioms FX1Poly.Tier0.le_meetScopes
#assert_no_axioms FX1Poly.Tier0.meetScopes_eq_right_of_le
#assert_no_axioms FX1Poly.Tier0.thinScopeCategory
#assert_no_axioms FX1Poly.Tier0.thinScopeRepresentableMaps
#assert_no_axioms FX1Poly.Tier0.thinScopeRMC
-- GlobalSections over the thin scope CwR via the Yoneda representable presheaf (FxThinScopeGlobalSections.lean,
-- next Tier-0 sconing-pipeline rung above the thin RMC). sections scope = Hom(scope, topScope) = PLift(scope <=
-- topScope); the contravariant action precomposes by Nat.le_trans; both functor laws are rfl (sections are
-- Prop-proofs, so proof irrelevance makes parallel sections equal -- no funext). thinScopeSections: the
-- representable presheaf as a literal-Nat family (dodges the LE .Object synth trap). thinScopeGlobalSections:
-- the GlobalSections instance. thinScopeTautologicalSconing: SconingObject.tautological inhabits over it. A
-- genuine canonical presheaf (Yoneda), establishing the GlobalSections/SconingObject interfaces are inhabitable
-- zero-axiom; honestly the representable, NOT the "closed terms" CwR semantics (needs the data-morphism base).
#assert_no_axioms FX1Poly.Tier0.thinScopeSections
#assert_no_axioms FX1Poly.Tier0.thinScopeGlobalSections
#assert_no_axioms FX1Poly.Tier0.thinScopeTautologicalSconing

-- Bound-carrying telescope-reducibility relation (DenoteKeyedBoundedTelescopeReducible.lean) — the motive_2
-- shape for the grown-FT HasTypeDescPi.rec dispatch. The bound-carrying analogue of TelescopeReducibleAtDenote,
-- carrying TWO nat levels: `bound` (each child head a bound-reducible member of its universe code) and `argLevel`
-- (the tail's domain argument quantification level = the former's decoded output level, strictly below `bound` by
-- gate-extraction). twoChild is the Π/Σ-former unfolder (consecutiveShifts 0 2), the shape the bounded
-- genFormationPi arm reads domain/codomain reducibility off before lifting via free bounded cumulativity.
-- Structural-recursion def on `count` + nil (True.intro) + twoChild (anonymous conjunction constructor).
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtBounded
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtBounded.nil
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtBounded.twoChild

-- Bound-carrying telescope fundamental-theorem companion arms (DenoteKeyedBoundedTelescopeFundamental.lean) — the
-- nil/cons minor-premise bodies that PRODUCE TelescopeReducibleAtBounded, the bound-carrying analogue of
-- fundamentalTelescopeNil/ConsAtDenote. nil is True.intro; cons reads the head member off its
-- FundamentalConclusionAtBounded (head member at `bound` via subst_universeCodeCell) and threads the tail premise
-- (argument at `argLevel`). Non-recursive minor-premise bodies the eventual HasTypeDescPi/DescTelescopePi FT
-- recursor discharges; no induction, no funext.
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeNilAtBounded
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtBounded

-- Two-child bounded telescope projection (DenoteKeyedBoundedTelescopeProjection.lean) — reads the domain +
-- codomain bound-reducible universe-members off the depth-0/count-2 Π/Σ telescope in the EXACT shape
-- piReducibleAsTypeFromNonUniformLevelMemberBounded consumes; codomain reshaped subst(cons)→subst0(subst(lift))
-- via RawTerm.subst_cons_eq_subst0_lift. The telescope→discharge bridge for the genFormationPi recursor arm.
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtBounded.twoChildMembers
-- GTL-11 bounded substrate: the one-child [0] data-former analogue (listCode / optionCode) — a pure
-- telescope.1 projection (no codomain reshaping, the data former is non-dependent), feeding the bounded
-- genFormationPi data-former arm.
#assert_no_axioms FX1Poly.Typed.TelescopeReducibleAtBounded.oneChildMember

-- Π/Σ-former output-level bounds (FormerOutputLevelBounds.lean) — the genFormationPi belowOutput premises:
-- each child level ≤ the former's lmaxAll output level. lmaxAll [a,b] = lmax a b (definitional fold collapse);
-- denote_lmax → structural levelMax; levelMax_le_left/right re-derived (the ClassifierLevelMeasure ones are
-- file-private). Feeds piReducibleAsTypeFromNonUniformLevelMemberBounded's domainBelowOutput/codomainBelowOutput.
#assert_no_axioms FX1Poly.Typed.levelMax_le_left
#assert_no_axioms FX1Poly.Typed.levelMax_le_right
#assert_no_axioms FX1Poly.Typed.lmaxAll_pair
#assert_no_axioms FX1Poly.Typed.denote_domainLevel_le_lmaxAll_pair
#assert_no_axioms FX1Poly.Typed.denote_codomainLevel_le_lmaxAll_pair

-- Open-codomain SN from a bounded FILLED codomain member (BoundedCodomainOpenSN.lean) — the genFormationPi
-- codomainSN premise. The bounded telescope gives the codomain filled at an argument (subst0 (subst (lift σ)
-- codomain) arg); bounded CR1 (stronglyNormalizing_of_memberAtBoundedSucc) → SN of the instance; the
-- relation-agnostic IsStronglyNormalizing.ofSubst0Body reflects it to the OPEN body subst (lift σ) codomain.
-- The hardest sub-piece of the genFormationPi recursor arm (BFT-4), via shipped primitives only.
#assert_no_axioms FX1Poly.Typed.codomainOpenStronglyNormalizing_ofBoundedFilledMember

-- Last two genFormationPi recursor-arm prerequisites (BoundedDomainInhabitant.lean): levelMax_lt (the output
-- belowBound — max of two below-bound child levels is below bound, via LevelExpr.levelMax_le); and
-- variableZeroMemberOfBoundedUniverseMember (the var-0 neutral inhabits the cumulatively-lifted domain candidate
-- at argLevel: decode universe member → reducible type at its level → isReducibleBounded_cumulative lift →
-- IsReducibilityCandidate.containsVariable). The argument the genFormationPi arm feeds the codomain telescope.
#assert_no_axioms FX1Poly.Typed.levelMax_lt
#assert_no_axioms FX1Poly.Typed.variableZeroMemberOfBoundedUniverseMember

-- The bounded genFormationPi recursor arm (BoundedGenFormationPiFromTelescope.lean) — a two-child Π/Σ former is a
-- +1-closing fundamental member of Type@(lmaxAll levels) from the telescope IH. Builds the universe member INSIDE
-- the ∀ (resolving the belowBound threading: every level bound extracted per-substitution, no canonical env),
-- lifting children to the output level by free bounded cumulativity (the non-uniform case). Composes ALL the BFT
-- pieces: twoChildMembers + gate-extraction + variableZeroMember + levelMax_lt + belowOutput + codomainOpenSN +
-- piReducibleAtLevelFromComponentsBounded + universeMembershipIntroAtBounded. The hardest dispatch arm.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationPiFromTelescopeAtBoundedSucc

-- The +1-closing cons telescope companion (BoundedTelescopeConsSucc.lean) — the cons recursor-arm body for the
-- bounded grown-FT motive_2. Mirrors fundamentalTelescopeConsAtBounded but the head child's IH is the +1-closing
-- FundamentalConclusionAtBoundedSucc (the recursor's motive_1) and the closing substitution targets targetScope+1.
-- Reads the head member off the +1 conclusion (subst_universeCodeCell cancels the closed-code substitution) and
-- threads the tail premise — uniform in argLevel (the dispatch instantiates it to the former's decoded level).
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtBoundedSucc

-- Member cumulativity (bound-carrying) (DenoteKeyedBoundedReducibleEnv.lean) — a bound-reducible member at
-- lowerBound is one at any higherBound ≥ lowerBound, SAME candidate (the type relation lifts by
-- stepBounded_cumulative, which preserves the candidate; the membership witness carries over). The member analogue
-- of isReducibleBounded_cumulative; reconciles the bounded telescope's argument level (the former's decoded OUTPUT
-- level, used by twoChildMembers) with the uniform environment bound in the grown-FT consTelescope dispatch arm.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtBounded.cumulative

-- The Σ twin of BFT-4 (BoundedGenFormationSigmaFromTelescope.lean) — a two-child Σ former is a +1-closing
-- fundamental member of Type@(lmaxAll levels) from the SAME telescope IH. Σ is classified by the relation's
-- `neutral` arm (SN candidate; no sigmaType arm), so the former reducible-as-type needs only former SN, NOT the
-- per-component cumulative lifts the Π arm needs; domain/codomain SN + level bounds + var-0 instantiation are
-- identical to the Π arm. The Σ-branch body of the eventual HasTypeDescPi.rec dispatch (BFT-6) + formation FT.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc
-- GTL-11 bounded reassembly: the 1-child listCode data-former twin (non-dependent; neutral SN-candidate path,
-- lmaxAll [elementLevel] = elementLevel collapses the level bookkeeping). The bounded analogue of
-- listCodeFormationUnderSubst; the last reassembly piece before the atomic landing.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationListFromTelescopeAtBoundedSucc

-- The bounded grown-engine fundamental theorem BFT-6 (BoundedGrownDispatch.lean) — the HasTypeDescPi.rec dispatch
-- with motive_1 = FundamentalConclusionAtBoundedSucc, motive_2 = IsTelescopeReducibleAtBoundedSucc (the +1
-- telescope wrapper carrying the argLevel≤bound cumulativity gate), conditional on a bounded HasTypeDesc formation
-- premise. Pure assembly of shipped arms: ofFormation[premise]/conv[inline]/piIntro/piElim/genFormationPi
-- [BFT-4 Π + Σ-twin, double-applying premisesFundamental to gate-extract output<bound]/nil/consTelescope[cons
-- companion + member cumulativity]. The +1-closing analogue of the denote HasTypeDescPi.fundamentalVectorFromFormation.
#assert_no_axioms FX1Poly.Typed.IsTelescopeReducibleAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalAtBoundedSuccFromFormation

-- The bounded formation leaf arms (BoundedFormationLeafArms.lean) — the +1-closing var (BFT-7) and
-- universeFormation (BFT-9) arms of the bounded FORMATION FT (HasTypeDesc.rec dispatch). Each is the
-- FundamentalConclusionAtBounded.toSucc lift of the shipped arbitrary-scope leaf arm (no binder); the
-- universeFormation arm threads belowBound : denote (lsucc levelExpr) env < bound (the per-term gate the dispatch
-- supplies). The conv arm (BFT-8) is already fundamentalConvArmBoundedSucc; genFormation (BFT-10) reuses BFT-4+Σ-twin.
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationAtBoundedSucc

-- The per-derivation universe-level budget (BoundExceedsDesc.lean) — the BFT-11/12 fuel. An INDUCTIVE Prop family
-- indexed by the HasTypeDesc derivation (a budget FUNCTION over the Prop derivation would be large elimination,
-- forbidden), mutual with the telescope budget. `bound` exceeds the denoted lsucc-level of every universeFormation
-- leaf; conv/genFormation carry sub-budgets by construction (sidestepping a term-syntactic budget's inner-classifier
-- obstruction). Foundation for the bounded formation FT dispatch (BFT-11) + the ∃-bound discharge (BFT-12).
#assert_no_axioms FX1Poly.Typed.BoundExceeds
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

-- The bounded FORMATION-engine fundamental theorem (BoundedFormationDispatch.lean, BFT-10 + BFT-11). Discharges the
-- formationFundamental premise shape of BFT-6: given a BoundExceeds budget, every HasTypeDesc formation derivation
-- satisfies FundamentalConclusionAtBoundedSucc. Proved by BoundExceeds.rec (induction on the BUDGET, not the
-- derivation) so the universeFormation arm receives belowBound NAMED — sidestepping the opaque-outputType-index
-- inversion that blocks a match on the budget. IsFormationTelescopeReducibleAtBoundedSucc is the DescTelescope
-- motive_2 wrapper (BFT-10).
#assert_no_axioms FX1Poly.Typed.IsFormationTelescopeReducibleAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.fundamentalAtBoundedSucc

-- The GROWN-engine per-derivation budget (BoundExceedsPi.lean, BFT-12a). Mutual inductive Prop over HasTypeDescPi /
-- DescTelescopePi. The grown engine has NO universeFormation leaf, so this carries NO belowBound of its own — the
-- ofFormation ctor carries the embedded BoundExceeds (where the fuel lives), every other ctor threads
-- sub-BoundExceedsPi (conv/piIntro/piElim) or the telescope budget (genFormationPi). Foundation for the BFT-12c
-- grown FT discharge (BoundExceedsPi.rec, ofFormation arm → BFT-11) at a single fixed bound.
#assert_no_axioms FX1Poly.Typed.BoundExceedsPi
#assert_no_axioms FX1Poly.Typed.BoundExceedsPiTelescope

-- The BFT-12b grown-budget discharge (BoundExceedsPiDischarge.lean): monotonicity + existence for BoundExceedsPi.
-- Mirror of BoundExceedsDischarge over the grown engine; existsBound's ofFormation arm delegates to
-- BoundExceeds.existsBound (origin of the fuel), the piIntro arm sums THREE sub-bounds (Nat.le_trans chain). Feeds
-- the BFT-12c grown-FT bound-choice toward SN-043.
#assert_no_axioms FX1Poly.Typed.BoundExceedsPi.monotoneInBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPiTelescope.monotoneInBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPi.existsBound
#assert_no_axioms FX1Poly.Typed.BoundExceedsPiTelescope.existsBound

-- The UNCONDITIONAL (up to budget) grown FT (BoundedGrownFundamental.lean, BFT-12c). Given a BoundExceedsPi budget,
-- every HasTypeDescPi derivation satisfies FundamentalConclusionAtBoundedSucc. Via BoundExceedsPi.rec: the
-- ofFormation arm feeds the carried embedded BoundExceeds into HasTypeDesc.fundamentalAtBoundedSucc (BFT-11),
-- discharging BFT-6's formationFundamental premise inline; every other arm mirrors BFT-6 (budgets unused). With
-- BoundExceedsPi.existsBound (BFT-12b) this is one closed-corollary step (BFT-13) from SN-043.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalAtBoundedSucc

-- The closed-term bounded-reducibility corollary (ClosedBoundedReducibleMember.lean, BFT-13). Composes
-- BoundExceedsPi.existsBound (BFT-12b) → HasTypeDescPi.fundamentalAtBoundedSucc (BFT-12c) → the empty-context env
-- witness, instantiated at the unique closing substitution Fin.elim0 : RawTermSubst 0 1. Turns the
-- budget-conditional grown FT into an UNCONDITIONAL closed-reducibility fact; feeds the member→SN bridge (BFT-14).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedBoundedReducibleMember

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

-- OB-1 (BoundedNeutralMember.lean): a variable is a bound-reducible member of any bound-reducible type. The
-- candidate is an unconditional reducibility candidate (ReducibleTypeAtBounded.isReducibilityCandidate) and a
-- variable joins it by CR3 (neutralExpansion) with a vacuous reduct premise (noStep_var). The member-side leaf the
-- neutral/identity closing environment (reducibleEnvOfWfContext, OB-3) cons-feeds at every context position — the
-- first brick discharging the OpenStronglyNormalizing residual toward UNCONDITIONAL open SN-043 (#546).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtBounded.ofVariable

-- OB-2a (BoundedUniverseInversion.lean): the universe gate inversion. A bound-reducible-as-type universe code
-- Type@levelExpr has its decoded level < bound. Four arms impossible for a universe code (weak-head-normal, not
-- neutral, not a Π cell); the universeCode arm carries belowBound; ofPointwiseIff recurses. Recovers the
-- belowBound premise the universe-member decode (universeMemberReducibleAsTypeAtDecodedLevelBounded) consumes in
-- OB-2 (binding-type bounded-reducibility). Index-inversion via generalize + induction, propext-clean.
#assert_no_axioms FX1Poly.Typed.belowBound_of_reducibleUniverse

-- OB-2b (BoundedBindingTypeReducible.lean): a universe-typed subject is bound-reducible-as-type under a
-- reducible env. Given a grown derivation typing bindingType at Type@levelExpr, a BoundExceedsPi budget at bound,
-- and a bound-reducible closing env at bound, subst σ bindingType is bound-reducible-as-type at bound. Composes
-- fundamentalAtBoundedSucc (FT) → subst_universeCodeCell → belowBound_of_reducibleUniverse (OB-2a) →
-- universeMemberReducibleAsTypeAtDecodedLevelBounded (decode) → isReducibleBounded_cumulative. The type-side leaf
-- the reducible-closing-environment builder (reducibleEnvOfWfContext, OB-3/OB-4) cons-feeds toward open SN-043.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReducibleAsTypeUnderEnv

-- OB-3 (ReducibleEnvOfWfContext.lean): the reducible closing environment for a well-formed context. Every
-- WfContextDesc admits a bound + a closing substitution (every variable ↦ var 0 ∈ scope 1, the "var 0 head"
-- trick that sidesteps renaming closure) under which it is a bound-reducible environment. It reads each binding's
-- type-hood off the native WfContextDesc.headIsTypeDesc (= wellFormed.2) + the native HasTypeDesc.toHasTypeDescPi
-- formation -> grown embed. Telescope induction via ReducibleEnvAtBounded.cons: OB-2 makes each binding type
-- reducible, OB-1 puts var 0 in it, with a SUM bound (Nat.le_add_*, propext-free — the max-based attempt leaked
-- propext via Nat.le_max_*). The env half of the OpenStronglyNormalizing residual toward unconditional open
-- SN-043 (#546); the wf-hypothesis is genuinely external since HasTypeDescPi -> WfContext provably FAILS
-- (ContextValidityFails).
#assert_no_axioms FX1Poly.Typed.reducibleEnvOfWfContextDesc

-- ★ SN-043 OPEN (OpenStronglyNormalizingUnconditional.lean, OB-5): every well-typed grown term in a WELL-FORMED
-- context is strongly normalizing, UNCONDITIONALLY. WfContextDesc Γ → HasTypeDescPi Γ subject classifier →
-- IsStronglyNormalizing subject. The open generalization of closedStronglyNormalizing (BFT-14) from .empty to
-- arbitrary Γ. Composes existsBound (budget) + reducibleEnvOfWfContextDesc (OB-3, the reducible closing env over
-- the native WfContextDesc.headIsTypeDesc + HasTypeDesc.toHasTypeDescPi) at a common SUM bound, fed to
-- stronglyNormalizingOfReducibleEnv (reflects SN internally). The OB-1..OB-5 capstone — reached with NO #672, NO
-- KB merged candidate, NO renaming closure. The wf-hypothesis stays external (since HasTypeDescPi → WfContext
-- provably FAILS, ContextValidityFails). Closes #546.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDesc

-- SN-051 / SN-046-uncond (WfContextDecidableConv.lean): the open-SN-043 harvest, routed through the
-- HasTypeDesc-defined WfContextDesc via the bridge-free stronglyNormalizingOfWfContextDesc. Two well-typed
-- subjects in a well-formed context have DECIDABLE Conv (no typed-SN hypothesis — each OB-5 SN witness feeds the
-- parameter-free decider Conv.decidableOfStronglyNormalizing), and global confluence holds (per-term Newman on
-- the OB-5 SN witness). The qualifier is "assume WfContextDesc" (a decidable presupposition; the unqualified
-- typed-SN interface is unprovable since the var rule types in any context).
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfWellTypedInWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectConfluenceOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectWeaklyNormalizesOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.uniqueNormalFormOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convergencePackageOfWfContextDesc
-- SN-052 design fact, T2-FLIPPED: pre-T2 the bare Curry-style λ typed NON-uniquely (the identity λ
-- inhabited Π(Type@e)(Type@e) for every e, forcing a bidirectional checker). Under T2 the Church-style
-- annotation PINS the λ-domain — any two classifiers of one annotated λ agree on the syntactic domain
-- (each Conv to a Π over the annotation), so the checker SYNTHESISES the domain from the subject.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_identityLambda_atUniverse
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_lambdaDomain_pinnedByAnnotation
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_lambdaDomains_agree
-- SN-052 COMPARE step: checking a subject against a KNOWN-TYPE target reduces to deciding Conv (SN-051) — the
-- load-bearing infer-mode step of the bidirectional checker. isTrue via the grown conv rule; isFalse via the
-- subject's per-term uniqueness (holds for every non-λ subject). Typing witnesses threaded explicitly (data),
-- since Decidable cannot large-eliminate the Prop-valued IsTypeDesc existential.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckOfInferredUniqueAtType
-- SN-052 variable leaf: grown variable inversion (any classifier a variable receives is Conv to its context
-- lookup) — the per-subject UNIQUENESS the COMPARE step consumes at a variable. ofFormation delegates; conv
-- chains via unconditional Conv.trans; piIntro/piElim/genFormationPi impossible on a variable subject.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionVariableGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionVariable
-- SN-052 first COMPLETE checker case: deciding a VARIABLE against a known-type target (CHECK mode, SR-free)
-- composes the COMPARE step + variable inversion + variable inference + context validity
-- (IsType.decideWithWitness for the lookup's typehood-as-data, WfContext.lookupIsType refuting the impossible
-- non-type branch). The template for the application infer-mode case.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckVariableAtType
-- SN-052 universe-code leaf: grown universe-code inversion (any classifier a universe code receives is Conv to
-- the next universe) — the per-subject UNIQUENESS the COMPARE step consumes at a universe-code position. Same
-- recipe as the variable inversion with the universe-formation model: ofFormation delegates; conv chains via
-- unconditional Conv.trans; piIntro/piElim/genFormationPi impossible on a universe-code subject.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionUniverseCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionUniverseCode
-- SN-052 second COMPLETE checker case (closes the SR-free leaf fragment): deciding a UNIVERSE CODE against a
-- known-type target (CHECK mode, SR-free). Strictly simpler than the variable case — both the inference and
-- its classifier-typing are direct universeFormation constructors, so no IsType.decideWithWitness is needed.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckUniverseCodeAtType
-- SN-052 application uniqueness ingredient: the COMPARE-step `uniqueAtSubject` at an APPLICATION position,
-- PARAMETERIZED over the function's type uniqueness. Unlike the var/universeCode leaves, an application's type
-- is not unconditionally unique (it inherits the function's non-uniqueness — a bare λ in function position has
-- many Π types); given the function is unique up to Conv, invertApp + Conv.piTyCode_inj + Conv.subst0 push the
-- codomain Conv through the SAME argument to make the dependent output subst0 codomainCode argument unique.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.applicationTypeUniqueGivenFunction
-- SN-052 APPLICATION checker case, factored over the SR-gated function exposure: given the function's Π-typing
-- + type-uniqueness + the Π-components' universe-typings (threaded as input — the eventual recursive inference
-- delivers them once the SR exposure lands), the application check against a known-type target reduces to the
-- argument's check against the domain. isTrue: piElim + substituteUnderBinding + applicationTypeUniqueGivenFunction
-- + COMPARE step; isFalse: invertApp + Conv.piTyCode_inj + conv show the application cannot be typed at all.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckApplicationGivenFunction
-- SN-052 Π/Σ-FORMATION uniqueness ingredient: the COMPARE-step uniqueAtSubject at a former position,
-- PARAMETERIZED over the components' type uniqueness (a former's type universeCodeCell (lmaxAll [domLevel,
-- codLevel]) flag is pinned by the components' levels/flags; invertPiTyCode/invertSigmaTyCode force both
-- components at the SAME flag, levelFlag_eq_of_conv gives SYNTACTIC level/flag equality, subst aligns the
-- output universe codes). The former analogue of applicationTypeUniqueGivenFunction.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormationTypeUniqueGivenComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormationTypeUniqueGivenComponents
-- SN-052 Π/Σ-FORMATION checker cases (closes the infer-mode SR-free combinator coverage): deciding a former
-- against a known-type target given its components' universe-typings + uniqueness (threaded as input — the
-- recursive component-inference delivers them). SR-free: a former needs no exposure (its components are already
-- type codes), so the whole decision is the COMPARE step. {pi,sigma}FormationViaGenArm infers, universeFormation
-- types the inferred universe, {pi,sigma}FormationTypeUniqueGivenComponents supplies uniqueAtSubject.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckPiFormationGivenComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckSigmaFormationGivenComponents
-- SN-055 toward the former-domain SR: re-type a FORMATION codomain under a Conv-stepped domain — the
-- dischargeable half of congPiDomain/congSigmaDomain's codomainReTyping (the common formation-codomain case),
-- UNCONDITIONAL via the part-2a convContextOfFormation + convBackToUniverseCode (no grown-context-conversion
-- bundle). Pointwise context-Conv: index 0 via Conv.rename weaken; successors via Conv.refl.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.formationCodomainReTyping
-- SN-055: the UNCONDITIONAL former-domain SR rebuild for a FORMATION codomain (completes the formation-codomain
-- former-domain case). {pi,sigma}FormationViaGenArm reassembles the former from the stepped domain + the
-- re-typed codomain (formationCodomainReTyping), at the canonical Type@(lmax domLevel codLevel). The dispatcher
-- converts to the former's classifier via the invertPiTyCode Conv. No grown context-conversion bundle.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piFormerStepDomainFormationCodomain
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerStepDomainFormationCodomain
-- SN-055 per-shape ROUTING arms of the SR dispatcher (the non-former positions): turn a Step AT a λ / app head
-- into the SR conclusion, given the children's SR threaded as recursive hypotheses. subjectReductionAtLam =
-- Step.from_lam + congLamBody (λ heads no redex); subjectReductionAtApp = Step.from_app's 3-way (β →
-- betaSubjectReduction, fn-cong → congFunction, arg-cong → congArgument + one-step Conv). Unconditional. These
-- are the dispatcher's piIntro/piElim cases; the genFormationPi grown-codomain domain-cong still awaits the bundle.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtLam
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtApp
-- SN-055 FORMER routing arms (completes the routing-arm set for the 4 typed positions): Step.from_piTyCode /
-- from_sigmaTyCode's 2-way (domain-cong → congPiDomain/congSigmaDomain with codomainReTyping; codomain-cong →
-- congPiCodomain/congSigmaCodomain). codomainReTyping is threaded parameterized over the domain step (formation
-- codomain dischargeable via formationCodomainReTyping; grown codomain awaits the bundle). The dispatcher's
-- genFormationPi/ofFormation-former cases.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtPiFormer
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtSigmaFormer
-- SN-055 ASSEMBLY-USABLE (specific-IH) λ/app SR arms: the dispatcher inducts on the TYPING with the
-- step-quantified motive, so each child's IH is its SR at the CHILD'S SPECIFIC classifier — NOT the general
-- childPreserves the cong arms want. So the dispatcher reconstructs DIRECTLY: subjectReductionPiIntroArm
-- (Step.from_lam + piIntro with the body IH); subjectReductionPiElimArm (Step.from_app 3-way → betaSubjectReduction
-- / piElim with fn IH / piElim with arg IH + Conv.subst0 output-move). These are called verbatim with the IHs.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionPiIntroArm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionPiElimArm
-- SN-055 assembly-usable FORMER arms (specific-IH): Step.from_piTyCode/sigmaTyCode → {pi,sigma}FormationViaGenArm
-- at the canonical Type@(lmax) — domain step uses domainSR + codomainReTyping, codomain step uses codomainSR.
-- The dispatcher's genFormationPi case calls these with the children IHs; codomainReTyping = formationCodomainReTyping
-- for a formation codomain (unconditional), the grown-codomain case = the bundle.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionPiFormerArm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionSigmaFormerArm
-- SN-055 the LAST TWO routing arms (non-function-space, non-former positions), completing the per-arm routing
-- inventory for all FIVE grown-engine typing heads: subjectReductionAtOfFormation (the ofFormation case — a
-- FORMATION-typed subject admits no Step via subjectAdmitsNoStep, so SR is vacuous: absurd) and
-- subjectReductionAtConv (the conv case — re-wrap the already-SR'd inner reduct at the reclassifier via the conv
-- constructor). Both trivial (no child-SR, no WfContext). With these the routing set is exhaustive; the residual
-- to CLOSE the recursive dispatcher is the fundamental-metatheory bundle (WfContext↔WfContextDescPi / WFG-3),
-- recorded in the file docstring.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtOfFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtConv

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
#assert_no_axioms FX1Poly.Typed.convContextCondition_consStep
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectReduction
#assert_no_axioms FX1Poly.Typed.DescTelescope.subjectReduction
-- HONESTY: the formation fragment is NORMAL — subjectAdmitsNoStep is the genuinely content-bearing
-- characterization (every formation-typed subject admits no Step), making the SR above VACUOUSLY true.
-- childrenAdmitNoStep is the mutual telescope normality witness. subjectAdmitsNoStep is the tool the SN-055
-- dispatcher's ofFormation arm actually uses (absurd step via no-step), NOT the heavier vacuous subjectReduction.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectAdmitsNoStep
#assert_no_axioms FX1Poly.Typed.DescTelescope.childrenAdmitNoStep
-- FormationNormalSmoke: a NON-VACUOUS regression for subjectAdmitsNoStep on a concrete closed two-child
-- former — the Π-code Π(Type@0).Type@0, formation-typed via the genFormation arm, provably admits no Step.
-- Exercises the genFormation + telescope arms of the no-step mutual on a real former (not a leaf); the
-- formation-engine analogue of the SN smoke corpora.
#assert_no_axioms FX1Poly.Typed.formationNormalSmoke_piCodeTyped
#assert_no_axioms FX1Poly.Typed.formationNormalSmoke_piCodeAdmitsNoStep

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

-- OB-6 (ContextValidityFails.lean): the WfContext hypothesis in open SN-043 is NECESSARY. A lamCell is never a
-- type (lamCell_isNotType, via subjectIsVariableOrTypeFormerCode + Generator.noConfusion head-mismatch), so
-- Γ = (.empty).cons (λx.x) is ill-formed; yet the var rule types var 0 in it
-- (wellTypedInIllFormedContext) — refuting HasTypeDescPi Γ t T → WfContext Γ (contextValidityPresuppositionFails).
-- The honest negative result: OB-5's WfContext qualifier is an irreducible presupposition, not a removable
-- artifact (the closed Γ=.empty instance consumed by canonicity/consistency is trivially well-formed).
#assert_no_axioms FX1Poly.Typed.lamCell_isNotType
#assert_no_axioms FX1Poly.Typed.wellTypedInIllFormedContext
#assert_no_axioms FX1Poly.Typed.contextValidityPresuppositionFails

-- OSN-1 (OpenStronglyNormalizingBetaEta.lean): the η-reduct of a well-typed open term is β-SN. Well-typed open
-- terms are β-SN (OB-5) AND η-SN (unconditional, since η shrinks RawTerm.size) separately. The UNION βη-SN is
-- NOT their conjunction (β/η interleave), but the SN-of-union assembly is the Geser criterion accUnionBetaEta;
-- the η-postponement crux EtaQuasiCommutesOverBeta is discharged (etaQuasiCommutesOverBeta, the per-η-ctor
-- critical-pair assembly over all 5 η constructors). etaReductOfWellTypedIsBetaStronglyNormalizing is the
-- EtaPreservesBetaStronglyNormalizing payoff. No sorry/placeholder. (The WfContextDesc open βη-SN twins are
-- gated below.)
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaReductOfWellTypedIsBetaStronglyNormalizing

-- OSN-B8 (WfContextBetaEtaConfluence.lean): the GEUVERS harvest of OSN-1. Raw βη-CR is false (Nederpelt/Klop),
-- so CR on the WELL-TYPED fragment is the maximal honest statement (Geuvers LICS'92). Factored as raw local
-- βη-confluence (cd_lemma) ⊕ typed βη-SN (OSN-1) → typed global CR via Newman; unique-βη-NF is the CR corollary
-- via star-rigidity. Weak βη-normalization (existence) + decidable βη-Conv are DEFERRED to the Path-A βη
-- normalizer (not faked from confluence). eq_of_noBetaEtaStep is the raw βη star-rigidity (propext-clean cases).
-- (The βη-CR / unique-βη-NF over WfContextDesc are gated below.)
#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.eq_of_noBetaEtaStep
-- The WfContextDesc twins (the βη leg): the componentwise + conditional + headline open βη-SN
-- (OpenStronglyNormalizingBetaEta.lean) and the Geuvers βη-CR + unique-βη-NF (WfContextBetaEtaConfluence.lean),
-- all routed through the bridge-free stronglyNormalizingOfWfContextDesc — the η-SN component + the Geser union
-- criterion + the βη-Newman bridge are context-predicate-agnostic, so NO HasType on the path.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.componentwiseStronglyNormalizingOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectBetaEtaConfluenceOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.uniqueBetaEtaNormalFormOfWfContextDesc

-- CON-A0 (ConsistencyTargetSignature.lean): the SN-050 spike verdict. The data types are value-predicate
-- candidates, NOT engine cells (no gen_empty); HasTypeDescPi doesn't type data (typingRuleDescOf = some only
-- pi/sigma). So SN-050 = consistencyViaSconing (#697, shipped) specialized to engine typing, with the sole
-- residual the explicit candidateBridge (closed engine-typing at emptyTypeCode ⟹ empty-candidate member =
-- BFT closedBoundedReducibleMember + "emptyTypeCode's candidate is the empty candidate"). Plan's CON-A1/A2
-- (gen_empty cascade) mismodel the architecture; the gap is the engine data-representation (#483/#485-487).
#assert_no_axioms FX1Poly.Typed.consistencyFromEmptyCandidateBridge
-- The abstract target specialized to the CONCRETE emptyTypeCell (CON-A1's cell, mkGen gen_emptyCode () childNil):
-- SN-050 is now stated at the real cell, sole residual the candidateBridge AT emptyTypeCell. Confirms a FORMATION
-- arm (CON-A2 route-E/F) is OFF the critical path — consistency refutes typings AT emptyTypeCell, not constructs one.
#assert_no_axioms FX1Poly.Typed.emptyTypeCellConsistencyFromCandidateBridge
-- The candidate bridge at the MEMBER level: a bounded-reducible member of emptyTypeCell is an emptyTaitCandidate
-- member (family-level deterministic against the dataEmpty-derived candidate). The CON-A3 sconing-leg core,
-- DISCHARGED — the engine↔candidate representation identity now holds in the edited model.
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_memberIsEmptyCandidate
-- The reducibility/sconing leg witness: a closed engine typing at emptyTypeCell yields an emptyTaitCandidate
-- member of the +1 closing-weakened term (closedBoundedReducibleMember + subst_emptyTypeCell + the candidate bridge).
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_closedTypingYieldsEmptyCandidateMember
-- UNCONDITIONAL consistency: HasTypeDescPi .empty t emptyTypeCell → False with NO memberBridge hypothesis. The
-- candidate-bridge PAYOFF (the reducibility-leg member identity is discharged); the final False is delivered by the
-- syntactic-validity route emptyTypeConsistency. Both legs agree the empty type is uninhabited.
#assert_no_axioms FX1Poly.Typed.emptyConsistencyViaCandidateBridge
-- emptyTypeCell IS a reducible type, via the candidate-bridge dataEmpty arm, with candidate emptyTaitCandidate
-- (NOT the generic neutral arm, now gated rootGenerator ≠ gen_emptyCode). The formation half of the candidate bridge.
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_isReducibleType
-- The candidate bridge, the OBSTRUCTION REVERSED: ANY candidate for emptyTypeCell is PointwiseIff emptyTaitCandidate
-- (ReducibleTypeAtBounded.deterministic against the dataEmpty-derived candidate). Replaces the former
-- forcedStronglyNormalizing (which collapsed every candidate onto the maximal SN set). emptyTaitCandidate is
-- head-expansion-closed (unlike CanonicalFormsPredicate emptyIsValue), so it serves as a Π codomain across the FT.
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_candidate_isEmptyCandidate
-- The GO CERTIFICATE for the §5 candidate-bridge edit (CandidateBridgeEditViability.lean), companion to the
-- obstruction proof above: a FAITHFUL MINIATURE of the EDITED relation (gated neutral excluding gen_emptyCode +
-- a dataEmpty arm), built over the REAL RawTerm/Generator/WeakHeadStep, PROVES the determinism-survival crux —
-- the only new interaction (neutral × dataEmpty) is ruled out by the rootGenerator contradiction. So the model
-- change is VIABLE: emptyTypeCell routes to the empty candidate, consistency/canonicity become provable, and
-- non-empty neutral codes keep their SN candidate. The remaining ~12-file work is mechanical mirror, not new math.
#assert_no_axioms FX1Poly.Typed.ScratchReducibleTypeEdited.deterministic
#assert_no_axioms FX1Poly.Typed.ScratchReducibleTypeEdited.emptyCodeCandidateIsEmpty
#assert_no_axioms FX1Poly.Typed.ScratchReducibleTypeEdited.consistencyCore
#assert_no_axioms FX1Poly.Typed.ScratchReducibleTypeEdited.nonEmptyNeutralStillSN

-- Canonicity target signature (CanonicityTargetSignature.lean): the SN-047/048/049 twin of CON-A0. Engine
-- canonicity reduces to the SAME data-candidate bridge as consistency, making the Phase-A boundary uniform.
-- Refined cost finding: HasTypeDesc typing is cascade-free (P13 typingRuleDescOf table + generic
-- genFormationPi); naming a data type is a BOUNDED ~10-12-site generator addition (like gen_arrowCode) + the
-- high-risk candidate identification — NOT 80-arm cascade-death. Gated on the engine data-representation (#483).
#assert_no_axioms FX1Poly.Typed.dataCanonicityFromCandidateBridge

-- Nullary-former formation (NullaryFormerFormation.lean): the engine-side CON-A2 (#809), parametric. The
-- empty type is a nullary type-former; a generator carrying the shared universeFormerOutput row with ZERO
-- children types as Type@0 through the SAME generic genFormationPi arm (no new arm; P13), because
-- lmaxAll [] = lzero (universeFormerOutput_nil). Instantiating at the future gen_emptyCode (binderShifts = [],
-- children := .childNil, premise := DescTelescopePi.nil, all rfl) gives ⊢ Empty : Type@0 — SN-050's formation
-- half (its NON-VACUITY), settled here; the residual is the substrate generator + candidate bridge (CON-A3).
#assert_no_axioms FX1Poly.Typed.universeFormerOutput_nil
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

-- GROWN-engine VARIABLE honesty (GrownVariableHonesty.lean, SN-140 L1): the variable leaf of the grown 0-FP shape
-- discipline, completing the triad with GrownEngineHonesty (λ/type-code) + GrownUniverseConsistency (universe-code).
-- Unlike the λ leaf (classifier shape fixed by the λ itself), a variable's classifier shape is fixed by its CONTEXT
-- LOOKUP, so the honesty is relative: inversionVariable pins any classifier Conv to context.lookup index, and the
-- general rejection is its contrapositive (var not typed at a Conv-distinct classifier). The concrete instances
-- compose it with the conv-rigidity family for a known-shape lookup: a Π-typed variable is not a type (not at a
-- universe code); a type variable (universe-code lookup) is not a function/pair (not at a Π/Σ-type code).
#assert_no_axioms FX1Poly.Typed.variable_notTypedAtNonConvLookup
#assert_no_axioms FX1Poly.Typed.piTypedVariable_notTypedAtUniverseCode
#assert_no_axioms FX1Poly.Typed.universeTypedVariable_notTypedAtPiTyCode
#assert_no_axioms FX1Poly.Typed.universeTypedVariable_notTypedAtSigmaTyCode

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
-- VAR-HEADED Abel-reflection piElim arm (VarHeadedAppContextConversion.lean): the GrownCtxConv-5 (#842) crux for
-- a var-headed neutral application. varConvertedUnderContextConv = the reflection LEAF (a variable's typing
-- converts under context conversion: invertVar #1118 + Conv.trans the context-conv premise + the var rule under
-- tgt — NO recursion, the var leaf looks up). varHeadedAppReassemblyUnderContextConv = the assembled
-- reconstruction: (var f)(var a) reassembles under the converted target via reassembleApplicationUnderContext
-- Conversion (#1092), with both functionConverted/argumentConverted DISCHARGED by the leaf, REDUCED to the single
-- piValidityTarget = IsTypeDescPi tgt (Π D C) — exactly the named residual ConvContextPreservesPiValidity the
-- typed-LR semantic route supplies. The application reassembly + both spine re-typings are now FREE for var heads.
-- Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.varConvertedUnderContextConv
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.varHeadedAppReassemblyUnderContextConv

-- Fully-general β subject reduction (HasTypeDescPiBetaSR.lean, TY-SR-β #474). For ANY grown derivation of a β-redex
-- appCell (lamCell body) argument at classifier (over a well-formed context), the β-reduct subst0 body argument is
-- typed at the SAME classifier. The INVERTED form (vs the shipped component-given betaCoherence): invertApp +
-- invertLam recover the components, Conv.piTyCode_inj reconciles the application's vs the λ's domain/codomain,
-- substituteUnderBinding retypes the reduct, and validity (classifierIsTypeDesc, the WfContext consumer) + the conv
-- rule convert it back to classifier. The Step.beta case of the SR master dispatcher (#458).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaSubjectReduction

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

-- CONTEXT-CONVERSION for the FORMATION engine (HasTypeDescContextConversion.lean, #814 part 1): typing stable
-- under a pointwise-Conv-replaced context, the leaf fragment (the clean wf-free half; the grown HasTypeDescPi
-- version's ofFormation arm delegates here, and its piIntro/piElim need wf-validity — the deferred half). The
-- EXISTENTIAL formulation (∃ T', Conv T T' ∧ ... Γ' t T') keeps the var arm honest (no old-entry-under-new-ctx
-- circularity). convContext ⋈ convTelescope mutual; convBackToUniverseCode + convContextCondition_cons helpers.
-- This is the former-DOMAIN SR-cong unblocker (#558/SN-055): codomain re-types under a Conv-replaced binder.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.convBackToUniverseCode
#assert_no_axioms FX1Poly.Typed.convContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.convContext
#assert_no_axioms FX1Poly.Typed.DescTelescope.convTelescope

-- GROWN context-conversion: the validity-free arms (HasTypeDescPiContextConversion.lean, #814 part 2a). Of
-- the grown engine's six arms, FIVE are validity-free; the LONE hard arm is piElim (conv-backing the function
-- to its exact Π needs "typing a Conv-equal type" = type-Conv-closure, which reduces to SR — no such lemma
-- exists, it would be circular). So the full grown context-conversion is part of the mutual fundamental-
-- metatheory bundle (deferred). These two validity-free pieces already discharge former-DOMAIN congruence for
-- the COMMON case (a former whose codomain is a FORMATION type): convBackToUniverseCode + the ofFormation arm.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convBackToUniverseCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convContextOfFormation
-- GROWN context-conversion mutual pair, conditional on the lone piElim arm (HasTypeDescPiContextConversion
-- Conditional.lean, GrownCtxConv-1/2/3/4/6): the SRD-1 conditional-package discipline (#664) applied to GrownCtxConv. ALL five
-- non-piElim arms discharged — ofFormation (convContextOfFormation), conv (recurse+compose), piIntro
-- VALIDITY-FREE (components conv-backed to universe codes; body via the recursively-obtained codomain re-typing),
-- genFormationPi (mutual convTelescope), telescope nil/cons. The piElim arm (type-Conv-closure, circular with SR
-- = the mutual fundamental-metatheory bundle GrownCtxConv-5) is the LONE explicit hypothesis. convTelescopeOfPiElimArm =
-- the grown telescope context-conversion (GrownCtxConv-3) the grown telescope SR consumes ⟹ SRD-2 ⟹ unconditional SN-055.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convContextOfPiElimArm
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.convTelescopeOfPiElimArm

-- GrownCtxConv-5 piElim arm REDUCED to one pure type-formation residual (HasTypeDescPiContextConversionPiElimReduction
-- .lean, GrownCtxConv-5-REASSEMBLY, toward #842). reassembleApplicationUnderContextConversion: the piElim arm's reassembly
-- (rebuild appCell function argument under the target at a Conv-equal classifier) follows from the function-IH
-- output, the argument-IH output, and the SINGLE residual piValidityTarget : IsTypeDescPi tgt (Π D C) — NO
-- WfContextDescPi tgt, because that one Π-validity supplies BOTH the conv reclassifier for the function AND
-- (via inversionPiCodeComponentsUnconditional) the domain typing for the argument. ConvContextPreservesPiValidity
-- NAMES the residual (a Π-type-code's validity is context-conversion-stable — pure type-formation, no elimination).
-- piElimArmFromPiValidityTransfer: under that residual + WfContextDescPi src (master-SR-threaded) + the convContext
-- IH, the full GrownCtxConv-5 arm holds (classifierIsTypeDescPi/WFG-3 → residual transfer → reassembly). FINDING: the
-- residual itself is NOT discharged — it context-converts a Π-validity derivation that classifierIsTypeDescPi can
-- make TALLER (non-structural), and master SR is gated on the same arm (circular), so closure is the mutual
-- fundamental-metatheory bundle (GTL-20) or the semantic route. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.reassembleApplicationUnderContextConversion
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piElimArmFromPiValidityTransfer

-- GrownCtxConv-5 WfContext-threaded context-conversion conditional on the MINIMAL residual (HasTypeDescPiContextConversion
-- Wf.lean, GrownCtxConv-5-WFTHREAD, toward #842). convContextWfOfPiValidity / convTelescopeWfOfPiValidity: a
-- WfContextDescPi-threaded grown context-conversion mutual pair conditional on ConvContextPreservesPiValidity (the
-- minimal type-formation residual from #1092) INSTEAD of the opaque full piElimArm. The piElim arm is INLINED via
-- piElimArmFromPiValidityTransfer (threaded wfSrc → classifierIsTypeDescPi/WFG-3 source Pi-validity → residual
-- transfers it → reassembly) using the recursive convContext IH on the function/argument children. WfContextDescPi
-- (a structural def) is extended at each binder from the SOURCE-side domain/head typing via WfContextDescPi.cons --
-- every recursive call's well-formedness is discharged from premises already present. Strictly improves on
-- convContextOfPiElimArm: residual is now the minimal Pi-type-code-validity-is-context-conversion-stable fact,
-- WfContext is threaded (the SR consumers have it), the piElim arm is demonstrably inlinable. Leaves
-- ConvContextPreservesPiValidity as the single open obligation (GTL-20 bundle / semantic-reflection). The telescope
-- theorem orders (telescope)(wf) so the baseScope/currentDepth split is pinned before the sum-only wf. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convContextWfOfPiValidity
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.convTelescopeWfOfPiValidity

-- GTL-20 (#1098): the grown mutual fundamental-metatheory bundle, conditional on the SINGLE residual
-- (GrownMutualMetatheoryFromPiValidity.lean, toward #834). PROVES that ConvContextPreservesPiValidity discharges BOTH
-- open grown-metatheory release blockers: grown context-conversion (GrownCtxConv-5/#842) AND the grown master subject
-- reduction (SRD-2/#845/SN-055/#558). grownContextConversionFromPiValidity = the clean top-level GrownCtxConv-5 closure (wraps
-- #1093). masterSubjectReductionFromPiValidity ⋈ DescTelescopePi.subjectReductionFromPiValidity = the Wf-THREADING
-- master SR re-statement: the shipped subjectReductionOfPiElimArm is conditional on the WHOLE grown context-conversion
-- piElim arm as a WfContextDescPi-FREE hypothesis, which CANNOT be discharged from the residual (the route needs
-- WfContextDescPi to expose the function's Π-classifier validity, and HasTypeDescPi → WfContextDesc is REFUTED by
-- ContextValidityFails — the var rule types in ill-formed contexts — so Wf can't be recovered inside the arm). The
-- shipped master SR consumes its piElim arm in EXACTLY ONE place (the telescope here arm's convTelescopeOfPiElimArm);
-- replacing that ONE call with #1093's Wf-threading convTelescopeWfOfPiValidity (source Wf from WfContextDescPi.cons)
-- re-bases the whole mutual block on the residual, every other arm unchanged — a mechanical re-statement, not a new
-- proof. grownMutualMetatheoryFromPiValidity = the explicit unification: ONE residual ⟹ BOTH. So GrownCtxConv-5 and SRD-2
-- provably share a single obligation; discharging it (syntactic GTL-21 OR the semantic/reducibility route) closes
-- both. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.grownContextConversionFromPiValidity
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.masterSubjectReductionFromPiValidity
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.subjectReductionFromPiValidity
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.grownMutualMetatheoryFromPiValidity

-- HasTypeDescPiContextConversionPiElimEquivalence: the REVERSE direction `piElimArm → residual`, completing the
-- equivalence `ConvContextPreservesPiValidity ⟺ piElimArm`. piElimArmFromPiValidityTransfer (#1092) gives the forward
-- (residual + source Wf ⟹ piElimArm — the conv rule re-types the function at the literal Π-code, needing IsTypeDescPi
-- tgt (Π D C)). piValidityFromPiElimArm gives the reverse with NO Wf premise: convContextOfPiElimArm transports the
-- Π-CODE's universe typing, and the conv-back to the literal universe code is FREE (the conv rule's reclassifierTyped
-- obligation is here the universe code's OWN validity via ofFormation∘universeFormation, not a Π-code's — so the
-- circularity that blocks the application case does NOT arise for the type-code case). Together: GrownCtxConv-5's entire
-- remaining content IS the single piElim arm. masterSubjectReductionFromPiElimArm = the capstone: piElimArm alone yields
-- master SR (chaining the reverse through GTL-20's masterSubjectReductionFromPiValidity); combined with
-- convContextOfPiElimArm (grown context conversion from piElimArm, no extra premise) this exhibits piElimArm as the
-- single lynchpin of the grown metatheory. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.piValidityFromPiElimArm
#assert_no_axioms FX1Poly.Typed.masterSubjectReductionFromPiElimArm

-- HasTypeDescPiContextStepConversion (SR-U1, the unconditional DIRECTED context-conversion route toward #842/#845/#558):
-- ConvContextWithOldValid Γ Γ' := ∀ i, Conv (Γ.lookup i) (Γ'.lookup i) ∧ IsTypeDescPi Γ' (Γ.lookup i) — old entries Conv
-- to new AND valid in new (FREE for a directed step / unchanged prefix; FAILS for arbitrary Conv = the residual).
-- convContextExactToGrown: a FORMATION subject re-types EXACTLY into the GROWN engine under the enriched condition. var
-- conv's back to the EXACT old classifier via the enriched validity (the linchpin that arbitrary-Conv convContext can't
-- make — its docstring names "type the OLD entry under the NEW context" as the sinking circularity); universe/conv/
-- genFormation are universe-classified/free (genFormation via the shipped exact DescTelescope.convTelescope on the .1
-- projection). This is the ofFormation leaf of the grown directed context conversion (SR-U2 next). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.convContextExactToGrown

-- ConvContextWithOldValid.cons (SR-U2 infra): the enriched condition LIFTS under a shared binder — the binder-crossing
-- closure the grown directed context conversion needs at its piIntro / genFormationPi arms. index 0: both sides look up
-- the weakened binder (Conv.refl) + its validity from weakening bindingValid (weakenUnderBinding + rename_universeCodeCell,
-- the universe classifier is closed so weakening fixes it); index k+1: the weakened old condition. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.ConvContextWithOldValid.cons

-- ★ SR-U2 (the grown half, the crux): HasTypeDescPi.contextConversionExact ⋈ DescTelescopePi.contextConversionTelescopeExact
-- — the GROWN directed context conversion under the enriched condition, EXACT classifier. Mirrors the shipped conditional
-- convContextOfPiElimArm ⋈ convTelescopeOfPiElimArm BUT unconditional: exact conclusion (not up-to-Conv), enriched
-- condition, and ★ the piElim arm RECURSES INLINE (re-type fn+arg by the EXACT IH, reform via native HasTypeDescPi.piElim)
-- instead of the factored-out piElimArm hypothesis. No residual arises because the var arm conv's back to the LITERAL
-- looked-up type (enriched validity), so the IH delivers the function at the LITERAL piTyCodeCell — exactly what the
-- up-to-Conv convContextOfPiElimArm could NOT do (its conv-back to a literal Π-code needed the Π-validity residual = the
-- logical relation). This STRUCTURALLY discharges the piElimArm core that was believed to require the intrinsic LR. The
-- binder arms lift via ConvContextWithOldValid.cons; cleaner than the shipped existential (no convBackToUniverseCode).
-- The directed-step instance (SR-U3) + master SR (SR-U4, closes #845/#558) + GTL-20 firing (SR-U5, closes #842) follow.
-- Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.contextConversionExact
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.contextConversionTelescopeExact

-- SR-U3 (the directed-step instance): ConvContextWithOldValid.ofHeadStep builds the enriched condition FREE for a head
-- domain step (domain ↝ domainReduct, prefix UNCHANGED): index 0 = Conv (weaken domain) (weaken domainReduct) from the
-- step + domain's prefix-validity (headIsType) weakened; index k+1 = refl (prefix entries unchanged) + lookupIsType
-- weakened. ★ HasTypeDescPi.codomainReTypingStep = contextConversionExact ∘ ofHeadStep: a codomain re-types across a
-- stepped domain binder at the SAME classifier, UNCONDITIONALLY — the grown twin of the shipped FORMATION
-- codomainReTypingOfFormationStep (#1096), discharging the grown codomainReTyping that gated master SR (SRD-1/#844 →
-- SRD-2/#845 → SN-055/#558). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.ConvContextWithOldValid.ofHeadStep
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.codomainReTypingStep

-- ★ SR-U4 — the UNCONDITIONAL grown master subject reduction (closes SRD-2 / SN-055).
-- HasTypeDescPi.subjectReduction ⋈ DescTelescopePi.subjectReduction: the mutual master SR + grown telescope SR,
-- mirroring the conditional subjectReductionOfPiElimArm pair but with the piElim context-conversion hypothesis
-- DROPPED.  The lone use of that hypothesis — the telescope here-arm tail re-typing across a stepped binding — is
-- discharged UNCONDITIONALLY by the EXACT directed context conversion contextConversionTelescopeExact (SR-U2) fed
-- the head-step enriched condition ofHeadStep (SR-U3): a head step keeps the PREFIX FIXED, so the directed case the
-- master SR actually needs never touches the arbitrary-Conv logical-relation residual that gated the believed crux.
-- subjectReductionStar lifts it along a whole StepStar chain — the preservation form the grown closed / open
-- type-safety theorems consume as a hypothesis, now dischargeable.  Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReduction
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionStar

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

-- piElimArmUnderWfTarget: the flexible grown context-conversion piElim arm, UNCONDITIONAL under target
-- well-formedness — the FIRST unconditional discharge of the obstruction every prior context-conversion firing left
-- "reduced to the Π-validity residual."  The well-formed-context twin of piElimArmFromValidityRespectsReduction
-- (#1094): same Conv.reducesToPiTyCode + reassembleApplicationFromConvEqualPiValidity, but the global
-- TypeCodeValidityRespectsReduction residual application is replaced by typeValiditySurvivesReductionUnderWf at the
-- (well-formed) target.  It is the IH-consuming piElim CASE of a flexible context-conversion mutual: functionFlexible
-- is NOT a separate recursion — under the target wf it derives from functionConverted via classifierIsTypeDescPi, so a
-- flexible mutual built on this arm needs only the single term-conversion recursion.  Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piElimArmUnderWfTarget

-- ★ convContextUnderWf ⋈ convTelescopeUnderWf — the GROWN context conversion, UNCONDITIONAL under target
-- well-formedness: the structural closure of GrownCtxConv-5/#842 (the piElim context-conversion arm that resisted
-- 40+ firings).  A faithful transform of the conditional convContextOfPiElimArm ⋈ convTelescopeOfPiElimArm with the
-- piElimArm hypothesis DROPPED: the piElim arm uses piElimArmUnderWfTarget (functionFlexible derived from
-- functionConverted via classifierIsTypeDescPi), the var-style leaves are wf-FREE (the var rule types
-- unconditionally), and target wf is threaded + extended at piIntro/telescope-cons via WfContextDescPi.cons.  The
-- wf-FREE arbitrary-Conv version is genuinely LR-bound (the source→target wf bridge is circular with the theorem,
-- and classifierRespectsConv is refuted #1058); carrying TARGET wf cuts the knot, reading every needed target
-- validity off lookupIsType/classifierIsTypeDescPi.  So this is the MAXIMAL structural closure — unconditional
-- modulo a presupposition of exactly SN-043's benign character (HasTypeDescPi → WfContextDesc is itself refuted).
-- Master SR does NOT consume this (SR-U4 routed through the EXACT directed conversion); this is the standalone
-- GrownCtxConv-5 result.  Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convContextUnderWf
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.convTelescopeUnderWf

-- GrownCtxConv-5-FORMFRAG (#1099): the residual ConvContextPreservesPiValidity is UNCONDITIONALLY free for FORMATION-valid
-- Π-codes (ConvContextPreservesPiValidityFormationFragment.lean). convContextPreservesPiValidityForFormationCode:
-- a piTyCodeCell D C that is a FORMATION type (IsTypeDesc, no type-level computation) context-converts to a grown
-- type (IsTypeDescPi) under any pointwise-Conv-related target, via the shipped unconditional formation
-- context-conversion convContextOfFormation (HasTypeDesc.convContext re-embedded through ofFormation) +
-- convBackToUniverseCode — NO semantic input. Together with #1095 (the validity-respects-reduction twin is likewise
-- free for the formation fragment), this LOCALIZES the residual's genuinely-open core precisely to the
-- GENUINELY-GROWN Π-codes: open NEUTRAL type-level applications ((var f)(var a) at a universe) / type-level λ, typed
-- via piElim/piIntro at the type level, NOT via ofFormation/genFormationPi-from-formation. That open-neutral case IS
-- GrownCtxConv-5 itself (context-converting a neutral type-level application is the piElim context-conversion), so the
-- residual's hard core is irreducibly the open semantic-model obligation (Kripke/sconing logical relation — the
-- bounded reducibility model is closed-substitution-based, unfit; reflection fails at the neutral base). No further
-- syntactic fragment to peel. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convContextPreservesPiValidityForFormationCode
-- GrownCtxConv-5-FORMERSTEP (#1120): the Π-FORMER recursion step of the residual — its inductive ENGINE, between the
-- formation base (#1099 above) and the var-headed neutral leaf (#1119). ConvContextPreservesPiValidityFormerStep.lean.
-- piCodeValidityContextConversionFormerStep: given the universe-code-PRESERVING context conversions of the domain
-- (at sourceContext) and codomain (at sourceContext.cons domainCode) type-codes — the structural IHs — a Π domainCode
-- codomainCode's grown validity transports across any pointwise-Conv context conversion: inversionPiCodeComponents
-- Unconditional decomposes the source Π-validity into its component universe-typings (at a COMMON flag), the IHs
-- transport each (the codomain under the cons-lifted condition convContextCondition_cons, PRESERVING that common
-- flag — essential since piFormationViaGenArm needs the domain+codomain flags to match), and piFormationViaGenArm
-- re-forms the Π-code validity under the target. "Semantic types are Conv-closed by construction" made concrete for
-- the Π-former: the validity is REBUILT from its transported parts, never carried as a black box. With the base
-- (#1099), this engine, and the var-spine leaf (#1119) in place, the residual's genuinely-open core is precisely the
-- APP-HEADED neutral leaf (arbitrary-term argument → general-term context conversion = the GTL-20 mutual bundle).
-- Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piCodeValidityContextConversionFormerStep
-- GrownCtxConv-5-SIGMASTEP (#1121): the Σ-former recursion step, the exact twin of the Π step (#1120 above) over
-- sigmaTyCodeCell / inversionSigmaCodeComponents / sigmaFormationViaGenArm. A genuinely-needed companion, NOT a
-- separate concern: the residual's Π-engine recurses on the component type-codes, which can THEMSELVES be Σ-codes.
-- sigmaCodeValidityContextConversionFormerStep: given the universe-code-preserving context conversions of the
-- domain + codomain type-codes, a Σ D C's grown validity transports across any pointwise-Conv context conversion
-- (decompose via inversionSigmaCodeComponents at a common flag, transport each via the IHs with the cons-lifted
-- convContextCondition_cons, re-form via sigmaFormationViaGenArm). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaCodeValidityContextConversionFormerStep
-- GrownCtxConv-5-GENFORMERSTEP (#1122): the TABLE-GENERIC genFormationPi former step
-- (GenFormerValidityContextConversion.lean) — ONE theorem covering EVERY genFormationPi type-code former (Π, Σ,
-- list, option, id, equiv, and any future typingRuleDescOf row), the cascade-free consolidation of the per-former
-- Π (#1120) and Σ (#1121) steps. convTelescopeFromChildIH: the reusable telescope-validity transport — a grown
-- premise telescope transports across a pointwise-Conv context conversion GIVEN a scope-polymorphic,
-- universe-code-PRESERVING per-child IH (each head re-types via the IH, each tail recurses under the cons-lifted
-- convContextCondition_cons); the validity-rebuild analogue of convTelescopeOfPiElimArm gated on the recursive
-- type-code IH rather than the general piElimArm. genFormerValidityContextConversion: re-form a genFormationPi
-- former under the converted target by transporting its premise telescope and re-firing genFormationPi (same
-- rule.outputType). FRAME-2 cascade-freedom: a new type-code former needs ZERO new context-conversion arms.
-- Zero-axiom.
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.convTelescopeFromChildIH
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.genFormerValidityContextConversion
-- GrownCtxConv-5-VARLEAF (#1123): the universe-preserving bare-variable childConverts case
-- (variableTypeCodeContextConversion, GenFormerValidityContextConversion.lean) — a variable typed AS A TYPE CODE
-- (at a universe) transports to the SAME universe code under any pointwise-Conv target: invertVar (#1118) +
-- Conv.trans the context-conv premise + the var rule under tgt + convBackToUniverseCode (pin the classifier).
-- The unconditional bare-variable case of the per-child IH childConverts that genFormerValidityContextConversion
-- consumes. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.variableTypeCodeContextConversion
-- TYPED-LR-LEVELED (#1124): the UNIVERSE-TRACKING refined typed type-validity LR (GrownCtxConv-5 route B,
-- TypedTypeValidityLeveled.lean). Carries the universe (level, flag) in the INDEX, so the piType arm FORCES the
-- domain at (domainLevel, flag) and codomain at (codomainLevel, flag) to share the flag — resolving the
-- flag-matching obstacle (firing 34) that blocked the unindexed TypedTypeValidityBoxed (#1110) from rebuilding
-- Π-validity via piFormationViaGenArm. toHasTypeDescPi is UNIVERSE-PRESERVING (returns the EXACT
-- universeCodeCell level flag typing, not an existential) — the soundness shape the transport's piType rebuild
-- consumes; toIsTypeDescPi forgets the level/flag to bridge to the unindexed shape; smoke_closedUniverseLeveled
-- is the first scope-0 inhabitant. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.toHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.toIsTypeDescPi
#assert_no_axioms FX1Poly.Typed.smoke_closedUniverseLeveled
-- TYPED-LR-LEVELED-TRANSPORT (#1125): the LEVELED transport across context conversion (route B payoff,
-- TypedTypeValidityLeveledTransport.lean) — the firing-35 flag-matching resolution HARVESTED. transport: by
-- induction on the leveled relation — universeType arm FREE (universe codes context-free, rebuilt via
-- universeFormation under tgt); piType arm RECURSES on domain+codomain (codomain under the cons-lifted
-- convContextCondition_cons) and REBUILDS Π-validity via piFormationViaGenArm — the rebuild's flag-matching is
-- DISCHARGED by the leveled index (transported domain+codomain share the flag); neutral arm = the lone
-- conditional Abel-reflection reconstruction hypothesis neutralRecon. transportValidity: a leveled-valid type
-- code's EXACT universe-code typing transports across context conversion (conditional on neutralRecon) —
-- specialized to a Π-code this is precisely the ConvContextPreservesPiValidity residual shape, discharged for
-- LEVELED-VALID Π-codes conditional ONLY on the neutral reconstruction. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.transport
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportValidity
-- neutralRecon DISCHARGED under target wf (TypedTypeValidityLeveledTransportUnderWf.lean) — the leveled
-- transport's lone conditional arm closed by composing convContextUnderWf (#1133, post-dates the transport)
-- with convBackToUniverseCode: a subject typed at an EXACT universe code survives pointwise-Conv context
-- conversion at that SAME code given WfContextDescPi target (IsNeutral not even needed).
-- universeClassifiedConvContextUnderWf is the discharge; transportUnderWf re-runs the leveled-LR transport
-- with the neutral arm closed (wf extended at the piType binder via the transported domain's exact universe
-- typing), PRESERVING the candidate box — the LR structure transports, not just the typing;
-- transportValidityUnderWf is the GrownCtxConv-5-residual-shaped payoff. Converts the #1168
-- grown-strengthening chain's neutralRecon link from an open LR research hypothesis into the same benign
-- WfContextDescPi presupposition SN-043/OSN-1 carry. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.universeClassifiedConvContextUnderWf
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportUnderWf
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportValidityUnderWf
-- GrownCtxConv-5-MODELNEUTRAL (#1106): the SEMANTIC half of the residual's open neutral core, discharged unconditionally
-- (ConvContextPiValidityModelNeutral.lean). neutralTypeCodeSemanticReducibilityIsContextFree: a neutral type code
-- is ReducibleTypeStep-reducible, and that judgment carries NO typing context (the theorem takes none), so the
-- semantic neutral-type interpretation is IDENTICAL under both sides of the residual's pointwise-Conv context
-- conversion — context conversion is invisible to the semantic side. This isolates the genuinely-open residual
-- entirely to the SYNTACTIC reflection carrying the IsTypeDescPi typing WITNESS across the conversion (the typed
-- logical relation's neutral reflection, re-assembling the type-level piElim for (var f)(var a) = GrownCtxConv-5). Substrate
-- in hand for the typed model: Step.reflectRename + kripkeArrow_neutralBackwardClosure (firings 13/14) +
-- Conv.piTyCode_injective (#865). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.neutralTypeCodeSemanticReducibilityIsContextFree
-- Concrete smoke: the simplest neutral type code (a bare variable `var index` used as a type) is semantically
-- reducible context-free — the non-circular leaf the open type-level neutral reflection bottoms out at.
#assert_no_axioms FX1Poly.Typed.smoke_variableTypeCodeSemanticReducibilityIsContextFree
-- TYPED-TYPE-VALIDITY RELATION (TypedTypeValidityRelation.lean): the open-context typed logical-relation OBJECT
-- for GrownCtxConv-5 (#842), the Kripke-model interpretation of a valid type code, PAIRING a reducibility candidate
-- (KripkeCand) with the IsTypeDescPi typing witness. The `neutral` arm: a neutral type code is typed-valid,
-- carrying snKripkeCand (#1108) + its IsTypeDescPi witness — the base case of the open type-level neutral
-- reflection on which the residual ConvContextPreservesPiValidity bottoms out. ★ DESIGN FINDING: a
-- function-valued KripkeCand CANNOT be a dependent index (Lean's dependent `cases` fails to unify the
-- eta-expanded `fun {ts} => candidate`), so the candidate is a stored ARGUMENT recoverable by `cases`, not an
-- index. toIsTypeDescPi = soundness (relation ⟹ grown validity, the half feeding the residual);
-- carriesSnCandidate = the candidate-pairing recovered; smoke_variableTypeIsTypedValid = non-vacuity (a
-- variable type code is in the relation). Zero-axiom. (Π-FORMER arm + transport-across-context-conversion
-- are the next spike: candidate-as-argument means the Π-former can't read sub-candidates inside a ctor.)
#assert_no_axioms FX1Poly.Typed.TypedTypeValidity.toIsTypeDescPi
#assert_no_axioms FX1Poly.Typed.TypedTypeValidity.carriesSnCandidate
#assert_no_axioms FX1Poly.Typed.smoke_variableTypeIsTypedValid
-- TYPED-LR-BOXED (TypedTypeValidityBoxedRelation.lean): the CANDIDATE-INDEXED relation resolving the firing-19
-- spike — ★ DESIGN A (GO): wrap KripkeCand in the first-order structure KripkeCandBox so it can be a dependent
-- INDEX (a structure-valued index dodges the function-valued-index dependent-elimination failure). The candidate
-- is now a readable INDEX (indexCandidate), so the Π-FORMER arm (piType) can THREAD the domain sub-derivation's
-- exposed candidate domainBox.run into kripkeArrowDep — the capability the candidate-as-argument first cut
-- (#1109) structurally could NOT express. toIsTypeDescPi = soundness over BOTH arms (cases FIRES on the boxed
-- index); smoke_variableTypeIsBoxedTypedValid = non-vacuity. Zero-axiom. (Next brick: tie codomainFamily to the
-- codomain candidate via the scope+1→family candidate-instantiation op, then transport + the fundamental theorem.)
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityBoxed.toIsTypeDescPi
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityBoxed.indexCandidate
#assert_no_axioms FX1Poly.Typed.smoke_variableTypeIsBoxedTypedValid
-- UNIVERSE ARM: a universe code Type@e is typed-valid at snKripkeCand (the other base case beside `neutral`).
-- smoke_universeTypeIsBoxedTypedValid = non-vacuity from a validity hypothesis; smoke_closedUniverseIsBoxedTypedValid
-- = the relation's FIRST CLOSED (scope-0) inhabitant (validity built from ofFormation∘universeFormation, Type@e :
-- Type@(e+1)). Before this arm the boxed relation had no scope-0 inhabitant (neutral needs scope ≥ 1, piType recurses
-- to that base), so a WfContext-indexed typed-LR-validity predicate over it would be vacuous beyond empty — this is the
-- foundation that unblocks the Abel-reflection well-formed-context base. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.smoke_universeTypeIsBoxedTypedValid
#assert_no_axioms FX1Poly.Typed.smoke_closedUniverseIsBoxedTypedValid
-- WfContextTypedLrValid: typed-LR well-formedness of a context — each binding is TYPED-LR-VALID (in
-- TypedTypeValidityBoxed at some candidate box) in its prefix. STRENGTHENS WfContextDescPi (which only says each
-- binding IsTypeDescPi) by pairing each entry's grown validity with a reducibility candidate — the well-formed
-- context the Abel-reflection neutral arm of GrownCtxConv-5 (#842) needs (the transportNeutralArm finding #1112
-- said neutral-app typing must reconstruct from a var-spine under a context where each entry is itself LR-valid).
-- Non-vacuous only because the universe arm gave the LR a closed inhabitant (#1114, used by the universeBinding
-- witness). toWfContextDescPi = ★ soundness: typed-LR-validity REFINES formation-validity (each entry's
-- toIsTypeDescPi), so a typed-LR-valid context is grown-well-formed. Zero-axiom. (Next brick: the LOOKUP lemma,
-- which needs LR-weakening under context extension — a genuinely new proof, not a projection.)
#assert_no_axioms FX1Poly.Typed.WfContextTypedLrValid.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextTypedLrValid.tailValid
#assert_no_axioms FX1Poly.Typed.WfContextTypedLrValid.headLrValid
#assert_no_axioms FX1Poly.Typed.WfContextTypedLrValid.cons
#assert_no_axioms FX1Poly.Typed.WfContextTypedLrValid.toWfContextDescPi
#assert_no_axioms FX1Poly.Typed.wfContextTypedLrValid_universeBinding
-- LR-WEAKENING: the boxed typed LR respects context renaming — the genuinely-new proof the lookup lemma needs (a
-- context entry typed at a prefix scope transports to the full scope). renameRespectingContextExists mirrors
-- HasTypeDescPi.renameRespectingContext over the 3 LR arms (existential box): neutral via IsNeutral.rename, universe
-- via rename_universeCodeCell, piType via the lift-ρ codomain recursion + piTypeViaSnCodFamily reassembly (the lift
-- is why a weaken-only statement is insufficient — weakening descends the binder). IsTypeDescPi.renameRespectingContext
-- = the grown-validity rename helper each arm delegates to. weakenUnderBinding = the single-step corollary (ρ=weaken,
-- condition definitional) the lookup threads down a context telescope. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityBoxed.renameRespectingContextExists
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityBoxed.weakenUnderBinding
-- TYPED-LR LOOKUP: in a WfContextTypedLrValid context, every variable's type (the looked-up entry,
-- iterated-weakened to the full scope) is TYPED-LR-VALID. The typed-LR analogue of WfContextDescPi.lookupIsType,
-- by structural induction folding weakenUnderBinding (#1116) down the telescope (each cons descended re-weakens
-- the carried derivation once, matching the de Bruijn shift lookup accumulates). The lookup leg the Abel-reflection
-- neutral arm of GrownCtxConv-5 (#842) consumes — a neutral application's typing reconstructs from the looked-up
-- function-variable's LR-valid type. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.WfContextTypedLrValid.lookupLrValid
-- TYPED-LR-CODFAMILY: close the Π-former's free-codomainFamily gap (the firing-20 next brick). snKripkeCodFamily
-- is the SN codomain family (codomain analogue of snKripkeCand #1108) — the CANONICAL codomain family for the
-- type-VALIDITY relation (which only needs the family to EXIST + TRANSPORT, not to depend on the argument: the
-- residual is Π-type validity, not Π-member semantics). snKripkeCodFamily_transport_pointwise = rename-invariance
-- (Iff.rfl). piTypeViaSnCodFamily = the Π-former with codomainFamily DERIVED from snKripkeCodFamily (no free data
-- at the call site) — the form the fundamental theorem's Π case will use. ★ FINDING: a genuinely-dependent codomain
-- family needs to INSTANTIATE a KripkeCand (scope+1) with a TERM argument, but KripkeCand is RENAMING-indexed
-- (Fin→Fin, can't encode a term subst) — so the dependent instantiation needs a substitution-Kripke refactor,
-- reserved for member-level canonicity, OFF the GrownCtxConv-5 critical path. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.snKripkeCodFamily_transport_pointwise
#assert_no_axioms FX1Poly.Typed.piTypeViaSnCodFamily
-- TYPED-LR-TRANSPORT-NEUTRAL: the neutral arm of context-conversion transport on TypedTypeValidityBoxed. The
-- candidate (snKripkeCand) is context-INVARIANT (#1108), so the neutral-arm transport's SOLE obligation is the
-- target typing targetValid (the semantic side is free). ★ ARCHITECTURAL FINDING: the neutral arm carries
-- validity as a BLACK BOX, so transporting it for a NEUTRAL APP (var f)(var a) IS GrownCtxConv-5 (#842) — the black-box
-- LR RE-PACKAGES GrownCtxConv-5, not dissolves it. Genuine discharge needs DERIVED (not carried) validity: a well-formed-
-- context-indexed LR where a neutral app's typing reconstructs from the looked-up function-var type (var rule +
-- pointwise-Conv leaf) + piElim reassembly (Abel reflection). The Π case already derives validity from parts
-- (piTypeViaSnCodFamily), so the neutral-APP case is the sole obstruction. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityBoxed.transportNeutralArm
-- GrownCtxConv-5-RESIDUAL ★ NEGATIVE RESULT (firing-24 correction of firing-23): the SN-only type-Conv-closure
-- IsTypeDescPiRespectsConvOnStronglyNormalizing is FALSE (NOT the residual). Counterexample T=Type@0, S=(λx.
-- Type@0)(λz.zz): λz.zz is a NORMAL FORM (zz is a neutral var-app, no redex), so S β-reduces in one step to
-- Type@0 — S is SN and Conv Type@0 — yet S is UNTYPED (λz.zz untypable by occurs-check). So SN (and context-free
-- reducibility, which head-expands S to the universe) does NOT imply typedness. GrownCtxConv-5 is therefore NOT
-- reducible to an SN/reducibility Conv-closure; its genuine residual stays the context conversion of Π-validity
-- (ConvContextPreservesPiValidity #1092), discharged only by the TYPED logical relation (TypedTypeValidityBoxed
-- #1110) with validity DERIVED. File retained as a guardrail against re-deriving the false simplification.
-- smoke_residualRefl = the sole true (reflexive) instance. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.smoke_residualRefl

-- GrownCtxConv-5 SECOND piElim-arm reduction, to TypeCodeValidityRespectsReduction (HasTypeDescPiContextConversionValidity
-- Reduction.lean, GrownCtxConv-5-VALRED, toward #842). The FLEXIBLE route, twin of #1092's exact route. The fine-grained
-- obstruction: a context-conversion bundle's piElim arm must re-type the function under tgt at SOME Π-code. EXACT
-- motive (re-type at the original Π D C) closes piElim (#1092 reassembly) but var needs IsType-respects-Conv
-- (FALSE #1058); FLEXIBLE motive (any Conv-equal Π-code) closes var (WfContextDescPi.lookupIsType gives the tgt
-- binding's validity) but piElim needs validity-survives-reduction. Both bridges = the same SR-grade fact, routing
-- through the logical relation. TypeCodeValidityRespectsReduction = the flexible residual (IsTypeDescPi ctx S →
-- StepStar S T → IsTypeDescPi ctx T, single-context "subject reduction for type codes"). reassembleApplication
-- FromConvEqualPiValidity generalizes #1092's reassembly to a Conv-equal Π reductD reductC (via Conv.piTyCode_cong
-- + Conv.subst0). piElimArmFromValidityRespectsReduction: from the function's flexible classifier-transfer IH +
-- reducesToPiTyCode (PC' ⤳* Π reductD reductC) + the residual + the generalized reassembly. Triangulates the GrownCtxConv-5
-- residual with #1092/#1093 (exact ConvContextPreservesPiValidity vs flexible TypeCodeValidityRespectsReduction,
-- inter-derivable, both logical-relation-discharged). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piElimArmFromValidityRespectsReduction

-- GrownCtxConv-5 formation BASE of the validity-respects-reduction residual (same file, GrownCtxConv-5-FORMBASE, toward #842).
-- IsTypeDesc.respectsReductionStar: formation type validity survives reduction UNCONDITIONALLY -- HasTypeDesc
-- .subjectReduction preserves the universe classifier and is itself unconditional (its telescope arm re-types a
-- former's codomain under a stepped domain binder via the UNCONDITIONAL formation convTelescope, the exact move the
-- grown engine cannot make = why GrownCtxConv-5 is open), iterated along StepStar. validityRespectsReductionOfFormation: the
-- grown corollary (formation-typed type code, S⤳*T ⟹ grown IsTypeDescPi T, via ofFormation). This discharges the
-- grown residual TypeCodeValidityRespectsReduction (#1094) on the FORMATION fragment for free, precisely localizing
-- the genuinely-open part to the type-level-computing (genuinely-grown) type codes -- the logical-relation
-- obligation. Zero-axiom.
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

-- GrownCtxConv-5 formation/grown BOUNDARY, named (same file, GrownCtxConv-5-FORMBOUND, toward #842). HasTypeDesc.codomainReTyping
-- OfFormationStep: codomain re-typing under a stepped domain binder is UNCONDITIONAL for FORMATION codomains -- the
-- single domain Step gives Conv domain domainReduct (Conv.fromStepStar), hence the pointwise context-conversion
-- condition (convContextCondition_consStep), and the UNCONDITIONAL formation HasTypeDesc.convContext re-types the
-- codomain (conv-backed to the same universe code). This is the formation analogue of the grown codomainReTyping
-- (GrownCtxConv-6 #843) but UNCONDITIONAL where the grown one is gated on GrownCtxConv-5. It IS exactly the move the grown engine
-- cannot make for genuinely-grown codomains -- that single asymmetry (formation context-conversion unconditional,
-- grown not) is the ENTIRE content of why GrownCtxConv-5 / master-SR genFormationPi / TypeCodeValidityRespectsReduction
-- remain open and need the FX logical relation. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.codomainReTypingOfFormationStep

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertPiTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertSigmaCodeTelescopeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertSigmaTyCode

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noConvReclassifierAtEmptyType

-- Table-generic root classification (HasTypeDescPiRootGeneric.lean, the cascade-death brick for typed root
-- inversion toward the generic typing layer, polycell.md §3.16.19). subjectRootGenerator HARD-CODES the
-- formation table (enumerates gen_piTyCode/gen_sigmaTyCode, proving typingRuleDescOf=none for all else), so a
-- new formation row breaks it. subjectRootGeneratorGeneric instead concludes "four non-former heads (var/
-- universeCode/lam/app) ∨ ∃ rule, typingRuleDescOf root = some rule" — the genFormationPi arm becomes a
-- one-liner ⟨rule, isFormation⟩ (witness already in the arm), pi/sigma absorbed via the typingRuleDescOf_*
-- table facts, so adding a formation row leaves it intact. cellHasNoTypingWhenRootGenericallyExcluded is the
-- future-proof refutation (data ctors/elims have typingRuleDescOf=none permanently, refuted for all time).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectRootGeneratorGeneric
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded

-- Table-generic root classification — formation engine + closed grown (HasTypeDescPiRootGeneric.lean,
-- completing the generic root-classification family). HasTypeDesc.subjectRootGeneratorGeneric is the
-- FORMATION-engine table-generic root inversion (var/universeCode ∨ ∃ rule, typingRuleDescOf root = some
-- rule); the grown subjectRootGeneratorGeneric's ofFormation arm now DELEGATES to it (removing the last
-- hard-coded gen_piTyCode/gen_sigmaTyCode dependency from grown root inversion). closedSubjectRootGenerator
-- Generic is the empty-context twin (drops the gen_var disjunct via the Fin 0 payload) — the consistency
-- inversion that survives table growth. Together with last fire's subjectRootGeneratorGeneric these make the
-- whole root-classification family table-generic.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGeneratorGeneric
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectRootGeneratorGeneric

-- RAW NON-SN — the honest NEGATIVE counterpart to SN-043 (five-layer-defense L1, §27.3). SN-043 proves
-- WELL-TYPED terms are strongly normalizing; this proves the RAW Step relation is NOT (Ω = (λx.x x)(λx.x x)
-- β-steps to itself, so it is not Acc StepSuccessor), confirming the typing restriction is load-bearing and
-- that global raw SN (HasStrongNormalization) is FALSE, not merely unproved. The first non-SN witness in the
-- kernel. notAccessibleOfSelfLoop is the general Acc self-loop fact; divergentOmega_stepsToSelf is Step.beta
-- (the subst0 of the self-applicator into its body computes to Ω definitionally).
#assert_no_axioms FX1Poly.Typed.divergentOmega_stepsToSelf
#assert_no_axioms FX1Poly.Typed.notAccessibleOfSelfLoop
#assert_no_axioms FX1Poly.Typed.divergentOmega_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.rawStep_notStronglyNormalizing

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
-- fromTag_toNat) + finite-polygraph bound (toNat_lt over Fin 197) already re-verify gen_natCode uniformly.
-- baseTypeRuleDescOf gen_natCode = none today (Nat:Type@0 base-type formation deferred to keep the
-- baseTypeRuleDescOf two-way enumeration cascade-free); natTypeCell is a raw classifier for HasTypeDescNatIntro.
#assert_no_axioms FX1Poly.Typed.natTypeCell
#assert_no_axioms FX1Poly.Typed.gen_natCode_isNullaryTypeCode
#assert_no_axioms FX1Poly.Typed.gen_natCode_isAdmitted

-- Ω HAS NO NORMAL FORM — sharpening "not SN" into "never reaches a Step-normal term." selfApplicator is itself
-- normal (by decide); Ω's only one-step reduct is Ω (Step.from_app inversion, congruence shapes refuted by the
-- self-applicator being normal); its only StepStar-reduct is Ω (chain induction, both endpoints generalized);
-- hence no reachable term is normal. The exact obstruction a raw weak-normalization proof cannot clear — closed,
-- well-scoped, ill-typed, every reduction path diverges (the reason SN-043/WN need the typing restriction).
#assert_no_axioms FX1Poly.Typed.selfApplicator_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.divergentOmega_reductIsSelf
#assert_no_axioms FX1Poly.Typed.divergentOmega_starReductIsSelf
#assert_no_axioms FX1Poly.Typed.divergentOmega_noNormalForm

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
-- IsTypeDescRigidity = the native rigidity + leaf characterization of formation type-hood, feeding the native
-- Decidable (IsTypeDesc Γ T) decision procedure.
-- hasNoStep = formation types are normal (read off subjectAdmitsNoStep); eq_of_isTypeDesc =
-- convertible formation types are equal (Conv.eq_of_noStep on the two normal endpoints);
-- ofUniverseCodeCell = a universe code is a formation type (universeFormation); variableCell_iff = a variable
-- cell is a type iff its lookup is a universe code (the ONE context-consulting leaf, over WfContextDesc).
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.hasNoStep
#assert_no_axioms FX1Poly.Typed.Conv.eq_of_isTypeDesc
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.ofUniverseCodeCell
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.variableCell_iff_lookupIsUniverseCode
-- not_of_rootGenerator = the decider's default leaf: a cell whose root is neither gen_var nor gen_universeCode
-- nor a formation former (typingRuleDescOf = none) is NOT a formation type. Table-generic via
-- subjectRootGeneratorGeneric — the formation-former case is the single typingRuleDescOf=some disjunct, so a
-- future formation row needs no change here.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.not_of_rootGenerator
-- IsTypeDescDecidable = the concrete-children Π/Σ former-code inversions. The cascade-free
-- IsTypeDesc.decideTypeGeneric below decides formation type-hood, absorbing any future formation row zero-touch.
-- inversionPiCodeChildren/inversionSigmaCodeChildren = WfContext-FREE concrete-children unpacking (vs the
-- WfContext-carrying ...Components and the generic inversionFormerWithConvGeneric, which existentially repack),
-- a reusable inversion API for the dependent type-formers.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeChildren
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeChildren
-- HasTypeDescNativeDecidable = native Decidable (HasTypeDesc Γ t T), CASCADE-FREE. inferWithWitness =
-- principal-type synthesis (non-recursive: var/universe leaves; EVERY other
-- head delegates to IsTypeDesc.decideTypeGeneric — its universe witness IS the head's principal type, its
-- refutation reconstructs the denied IsTypeDesc witness via subjectRootGeneratorGeneric + the generic former
-- inversion + genFormation, with NO Π/Σ enumeration and no typingRuleDescOf_isPiOrSigma else-branch).
-- decidableOfWellFormedNative = the decision via the IsType-gate on the classifier (Conv principal classifier
-- decided by Conv.decidableOfStronglyNormalizing — principal SN by classifierStronglyNormalizingNative,
-- classifier SN by IsTypeDesc.isStronglyNormalizing via decidableOfWellFormedGeneric) + conv rule forward +
-- uniquenessNative refute. The native twin of HasTypeDesc.decidableOfWellFormed.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inferWithWitness
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormedNative
-- IsTypeDescDecidableGeneric = the FULLY cascade-free IsTypeDesc decider (GTL-10/11 payoff): a 3-function
-- STRUCTURAL mutual recursion over RawTerm/RawTermChildren (no size measure, no termination_by) with no Π/Σ
-- enumeration and no typingRuleDescOf_isPiOrSigma else. decideTypeGeneric does the var/universe
-- leaves + a typingRuleDescOf dispatch (some → decideSynthGeneric → genFormation; none → not_of_rootGenerator);
-- decideSynthGeneric synthesises the shared flag (ASSEMBLE form, recurses on childTail); decideAtFlagGeneric is
-- the fixed-flag spine. subst eliminates currentDepth (not childHead's shift), keeping it structural. A future
-- formation row is absorbed zero-touch — the FRAME-2 extensibility property, realized for the decider.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.decideTypeGeneric
#assert_no_axioms FX1Poly.Typed.DescTelescope.decideSynthGeneric
#assert_no_axioms FX1Poly.Typed.DescTelescope.decideAtFlagGeneric
-- The cascade-free Decidable instance — the typeclass form of decideTypeGeneric (cascade-free twin of
-- decidableOfWellFormed), the canonical decidability for the formation type-hood judgment.
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.decidableOfWellFormedGeneric
-- IsTypeDescGenericSmoke = non-vacuity + definitional-computation corpus for decideTypeGeneric: each fixture is
-- `by rfl` (the kernel REDUCES the whole structural mutual recursion to the right constructor), proving the
-- decider is a genuine computable function that returns .inl on Π/Σ/nested-Π/universe types and .inr on
-- unitCell (a value) + emptyTypeCell (the GTL-11-deferred row, which FLIPS to .inl zero-touch when it lands).
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.decidesAsTypeBool
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_universeCode
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_pi
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_sigma
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_nestedPi
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_unit
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_emptyCodeDeferred

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
#assert_no_axioms FX1Poly.Typed.piIntroOutput
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
#assert_no_axioms FX1Poly.Typed.piElimOutput
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
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_genElim_computesTypeStably

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectHeadHasRoleOrIsUniverseCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.cellUntypedWhenRolelessAndNonBespoke
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.boolTrueCellUntypedViaRole
-- TypingRoleCoverage (GTL-19 coverage capstone): the exhaustive FIVE-class head-classification of grown-typed
-- mkGen cells — every typed head is a formation former / intro former / elim former / bespoke gen_var /
-- bespoke gen_universeCode. Resolves the existential role of subjectHeadHasRoleOrBespoke into the three concrete
-- TypingRole ctors and reads the head off the mkGen index (rootGenerator = generator by rfl). The exhaustive-
-- partition coherence headline of the cascade-free extensibility gate (FRAME-2): the 3 rule tables + 2 bespoke
-- arms cover EVERY typed head, so a new former is one new table row, never a partition change. closed* drops
-- the gen_var class in the empty context (Fin 0 var payload) → the four-way closed taxonomy.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.headClassificationExhaustive
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedHeadClassificationExhaustive

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.natElimCellUntypedViaDecision

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
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_hilbertSpace
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_natElim
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_idCode
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_unit
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
#assert_no_axioms FX1Poly.Typed.semanticTier_unit
#assert_no_axioms FX1Poly.Typed.semanticTier_idCode
#assert_no_axioms FX1Poly.Typed.semanticTier_quantumGate
#assert_no_axioms FX1Poly.Typed.natElim_reducesButUntyped_stillLive
#assert_no_axioms FX1Poly.Typed.boolTrue_typedNotRedex_stillLive
#assert_no_axioms FX1Poly.Typed.semanticTier_discriminates

-- GeneratorHonestyOverview (HON-4): the build-time honesty dashboard. allGenerators enumerates all 197 via the
-- total tag-inverse Generator.fromTag over 0..196; the four count defs fold the HON-1/HON-2/HON-3 classifiers
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
#assert_no_axioms FX1Poly.Typed.KnownTypeTheoryBug.dimension
#assert_no_axioms FX1Poly.Typed.KnownTypeTheoryBug.literatureSource
#assert_no_axioms FX1Poly.Typed.KnownTypeTheoryBug.isEncodableNow
#assert_no_axioms FX1Poly.Typed.corpusRejectsAtkeyBrokenLam
#assert_no_axioms FX1Poly.Typed.corpusRejectsNaiveGradeCheck
#assert_no_axioms FX1Poly.Typed.atkeyBug_isEncodableNow
#assert_no_axioms FX1Poly.Typed.girardBug_isEncodableNow
#assert_no_axioms FX1Poly.Typed.sessionBug_isPending
#assert_no_axioms FX1Poly.Typed.mlValueRestrictionBug_isPending
#assert_no_axioms FX1Poly.Typed.implicitFlowBug_isPending
#assert_no_axioms FX1Poly.Typed.constantTimeBug_isPending
#assert_no_axioms FX1Poly.Typed.fractionalPermissionBug_isEncodableNow
#assert_no_axioms FX1Poly.Typed.corpusNonVacuous
-- Part 5: the FIRST security-dimension noninterference witnesses (now that the security graded judgment
-- HasGradeOver over fxSecuritySemiring ships).  The var rule fixes a used variable's grade to R.one =
-- classified (no subsumption lowers it), and the App-scaling rule adds the function's grades directly so a
-- classified SELECTOR `+`-poisons the result (classified + a = classified).  securityVarUsedIsClassified
-- (baseline) + securityDirectUseCannotBePublic (EXPLICIT-flow rejection: a used secret can't be graded
-- public, Denning-Denning's direct case) + securitySelectorAppResultIsClassified (the implicit-flow
-- mechanism, positive: a classified selector's secrecy flows to the app result) +
-- securitySelectorAppCannotLaunderSelector (IMPLICIT-flow rejection, the application form of "branch on
-- secret": the App-scaled selector grade one+binder·zero poisons to classified, so it can't be laundered to
-- public) + securityNoninterferenceWitnessed (non-vacuity bundle).  The native-`if` surface of the cataloged
-- implicit-flow bug stays pending (implicitFlowBug_isPending refined to point here).
#assert_no_axioms FX1Poly.Typed.securityVarUsedIsClassified
#assert_no_axioms FX1Poly.Typed.securityDirectUseCannotBePublic
#assert_no_axioms FX1Poly.Typed.securitySelectorAppResultIsClassified
#assert_no_axioms FX1Poly.Typed.securitySelectorAppCannotLaunderSelector
#assert_no_axioms FX1Poly.Typed.securityNoninterferenceWitnessed
-- GENERAL App-rule security-flow law (SecurityNoninterferenceGeneral.lean): the §12.2 noninterference
-- backbone lifting Part 5's two fixed-term WITNESSES to a THEOREM over ALL applications.  GradeVectorOver.get
-- (positional lookup) + getAddSecurity/getScaleSecurity (the get-commutations) feed securityApplicationGradeAt
-- = the §6.2 App-scaling rule read pointwise (grades.get i = functionGrades.get i + binderGrade · argument-
-- Grades.get i).  Corollaries: a classified function-position (securityClassifiedFunctionPoisonsApplication,
-- generalizing securitySelectorAppCannotLaunderSelector) OR a classified binder + classified argument-position
-- (securityClassifiedArgumentPoisonsApplication) poisons the result to classified — secrets can't be laundered
-- through application.
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.get
#assert_no_axioms FX1Poly.Modal.getAddSecurity
#assert_no_axioms FX1Poly.Modal.getScaleSecurity
#assert_no_axioms FX1Poly.Modal.securityApplicationGradeAt
#assert_no_axioms FX1Poly.Modal.securityClassifiedFunctionPoisonsApplication
#assert_no_axioms FX1Poly.Modal.securityClassifiedArgumentPoisonsApplication
-- GENERIC App-scaling flow law (GradedApplicationFlow.lean): the dimension-agnostic generalization of the
-- security flow law above, over ANY IsLawfulOrderedGradeSemiring (all 21 graded dimensions).  get_add_lawful
-- / get_scale_lawful (generic get-commutations, nil arm via lawful.add_zero / mul_zero) feed
-- HasGradeOver.applicationGradeAt = the §6.2 App rule read pointwise for any R; applicationGradePoisonsOf-
-- Absorbing = the generic poison (an R.add-absorbing grade in the function position poisons the result).
-- securityFunctionPoison_viaGeneric instantiates at fxSecuritySemiring + classified to recover the firing-52
-- security poison — every dimension's flow-soundness is now a corollary.
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.get_add_lawful
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.get_scale_lawful
#assert_no_axioms FX1Poly.Modal.HasGradeOver.applicationGradeAt
#assert_no_axioms FX1Poly.Modal.HasGradeOver.applicationGradePoisonsOfAbsorbing
#assert_no_axioms FX1Poly.Modal.securityFunctionPoison_viaGeneric
-- Part 6: the fractional-permission OVERALLOCATION rejection (the last usage `no` row, flipped to YES now
-- that the §6.4 permission algebra FX1Poly.Modal.Permission ships).  corpusRejectsFractionalOverallocation
-- (sound guarded add of 2/3+2/3 = conflict, not an over-full share; backed by Permission.add_neverOver-
-- allocates) + corpusNaiveFractionalOverallocates (the bug: the unguarded naiveAdd produces frac 12 9 = 4/3
-- which does NOT fitsWhole).  fractionalPermissionBug_isEncodableNow flips the ledger (was _isPending).
#assert_no_axioms FX1Poly.Typed.corpusRejectsFractionalOverallocation
#assert_no_axioms FX1Poly.Typed.corpusNaiveFractionalOverallocates
-- Part 7: the linearity-MECHANISM defense of session-endpoint aliasing (the `sessionEndpointAliased` row stays
-- pending for the native session-typed surface, mirroring Part 5's native-`if` treatment).  A session endpoint
-- IS a linear resource and aliasing it IS using it twice, so the usage dimension already rejects the mechanism:
-- aliasedLinearEndpointUsageIsOmega (g g uses the endpoint at ω=1+1) + corpusRejectsLinearEndpointAliasing
-- (ω ≰ 1, re-exported from dupReduct_illGraded) + corpusRejectsErasedEndpointAliasing (ω ≰ 0) +
-- unrestrictedEndpointAliasingAccepted (ω ≤ ω, no over-rejection) + endpointAliasingPermittedIffUnrestricted
-- (the line is EXACTLY at ω).  The witnessed `g g` is the usage-calculus image of δ=λx.x x's body — the same
-- self-application whose self-application is Ω, so one syntactic root drives both non-termination (type dim)
-- and resource-aliasing (usage dim).
#assert_no_axioms FX1Poly.Typed.erasedEndpointContext
#assert_no_axioms FX1Poly.Typed.unrestrictedEndpointContext
#assert_no_axioms FX1Poly.Typed.aliasedLinearEndpointUsageIsOmega
#assert_no_axioms FX1Poly.Typed.corpusRejectsLinearEndpointAliasing
#assert_no_axioms FX1Poly.Typed.corpusRejectsErasedEndpointAliasing
#assert_no_axioms FX1Poly.Typed.unrestrictedEndpointAliasingAccepted
#assert_no_axioms FX1Poly.Typed.endpointAliasingPermittedIffUnrestricted
-- Part 8 — the constant-time MECHANISM (§27.2 / §12.5): constant-time = address-trace noninterference (which
-- memory ADDRESS is touched is secret-independent), genuinely distinct from Part 5's value noninterference.
-- secretIndexAccessViolatesConstantTime: indexing AT the secret leaks via the address trace; ★ constantTime
-- StrictlyStrongerThanNoninterference: a secret-indexed read of a CONSTANT array is value-NI-clean yet NOT
-- constant-time — CT strictly stronger. Native `with CT` surface stays pending (constantTimeBug_isPending).
#assert_no_axioms FX1Poly.Typed.SecretDependentAccess
#assert_no_axioms FX1Poly.Typed.SecretDependentAccess.addressTrace
#assert_no_axioms FX1Poly.Typed.SecretDependentAccess.valueObservable
#assert_no_axioms FX1Poly.Typed.SecretDependentAccess.isConstantTime
#assert_no_axioms FX1Poly.Typed.SecretDependentAccess.isValueNoninterfering
#assert_no_axioms FX1Poly.Typed.publicConstantIndexAccess
#assert_no_axioms FX1Poly.Typed.secretIndexAccess
#assert_no_axioms FX1Poly.Typed.publicConstantIndexAccessIsConstantTime
#assert_no_axioms FX1Poly.Typed.secretIndexAccessViolatesConstantTime
#assert_no_axioms FX1Poly.Typed.secretIndexConstantArrayIsValueNoninterfering
#assert_no_axioms FX1Poly.Typed.constantTimeStrictlyStrongerThanNoninterference
#assert_no_axioms FX1Poly.Typed.corpusConstantTimeMechanismWitnessed
-- Part 9 — the ML VALUE RESTRICTION mechanism (§27.2; Wright 1995), the LAST undefended §27.2 row. Syntactic:
-- isSyntacticValue + isGeneralizableUnderValueRestriction; refAllocationIsNotGeneralizableUnderValueRestriction
-- rejects generalizing a `ref` (a non-value), valueRestrictionRejectsRefThatNaiveAccepts is the strictly-tighter
-- contrast. Semantic: ★ naivePolyRefCoercionIsUnsound — naive generalization's `∀ a b, a→b` (write-at-a/read-at-b
-- on a poly ref) is uninhabited (→ Empty); valueRestrictedRefCoercionIsInhabited — `∀ a, a→a` is the identity.
-- valueRestrictionSeparatesSoundFromUnsound bundles them. Native ML-ref surface pending (mlValueRestrictionBug_isPending).
#assert_no_axioms FX1Poly.Typed.MLExpr
#assert_no_axioms FX1Poly.Typed.MLExpr.isSyntacticValue
#assert_no_axioms FX1Poly.Typed.MLExpr.isGeneralizableUnderValueRestriction
#assert_no_axioms FX1Poly.Typed.MLExpr.isGeneralizableNaively
#assert_no_axioms FX1Poly.Typed.lambdaIsGeneralizableUnderValueRestriction
#assert_no_axioms FX1Poly.Typed.variableIsGeneralizableUnderValueRestriction
#assert_no_axioms FX1Poly.Typed.refAllocationIsNotGeneralizableUnderValueRestriction
#assert_no_axioms FX1Poly.Typed.applicationIsNotGeneralizableUnderValueRestriction
#assert_no_axioms FX1Poly.Typed.valueRestrictionRejectsRefThatNaiveAccepts
#assert_no_axioms FX1Poly.Typed.naivePolyRefCoercionIsUnsound
#assert_no_axioms FX1Poly.Typed.valueRestrictedRefCoercionIsInhabited
#assert_no_axioms FX1Poly.Typed.valueRestrictionSeparatesSoundFromUnsound

-- §27.2 / §1.4 Girard-acyclicity STRENGTHENING (UniverseClassificationAcyclic.lean): the corpus ships the
-- Type:Type entry as length-1 (corpusRejectsTypeInType) + length-2 (grownUniverseTypingHasNoTwoCycle), but
-- its docstring promises "no Girard cycle of any length".  This delivers the general statement: the
-- TRANSITIVE CLOSURE of universe classification (UniverseClassificationChain: single edge + step) is
-- irreflexive — each edge forces classifier = subject.lsucc so LevelExpr.size strictly increases along the
-- chain (subjectSizeLtClassifier), and a cycle gives size < itself (Nat.lt_irrefl).  trans confirms genuine
-- transitive closure; HasNoTwoCycleViaChain re-derives the shipped 2-cycle as the length-2 instance;
-- nonVacuous / twoStep_nonVacuous witness real length-1 and length-2 chains (Type@0:Type@1[:Type@2]).
#assert_no_axioms FX1Poly.Typed.UniverseClassificationChain
#assert_no_axioms FX1Poly.Typed.UniverseClassificationChain.subjectSizeLtClassifier
#assert_no_axioms FX1Poly.Typed.UniverseClassificationChain.trans
#assert_no_axioms FX1Poly.Typed.grownUniverseTypingHasNoCycleOfAnyLength
#assert_no_axioms FX1Poly.Typed.grownUniverseTypingHasNoTwoCycleViaChain
#assert_no_axioms FX1Poly.Typed.universeClassificationChain_nonVacuous
#assert_no_axioms FX1Poly.Typed.universeClassificationChain_twoStep_nonVacuous
-- Well-foundedness — the order-theoretic companion to acyclicity.  UniverseClassifies = the single-step
-- level-classification relation; universeClassifies_size_lt = each edge strictly increases LevelExpr.size;
-- grownUniverseClassificationIsWellFounded = WellFounded via Subrelation of InvImage Nat.lt size (no infinite
-- DESCENDING classification chain — distinct from acyclicity's no-cycle).  Together: strict well-founded order.
#assert_no_axioms FX1Poly.Typed.UniverseClassifies
#assert_no_axioms FX1Poly.Typed.universeClassifies_size_lt
#assert_no_axioms FX1Poly.Typed.grownUniverseClassificationIsWellFounded
#assert_no_axioms FX1Poly.Typed.universeClassifies_nonVacuous

-- §27.3 Layer-2 property-based metatheory fuzzer: a TOTAL deterministic generator of well-typed terms
-- (`metatheoryFuzzFamily`, the depth-n β-redex tower `(λx.x)ⁿ Type@0`) with the four Layer-2 properties
-- PROVEN over the whole infinite family — preservation (β-SR, `…_betaPreservation`), progress
-- (`…_progress`), strong normalization (`…_stronglyNormalizing`, ⊇ reducibility via CR1), plus the concrete
-- evaluation results (`…_reducesToType0` / `…_uniqueNormalForm`).  The zero-axiom, no-`native_decide`
-- realization of "fuzz": systematic total generation + proof over the family, strictly stronger than a
-- randomized sample.  `metatheoryFuzzFamilySound` is the bundled "fuzz run passes" verdict.
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_typed
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_betaStep
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_betaPreservation
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_progress
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_reducesToType0
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_uniqueNormalForm
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_base_isNormal
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_succ_isNotNormal
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamilySound
-- The SECOND fuzz family (constant function `λx.Type@0`): the argument-DISCARDING β tower, complementing the
-- identity tower's argument-SUBSTITUTING β.  Every member reduces to Type@0 in ONE step (erasing the entire
-- inner redex stack), exercising that SN / confluence handle ERASED redexes.  Same four §27.3-L2 properties +
-- eval + the metatheoryFuzzConstantFamilySound bundle.
#assert_no_axioms FX1Poly.Typed.closedConstantLambdaTyping
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_typed
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_betaStep
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_betaPreservation
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_progress
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_reducesToType0
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_uniqueNormalForm
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_base_isNormal
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_succ_isNotNormal
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamilySound

-- FUZZ CORPUS CONVERTIBILITY (FuzzCorpusConvertibility.lean): the two §27.3-L2 fuzz families form ONE PROPER
-- Conv class. Both families convert to Type@0 (Conv.fromStepStar on the shipped *_reducesToType0); so any two
-- members convert (Conv.sym/trans). metatheoryFuzz_crossFamilyConvertible = the SUBSTITUTE-path (identity tower)
-- and ERASE-path (constant tower) members are mutually convertible — definitional equality does not distinguish
-- the two β-paths despite their different step counts. metatheoryFuzzFamily_notConvToType1 = the class is PROPER
-- (no member converts to Type@1, via universeCodeCell_inj_of_conv + LevelExpr no-confusion: lzero ≠ lsucc lzero) —
-- the non-degeneracy making the convertibility content meaningful.
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_convToType0
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_convToType0
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_intraConvertible
#assert_no_axioms FX1Poly.Typed.metatheoryFuzz_crossFamilyConvertible
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_notConvToType1

-- FUZZ CORPUS NORMALIZES (FuzzCorpusNormalizes.lean): the verified SN-normalizer (HasTypeDescPi.normalForm,
-- SN-112) COMPUTES every member of both L2 fuzz families to the canonical value Type@0 — the computational
-- sharpening of the Conv capstone (the actual normalizer OUTPUT is pinned, not just Conv). Via
-- reachedNormalForm_eq_normalForm fed *_reducesToType0 + Type@0's normality. metatheoryFuzz_normalFormsAgree =
-- both families' computed normal forms coincide (Type@0), the decidable witness (conv_iff_normalForm_eq) under
-- the cross-family convertibility: substitute-path and erase-path identified by the normalizer's actual output.
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzFamily_normalizesToType0
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzConstantFamily_normalizesToType0
#assert_no_axioms FX1Poly.Typed.metatheoryFuzz_normalFormsAgree

-- LAMBDA-VALUE FUZZ FAMILY (LambdaValueFuzzFamily.lean): the THIRD §27.3-L2 fuzz family — one that EVALUATES TO
-- A FUNCTION value (a λ at a Π type), completing the corpus's canonical-forms coverage (the identity/constant
-- towers both reach the universe code Type@0; this reaches the constant lambda λy.Type@0). arrowType1Type1 =
-- Π(Type@1,Type@1):Type@2 formation (universe-code analogue of churchNatArrow); nestedConstantLambdaTyping =
-- λx.λy.Type@0 : Π(Type@1,Π(Type@1,Type@1)) (returns the constant lambda, discarding its arg). ★
-- metatheoryFuzzLambdaFamily_evaluatesToFunction = every member's normal form is a λ (via firing-117
-- reachedNormalForm_eq_normalForm on the single discarding β-step). progress via firing-112
-- closedFunctionStepsOrIsLambda (steps-or-is-λ at the Π type); SN via SN-043.
#assert_no_axioms FX1Poly.Typed.arrowType1Type1
#assert_no_axioms FX1Poly.Typed.nestedConstantLambdaTyping
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_typed
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_betaStep
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_reducesToLambdaValue
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_normalizesToLambda
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_evaluatesToFunction
#assert_no_axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_progress
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
#assert_no_axioms FX1Poly.Typed.crossRef_subjectReductionBeta
#assert_no_axioms FX1Poly.Typed.crossRef_strongNormalization
#assert_no_axioms FX1Poly.Typed.crossRef_progress
#assert_no_axioms FX1Poly.Typed.crossRef_consistency
#assert_no_axioms FX1Poly.Typed.crossRef_universePredicativity
#assert_no_axioms FX1Poly.Typed.crossRef_uniqueNormalForm
#assert_no_axioms FX1Poly.Typed.crossRef_decidableConversion
#assert_no_axioms FX1Poly.Typed.crossRef_newmanLemma
#assert_no_axioms FX1Poly.Typed.subjectReductionBeta_hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.consistency_hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.strongNormalization_hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.gradedDimensionOrthogonality_isFxOriginal
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
#assert_no_axioms FX1Poly.Typed.FormalReviewGate.passesReview
#assert_no_axioms FX1Poly.Typed.correctedLamReview_provenance
#assert_no_axioms FX1Poly.Typed.correctedLamReview_positiveTest
#assert_no_axioms FX1Poly.Typed.correctedLamReview_negativeTest
#assert_no_axioms FX1Poly.Typed.correctedLamReview_metatheoryReProof
#assert_no_axioms FX1Poly.Typed.correctedLamReview_fuzzRun
#assert_no_axioms FX1Poly.Typed.correctedLamReview_corpusCheck
#assert_no_axioms FX1Poly.Typed.correctedLamReviewGate
#assert_no_axioms FX1Poly.Typed.correctedLamReviewGate_passes
#assert_no_axioms FX1Poly.Typed.universeFormationReview_provenance
#assert_no_axioms FX1Poly.Typed.universeFormationReview_positiveTest
#assert_no_axioms FX1Poly.Typed.universeFormationReview_negativeTest
#assert_no_axioms FX1Poly.Typed.universeFormationReview_metatheoryReProof
#assert_no_axioms FX1Poly.Typed.universeFormationReview_fuzzRun
#assert_no_axioms FX1Poly.Typed.universeFormationReview_corpusCheck
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
#assert_no_axioms FX1Poly.Typed.formationMetatheory_progress
#assert_no_axioms FX1Poly.Typed.grownMetatheory_progress
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationBeta
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationFormerArm
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationConvArm
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationOfFormationArm
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationConditionalMaster
#assert_no_axioms FX1Poly.Typed.formationSelfVerifiedMetatheory
#assert_no_axioms FX1Poly.Typed.grownSelfVerifiedMetatheory
#assert_no_axioms FX1Poly.Typed.formationIsUnconditionallySelfVerified
#assert_no_axioms FX1Poly.Typed.grownIsSelfVerified
#assert_no_axioms FX1Poly.Typed.grownNotUnconditionallySelfVerified
#assert_no_axioms FX1Poly.Typed.incompleteMetatheory
#assert_no_axioms FX1Poly.Typed.incompleteMetatheory_notSelfVerified
#assert_no_axioms FX1Poly.Typed.incompleteMetatheory_missingProgress

-- SN-082 (DataReducibilityCoverage): the reducibility-coverage gate over the ten data-former families.
-- `hasReducibilityCandidate` is the total dependent dispatch — every family's CanonicalFormsPredicate is a
-- full Girard candidate (each arm its OWN shipped candidate, indexed by valuePredicate so no cross-family
-- discharge). A regression gate: adding a DataFormerFamily ctor without a candidate fails to compile.
-- Non-vacuity: bool's candidate is inhabited (boolTrueCell); empty's is the bottom (no closed member).
#assert_no_axioms FX1Poly.Core.DataFormerFamily.valuePredicate
#assert_no_axioms FX1Poly.Core.DataFormerFamily.hasReducibilityCandidate
#assert_no_axioms FX1Poly.Core.DataFormerFamily.coveredCount
#assert_no_axioms FX1Poly.Core.DataFormerFamily.coveredCount_correct
#assert_no_axioms FX1Poly.Core.boolFamilyCandidateInhabited
#assert_no_axioms FX1Poly.Core.emptyFamilyCandidateHasNoClosedMember

-- PAR-1 (MetatheoryParityLedger): formation↔grown reduction-metatheory parity. Weakening + substitution at
-- FULL parity (both unconditional, anchored both engines); SN both hold (grown carries the decidable WF-ctx
-- presupposition); SR is the ASYMMETRY — formation unconditional MASTER, grown only unconditional ARMS, its
-- master conditional on the GrownCtxConv-5 bundle (#842/#845). The parityAnchor_* defs re-certify each engine's proof
-- is zero-axiom + break if renamed; the discrimination theorems prove the benign WF presupposition is kept
-- DISTINCT from the real SR blocker (no overstatement).
#assert_no_axioms FX1Poly.Typed.MetatheoryProperty
#assert_no_axioms FX1Poly.Typed.EngineParityStatus
#assert_no_axioms FX1Poly.Typed.MetatheoryProperty.parityStatus
#assert_no_axioms FX1Poly.Typed.parityAnchor_weakening_formation
#assert_no_axioms FX1Poly.Typed.parityAnchor_weakening_grown
#assert_no_axioms FX1Poly.Typed.parityAnchor_substitution_formation
#assert_no_axioms FX1Poly.Typed.parityAnchor_substitution_grown
#assert_no_axioms FX1Poly.Typed.parityAnchor_strongNormalization_formation
#assert_no_axioms FX1Poly.Typed.parityAnchor_strongNormalization_grown
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_formation
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_grownFormerArm
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_grownConvArm
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_grownOfFormationArm
#assert_no_axioms FX1Poly.Typed.weakening_atFullParity
#assert_no_axioms FX1Poly.Typed.substitution_atFullParity
#assert_no_axioms FX1Poly.Typed.strongNormalization_grownNeedsWfContext
#assert_no_axioms FX1Poly.Typed.subjectReduction_grownConditionalOnBundle
#assert_no_axioms FX1Poly.Typed.parity_discriminates_weakening_vs_subjectReduction
#assert_no_axioms FX1Poly.Typed.parity_discriminates_strongNormalization_vs_subjectReduction
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
#assert_no_axioms FX1Poly.Typed.notStronglyNormalizing_of_infiniteReduction
#assert_no_axioms FX1Poly.Typed.growingReductionSequence_steps
#assert_no_axioms FX1Poly.Typed.growingDivergentTerm_notStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.growingFirstReduct_ne_source
#assert_no_axioms FX1Poly.Typed.nonSelfLoopingDivergenceExists
-- SN-112 (TypedNormalizer): the term-layer normalizer keyed DIRECTLY on the grown HasTypeDescPi judgment —
-- SN-043 (closedStronglyNormalizing) supplies RawTerm.normalize's Acc witness, so typing IS the termination
-- certificate (no Acc passed by hand). Distinct from firing 67's level-indexed route, the SimplyTypedTermLF
-- normalForm_typed, and SN-051's formation-engine classifier-side Conv.decidableOfHasTypeDesc. normalForm (the
-- NF fn) + normalForm_reducesTo (StepStar) + normalForm_isStepNormalForm + normalForm_conv (Conv to NF) +
-- conv_iff_normalForm_eq (NF is a COMPLETE conversion invariant) + closedConvDecidable (grown-keyed closed-
-- subject Conv decider, UNCONDITIONAL — grown twin of decidableOfHasTypeDesc). identityApplicationNormalForm
-- _convReduct = non-vacuity: the normalizer takes the closed β-redex (λx.x)(Type@e) to a NF convertible to its
-- reduct Type@e (real reduction work on firing 64's piElim derivation). Closes SN-112 (#615).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalForm_reducesTo
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalForm_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalForm_conv
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.conv_iff_normalForm_eq
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedConvDecidable
#assert_no_axioms FX1Poly.Typed.identityApplicationNormalForm_convReduct
-- DETERMINISM CONNECTOR (TypedNormalizer, appended): identify the COMPUTED normalForm (SN-112) as THE unique
-- normal form. closedHasUniqueNormalForm (GrownTypeSafety) proves a closed grown-typed term has a unique NF
-- EXISTENTIALLY; reachedNormalForm_eq_normalForm pins it to the computed function — any reached NF = typing.
-- normalForm (both = the unique value, via closedHasUniqueNormalForm's ∀-uniqueness on normalForm_reducesTo +
-- normalForm_isStepNormalForm). normalForm_eq_self_of_isStepNormalForm: already-normal subjects are fixed
-- points (reflexive instance). identityNormalForm_eq: the identity λx.x normalizes to itself (by decide on
-- isStepNormalForm). The normalizer computes THE canonical NF, not an arbitrary one.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.reachedNormalForm_eq_normalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalForm_eq_self_of_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.identityNormalForm_eq
-- IDENTITY TOWER (IdentityTowerFamily): a uniformly-typed INFINITE family idTower e flag n = (λx.x)^n (Type@e),
-- complementing the §27.3 L2 constant-function tower (metatheoryFuzzFamily) with an identity tower. idTower_has
-- TypeDescPi: every height types uniformly at Type@(e+1) — base universeFormation, step RECURSIVE piElim of the
-- identity at Type@(e+1) against the IH (the rule fires n times in the n-th derivation; piElim result subst0
-- Type@(e+1) (idTower n) is defeq Type@(e+1), constant codomain). idTower_stronglyNormalizing: SN for all heights
-- via SN-043 uniformly. idTower_reducesToValue: β-reduces to Type@e in exactly n identity contractions ((λx.x)t ↝
-- t via Step.beta subst0 (var 0) t = t, StepStar.trans chain). idTowerUniformlyTypedReducesToValue packages the
-- headline — the typing engine + SN-043 scale to an INFINITE uniformly-typed family, not just finite fixtures.
#assert_no_axioms FX1Poly.Typed.idTower_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.idTower_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.idTower_reducesToValue
#assert_no_axioms FX1Poly.Typed.idTowerUniformlyTypedReducesToValue
-- ID-TOWER COLLAPSE (IdentityTowerFamily, appended): the family collapses to one canonical value via conversion
-- + the SN-112 normalizer. universeCodeCell_isStepNormalForm: Type@e is a step-NF (rfl over the Bool normality
-- check, free level/flag — nullary leaf, payload-independent). idTower_convToValue: each member converts to Type@e
-- (Conv.fromStepStar of idTower_reducesToValue). idTower_allConvertible: all members mutually convertible (one
-- Conv-class joined through Type@e, trans+sym). idTower_normalForm_eq_value: the computed normalForm of every
-- member = Type@e (firing-72 reachedNormalForm_eq_normalForm on the reduction to the normal value).
-- idTowerCollapsesToCanonicalValue: ★ infinitely many syntactically-distinct well-typed terms, all definitionally
-- equal, all normalizing to the single canonical value — the conversion/normalization face of the typed family.
#assert_no_axioms FX1Poly.Typed.universeCodeCell_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.idTower_convToValue
#assert_no_axioms FX1Poly.Typed.idTower_allConvertible
#assert_no_axioms FX1Poly.Typed.idTower_normalForm_eq_value
#assert_no_axioms FX1Poly.Typed.idTowerCollapsesToCanonicalValue
-- UNIVERSE TOWER (TypedUniverseTower): the predicative universe hierarchy is an infinite NON-COLLAPSING tower —
-- the POSITIVE complement of L1-GIRARD-ACYCLIC (#941, irreflexivity: no Girard cycle of any length). universe
-- LevelOfNat is the n-fold-lsucc family ℕ→LevelExpr; universeLevelOfNat_injective injects ℕ into the level
-- algebra (induction generalizing: lzero/lsucc cross-cases by `cases` no-confusion, lsucc/lsucc by injection +
-- congrArg Nat.succ). universeLevelTower flag n = Type@n as a closed RawTerm 0. universeLevelTower_hasTypeDescPi:
-- each rung types at the next (Type@n : Type@(n+1)) — ofFormation of the universeFormation rule, the .lsucc output
-- DEFEQ to universeLevelOfNat (n+1) (no coercion). universeLevelTower_notConvertible_of_ne: distinct rungs are
-- non-convertible — universeCodeCell_inj_of_conv (conv-rigid step-NF universe codes, global confluence) reduces
-- Conv to level equality, refuted by level injectivity. universeHierarchy_isInfiniteNonCollapsingTower (★) bundles
-- the family: an injection ℕ ↪ a strictly-ascending classification chain — the hierarchy genuinely ascends and
-- never collapses (the antithesis of impredicative Type:Type). Contrasts #941 (no collapse) with real ascent.
#assert_no_axioms FX1Poly.Typed.universeLevelOfNat_injective
#assert_no_axioms FX1Poly.Typed.universeLevelTower_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.universeLevelTower_notConvertible_of_ne
#assert_no_axioms FX1Poly.Typed.universeHierarchy_isInfiniteNonCollapsingTower
-- UNIVERSE NO-TOP (TypedUniverseNoTop): sharpen #1010 — the universe-code classifier is EXACTLY the successor,
-- and the tower has NO TOP. Engine input = the shipped grown inversion HasTypeDescPi.inversionUniverseCode (any
-- classifier a universe code receives is Conv to Type@(e+1)). universeCodeClassifierIsSuccessor: a universe code
-- typed at ANOTHER universe code pins classifierLevel = subjectLevel.lsucc ∧ flags agree (no conv slack) — via
-- inversion + universeCodeCell_inj_of_conv. universeCodeClassifierUnique: classifier uniqueness at a universe code
-- (concrete #469 — both classifiers Conv to Type@(subject+1), trans+sym). universeHierarchyHasNoTop (★): ¬∃ closed
-- topClassifier classifying the whole tower — instantiate at n=0,1, inversion gives Conv to Type@1 AND Type@2, so
-- Type@1 ≡ Type@2 (trans+sym), refuted by universeCodeCell_inj_of_conv + universeLevelOfNat_injective + decide ¬(1=2).
-- The antithesis of impredicative Type:Type (self-classifying top → Girard). Sits with #941 (irreflexive) + #945
-- (well-founded): the universe-code classification relation is a strict, rigid, well-founded, top-less ℕ-copy.
#assert_no_axioms FX1Poly.Typed.universeCodeClassifierIsSuccessor
#assert_no_axioms FX1Poly.Typed.universeCodeClassifierUnique
#assert_no_axioms FX1Poly.Typed.universeHierarchyHasNoTop
-- UNIVERSE PREDICATIVE (TypedUniversePredicative): the CAPSTONE of the universe arc — universe-code classification
-- IS the successor relation (both directions), and the engine is predicative (non-cumulative).
-- universeClassificationCharacterization (★): HasTypeDescPi Γ (Type@m,sf) (Type@n,cf) ↔ (n = m.lsucc ∧ cf = sf) —
-- forward = #1011 universeCodeClassifierIsSuccessor, backward = ofFormation∘universeFormation (the formation rule
-- is the ONLY way a universe code classifies into another). universeClassificationNotTransitive: Type@0:Type@1 ∧
-- Type@1:Type@2 ∧ ¬Type@0:Type@2 (predicativity as non-transitivity; positive rungs = #1010, negative = exact
-- char + level injectivity + decide ¬(2=1)). universeNotCumulativeBySkip (★): ∀ e flag, ¬ Type@e : Type@(e+2) —
-- the engine NEVER lets a universe code skip a level (mechanizes FX §1.1's predicative-hierarchy commitment), via
-- the exact char forcing e.lsucc.lsucc = e.lsucc, refuted by LevelExpr.ne_lsucc_self. With #941 (irreflexive),
-- #945 (well-founded), #1010 (inhabited), #1011 (rigid/top-less): the universe-code _:_ relation is now COMPLETELY
-- characterized as the successor relation on ℕ — every property distinguishing a predicative tower from Type:Type.
#assert_no_axioms FX1Poly.Typed.universeClassificationCharacterization
#assert_no_axioms FX1Poly.Typed.universeClassificationNotTransitive
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
#assert_no_axioms FX1Poly.Typed.curryOmega_notStronglyNormalizing
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
#assert_no_axioms FX1Poly.Typed.skkApplied_conv_identityApplied
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
-- CHURCH PAIR INJECTIVE (ChurchPairsInjective): faithfulness companion to #1017. pair_conv_injective (★): Conv
-- (pair a b)(pair c d) → Conv a c ∧ Conv b d — convertible pairs have convertible components. Apply churchFst/Snd
-- to both sides (Conv.app_cong, ConvCongruence.lean:193, + Conv.refl on the projector), the projections #1017 give
-- Conv (fst (pair a b)) a / Conv (fst (pair c d)) c, then Conv.trans∘Conv.sym∘Conv.fromStepStar collapse to Conv a
-- c (pairFst_conv_injective; pairSnd dual). With #1017's pairProjectionsRecover (recover), the Church pair is a
-- FAITHFUL product encoding: stores + recovers + distinguishes both components — the product universal property in
-- the pure Π-fragment.
#assert_no_axioms FX1Poly.Typed.pairFst_conv_injective
#assert_no_axioms FX1Poly.Typed.pairSnd_conv_injective
#assert_no_axioms FX1Poly.Typed.pair_conv_injective
-- CHURCH SUMS (ChurchSums): coproducts (Either) in the Π-fragment, dual to Church pairs (#1017), completing the
-- data-encoding story (bool #981 / nat #989 / products #1017 / SUMS). leftInjection a = λl.λr. l a (left handler,
-- var 1); rightInjection b = λl.λr. r b (right handler, var 0); a Church sum IS its own eliminator and its tag =
-- which handler it applies. caseLeft_selectsLeftHandler: case (inl I) l r ↝* l I — outer-binder β discards the
-- unselected handler r (left injection's body never mentions inner binder), lifted via function-position
-- Step.cong .gen_app () + StepChildren.here, then inner β recovers handlerL + the stored value through named
-- subst0-typed weaken_subst_singleton cancellations. caseRight_selectsRightHandler: case (inr I) l r ↝* r I
-- (dual, discards handlerL). caseSelectsByTag (★): both selections at once — the two injections distinguished
-- operationally by which handler case fires (the coproduct universal property syntactically). CONCRETE stored
-- value combinatorI (symbolic payload's weaken²a→weaken a is NOT rfl, needs a weaken/subst commutation lemma —
-- same deferral as CombinatoryCompleteness SKK / the general S-rule); symbolic-payload generalization deferred.
#assert_no_axioms FX1Poly.Typed.caseLeft_selectsLeftHandler
#assert_no_axioms FX1Poly.Typed.caseRight_selectsRightHandler
#assert_no_axioms FX1Poly.Typed.caseSelectsByTag
-- CHURCH SUM DISJOINT (ChurchSumsDisjoint): the coproduct FAITHFULNESS capstone, dual to Church-pair injectivity
-- (#1018). Case-selection (#1019) alone is not a coproduct; the defining property is that the two injections are
-- DISJOINT. leftInjection_not_conv_rightInjection (★): ¬ Conv (inl I)(inr I). Operational proof = the coproduct
-- universal property backwards: were they convertible, applying both to distinguishing handlers handlerToUniverse
-- (λx. Type@0) / handlerToIdentity (λx. I) and reducing via the shipped caseLeft/caseRight (#1019) forces
-- Conv (universeCode)(identity) — refuted by the shipped closedUniverseCode_not_conv_identity (distinct closed NFs,
-- different head generators). Conv.app_cong ×2 over hConv + StepStar.trans_compose with the two handler β-reductions
-- (handlerTo·_app_I, each one Step.beta + named subst0-typed weaken_subst_singleton cancellation). The sum-side
-- analogue of #983 (churchTrue ≢ churchFalse): two closed values kept operationally apart. rightInjection_not_conv_
-- leftInjection = symmetric via Conv.sym. Concrete payload combinatorI (as #1019); tags differ regardless.
#assert_no_axioms FX1Poly.Typed.handlerToUniverse_app_I
#assert_no_axioms FX1Poly.Typed.handlerToIdentity_app_I
#assert_no_axioms FX1Poly.Typed.leftInjection_not_conv_rightInjection
#assert_no_axioms FX1Poly.Typed.rightInjection_not_conv_leftInjection
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
#assert_no_axioms FX1Poly.Typed.succTowerOneParity
#assert_no_axioms FX1Poly.Typed.succTowerTwoParity
#assert_no_axioms FX1Poly.Typed.lengthOneAppliedParity
#assert_no_axioms FX1Poly.Typed.lengthTwoAppliedParity
#assert_no_axioms FX1Poly.Typed.lengthDistinguishesByParity

/- Variable arm of grown strengthening (GrownStrengthening): the inverse of weakenUnderBinding for the
non-recursive (var) leaf — the base case of strengthenUnderBinding and first consumer of Conv.reflectWeaken
(#1167). strengthenVariableClassifier strips the weaken off a var's classifier Conv; strengthenVariableUnderBinding
re-types the var at the strengthened classifier given its validity. Toward grown η-contraction SR (#477/PAR-2). -/

#assert_no_axioms FX1Poly.Typed.lookupConsSuccEqWeaken
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.strengthenVariableClassifier
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.strengthenVariableUnderBinding

/- Existential-form grown strengthening REFUTED (GrownStrengtheningRefutation): the grown conv arm
reclassifies a weakened subject at a β-expansion mentioning the fresh variable, so a weakened subject's
classifier is NOT forced into the weaken image. Pins GrownStrengtheningUnderBindingTarget (both subject
and classifier weakened) as the campaign target — proven via checker completeness ∘ rename-equivariance ∘
soundness, not derivation induction. -/

#assert_no_axioms FX1Poly.Typed.escapingReclassifier
#assert_no_axioms FX1Poly.Typed.weakenedSubjectGrownTypedAtEscapingClassifier
#assert_no_axioms FX1Poly.Typed.escapingReclassifier_isOutsideWeakenImage
#assert_no_axioms FX1Poly.Typed.grownStrengtheningExistentialForm_isFalse
#assert_no_axioms FX1Poly.Typed.GrownStrengtheningUnderBindingTarget

/- The syntax-directed grown checking RELATION (GrownCheck): one arm per subject head shape, recursive
premises only on strict subterms, Conv only at compare leaves, no typehood premises — the
grown-strengthening campaign's central object (completeness ∘ rename-reflection ∘ soundness). absorbConv is
the recursion-free conv-absorption (completeness's conv-arm discharge); the leaf soundness lemmas
reconstruct typing at a typed target; the smokes pin the identity-λ check and the STR-1 escaping
reclassifier's GrownCheck-reachability (why the reflection conclusion is the Conv-existential). -/

#assert_no_axioms FX1Poly.Typed.GrownCheck
#assert_no_axioms FX1Poly.Typed.GrownCheckTelescope
#assert_no_axioms FX1Poly.Typed.GrownCheck.absorbConv
#assert_no_axioms FX1Poly.Typed.GrownCheck.variableSoundAtTypedTarget
#assert_no_axioms FX1Poly.Typed.GrownCheck.universeCodeSoundAtTypedTarget
#assert_no_axioms FX1Poly.Typed.grownCheckIdentityLambdaSmoke
#assert_no_axioms FX1Poly.Typed.grownCheckEscapingReclassifierSmoke

/- GrownCheck structural helpers (GrownCheckContextConversion): EXACT-target context conversion under
pointwise-Conv contexts (raw relation → no wf needed, contrast convContextUnderWf) + the Conv-related-binders
cons condition + the binder-swap corollary (the reflection's swap-the-floating-binder ingredient) + the
target-side Π exposure (reducesToPiTyCode ∘ subjectReductionStar ∘ invertPiTyCode, wf-conditional) + the
lam/app soundness reassembly shapes consumed by the STR-5 soundness induction. -/

#assert_no_axioms FX1Poly.Typed.convContextCondition_consConv
#assert_no_axioms FX1Poly.Typed.GrownCheck.convContext
#assert_no_axioms FX1Poly.Typed.GrownCheckTelescope.convContext
#assert_no_axioms FX1Poly.Typed.GrownCheck.convBinder
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piTargetExposure
#assert_no_axioms FX1Poly.Typed.GrownCheck.lamSoundGivenBodyTyped
#assert_no_axioms FX1Poly.Typed.GrownCheck.appSoundGivenComponentsTyped

/- Raw-relation SOUNDNESS REFUTED (GrownCheckSoundnessRefutation): the Curry fix-point TYPE
X := curryOmega (λT. Π T. Type@0) — with X ~Conv~ Π X. Type@0 — threads the app arm's floating Π-code, so
Ω = (λx.xx)(λx.xx) CHECKS at the typed target Type@0 while being untypable (SN-043). The
completeness ∘ reflection ∘ soundness pipeline cannot run over the RAW relation; typehood must enter via an
annotated judgment (campaign log carries the surviving routes). -/

#assert_no_axioms FX1Poly.Typed.recursivePiType
#assert_no_axioms FX1Poly.Typed.recursivePiType_convPi
#assert_no_axioms FX1Poly.Typed.selfApplicationBodyChecks
#assert_no_axioms FX1Poly.Typed.selfApplicationChecksAtPi
#assert_no_axioms FX1Poly.Typed.selfApplicationChecksAtRecursiveType
#assert_no_axioms FX1Poly.Typed.omegaChecksAtTypeZero
#assert_no_axioms FX1Poly.Typed.grownCheckRawSoundness_isFalse

/- ConvExistentialStrengtheningRefutation — RETIRED refutation (T2 flipped it; user-approved
deletion 2026-06-10).  `convExistentialStrengthening_isFalse` is gone: under T2 `piIntro` pins
the λ annotation, the pre-T2 floating-domain witness is untypeable, and the Conv-existential
strengthening is expected TRUE.  Survivors: the variable-domain Π and its normality, the
RESTATED typing witness (the var-0-ANNOTATED identity), and `notConvWeakenImage` — which now
documents WHY the annotation pin is load-bearing rather than refuting anything. -/

#assert_no_axioms FX1Poly.Typed.variableDomainPi
#assert_no_axioms FX1Poly.Typed.variableDomainPi_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.weakenedIdentityTypedAtVariableDomainPi
#assert_no_axioms FX1Poly.Typed.variableDomainPi_notConvWeakenImage

/- The pinning analysis (PinnedPiImageComponents): a Π-classifier Conv to a weakening exposes components
EXACTLY in the weaken image (reducesToPiTyCode ∘ StepStar.reflectRename ∘ the mkGen drilling) — the brick
every binder arm of the route-H pinned reflection consumes; under the pinned premise the historical
floating-domain wall hands the piIntro arm an exact in-image representative. -/

#assert_no_axioms FX1Poly.Typed.Conv.pinnedPiComponentsInWeakenImage

/- The pinning analysis over an arbitrary renaming (PinnedPiRenameImage) — under binders the route-H
reflection works at lift ρ, so the weaken-specific analysis generalizes over the renaming; plus the
λ-head rename inversion (the subject-destructuring step of the reflection's piIntro arm: an image λ
comes from a λ with the body an exact lift-image). -/

#assert_no_axioms FX1Poly.Typed.Conv.pinnedPiComponentsInRenameImage
#assert_no_axioms FX1Poly.Typed.Conv.pinnedPiComponentsWithSourceChain
#assert_no_axioms FX1Poly.Typed.renameEqLamCellInversion
#assert_no_axioms FX1Poly.Typed.renameEqAppCellInversion

/- The pinned reflection's context condition + leaf arms (PinnedReflectionContext): the
Kripke/Conv-relaxed image context condition (exact-image base instance for strengthening + the
lift/cons extension that survives binders with a merely Conv-pinned domain), the var/universe head
rename inversions, and the formation-engine var/universeFormation arms of the route-H reflection in
the motive's conclusion shape. -/

#assert_no_axioms FX1Poly.Typed.ContextReflectsRename.ofWeakenCons
#assert_no_axioms FX1Poly.Typed.ContextReflectsRename.consConv
#assert_no_axioms FX1Poly.Typed.renameEqVariableCellInversion
#assert_no_axioms FX1Poly.Typed.renameEqUniverseCodeCellInversion
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.varArmPinnedReflection
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.universeArmPinnedReflection

/- THE route-H reflection motive + its piIntro arm (PinnedReflectionPiIntro) — the historical
strengthening wall (the freely-chosen-domain binder case behind the STR-1/STR-5b refutations),
closed under the pinned motive: λ-subject inversion → pinning analysis with source chain → source
SR + Π-formation inversion (source-side universe premises) → Kripke context extension → body IH at
lift ρ → injective Conv reflection re-pins the reflected body classifier → piIntro rebuild. -/

#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiIntroArm

/- The formation-engine MASTER reflection (FormationPinnedReflection) — UNCONDITIONAL and PIN-FREE:
the formation engine has no piElim, so the full mutual (term + telescope legs) closes with no
residual.  retypeAtUniverse is the telescope-head re-pin move (injective Conv reflection + the conv
rule); renameEqMkGenInversion the non-var subject destructuring; the telescope leg reflects EXACTLY
(exact-image heads at the depth-lifted renaming). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDesc.retypeAtUniverse
#assert_no_axioms FX1Poly.Typed.renameEqMkGenInversion
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.pinnedReflection
#assert_no_axioms FX1Poly.Typed.DescTelescope.pinnedReflectionTelescope

/- THE CONDITIONAL GROWN MASTER reflection (GrownPinnedReflection): the full pinned reflection over
HasTypeDescPi/DescTelescopePi with ofFormation (pin-free formation master) / conv (re-pin through
the conversion) / piIntro (the brick-6 arm) / genFormationPi (grown telescope leg, heads pinned by
rename-invariant universe codes) all discharged — piElim is the ONE explicit residual
(PinnedReflectionPiElimResidual, the function-Π float, the campaign's open core). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.retypeAtUniverse
#assert_no_axioms FX1Poly.Typed.pinnedReflectionOfFormationArm
#assert_no_axioms FX1Poly.Typed.pinnedReflectionConvArm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionConditional
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.pinnedReflectionTelescopeConditional

/- THE piElim residual's CORE + first concrete instance (PinnedReflectionPiElimCore): the residual
conclusion holds whenever the FUNCTION's Π classifier is pinned (the consumer shape for every head
analysis — pin analysis with source chain → source SR + Π-formation inversion → reflect function +
argument via the premise IHs → injective-Conv re-pins → piElim rebuild → rename_subst0_commute
output Conv); and the var-headed producer, whose Π pin is free from invertVar + the Kripke context
condition + lookupIsType. -/

#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimCore
#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimVarArm
#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimReducesToVarArm

/- Open SN under GROWN context well-formedness (GrownWfOpenStronglyNormalizing): the
WfContextDescPi-keyed twins of the formation-wf open SN — the reducible closing environment reads
each binding's grown universe typing directly off the grown wf's cons component (no
formation→grown embedding), and the SN assembly is the identical wire.  The SN supply for the
pinned-reflection whnf dispatcher, whose motive carries exactly this wf. -/

#assert_no_axioms FX1Poly.Typed.reducibleEnvOfWfContextDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDescPi

/- The piElim-residual whnf DISPATCHER (PinnedReflectionPiElimDispatcher): the FULL residual
reduces to the two head-specific residuals (λ-after-whnf + neutral-reduct-after-whnf, the latter's
bare-var instance pre-discharged) via grown-wf SN → normalize → SR-star → the wf-FREE canonical
forms (copies of the shipped open canonical forms with the vestigial formation-wf premise
deleted). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalSubjectCanonicalOrNeutralOfTyping
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalFunctionIsLambdaOrNeutralOfTyping
#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimResidualOfHeadResiduals

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
#assert_no_axioms FX1Poly.Typed.RawTerm.isStepNormalForm_childrenNormal
#assert_no_axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_head
#assert_no_axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_tail

/- The SIZE-GUARDED conditional master (GuardedPinnedReflection) — the knot-cutting form: the
conditional master with (size ≤ bound) + normality threaded through the mutual, residual parameter
weakened to the bound-guarded normal-application form.  The guarded residual at bound N only ever
consumes the guarded master at strictly smaller pieces, making ∀ bound, ResidualGuarded provable
by strong induction (the plateau master). -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionGuarded
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.pinnedReflectionTelescopeGuarded

/- ★ THE PLATEAU INDUCTION (PlateauPinnedReflection): the guarded piElim residual holds at EVERY
bound — the strengthening campaign's recursion knot CLOSES.  The spine pin-extraction pins the
classifier of every normal non-λ in-image subject (formation classifiers by condition/
rename-invariance; application classifiers by recursive head pin + guarded-master argument
reflection at a smaller bound + substitution-lemma codomain instantiation); the residual then
finishes through pinnedReflectionPiElimCore.  Harvest: pinnedReflectionNormal — the FULL pinned
reflection for every NORMAL grown-typed subject. -/

#assert_no_axioms FX1Poly.Typed.formationClassifierPinned
#assert_no_axioms FX1Poly.Typed.normalNonLambdaClassifierPinned
#assert_no_axioms FX1Poly.Typed.piElimResidualGuardedWithinBudget
#assert_no_axioms FX1Poly.Typed.piElimResidualGuardedAtEveryBound
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionNormal

/- The NEUTRAL-REDUCT head residual HOLDS (NeutralReductResidualDischarge): a neutral is never a
λ (12-arm head discrimination), the whnf reduct is in-image and keeps the Π classifier by subject
reduction, the plateau pin-extraction pins it (the ∀-bound guarded residual frees the budget
guard), and the pinned-function core finishes with the original premise reflections.  One
λ-reduct residual now remains before the full piElim residual discharges. -/

#assert_no_axioms FX1Poly.Typed.IsNeutral.ne_lamCell
#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimNeutralReductResidualHolds

/- The bare λ-classifier pin factorization (PinnedReflectionLamClassifierResidual): the residual
implies the λ-reduct head (mirror of the neutral discharge), hence the full piElim residual,
hence the MASTER.  Pre-T2 the residual was refuted (the unguarded λ-classifier float);
`pinnedReflectionLamClassifierResidual_isFalse` is RETIRED (user-approved deletion 2026-06-10) —
under T2 the annotation pin kills the float witness and the residual is expected TRUE, making
these conditionals the live assembly route. -/

#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimLamReductResidualOfLamClassifierResidual
#assert_no_axioms FX1Poly.Typed.pinnedReflectionPiElimResidualOfLamClassifierResidual
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionOfLamClassifierResidual

/- Enrichment brick E1 (FlagCoherentReflectionCondition): the flag-coherent reflection condition —
per-variable SHARED-universe validity pairs (the Π-pin reassembly's flag-coherence payload),
with the non-circular strengthening base instance (wf-lookup validity + weakening; the
implication-form payload would BE universe-classified strengthening at the root) and the
Kripke extension step. -/

#assert_no_axioms FX1Poly.Typed.SharedUniverseValidityWithImage.toSharedUniverseValidity
#assert_no_axioms FX1Poly.Typed.ContextReflectsRenameFlagCoherent.toContextReflectsRename
#assert_no_axioms FX1Poly.Typed.ContextReflectsRenameFlagCoherent.ofWeakenCons
#assert_no_axioms FX1Poly.Typed.ContextReflectsRenameFlagCoherent.consConv

/- Enrichment spike E2.5 GO (UniverseClassificationUnique): a Conv-class contains at most one
universe code (rigidity), so universe classifications drawn from one Conv-class coincide —
validated at the variable leaf via inversionVariable.  The flag negotiation closes at leaves. -/

#assert_no_axioms FX1Poly.Typed.Conv.universeCode_injective
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

/- E2.7 former-arm core (TelescopeUniverseDeterminism): two grown telescopes over the same
children agree on levels, and on the flag for nonempty children — IH-parameterized (the
strong-size-induction seam), table-generic, budget through size peeling. -/

#assert_no_axioms FX1Poly.Typed.DescTelescopePi.universeDeterminismOfChildIH

/- E2.7 former-arm inversion (GenericFormerTelescopeInversion): ONE table-generic grown
inversion for every formation row — keeps the premise telescope over the subject's own children
AND pins the classifier to the universe former's output code.  Unconditional; new rows need no
new arm. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.invertFormerTelescopeWithConvGeneric

/- E2.7 MASTER (NormalUniverseClassificationUnique): two grown universe classifications of one
NORMAL subject agree on (level, flag) — budget-recursive 5-way root dispatch; the former arm's
flag agreement is anchored by the table-wide nonempty-binder-shifts fact.  Unconditional,
table-generic — the flag-negotiation keystone of the strengthening enrichment campaign. -/

#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_binderShiftsNonempty
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.levelsNonemptyOfShiftsNonempty
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalUniverseClassificationUniqueAtBudget
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalUniverseClassificationUnique

/- E2.8 Conv-lift (ConvUniverseClassificationUnique): convertible subjects classified at
universe codes carry EQUAL (level, flag) under grown wf — open SN normalizes both, SR-star
re-types the pins, the join collapses at the shared normal form, the E2.7 master negotiates. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convUniverseClassificationUnique

/- E3 core (RenameAlongFlagCoherent): grown typing is preserved along ANY renaming satisfying
the flag-coherent Conv condition — both engines (the formation companion renames INTO the grown
engine; its var arm consumes the image component as the conv-rule reclassifier).  The forward
fibration leg that collapses every pinned-reflection flag negotiation to one E2.8 application. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDesc.renameAlongFlagCoherentToGrown
#assert_no_axioms FX1Poly.Typed.DescTelescope.renameAlongFlagCoherentToGrownTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.renameAlongFlagCoherent
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.renameAlongFlagCoherentTelescope

/- E3 capstone (PinSelectsCallerPair): THE flag wall closed — a pinned base's universe pair is
forced to the caller's (forward renaming + Conv-lifted uniqueness), and any ∃-flag pin base
re-types at the caller's EXACT (level, flag).  The λ-reduct Π-components inherit invertLam's
shared flag; piIntro reassembles. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinSelectsCallerPair
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinBaseValidAtCallerPair

/- E2-0 (PinnedReflectionFlagCoherent): the flag-coherent pinned-reflection motive + the free
transfer of the shipped conditional master (the enriched condition projects) + the enriched
residual definitions — the precise route-(A) discharge targets. -/

#assert_no_axioms FX1Poly.Typed.PinnedReflectionConclusion.toFlagCoherent
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.pinnedReflectionFlagCoherentOfPlainResidual
