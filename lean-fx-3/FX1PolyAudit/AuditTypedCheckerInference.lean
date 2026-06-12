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
import FX1Poly.Typed.CombinedClosedNormalValueHeads
import FX1Poly.Typed.CombinedNatCanonicalForms
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

/-! # FX1PolyAudit/AuditTypedCheckerInference — typed-layer zero-axiom gates: the typecheckers, deciders, NbE normalizers, and complexity witnesses
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

-- DECIDABILITY (P11 0-FN) of the description engine.  `decidableOfWellFormed` is a native
-- formation decision procedure.  `Conv.decidableOfHasTypeDesc` decides Conv by SN: each classifier
-- is SN by the native `HasTypeDesc.classifierStronglyNormalizing`, fed to the parameter-free
-- `Conv.decidableOfStronglyNormalizing`.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormed
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfHasTypeDesc
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
#assert_no_axioms FX1Poly.Typed.discardedBody_isNormalForm
#assert_no_axioms FX1Poly.Typed.discardingApplicationOnOmega_argumentSelfLoop
-- Conv on the NORMAL FRAGMENT is DECIDABLE and the decider EXECUTES (ConvValueDiscrimination, constructive
-- companion to the non-degeneracy facts): convDecidableOfBothNoStep packages the ConvNormalForm seed as an
-- actual Decidable (decidable_of_iff (left=right) ∘ Conv.iff_eq_of_noStep, over the propext-free DecidableEq
-- RawTerm — no normalizer). The convDecider_* equations are `@decide … = true/false` by rfl: the decider RUNS
-- and computes the right boolean (Conv boolTrue boolTrue → true; boolTrue/boolFalse, boolTrue/unit → false). No
-- native_decide; the evaluations reduce over the structural DecidableEq.
#assert_no_axioms FX1Poly.Typed.convDecidableOfBothNoStep
#assert_no_axioms FX1Poly.Typed.convDecider_boolTrueValue_self_isTrue
#assert_no_axioms FX1Poly.Typed.convDecider_boolTrueValue_boolFalseValue_isFalse
#assert_no_axioms FX1Poly.Typed.lamCell_isStepNormalForm
-- FIRST LANE CROSSING: the FT-derived SN results discharge the SN-fragment conversion decider
-- (Conv.decidableOfStronglyNormalizing — normalize each, compare NF), yielding UNCONDITIONAL decidable Conv
-- for concrete closed terms (β-redex vs reduct, β-redex vs identity). The general bridge is conditional on the
-- FT conclusion (becomes unconditional with the recursor). betaRedexConvertsToReduct is the non-vacuity witness
-- (the redex really converts to its reduct). Concrete realization of raw decidable Conv (#267 / #503).
#assert_no_axioms FX1Poly.Typed.closedConvDecidableFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.decidableConvBetaRedexAndReduct
#assert_no_axioms FX1Poly.Typed.decidableConvBetaRedexAndIdentity
#assert_no_axioms FX1Poly.Typed.closedConv_iff_normalForm_eq
#assert_no_axioms FX1Poly.Typed.closedBetaRedexNormalForm_eq
#assert_no_axioms FX1Poly.Typed.closedIdentityNormalForm_eq
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
#assert_no_axioms FX1Poly.Typed.konstAppliedToVariableNormalForm
#assert_no_axioms FX1Poly.Typed.konstAppliedToVariable_normalizes
#assert_no_axioms FX1Poly.Typed.konstNormalForms_congruentlyEqual

/-! ### TypedNbeNormalizer — ★ #480: the typed NbE EVAL half + the eval∘quote composition

The typed normalizer assembled from its two halves.  EVAL (`evalNormalForm`, #480): β/ι
normalization of well-typed OPEN terms — `RawTerm.normalize` with the open-SN witness
(`stronglyNormalizingOfWfContextDesc`) as the termination certificate; total, fuel-free; the
output reduces from the input, is structurally normal, converts to the input, and — the
headline — is TYPED AT THE SAME CLASSIFIER (`evalNormalForm_typed` via the unconditional master
`subjectReductionStar`).  QUOTE: the #481 type-directed η-long readback.  The composition
`nbeNormalForm = quote ∘ eval` carries the composed soundness (`nbeNormalForm_congruent`:
`ofBetaEtaConv` along the normalization chain, then the readback soundness on the typed eval
output) and the #364-shaped semi-decision (`DefEqUnitEtaCong.ofNbeEqual`).  EACH HALF IS
LOAD-BEARING: eval contracts the typed β-redex `(λx.x)(Type@e)` (the pair with its reduct is
decided — `identityApplicationPair_decidedByNbe`) while quote alone provably fixes the
unevaluated redex (`readbackAlone_keepsBetaRedex`); conversely the η/unit pairs of the #481
modules are β-normal and decided only by quote.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.evalNormalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.evalNormalForm_reducesTo
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.evalNormalForm_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.evalNormalForm_conv
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.evalNormalForm_typed
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.nbeNormalForm
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.nbeNormalForm_congruent
#assert_no_axioms FX1Poly.Typed.universeCode_evalNormalForm_eq
#assert_no_axioms FX1Poly.Typed.identityApplication_evalNormalForm_eq
#assert_no_axioms FX1Poly.Typed.identityApplicationPair_decidedByNbe

/-! ### TypedNbeConvDecision — ★ #364: the typed NbE conversion check, sound + complete-at-unit

The normalize-and-compare check over the composed typed NbE normalizer: `checkNbeEqual`
(executable `decide` over the kernel's `DecidableEq RawTerm`), SOUND unconditionally
(`checkNbeEqual_sound` — a passing check certifies the full typed judgmental equality
`DefEqUnitEtaCong`), and sound AND complete at the UNIT classifier: the readback is CONSTANT
at `unitTypeCell` on a SYMBOLIC subject (`readbackAtClassifier_constantAtUnit`, `rfl`), so
every unit-typed NbE form at positive fuel is `unitCell`
(`nbeNormalForm_constantAtUnit`, still `rfl` through eval), any two unit-typed subjects check
equal (`nbeComplete_atUnit`), and `checkNbeEqual = true ↔ DefEqUnitEtaCong` there
(`checkNbeEqual_iff_atUnit` — the first total 0/0 cell of the NbE decider;
`DefEqUnitEtaCong.decidableAtUnit` realizes the `Decidable`).  Honest ledger: β/ι completeness
is the shipped `conv_iff_normalForm_eq`; η/congruent completeness holds on the ten #481
boundary verdicts and is UNPROVEN jointly (O-NORM).  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.checkNbeEqual
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.checkNbeEqual_sound
-- FIRST CONCRETE DATA CANDIDATE — bool (SN-063 data core), unconditional + zero-axiom: boolIsValue := the
-- true/false constructor cells; boolIsValue values are structural normal forms (isStepNormalFormBool computes
-- to true); the candidate is isReducibilityCandidateOfValuesNormal at boolIsValue (CR1+CR2+CR3, neutral half
-- via IsNeutral.closedUnderStep); both canonical inhabitants are members (Acc.intro over no_step_from_bool*).
#assert_no_axioms FX1Poly.Core.boolIsValue_impliesStepNormalForm
-- RECURSIVE data candidate — Nat (SN-060/062): IsNatValue is the inductive numeral predicate; numerals are
-- structural normal forms by induction (a natSucc cell is normal iff its predecessor is); the candidate is
-- isReducibilityCandidateOfValuesNormal at IsNatValue; every numeral is a member (memberOfValue); a closed
-- member reduces to a numeral (closedReducesToValue). Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isNatValue_impliesStepNormalForm
-- BINARY data candidate — Σ pairs (SN-057/059): isPairValue := a pairCell with both components normal; a
-- pair of normals is a structural normal form (the two-child spine recursion); the candidate is
-- isReducibilityCandidateOfValuesNormal at isPairValue; a normal pair is a member (memberOfValue); a closed
-- member reduces to a pair (closedReducesToValue). Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isPairValue_impliesStepNormalForm
-- MODAL layer data candidate — modIntro (SN-073 data core): the modal box is a single unary constructor
-- (option-some shape); isModIntroValue := modIntro of a normal payload; value-normality is the one-child
-- spine; candidate via isReducibilityCandidateOfValuesNormal; a normal box is a member (memberOfValue); a
-- closed member reduces to a modIntro. Over β+ι Step (raw modal η is a separate relation). #672-free.
#assert_no_axioms FX1Poly.Core.isModIntroValue_impliesStepNormalForm
-- RICHEST data candidate — List (SN-064): IsListValue inductive combines nullary nil + binary-recursive cons
-- (head normal like pair, tail recursive like Nat); list values are normal forms by induction; the candidate
-- is isReducibilityCandidateOfValuesNormal at IsListValue; every list value is a member (memberOfValue); a
-- closed member reduces to a list constructor (closedReducesToValue). Unconditional + #672-free.
#assert_no_axioms FX1Poly.Core.isListValue_impliesStepNormalForm
-- OPTION data candidate (SN-065): isOptionValue := none | some payload (payload normal) — nullary + unary,
-- no recursion; option values are normal forms; the candidate is isReducibilityCandidateOfValuesNormal at
-- isOptionValue; every option value is a member (memberOfValue); a closed member reduces to none/some.
#assert_no_axioms FX1Poly.Core.isOptionValue_impliesStepNormalForm
-- EITHER (sum) data candidate (SN-066): isEitherValue := inl payload | inr payload (payload normal) — two
-- unary tagged arms; either values are normal forms; the candidate is isReducibilityCandidateOfValuesNormal
-- at isEitherValue; every either value is a member (memberOfValue); a closed member reduces to inl/inr.
-- Completes the tagged-union extraction family (option + either).
#assert_no_axioms FX1Poly.Core.isEitherValue_impliesStepNormalForm
-- IDENTITY refl data candidate (SN-067): isReflValue := refl witness (witness normal) — the single unary
-- introduction of the identity type; refl values are normal forms; the candidate is
-- isReducibilityCandidateOfValuesNormal at isReflValue; every refl value is a member (memberOfValue); a closed
-- member reduces to a refl. Completes the data-introduction extraction family.
#assert_no_axioms FX1Poly.Core.isReflValue_impliesStepNormalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormUniqueUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormUniqueClosed

-- INHABITATION CORPUS for the simply-typed term FT (the fundamental theorem is non-vacuous): concrete
-- `SimplyTypedTermLF` derivations of the polymorphic identity at a universe base type and at an arrow type,
-- with their strong normalization as fundamental-theorem corollaries.  Simply-typed analogue of TY-honesty.
#assert_no_axioms FX1Poly.Typed.identityIsSimplyTyped
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
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedBareClosed
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
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_betaRedex_false
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_identityLambda_true
#assert_no_axioms FX1Poly.Typed.fireRootRedex_betaIdentity_fires
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_typed

-- CANONICITY (PROGRESS) — the classic STLC capstone, completing the simply-typed metatheory.  Closed normal
-- forms are lambdas: a LnNeutral term (var-headed app spine) is impossible at scope 0, the canonicalSplit
-- inducts on typing (β-redex case killed by Step.beta + blocks_step, child-normality via cong), and
-- normalFormIsLambda composes it with type-preserving normalization — every closed simply-typed term
-- normalizes to a lambda.
#assert_no_axioms FX1Poly.Typed.lnNeutral_scopeZero_absurd
#assert_no_axioms FX1Poly.Typed.isStepNormalForm_appCell_function
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormIsLambda

-- INHABITATION / CONSISTENCY — the final theorem of the simply-typed metatheory.  Every closed simply-typed
-- term has an arrow type (canonicity says its NF is a lambda, type-preserving normalization keeps the type,
-- lambda inversion makes the type an arrow); hence universe codes are uninhabited by closed terms (arrow vs
-- universe-code head generators differ) — the fragment's consistency.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.closedTermHasArrowType
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.noClosedTermAtUniverseCode
#assert_no_axioms FX1Poly.Typed.SimplyTypedClosedTerm.decidableConvertsTo

-- The PRODUCTIVE MIRROR of `isStepNormalForm_blocks_step`: a non-normal term genuinely reduces, with the
-- reduct exhibited.  Mutual term + child-spine halves.  Combines the root-redex dispatch (root conjunct) with
-- a structural recursion into the child spine (`Step.cong` / `StepChildren.here` / `StepChildren.there`).
-- The step-extraction the `Acc StepSuccessor` weak-normalization descent calls at every non-normal node.
#assert_no_axioms FX1Poly.Core.exists_step_of_not_isStepNormalForm
#assert_no_axioms FX1Poly.Core.exists_stepChildren_of_not_areStepNormalForms

-- NORMAL-FORM UNIQUENESS: confluence forces two normal reducts of one SN term to coincide, so the SN
-- fragment has a UNIQUE normal form (existence from WN + this uniqueness clause).  The "the normal form"
-- handle a normalizer function realizes and SN-fragment decidable Conv (#267) rests on.
#assert_no_axioms FX1Poly.Core.normalForm_unique
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

-- SN-051 / SN-046-uncond (WfContextDecidableConv.lean): the open-SN-043 harvest, routed through the
-- HasTypeDesc-defined WfContextDesc via the bridge-free stronglyNormalizingOfWfContextDesc. Two well-typed
-- subjects in a well-formed context have DECIDABLE Conv (no typed-SN hypothesis — each OB-5 SN witness feeds the
-- parameter-free decider Conv.decidableOfStronglyNormalizing), and global confluence holds (per-term Newman on
-- the OB-5 SN witness). The qualifier is "assume WfContextDesc" (a decidable presupposition; the unqualified
-- typed-SN interface is unprovable since the var rule types in any context).
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfWellTypedInWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectWeaklyNormalizesOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.uniqueNormalFormOfWfContextDesc
-- SN-052 COMPARE step: checking a subject against a KNOWN-TYPE target reduces to deciding Conv (SN-051) — the
-- load-bearing infer-mode step of the bidirectional checker. isTrue via the grown conv rule; isFalse via the
-- subject's per-term uniqueness (holds for every non-λ subject). Typing witnesses threaded explicitly (data),
-- since Decidable cannot large-eliminate the Prop-valued IsTypeDesc existential.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckOfInferredUniqueAtType
-- SN-052 first COMPLETE checker case: deciding a VARIABLE against a known-type target (CHECK mode, SR-free)
-- composes the COMPARE step + variable inversion + variable inference + context validity
-- (IsType.decideWithWitness for the lookup's typehood-as-data, WfContext.lookupIsType refuting the impossible
-- non-type branch). The template for the application infer-mode case.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckVariableAtType
-- SN-052 second COMPLETE checker case (closes the SR-free leaf fragment): deciding a UNIVERSE CODE against a
-- known-type target (CHECK mode, SR-free). Strictly simpler than the variable case — both the inference and
-- its classifier-typing are direct universeFormation constructors, so no IsType.decideWithWitness is needed.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckUniverseCodeAtType
-- SN-052 APPLICATION checker case, factored over the SR-gated function exposure: given the function's Π-typing
-- + type-uniqueness + the Π-components' universe-typings (threaded as input — the eventual recursive inference
-- delivers them once the SR exposure lands), the application check against a known-type target reduces to the
-- argument's check against the domain. isTrue: piElim + substituteUnderBinding + applicationTypeUniqueGivenFunction
-- + COMPARE step; isFalse: invertApp + Conv.piTyCode_inj + conv show the application cannot be typed at all.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckApplicationGivenFunction
-- SN-052 Π/Σ-FORMATION checker cases (closes the infer-mode SR-free combinator coverage): deciding a former
-- against a known-type target given its components' universe-typings + uniqueness (threaded as input — the
-- recursive component-inference delivers them). SR-free: a former needs no exposure (its components are already
-- type codes), so the whole decision is the COMPARE step. {pi,sigma}FormationViaGenArm infers, universeFormation
-- types the inferred universe, {pi,sigma}FormationTypeUniqueGivenComponents supplies uniqueAtSubject.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckPiFormationGivenComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckSigmaFormationGivenComponents

-- Ω HAS NO NORMAL FORM — sharpening "not SN" into "never reaches a Step-normal term." selfApplicator is itself
-- normal (by decide); Ω's only one-step reduct is Ω (Step.from_app inversion, congruence shapes refuted by the
-- self-applicator being normal); its only StepStar-reduct is Ω (chain induction, both endpoints generalized);
-- hence no reachable term is normal. The exact obstruction a raw weak-normalization proof cannot clear — closed,
-- well-scoped, ill-typed, every reduction path diverges (the reason SN-043/WN need the typing restriction).
#assert_no_axioms FX1Poly.Typed.selfApplicator_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.divergentOmega_reductIsSelf
#assert_no_axioms FX1Poly.Typed.divergentOmega_starReductIsSelf
#assert_no_axioms FX1Poly.Typed.divergentOmega_noNormalForm
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
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_emptyCodeDeferred
#assert_no_axioms FX1Poly.Typed.crossRef_uniqueNormalForm
#assert_no_axioms FX1Poly.Typed.crossRef_decidableConversion
#assert_no_axioms FX1Poly.Typed.crossRef_newmanLemma
#assert_no_axioms FX1Poly.Typed.correctedLamReview_corpusCheck
#assert_no_axioms FX1Poly.Typed.correctedLamReviewGate
#assert_no_axioms FX1Poly.Typed.correctedLamReviewGate_passes
#assert_no_axioms FX1Poly.Typed.universeFormationReview_corpusCheck
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
-- ID-TOWER COLLAPSE (IdentityTowerFamily, appended): the family collapses to one canonical value via conversion
-- + the SN-112 normalizer. universeCodeCell_isStepNormalForm: Type@e is a step-NF (rfl over the Bool normality
-- check, free level/flag — nullary leaf, payload-independent). idTower_convToValue: each member converts to Type@e
-- (Conv.fromStepStar of idTower_reducesToValue). idTower_allConvertible: all members mutually convertible (one
-- Conv-class joined through Type@e, trans+sym). idTower_normalForm_eq_value: the computed normalForm of every
-- member = Type@e (firing-72 reachedNormalForm_eq_normalForm on the reduction to the normal value).
-- idTowerCollapsesToCanonicalValue: ★ infinitely many syntactically-distinct well-typed terms, all definitionally
-- equal, all normalizing to the single canonical value — the conversion/normalization face of the typed family.
#assert_no_axioms FX1Poly.Typed.universeCodeCell_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.idTower_normalForm_eq_value

/- The syntax-directed grown checking RELATION (GrownCheck): one arm per subject head shape, recursive
premises only on strict subterms, Conv only at compare leaves, no typehood premises — the
grown-strengthening campaign's central object (completeness ∘ rename-reflection ∘ soundness). absorbConv is
the recursion-free conv-absorption (completeness's conv-arm discharge); the leaf soundness lemmas
reconstruct typing at a typed target; the smokes pin the identity-λ check and the STR-1 escaping
reclassifier's GrownCheck-reachability (why the reflection conclusion is the Conv-existential). -/

#assert_no_axioms FX1Poly.Typed.GrownCheck
#assert_no_axioms FX1Poly.Typed.GrownCheck.absorbConv
#assert_no_axioms FX1Poly.Typed.GrownCheck.variableSoundAtTypedTarget
#assert_no_axioms FX1Poly.Typed.GrownCheck.universeCodeSoundAtTypedTarget
#assert_no_axioms FX1Poly.Typed.grownCheckIdentityLambdaSmoke
#assert_no_axioms FX1Poly.Typed.grownCheckEscapingReclassifierSmoke
#assert_no_axioms FX1Poly.Typed.GrownCheck.convBinder
#assert_no_axioms FX1Poly.Typed.GrownCheck.lamSoundGivenBodyTyped
#assert_no_axioms FX1Poly.Typed.GrownCheck.appSoundGivenComponentsTyped

/- Raw-relation SOUNDNESS REFUTED (GrownCheckSoundnessRefutation): the Curry fix-point TYPE
X := curryOmega (λT. Π T. Type@0) — with X ~Conv~ Π X. Type@0 — threads the app arm's floating Π-code, so
Ω = (λx.xx)(λx.xx) CHECKS at the typed target Type@0 while being untypable (SN-043). The
completeness ∘ reflection ∘ soundness pipeline cannot run over the RAW relation; typehood must enter via an
annotated judgment (campaign log carries the surviving routes). -/

#assert_no_axioms FX1Poly.Typed.recursivePiType
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
#assert_no_axioms FX1Poly.Typed.RawTerm.isStepNormalForm_childrenNormal
#assert_no_axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_head
#assert_no_axioms FX1Poly.Typed.RawTermChildren.areStepNormalFormsBool_tail

/-! ### NormalizeSteps + NormalizeStepsTower — the SN-normalizer STRICT-COMPLEXITY witness (SN-145)

The normalizer's EXACT cost instrumentation: `normalizeSteps` (the `Acc.rec` twin of
`RawTerm.normalize`), the counted-chain identity (`StepStarN (normalizeSteps t acc) t
(normalize t acc)`), zero-cost-iff-normal, and the identity-tower family realizing the counter
exactly (`= towerHeight`) — yielding the unboundedness boundary brick.  HONEST scope: exactness +
unboundedness are machine-checked; NO size-polynomial bound is claimed in either direction (the
non-elementary β-normalization lower bound, Statman 1979, is literature-cited, not mechanized);
the polynomial-shape `StrictNormalizer` contract is deliberately NOT instantiated for the term
normalizer. -/

#assert_no_axioms FX1Poly.Core.RawTerm.normalizeSteps
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeSteps_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeSteps_eq
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_eq_none_of_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeSteps_chainExact
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeSteps_eq_zero_iff
#assert_no_axioms FX1Poly.Typed.normalizeSteps_idTower
#assert_no_axioms FX1Poly.Typed.normalizeSteps_unbounded
#assert_no_axioms FX1Poly.Typed.idTower_normalizeChainExact
#assert_no_axioms FX1Poly.Typed.convDecideSteps_idTower
#assert_no_axioms FX1Poly.Typed.convDecideSteps_unbounded
