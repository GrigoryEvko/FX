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

/-! # FX1PolyAudit/AuditTypedFundamentalBounded — typed-layer zero-axiom gates: the bounded reducibility fundamental theorem (the canonical SN route)
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationOptionFromTelescopeAtBoundedSucc

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
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtBounded
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtBounded
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationAtBounded
-- THE BOUNDED FT CONV ARM (DenoteKeyedBoundedConvArm): the bound-carrying analogue of the denote conv member arm +
-- FT arm. convTransfer is a ~3-line FORGET-BRIDGE transfer (bounded forgets to denote at the same lowerAt, and
-- ReducibleTypeStepDenote.convTransfer is lowerAt-parametric) — the canonical economy the forget bridge provides for
-- facts-about-candidates. The FT arm is premise-isolating (carries the A2 ambient-bound reducibility premise).
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAtBounded.convTransfer
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

-- The bounded FORMATION-engine fundamental theorem (BoundedFormationDispatch.lean, BFT-10 + BFT-11). Discharges the
-- formationFundamental premise shape of BFT-6: given a BoundExceeds budget, every HasTypeDesc formation derivation
-- satisfies FundamentalConclusionAtBoundedSucc. Proved by BoundExceeds.rec (induction on the BUDGET, not the
-- derivation) so the universeFormation arm receives belowBound NAMED — sidestepping the opaque-outputType-index
-- inversion that blocks a match on the budget. IsFormationTelescopeReducibleAtBoundedSucc is the DescTelescope
-- motive_2 wrapper (BFT-10).
#assert_no_axioms FX1Poly.Typed.IsFormationTelescopeReducibleAtBoundedSucc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.fundamentalAtBoundedSucc

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

-- OB-1 (BoundedNeutralMember.lean): a variable is a bound-reducible member of any bound-reducible type. The
-- candidate is an unconditional reducibility candidate (ReducibleTypeAtBounded.isReducibilityCandidate) and a
-- variable joins it by CR3 (neutralExpansion) with a vacuous reduct premise (noStep_var). The member-side leaf the
-- neutral/identity closing environment (reducibleEnvOfWfContext, OB-3) cons-feeds at every context position — the
-- first brick discharging the OpenStronglyNormalizing residual toward UNCONDITIONAL open SN-043 (#546).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtBounded.ofVariable

-- CAN-6 / FLAT-CANON (#936) PAYOFF (FlatCodeCanonicalForms): the SECOND §5 candidate-bridge pin harvested.
-- Non-vacuity (every flat-rooted cell is bounded-reducible via the dataFlat arm); the flat candidate bridge
-- (family determinism pins ANY candidate to dataTaitCandidate (flatCodeValuePredicate root) — before the
-- edit the neutral arm collapsed it onto the whole SN set); the member identity; and per-code CLOSED
-- canonicity: a closed candidate member of a product cell reduces to a PAIR, of an either cell to an
-- inl/inr injection, and the sum lane (no intro generators — empty value predicate, honest) has NO closed
-- member. MODEL-level (sconing leg): connecting ENGINE-typed members is future work, stated, not absorbed.
#assert_no_axioms FX1Poly.Typed.flatCode_isReducibleTypeAtBounded
