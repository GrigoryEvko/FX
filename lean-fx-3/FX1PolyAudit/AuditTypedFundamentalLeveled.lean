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

/-! # FX1PolyAudit/AuditTypedFundamentalLeveled — typed-layer zero-axiom gates: the level-indexed and all-level (Kripke) fundamental theorems
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.DescTelescope.oneChildLevel

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
    `typingRuleDescOf` (nested `if` over DecidableEq, no 203-ctor wildcard);
    `TypingRuleDesc` is pure syntax (no HasTypeDesc → genFormation strictly
    positive); output classifier an explicit INDEX (Prop, P14). -/

#assert_no_axioms FX1Poly.Typed.lmaxFold
#assert_no_axioms FX1Poly.Typed.lmaxAll

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
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.memberExtendsToAllPositive
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
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithPositiveTypeCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithPositiveTypeCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtDispatchLevelsAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtDispatchLevelsAtAll
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
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromAllLevelHeadCandidateCompanion
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consArgumentAtPositiveMemberLevelOfHeadFundamental
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.consArgumentAtPositiveMemberLevelOfHeadFundamental
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromPositiveDomainCandidateAndBaseLevelPremise
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromPositiveDomainCandidateAndBaseLevelPremise
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAllFromAllLevelDomainCandidateCompanion

-- Canonical per-level candidate companion extracted from an all-level `T : Type@u` fundamental result.  This
-- is weaker than the all-positive candidate discipline and avoids assuming stratified level-irrelevance.
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateUnderAllLevelSubstitution
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateAtPositiveLevelsUnderSubstitution
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateUnderAllLevelSubstitution.atPositiveLevels
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateAtPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtVector
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtVectorMatchingLevel
#assert_no_axioms FX1Poly.Typed.fundamentalConclusionAtAllOfVector
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromVectorPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAllFromVectorPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromVectorPremise
#assert_no_axioms FX1Poly.Typed.positiveUniformLevels
#assert_no_axioms FX1Poly.Typed.positiveUniformLevels_eq
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalConclusionAtAllOfUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAllFromUniformVectorPremise

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.allLevelFundamentalTheoremFromFormationVector
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toClosedStrongNormalizationTheorem
-- typeVariableAllLevelMember: a SYNTACTIC type variable (type = universe code) is a reducible member of its
-- universe at EVERY positive level (universe codes are level-poly types; vars inhabit any reducible type).
-- Records that the dependent-former DOMAIN obstruction is the per-variable-level ENV pinning, not an intrinsic
-- single-level limitation of variables — an all-level env for type-variable entries would discharge it.
#assert_no_axioms FX1Poly.Typed.typeVariableAllLevelMember
#assert_no_axioms FX1Poly.Typed.DescTelescope.twoChildLevels
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.twoChildLevels
-- GTL-11 substrate: the one-child [0] analogue (data type-code formers listCode / optionCode) — same
-- single-live-cons-then-nil discipline, no propext / Quot.sound; feeds the FT data-former branch.
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.oneChildLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormerOfChildMembershipsAtRequiredLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toDispatchLevels
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.toPiMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.toSigmaMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.ofTelescopeReducible

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

-- SN-002 spike: the reducibility level CAN be re-keyed to the classifier universe level `denote(LevelExpr)`
-- — `Type@e` is a reducible member at its DENOTED classifier level `denote(lsucc e)`, the `lsucc → +1`
-- alignment matching the shipped tarskiDecode discipline by definitional equality.  Setup verdict: GO;
-- the make-or-break universe-DOMAIN Π-formation case is deferred to SN-004.
#assert_no_axioms FX1Poly.Typed.universeCode_reducibleMemberAtClassifierLevel

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

-- Member-side leaf (dual of the type leaves): membership in a neutral / data-former classifier is
-- `IsStronglyNormalizing` (level-independent), so a one-level member extends to all positive levels — the
-- cons-arm `headMemberExtendsToAllPositive` premise for a neutral-domain former.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
#assert_no_axioms FX1Poly.Typed.headMemberExtendsToAllPositive_ofNeutralClassifier

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
#assert_no_axioms FX1Poly.Typed.IsSimplyTypedTypeExpr.reducibleAtAllLevels

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

-- The DEPENDENT analogue of IsFirstOrderSimplyTyped: an inductive fragment (neutral/data leaves + dependent Pi
-- over neutral domains with recursively-fragment codomain instantiations) + one fundamental theorem. Captures
-- curried dependent functions Pi(x:A).Pi(y:B x).C x y over neutral/data base types. reducibleAndMemberExtension
-- is the #672 fuel-stability gate proven for this fragment; the all-levels dependentPiOverNeutralDomain feeds
-- its member leg; typeFamilyApplication is the concrete Pi(x:A).P x fragment member. Universe-domain Pi open.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.dependentPiOverNeutralDomain

-- Cumulativity SN-072: reducibility respects Type@e ⊆ Type@(lsucc e). In the fuel-stratified model the
-- universe candidate is LevelExpr/flag-independent (meta-fuel decoupled from object levels; the hierarchy
-- discipline lives in HasType, not the semantic model), so universe membership is level-label-IRRELEVANT
-- (a two-way equivalence) and cumulativity is its named corollary (single-level + all-positive). Honest scope:
-- this is cumulativity in the coarse model; per-LevelExpr cumulativity awaits the LevelExpr-matching refinement.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.universeMembershipLevelLabelIrrelevant
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.universeCumulativity

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

-- piReducibleAsTypeFromUniformLevelMember (fully-uniform genFormationPi reducible-as-type, lift-free): for the
-- Π whose domain AND codomain are classified at the SAME universe levelExpr as the Π's own output
-- (levelExpr = lmaxAll [levelExpr, levelExpr]), the piReducibleAsType premise is discharged from the children's
-- raw universe-MEMBERSHIPS (the natural FT output) with NO cumulativity lift: each member of Type@levelExpr
-- decodes to a reducible TYPE at denote levelExpr env directly (universeMemberReducibleAsTypeAtDecodedLevel,
-- decoded level = the Π's level), fed to the connector. The non-uniform cases (levelExpr strictly above one
-- child's universe) need the level-bounded TYPE-reducibility cumulativity (the documented multi-lemma residual).
#assert_no_axioms FX1Poly.Typed.piReducibleAsTypeFromUniformLevelMember

-- gapUniverseDomainPiVacuouslyReducibleAtLowLevel (the cumulativity-obstruction WITNESS): at lowLevel ≤
-- denote gapLevel env, Type@gapLevel has the EMPTY member candidate (denoteBelowFamily empty at index ≥
-- lowLevel), so Π(Type@gapLevel) codomain is reducible-as-type at lowLevel for ANY codomain (vacuous codomain
-- obligation). Low-level reducibility of a gap-universe-domain Π is codomain-BLIND ⟹ cannot be lifted to a
-- higher level where the domain gains members. Pins WHY the non-uniform genFormationPi piReducibleAsType is
-- model-obstructed (semantic reducibility does NOT bound universes — universeCode_isReducibleAtDenote fires at
-- every level), so it needs a bound-carrying model OR stays a carried premise (conditional/fragment milestone).
#assert_no_axioms FX1Poly.Typed.gapUniverseDomainPiVacuouslyReducibleAtLowLevel

-- DenoteKeyedAmbientLevelBridge (SN-D5-A2bridge): the single shared deep ingredient of the denote FT's
-- conv/piIntro arms. universeMemberReducibleAtLevel turns a universe MEMBERSHIP at the ambient level into the
-- type's REDUCIBILITY at the ambient level (given denote levelExpr env < level). Real content: candidateIffUniverse
-- unpacking → universeDenotePredicate ∃-conjunct → denoteBelowFamily_eq_reducible (decoded-level reducibility) →
-- ofReducibleTypeStepDenote lift to all levels → project to level. Parametric over EXACTLY the
-- ofReducibleTypeStepDenote composite-domain piArm (at the decoded level's below-family) — the lone deep A2
-- residual = the denote restatement of #672. Consolidates: conv (SN-D5a) + piIntro (SN-D5c) BOTH reduce through
-- this bridge to that one piArm.
#assert_no_axioms FX1Poly.Typed.universeMemberReducibleAtLevel
#assert_no_axioms FX1Poly.Typed.lmaxAll_pair
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
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportUnderWf
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportValidityUnderWf
-- LRH-1: LR COMPLETENESS on the {neutral, universe, Pi} head fragment under wf
-- (TypedTypeValidityLeveledCompleteness.lean) — the THIRD leg closing the route-B loop: soundness
-- (toHasTypeDescPi) + transportUnderWf + completeOnHeadFragment = the leveled LR is a faithful
-- wf-conditional candidate-carrying model of the fragment. completeOnHeadFragment: fragment induction;
-- neutral arm consumes the typing, universeType pins (level, flag) via the predicativity inversion,
-- piType inverts the former typing (invertPiTyCode + universeCodeCell_inj_of_conv) and recurses under the
-- wf-extended binder, reassembling with the canonical snKripkeCodFamily. faithfulOnHeadFragment is the
-- iff. BOUNDARY committed, not absorbed: headCharacterization pins membership to the three heads;
-- sigmaTyCodeCell_notInHeadFragment proves the Sigma code OUTSIDE (no Sigma arm; same root argument
-- excludes data/flat/empty/modal codes — their model story is the §5 candidate bridge, not this LR).
-- For bare typing transport the direct LR-free witness remains convContextUnderWf. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.TypedLrHeadFragment.headCharacterization
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.completeOnHeadFragment
#assert_no_axioms FX1Poly.Typed.TypedTypeValidityLeveled.faithfulOnHeadFragment
#assert_no_axioms FX1Poly.Typed.smoke_completeOnHeadFragment_piOverUniverse
