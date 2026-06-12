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

/-! # FX1PolyAudit/AuditTypedSubjectReductionEta — typed-layer zero-axiom gates: subject reduction and the eta/beta-eta preservation arms
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

-- TY-ETA-GROWN (#1033): generalize the forward η-coherence from formation-typed f (effectively only variables of
-- function type) to ANY grown-typed f — λ-terms, applications, Church numerals. etaExpansionPreservesTypingGrown
-- (★): well-formed grown context + f : piTyCode D C ⟹ etaLamSource f : piTyCode D C, via validity +
-- invertPiTyCode (grown domain/codomain) + grown weakenUnderBinding + rename_piTyCodeCell + the η identity +
-- piIntro/piElim. etaCoherenceGrown = the redex/reduct coherence pair. The forward half of grown η-SR (#477);
-- the inverted half still needs grown strengthening. Zero-axiom (same de Bruijn substrate as the formation twin).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaExpansionPreservesTypingGrown
-- TY-ETA-COMPUTES (#1034): the OPERATIONAL content of η on top of forward η typing. etaLamSourceApplication (★):
-- (etaLamSource f) a ↝β f a for ANY scope/f/a — applying an η-expansion β-steps to applying the original (raw,
-- via subst0_etaLamSource_body's weaken/var-0 cancellations). etaExpansionTypedAndOperational bundles the static
-- (typing-preserved) and dynamic (application-preserved) halves into η-coherence. The two Church witnesses make it
-- concrete: η-expanding churchNumeralLambda n preserves BOTH its Church-Nat type (∘ #1007) AND its computed iterate
-- f^n x (∘ #1009, one leading admin β-step). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.subst0_etaLamSource_body
#assert_no_axioms FX1Poly.Typed.Step.etaLamSourceApplication
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaExpansionTypedAndOperational
-- SN-050 CONSISTENCY made concrete, gated on exactly SR-along-↝* (ConsistencyConditionalOnSubjectReduction.lean):
-- OB-5 (stronglyNormalizingOfWfContext) normalizes a closed t : EmptyType to a reachable normal form; the explicit
-- subjectReductionStar hypothesis carries the EmptyType classifier along the chain; noClosedNormalTermAtEmptyType
-- refutes the closed normal endpoint. The bounded SN model CANNOT discharge this (its emptyTypeCell candidate is
-- the coarse IsStronglyNormalizing via the neutral arm, NOT the empty candidate — CON-A3 needs a canonicity model),
-- so the syntactic route is the tractable one. subjectReductionStar = the iterated SN-055 master dispatcher
-- (SRD-1/SRD-3, blocked on WFG-3/the WfContext↔WfContextDescPi bundle); once it lands this is unconditional SN-050.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.consistencyOfSubjectReductionStarToEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyOfSubjectReductionStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedTypeSafetyUniqueOfSubjectReductionStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyOfSubjectReductionStar
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openTypeSafetyUniqueOfSubjectReductionStar
-- CASCADE-FREE GENERIC FORMER SR (SubjectReductionAtFormerGeneric.lean, TG-2): ONE former subject-reduction arm
-- over typingRuleDescOf, replacing the piTyCode/sigmaTyCode-specific subjectReductionAtPiFormer/SigmaFormer. By
-- TG-1 a former's step is a child congruence; re-type the premise telescope (telescopeSR, the mutual-partner
-- DescTelescopePi SR whose here-case consumes grown context-conversion #814 pt2b) and reassemble via the generic
-- genFormationPi at the unchanged rule.outputType. No formation generator is named — a new formation row is
-- absorbed zero-touch. The master dispatcher (TG-3) routes its genFormationPi case through this one arm.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionAtFormerGeneric
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
#assert_no_axioms FX1Poly.Typed.identityApplication_subjectReduction
-- THE POLYMORPHIC IDENTITY (TypedLambdaDerivations capstone): λ(A:Type@0).λ(x:A).x : Π(A:Type@0).Π(x:A).A —
-- the canonical dependently-typed term, typed by the grown engine via NESTED piIntro with a type-VARIABLE inner
-- domain. dependentArrowOverTypeVariable is the genuine Π-FORMATION with VARIABLE children (genFormationPi + a
-- DescTelescopePi typing var0/var1 each at Type@0 by the var rule; cumulative-lookup classifiers defeq Type@0).
-- stronglyNormalizing feeds it through SN-043. Tactic-mode refine threads the profile/contexts via goal-driven
-- unification (term-mode re-introduces TypingContext.empty with fresh profile metavars).
#assert_no_axioms FX1Poly.Typed.dependentArrowOverTypeVariable_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentity_hasTypeDescPi
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityInstantiation_subjectReduction
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityTwoArg_subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectReduction
#assert_no_axioms FX1Poly.Typed.konstNormalForms_notBetaEtaConv
#assert_no_axioms FX1Poly.Typed.betaEtaStar_preservesVariableBodiedLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.subjectReduction

-- CAN-3 (DataIntroSubjectReductionRecursive): SR for the two RECURSIVE data-intro engines (the
-- DI-3/DI-2e deferred debt) + the per-eliminator typed-ι SR coverage matrix.  Nat/list VALUES
-- have no root redexes (no β: head not gen_app; no ι: every ι head is an eliminator; η is the
-- sibling relation), so every step is payload congruence: nat-intro SR is UNCONDITIONAL (the
-- engine's only premise is recursive), list-intro SR consumes WfContextDescPi exactly once (the
-- cons HEAD is grown-typed, re-typed by the SR-U4 master).  The matrix reconciles the historical
-- #475/#476 claims (proved for the DELETED HasType engine): grown subjects are fully covered by
-- the one master SR; the 7 standalone families all have constructor-side typed-ι (DI-5 complete,
-- re-checked by enumeration); derivation-side SR of the standalone eliminator judgments is the
-- HONEST OPEN gap (the cons-index propext-trap inversion), deferred loudly via the matrix flags.
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescListIntro.subjectReduction
#assert_no_axioms FX1Poly.Typed.eliminatorIotaSrCoverage_count
#assert_no_axioms FX1Poly.Typed.eliminatorIotaSrCoverage_constructorSideComplete
#assert_no_axioms FX1Poly.Typed.FlatDescTelescope.subjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.subjectReduction

-- SUBJECT REDUCTION + TYPE-PRESERVING NORMALIZATION — the SR arc CULMINATION.  Reduction preserves typing
-- (single-step inverts Step per shape via StepInversion: var refuted, app = β/cong-fn/cong-arg with the
-- β-engine substituteUnderBinding + weaken_subst_singleton, lam = cong-body); multi-step iterates it; and
-- normalForm_typed (the gold payoff) threads the normalizer's reduction chain through SR* so the canonical
-- normal form of a closed simply-typed term is itself simply-typed at the same type.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.subjectReduction
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.subjectReductionStar

-- DenoteKeyedUniverseMemberBetaExpansion (the UNIVERSE arm of the denote member weak-head β-expansion / the
-- lambda-arm engine toward SN-043/#672): the β-redex app (lam body) arg is a member of the denote universe
-- candidate given its contractum subst0 body arg is. SN conjunct via appLam_isStronglyNormalizing_of_contractum
-- (last tick's neutral arm); the ∃c, lowerAt(denote e) · c conjunct via the lower backward-weak-head-step leg
-- on WeakHeadStep.beta — discharged UNCONDITIONALLY for denoteBelowFamily (backward-step is an implication
-- vacuous above the bound, not the bounded neutral-inclusion existence). So this arm is BOUND-FREE; the level
-- bound is confined to the remaining Π/spine arm (application-SN).
#assert_no_axioms FX1Poly.Typed.universeMemberBetaExpansionAtDenote
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
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectReduction
#assert_no_axioms FX1Poly.Typed.DescTelescope.subjectReduction

-- OSN-B8 (WfContextBetaEtaConfluence.lean): the GEUVERS harvest of OSN-1. Raw βη-CR is false (Nederpelt/Klop),
-- so CR on the WELL-TYPED fragment is the maximal honest statement (Geuvers LICS'92). Factored as raw local
-- βη-confluence (cd_lemma) ⊕ typed βη-SN (OSN-1) → typed global CR via Newman; unique-βη-NF is the CR corollary
-- via star-rigidity. Weak βη-normalization (existence) + decidable βη-Conv are DEFERRED to the Path-A βη
-- normalizer (not faked from confluence). eq_of_noBetaEtaStep is the raw βη star-rigidity (propext-clean cases).
-- (The βη-CR / unique-βη-NF over WfContextDesc are gated below.)
#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.eq_of_noBetaEtaStep
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectBetaEtaConfluenceOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.uniqueBetaEtaNormalFormOfWfContextDesc

-- BECR-1 ★ (WfContextBetaEtaConfluenceUnconditional.lean): the Geuvers βη-CR + unique-βη-NF with
-- the HereditaryLamDiagonal premise GONE — well-typedness in a well-formed context is the only
-- hypothesis.  The two ingredients the conditional file's docstring named as missing are both
-- fired: (a) the joinability-guarded local join + Newman twin (StepBetaEtaJoinableConfluence) and
-- (b) grown βη-SR (subjectReductionBetaEtaStar, PAR-2).  The guard discharge:
-- etaLamSourceAnnotationJoinable extracts Conv between the inner/outer annotations of any TYPED
-- lambda η-source whose inner function is a lambda (invertLam → invertApp → invertVar pins the
-- app domain to the weakened OUTER annotation; a second invertLamGeneral via rename_lamCell pins
-- it to the weakened INNER annotation through the Π classifier; Conv.piTyCode_inj aligns,
-- Conv.reflectWeaken strips the weakening) — and Conv IS StepStar.Join, so the conversion is
-- LITERALLY the joinability witness.  βη-SR-star makes the guard hereditary.  The raw-layer
-- Nederpelt non-joinability stands untouched; typing is exactly what buys the guard.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.etaLamSourceAnnotationJoinable
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.uniqueBetaEtaNormalFormTypedUnconditional

-- Fully-general β subject reduction (HasTypeDescPiBetaSR.lean, TY-SR-β #474). For ANY grown derivation of a β-redex
-- appCell (lamCell body) argument at classifier (over a well-formed context), the β-reduct subst0 body argument is
-- typed at the SAME classifier. The INVERTED form (vs the shipped component-given betaCoherence): invertApp +
-- invertLam recover the components, Conv.piTyCode_inj reconciles the application's vs the λ's domain/codomain,
-- substituteUnderBinding retypes the reduct, and validity (classifierIsTypeDesc, the WfContext consumer) + the conv
-- rule convert it back to classifier. The Step.beta case of the SR master dispatcher (#458).
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.masterSubjectReductionFromPiValidity
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.subjectReductionFromPiValidity
#assert_no_axioms FX1Poly.Typed.masterSubjectReductionFromPiElimArm

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
#assert_no_axioms FX1Poly.Typed.crossRef_subjectReductionBeta
#assert_no_axioms FX1Poly.Typed.subjectReductionBeta_hasClassicalPrecedent
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_formation
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_grownFormerArm
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_grownConvArm
#assert_no_axioms FX1Poly.Typed.parityAnchor_subjectReduction_grownOfFormationArm
#assert_no_axioms FX1Poly.Typed.subjectReduction_grownConditionalOnBundle
#assert_no_axioms FX1Poly.Typed.parity_discriminates_weakening_vs_subjectReduction
#assert_no_axioms FX1Poly.Typed.parity_discriminates_strongNormalization_vs_subjectReduction

/- η-SR λ-arm (GrownEtaSubjectReduction, STR-10): grown typing is preserved by etaLam
contraction — `lam domainAnn (app (weaken f) newestVar) : T` descends to `f : T` in a
well-formed context.  The strengthening campaign's first downstream harvest: invertLam +
invertApp + invertVar expose the η shape, the λ-inclusive pin extraction + premise-free master
reflect the weakened function to the smaller scope, `subst0_lift_weaken_newestVar` collapses
the instantiated codomain, and `Conv.reflectWeaken` strips the domain weakening.  The crux arm
of grown βη subject reduction (PAR-2); structural arms = STR-11. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEtaLam
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEtaLamStep

/- η-SR structural arms (STR-11) + the grown βη MASTER SR (PAR-2).  The pair/cubical/modal/Glue
arms hold VACUOUSLY today — their source heads (gen_pair/gen_pathLam/gen_modIntro/gen_glueIntro)
are grown-untypable (`isUntypableHead = true` by rfl), so each discharges via
`isUntypableHead_sound`; when those typing rules land, the rfl arguments break loudly and force
substantive re-proofs (the decision procedure is the cascade alarm).  The dispatcher assembles
all five η arms; the βη master = the shipped β/ι master (SR-U4) ∪ the η dispatcher (Step.betaEta
is the plain disjunction, η fires at the root only); the star version threads the chain.  The
round-trip regression witnesses the λ-arm NON-VACUOUS: every grown function typing η-expands
(TY-ETA-GROWN) to a real typed η-source the λ-arm contracts back. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEtaPair
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEtaPathLam
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEtaModIntro
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEtaGlueIntro
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByEta
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionBetaEta
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionBetaEtaStar

/-! ### BetaEtaConvGapStatement — the ETA-1 census verdict, machine-checked (gap statement for #364)

CORRECTION OF RECORD: tracker #806 overstated — decidable βη-Conv was DEFERRED by the shipped file
itself.  This module makes the βη conversion relation first-class (`BetaEtaConv =
betaEtaStar.Join`, mirroring the kernel's own join-based `Conv`), proves the equivalence package
(refl/sym structural; `Conv ⊆ BetaEtaConv`; STRICT extension via an η-pair that is provably not
β/ι-Conv; transitivity through a WELL-TYPED middle — raw βη-CR is Nederpelt-false, so typing is
load-bearing exactly there), and bundles the complete shipped decision METATHEORY
(`betaEtaDeciderMetatheoryPrerequisitesHold`: typed βη-SN + typed βη-CR + unique βη-NF +
star-rigidity).  The named gap: ONE computable artifact (a sound+complete βη one-step reducer,
ETA-2) yields decidable `BetaEtaConv` on the wf fragment; unit-η/SProp-η remain genuinely
type-directed (η-M15d/e) and are NOT in `BetaEtaConv` at all. -/

#assert_no_axioms FX1Poly.Core.BetaEtaConv
#assert_no_axioms FX1Poly.Core.BetaEtaConv.refl
#assert_no_axioms FX1Poly.Core.BetaEtaConv.sym
#assert_no_axioms FX1Poly.Core.BetaEtaConv.fromBetaEtaStar
#assert_no_axioms FX1Poly.Core.BetaEtaConv.ofConv
#assert_no_axioms FX1Poly.Core.BetaEtaConv.strictlyExtendsConv
#assert_no_axioms FX1Poly.Typed.BetaEtaConv.transAtTypedMiddle
#assert_no_axioms FX1Poly.Typed.betaEtaDeciderMetatheoryPrerequisitesHold

/-! ### BetaEtaConvDecidable — ★ decidable βη-conversion on the wf-typed fragment (ETA-2 closure)

The ETA-1 gap is discharged: with the reducer (`reduceOnceBetaEta`) and its normalizer
(`normalizeBetaEta`) shipped, βη-conversion of two well-typed terms over a well-formed context IS
βη-normalizer-output equality (forward: typed βη-CR + star-rigidity + unique typed βη-NF;
backward: the two normalizer chains meet), hence decidable by normalize-and-compare.  Typing is
load-bearing in both legs: termination = typed βη-SN (raw βη is not SN), well-definedness = typed
βη-CR (raw βη-CR is Nederpelt-false).  The remaining #364 content is exactly its (B) half:
type-directed unit-η/SProp-η (η-M15d/e), which is judgmental-equality extension, not decision. -/

#assert_no_axioms FX1Poly.Typed.BetaEtaConv.iff_normalizeBetaEta_eq_of_wfTyped
#assert_no_axioms FX1Poly.Typed.BetaEtaConv.decidableOfWfTyped
#assert_no_axioms FX1Poly.Typed.betaEtaConvDecidableOnWfFragment
#assert_no_axioms FX1Poly.Typed.cascadeAnchor_subjectReduction_formation
#assert_no_axioms FX1Poly.Typed.cascadeAnchor_subjectReduction_grown
#assert_no_axioms FX1Poly.Typed.cascadeAnchor_subjectReduction_genericArm
#assert_no_axioms FX1Poly.Typed.subjectReduction_isZeroArm
