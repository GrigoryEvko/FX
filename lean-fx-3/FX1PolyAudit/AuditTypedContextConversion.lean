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

/-! # FX1PolyAudit/AuditTypedContextConversion — typed-layer zero-axiom gates: context conversion and Pi-validity transport
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

#assert_no_axioms FX1Poly.Typed.renameContextCondition_cons
#assert_no_axioms FX1Poly.Typed.substContextCondition_cons
#assert_no_axioms FX1Poly.Typed.convContextCondition_consStep
#assert_no_axioms FX1Poly.Typed.convContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.convContext
#assert_no_axioms FX1Poly.Typed.DescTelescope.convTelescope
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

-- SR-U3 (the directed-step instance): ConvContextWithOldValid.ofHeadStep builds the enriched condition FREE for a head
-- domain step (domain ↝ domainReduct, prefix UNCHANGED): index 0 = Conv (weaken domain) (weaken domainReduct) from the
-- step + domain's prefix-validity (headIsType) weakened; index k+1 = refl (prefix entries unchanged) + lookupIsType
-- weakened. ★ HasTypeDescPi.codomainReTypingStep = contextConversionExact ∘ ofHeadStep: a codomain re-types across a
-- stepped domain binder at the SAME classifier, UNCONDITIONALLY — the grown twin of the shipped FORMATION
-- codomainReTypingOfFormationStep (#1096), discharging the grown codomainReTyping that gated master SR (SRD-1/#844 →
-- SRD-2/#845 → SN-055/#558). Zero-axiom.
#assert_no_axioms FX1Poly.Typed.ConvContextWithOldValid.ofHeadStep
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.codomainReTypingStep

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

/- GrownCheck structural helpers (GrownCheckContextConversion): EXACT-target context conversion under
pointwise-Conv contexts (raw relation → no wf needed, contrast convContextUnderWf) + the Conv-related-binders
cons condition + the binder-swap corollary (the reflection's swap-the-floating-binder ingredient) + the
target-side Π exposure (reducesToPiTyCode ∘ subjectReductionStar ∘ invertPiTyCode, wf-conditional) + the
lam/app soundness reassembly shapes consumed by the STR-5 soundness induction. -/

#assert_no_axioms FX1Poly.Typed.convContextCondition_consConv
#assert_no_axioms FX1Poly.Typed.GrownCheck.convContext
#assert_no_axioms FX1Poly.Typed.GrownCheckTelescope.convContext
