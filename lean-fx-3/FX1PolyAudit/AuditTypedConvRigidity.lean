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

/-! # FX1PolyAudit/AuditTypedConvRigidity — typed-layer zero-axiom gates: Conv injectivity, type-code disjointness, and shape stability
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

-- universe-code cell injectivity (no-Type-in-Type probe support): equal
-- universe codes have equal levels and flags, via `cases` on the cell equality
#assert_no_axioms FX1Poly.Typed.universeCodeCell_inj
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
-- `piTyCodeCell` is injective (domain/codomain recovered): the component extractor
-- the `piFormation` arm of `inversionPiCode` aligns the inducted arm's own
-- domain/codomain with the inversion target.  `cases` on the cell equality (the
-- propext-free substrate tactic), NOT `injection`.
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_inj
-- GTL-11 LANDED: the grown head-agnostic former-classifier inversion + the listCode piElim/empty refutations
-- (the grown twin of HasTypeDesc.inversionFormerWithConvGeneric); the one-child formation telescope level
-- projection (the DescTelescope sibling of DescTelescopePi.oneChildLevel) the formation vector-assembly arm uses.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.formerClassifierConvUniverseGeneric
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_inj
#assert_no_axioms FX1Poly.Typed.Conv.trans_of_hasTypeDescMiddle
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedClassifierConvUniverseCode

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
-- Generic former inversion FULL (telescope + classifier Conv at consistent levels/flag), the generic
-- analogue of inversionPiCodeWithConvGeneral. Merges the classifier + telescope halves off the SAME
-- genFormation arm — the consistency uniquenessAgree-style consumers need. Zero-axiom (same cracked-wall
-- idiom). NOTE: HasTypeDescUniqueness can't yet consume it generically — its flag-uniqueness guard
-- (levels ≠ []) needs binderShifts ≠ [] (former has ≥1 child), NOT a clean cascade invariant (nullary
-- Empty violates it); kept per-former pending the nullary-former flag-uniqueness treatment.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionFormerWithConvGeneric

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
#assert_no_axioms FX1Poly.Typed.Conv.formationFormersNotConvOfDistinct
#assert_no_axioms FX1Poly.Typed.Conv.listCode_not_conv_optionCode
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
-- Conv VALUE NON-DEGENERACY (ConvValueDiscrimination): the contrapositive of Conv.eq_of_noStep — distinct closed
-- normal-form values are NOT convertible. normalLeavesNotConvertibleOfDistinctRoot: two no-step terms with
-- distinct head generators ⟹ ¬Conv (Conv.eq_of_noStep collapses Conv→Eq, congrArg rootGenerator refutes).
-- boolTrue ≢ boolFalse + boolTrue ≢ unit concretely; convIsNonDegenerate (★ ∃ a b, ¬Conv a b) is the value-
-- discrimination sanity property canonicity rests on (if Conv collapsed values, every type would be inhabited
-- and the theory inconsistent). Distinct from Conv-INJECTIVITY (#947/948, same-head decomposition).
#assert_no_axioms FX1Poly.Typed.normalLeavesNotConvertibleOfDistinctRoot
#assert_no_axioms FX1Poly.Typed.boolTrueValue_notConvertible_boolFalseValue
#assert_no_axioms FX1Poly.Typed.convIsNonDegenerate
#assert_no_axioms FX1Poly.Typed.betaRedexConvertsToReduct
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
#assert_no_axioms FX1Poly.Typed.validTypingBridgeConv
-- SN-023 (LevelingBridge.lean): the binder + former bridge arms — each mirrors the matching ValidTyping ctor's
-- level discipline (piIntro: codes at predLevel+1+1, body at predLevel+1 under levelCons; piElim: shared level;
-- piFormation/sigmaFormation: the ∀-aboveLevel domain premise SN-025 produces; genFormationPi: the SN-021 ctor).
-- Per-arm TARGET SHAPES given coordinated inputs; the cross-IH coordination + ∀-aboveLevel production is the
-- inductive assembly SN-027 (ValidTyping is NOT level-weakenable — var pins its level — so coordination is the
-- deferred crux, not arm-local).
#assert_no_axioms FX1Poly.Typed.validTypingBridgePiIntro
#assert_no_axioms FX1Poly.Typed.validTypingBridgePiElim
-- SN-027 (refined-motive coordination): validTypingBridgeConvFromAllLevelReclassifier discharges the conv arm's
-- LEVEL alignment — the existential ∃-shape can't force aligned levels, but a REFINED MOTIVE giving type-code
-- subjects an ∀-level conclusion does: conv needs the reclassifier at subjectLevel+1, which is just the
-- subjectLevel-instance of the all-level reclassifier IH. Supersedes the pre-aligned validTypingBridgeConv
-- (SN-022). Type variables (var-pinned) are the sole non-level-flexible type code → reducibility route (SN-025).
#assert_no_axioms FX1Poly.Typed.validTypingBridgeConvFromAllLevelReclassifier
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

/-! ### FormationClassifierRigidity — ★ brick 8, POSITIVE: literal classifier matching is complete

The post-brick-7 completeness re-analysis closed the suspected 10th-boundary family EMPTY, as
theorems: formation subjects are step-free (`subjectAdmitsNoStep` — the formation engine has no
`piIntro`/`piElim` arms, so formation-typed terms are app-free, redex-free trees), hence
`Conv`-RIGID (`formationSubjects_convRigid` via `Conv.eq_of_noStep`).  Consequently a
formation-typed classifier `Conv` to a Π code literally IS a Π code with `Conv`-related
components (`piCodeDetection_completeOnFormationClassifiers` via `Conv.reducesToPiTyCode` +
chain collapse), `asPiCode?` fires on it (`asPiCode?_firesOnFormationClassifiers`), wf lookups
inherit the completeness (`WfContextDesc.piCodeDetection_completeOnLookups` via
`lookupIsTypeDesc`), and the unit arm's literal test is complete
(`unitDetection_completeOnFormationClassifiers`).  Within the soundness presupposition the
readback's literal dispatch loses NOTHING — `Conv`-disguised type codes are not
formation-typable; the 9th boundary's phenomenon cannot recur at classifier or lookup
positions.  The standing honest-boundary note (2) is RETIRED.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDesc.formationSubjects_convRigid
#assert_no_axioms FX1Poly.Typed.dataIntroAndBaseTypeSubjectsDisjoint
#assert_no_axioms FX1Poly.Typed.Conv.natTypeCell_not_piTyCode
#assert_no_axioms FX1Poly.Typed.Conv.natTypeCell_not_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.natTypeCell_not_universeCode
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
#assert_no_axioms FX1Poly.Typed.HasTypeDescFlat.inversionFormerWithConv

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
#assert_no_axioms FX1Poly.Typed.memberConvAtBounded
#assert_no_axioms FX1Poly.Typed.convMemberUnderClosingSubstitutionBounded

-- DenoteKeyedConvMember (the denote FT's conversion member arm): a denote-reducible member of typeLeft, with
-- Conv typeLeft typeRight + typeRight denote-reducible, is a denote-reducible member of typeRight (via the
-- shipped convTransfer). convMemberUnderClosingSubstitution is the FT-shaped form: pushes the raw conversion
-- under the closing substitution via Conv.subst, then transports. The conversion typing rule, member level.
#assert_no_axioms FX1Poly.Typed.memberConvAtDenote
#assert_no_axioms FX1Poly.Typed.convMemberUnderClosingSubstitution
#assert_no_axioms FX1Poly.Tier0.closedTermAsSection_injective
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convergencePackageOfWfContextDesc
-- SN-052 design fact, T2-FLIPPED: pre-T2 the bare Curry-style λ typed NON-uniquely (the identity λ
-- inhabited Π(Type@e)(Type@e) for every e, forcing a bidirectional checker). Under T2 the Church-style
-- annotation PINS the λ-domain — any two classifiers of one annotated λ agree on the syntactic domain
-- (each Conv to a Π over the annotation), so the checker SYNTHESISES the domain from the subject.
#assert_no_axioms FX1Poly.Typed.hasTypeDescPi_identityLambda_atUniverse

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

-- CONTEXT-CONVERSION for the FORMATION engine (HasTypeDescContextConversion.lean, #814 part 1): typing stable
-- under a pointwise-Conv-replaced context, the leaf fragment (the clean wf-free half; the grown HasTypeDescPi
-- version's ofFormation arm delegates here, and its piIntro/piElim need wf-validity — the deferred half). The
-- EXISTENTIAL formulation (∃ T', Conv T T' ∧ ... Γ' t T') keeps the var arm honest (no old-entry-under-new-ctx
-- circularity). convContext ⋈ convTelescope mutual; convBackToUniverseCode + convContextCondition_cons helpers.
-- This is the former-DOMAIN SR-cong unblocker (#558/SN-055): codomain re-types under a Conv-replaced binder.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.convBackToUniverseCode

-- GROWN context-conversion: the validity-free arms (HasTypeDescPiContextConversion.lean, #814 part 2a). Of
-- the grown engine's six arms, FIVE are validity-free; the LONE hard arm is piElim (conv-backing the function
-- to its exact Π needs "typing a Conv-equal type" = type-Conv-closure, which reduces to SR — no such lemma
-- exists, it would be circular). So the full grown context-conversion is part of the mutual fundamental-
-- metatheory bundle (deferred). These two validity-free pieces already discharge former-DOMAIN congruence for
-- the COMMON case (a former whose codomain is a FORMATION type): convBackToUniverseCode + the ofFormation arm.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convBackToUniverseCode

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
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.genFormerValidityContextConversion
-- GrownCtxConv-5-VARLEAF (#1123): the universe-preserving bare-variable childConverts case
-- (variableTypeCodeContextConversion, GenFormerValidityContextConversion.lean) — a variable typed AS A TYPE CODE
-- (at a universe) transports to the SAME universe code under any pointwise-Conv target: invertVar (#1118) +
-- Conv.trans the context-conv premise + the var rule under tgt + convBackToUniverseCode (pin the classifier).
-- The unconditional bare-variable case of the per-child IH childConverts that genFormerValidityContextConversion
-- consumes. Zero-axiom.
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.variableTypeCodeContextConversion
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.noConvReclassifierAtEmptyType
#assert_no_axioms FX1Poly.Typed.Conv.eq_of_isTypeDesc
#assert_no_axioms FX1Poly.Typed.grownMetatheory_preservationConvArm
#assert_no_axioms FX1Poly.Typed.idTower_convToValue
#assert_no_axioms FX1Poly.Typed.idTower_allConvertible
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
#assert_no_axioms FX1Poly.Typed.skkApplied_conv_identityApplied
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
#assert_no_axioms FX1Poly.Typed.recursivePiType_convPi
#assert_no_axioms FX1Poly.Typed.variableDomainPi_notConvWeakenImage

/- Enrichment spike E2.5 GO (UniverseClassificationUnique): a Conv-class contains at most one
universe code (rigidity), so universe classifications drawn from one Conv-class coincide —
validated at the variable leaf via inversionVariable.  The flag negotiation closes at leaves. -/

#assert_no_axioms FX1Poly.Typed.Conv.universeCode_injective

/- E2.8 Conv-lift (ConvUniverseClassificationUnique): convertible subjects classified at
universe codes carry EQUAL (level, flag) under grown wf — open SN normalizes both, SR-star
re-types the pins, the join collapses at the shared normal form, the E2.7 master negotiates. -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.convUniverseClassificationUnique
#assert_no_axioms FX1Poly.Typed.contextConversion_isZeroArm
#assert_no_axioms FX1Poly.Typed.cost_discriminates_weakening_vs_dispatch
