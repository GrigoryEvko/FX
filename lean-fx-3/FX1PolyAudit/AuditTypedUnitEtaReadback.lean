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
import FX1Poly.Typed.EtaReadbackFrameBoundary
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

/-! # FX1PolyAudit/AuditTypedUnitEtaReadback — typed-layer zero-axiom gates: unit-eta judgmental equality, the collapse deciders, and type-directed readback
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/


/-! ### Honesty — 0-false-positive probe (ill-typed cell has no derivation) -/

#assert_no_axioms FX1Poly.Typed.unitCell
#assert_no_axioms FX1Poly.Typed.boolTrueValue_notConvertible_unitValue
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

/-! ### UNIT-1 — the unit data story (gen_unitCode + formation + intro + canonical form)

The 198th generator landed cascade-free: gen_unitCode (nullary type code) + the Unit:Type@0
base-type row + the gen_unit:unitCode intro row (ending gen_unit's reserved status), each ONE
table row absorbed by the table-generic metatheory; the only per-row ripple is one disjunct in the
two membership lemmas and their consumers.  subjectIsUnitOfUnitClassifier is the ONE-VALUE
COLLAPSE at the data-intro engine — the substrate brick for typed unit-eta (the (B) half of #364,
eta-M15d). -/

#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_unitCode
#assert_no_axioms FX1Poly.Typed.HasTypeDescBaseType.unitCodeTyped
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_unit
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.unitValueTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescDataIntro.subjectIsUnitOfUnitClassifier
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_unit
#assert_no_axioms FX1Poly.Typed.semanticTier_unit
#assert_no_axioms FX1Poly.Core.generatorCount_upperBound
#assert_no_axioms FX1Poly.Core.generatorCount_lastIndex

/-! ### UnitEtaJudgmentalEquality — ★ typed unit-η, the equality βη-rewriting cannot express (#362)

`DefEqUnitEta` = βη-conversion (#1202-decided) ⊕ the type-directed one-value collapse at
`unitTypeCell`.  Equivalence package unconditional given derivations (transitivity discharges its
βη-βη peak with the wf + middle-typing the arm CARRIES); `strictlyExtendsBetaEtaConv` is the
machine-checked textbook witness — the unit-typed VARIABLE vs `unitCell`, judgmentally equal but
provably not βη-joinable; `decidableOfWfTyped` decides the relation by one structural classifier
comparison + the #1202 decider.  Honest boundaries in the module docstring: not congruent (η-long
readback is the #481/#364 remainder); the data-intro fragment is refl-degenerate
(`dataIntroUnitPairsCollapseToRefl`).  The raw-context boundary is DISCHARGED by the UNIT-3
formation row (payoff gates below). -/

#assert_no_axioms FX1Poly.Typed.DefEqUnitEta
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.reflOfGrownTyped
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.sym
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.trans
#assert_no_axioms FX1Poly.Typed.unitVariableTyped
#assert_no_axioms FX1Poly.Typed.unitVariableNotBetaEtaConvUnitValue
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.strictlyExtendsBetaEtaConv
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.dataIntroUnitPairsCollapseToRefl
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.betaEtaConvOfNotUnit
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.decidableOfWfTyped

/-! ### UNIT-3 payoff — unit-typed variables get the wf metatheory (#1205 closure)

The nullary `unitCode` formation row (flag-pinned `nullaryFormerOutput`) discharges the UNIT-2
raw-context boundary: `unitTypeCell` is formation-typed at the pinned `Type@0` in ANY context
(`unitTypeCellFormationTyped` — the row fires with the empty telescope, its floating flag absorbed
by the flag-IGNORING output), so `WfContextDesc` binds it (`unitVariableContextWellFormed`), the
grown lift hands the unit context the full wf metatheory — open SN / open βη-SN / βη
Church-Rosser (`unitVariableContextWellFormedPi`) — and BOTH the strictness witness and the
unit-η decider now live on the decidable wf fragment
(`strictlyExtendsBetaEtaConvOnWfFragment` / `unitVariableDecidable`).  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.unitTypeCellFormationTyped
#assert_no_axioms FX1Poly.Typed.unitTypeCellIsTypeDesc
#assert_no_axioms FX1Poly.Typed.unitVariableContextWellFormed
#assert_no_axioms FX1Poly.Typed.unitVariableContextWellFormedPi
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.strictlyExtendsBetaEtaConvOnWfFragment
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.unitVariableDecidable

/-! ### UnitEtaCongruenceGap — ★ `DefEqUnitEta` is NOT congruent, machine-checked (#481/#364 route)

The pair-of-units congruence gap: the COMPONENTS (unit variable / `unitCell`) are `DefEqUnitEta` at
`unitTypeCell`, yet the PAIRS `pair(x,x)` / `pair(unit,unit)` are `DefEqUnitEta` at NO classifier —
the `unitEta` arm refuted by both unit-typing engines (data-intro forces subject = `unitCell`;
the grown engine types no `gen_pair` cell), the βη arm by joint βη-normality.  This turns the
UNIT-2 docstring-only boundary (1) into a theorem and pins what the η-long type-directed readback
(#481, the #364 remainder) must close — no rewriting-relation extension can.  The module also
commits the route record: R1 unit-only congruent collapse (term-structural, checker-directed),
then R2 full η-long quote at Π/Σ/Unit (classifier-structure recursion, level-measured). -/

#assert_no_axioms FX1Poly.Typed.pairOfUnitVariables
#assert_no_axioms FX1Poly.Typed.pairOfUnitValues
#assert_no_axioms FX1Poly.Typed.pairOfUnitVariables_notBetaEtaConv_pairOfUnitValues
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.isNotCongruent

/-! ### UnitEtaCongruentEquality — the congruent unit-η SPEC + the strictness chain (ULC-1)

`DefEqUnitEtaCong` / `ChildrenUnitEtaCong` — the mutual congruent closure of `DefEqUnitEta`
(zero-shift fragment: `consZero` relates shift-0 children by the full relation, `consEqual` keeps
binder children equal).  Unconditional `refl`/`sym`; ★ `gapPairCongruentlyEqual` relates exactly
the pair `DefEqUnitEta.isNotCongruent` proves unreachable; ★ `strictlyExtendsDefEqUnitEta`
completes the machine-checked chain `BetaEtaConv ⊊ DefEqUnitEta ⊊ DefEqUnitEtaCong`.  Honest
boundaries: transitivity is a RULE of the declarative spec (`trans` ctor — its admissibility in
the trans-FREE algorithmic presentation is the canonicalizer-completeness question), no
binder-crossing congruence (needs per-generator binder-domain context extension), the congruence
skeleton is raw (leaves carry the typing).  ULC-1 verdict recorded in the module docstring:
spec-first; the classifier-supply question moves to the decider. -/

#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong
#assert_no_axioms FX1Poly.Typed.ChildrenUnitEtaCong
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.refl
#assert_no_axioms FX1Poly.Typed.ChildrenUnitEtaCong.refl
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.sym
#assert_no_axioms FX1Poly.Typed.ChildrenUnitEtaCong.sym
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.gapPairCongruentlyEqual
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.strictlyExtendsDefEqUnitEta

/-! ### UnitVariableCollapse — the computable unit-collapse + UNCONDITIONAL soundness (ULC-2)

`collapseUnitVariables` — the first computable canonicalizer for the congruent unit-η equality:
replace unit-typed VARIABLES (one decidable lookup comparison — no checker, no wf) with
`unitCell`, shift-0 descent, binder children untouched.  ★ Soundness UNCONDITIONAL
(`collapseUnitVariables_congruent`: each replacement discharges `unitEta` via the wf-free `var`
rule + `unitValueTyped`); ★ the canonicalizer COMPUTES the gap pair by `rfl`
(`collapseUnitVariables_computesGapPair`) and rederives the hand-built spec witness
(`collapse_rederivesGapPair`).  Boundaries: variables only (compound unit-typed neutrals need the
checker-directed detection — follow-on), canonicalizer half only (compare half + completeness/
transitivity payoff are the next bricks). -/

#assert_no_axioms FX1Poly.Typed.collapseUnitVariables
#assert_no_axioms FX1Poly.Typed.collapseUnitVariablesChildren
#assert_no_axioms FX1Poly.Typed.collapseUnitVariables_congruent
#assert_no_axioms FX1Poly.Typed.collapseUnitVariablesChildren_congruent
#assert_no_axioms FX1Poly.Typed.collapseUnitVariables_computesGapPair
#assert_no_axioms FX1Poly.Typed.collapse_rederivesGapPair

/-! ### The decision procedure's soundness (ULC-3A) — collapse, then compare

The declarative spec gained its `trans` RULE (standard for judgmental equality; admissibility in
the trans-free algorithmic presentation = the canonicalizer-completeness question), and the
decision procedure's soundness composes through the collapsed middle: `ofCollapsesEqual`
(syntactic mode — UNCONDITIONAL, decidable by structural `DecidableEq`),
`ofCollapsedBetaEtaConv` (βη mode — wf + COLLAPSED typings as hypotheses, since the collapse
moves dependent classifiers by the congruent equality itself, not `Conv`), and
`collapsedComparisonDecidable` (#1202 decides the βη comparison).
`unitEtaCongProcedure_decidesGapPair` decides the flagship gap pair in syntactic mode,
hypothesis-free — the third independent derivation.  COMPLETENESS (negative answers refute)
remains the named open brick. -/

#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.ofCollapsesEqual
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.ofCollapsedBetaEtaConv
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.collapsedComparisonDecidable
#assert_no_axioms FX1Poly.Typed.unitEtaCongProcedure_decidesGapPair

/-! ### UnitCollapseIncompleteness — ★ the one-pass procedure is INCOMPLETE (ULC-3B verdict)

The β-surfacing refutation: `app(lam(Unit, var₁), x)` is grown-typed at `unitTypeCell` (concrete
`piIntro`/`piElim` over the #1205 unit row) hence congruently unit-η-equal to `x` — yet its
collapse `app(lam(Unit, var₁), unitCell)` reduces ONLY to `var₀ = x`, never joining
`collapse(x) = unitCell`: β surfaces binder-hidden unit-variable occurrences AFTER the zero-shift
collapse has passed.  Completeness as planned (one collapse pass, then compare) is FALSE; the
ULC-2 soundness is untouched (sound SEMI-decision), and the corrected route is the
normalize-FIRST canonicalizer (βη-normalize via typed SN, then collapse — on the witness both
sides reach `unitCell`).  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.betaSurfacingRedex
#assert_no_axioms FX1Poly.Typed.collapsedBetaSurfacingRedex
#assert_no_axioms FX1Poly.Typed.collapse_betaSurfacingRedex
#assert_no_axioms FX1Poly.Typed.betaSurfacingRedexTyped
#assert_no_axioms FX1Poly.Typed.betaSurfacingPair_congruentlyEqual
#assert_no_axioms FX1Poly.Typed.noEtaFromAppHead
#assert_no_axioms FX1Poly.Typed.collapsedBetaSurfacingRedex_step_eq
#assert_no_axioms FX1Poly.Typed.collapsedBetaSurfacingRedex_notBetaEtaConv_unitCell
#assert_no_axioms FX1Poly.Typed.unitEtaCongProcedure_isIncomplete

/-! ### UnitCollapseBinderFence — ★ normalize-FIRST is ALSO incomplete (the ULC-4 sub-spike)

The binder-fence refutation: `app(λa.λb.a, x)` and `app(λa.λb.a, unitCell)` are Cong-related at
the ZERO-SHIFT argument position, but β relocates the unit-difference UNDER the surviving binder
— the βη normal forms `λb.x↑` / `λb.unitCell` are both βη-normal, both FIXED by the zero-shift
collapse, neither equal after collapse nor βη-convertible.  NO binder-fenced canonicalizer (any
normalize/collapse interleaving) is complete for the congruent relation.  Route consequence:
completeness requires collapsing UNDER binders — the per-generator binder-domain table, the true
#481 type-directed readback skeleton (the ULC-4 re-scope).  Both prior soundness packages remain
sound semi-decisions.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.konstUnitFunction
#assert_no_axioms FX1Poly.Typed.konstAppliedToUnitNormalForm
#assert_no_axioms FX1Poly.Typed.konstApplications_congruentlyEqual
#assert_no_axioms FX1Poly.Typed.konstAppliedToUnit_normalizes
#assert_no_axioms FX1Poly.Typed.collapsedKonstNormalForms_distinct

/-! ### UnitVariableCollapseDeep — the BINDER-CROSSING collapse crosses the fence (ULC-4 brick B)

The binder-domain "table" is the telescope discipline: a shift-1 child's binder domain IS its
preceding sibling (TELESCOPE-REACH), so the deep traversal threads the previous (original)
sibling and pushes it as the context extension — table-free, cast-free, structural.  ★ Proof of
life: the deep collapse sends the binder-fence witness `λ(b:Unit).x↑` to `λ(b:Unit).unitCell` BY
`rfl` (`deepCollapse_crossesBinderFence`) and IDENTIFIES the two normal forms that refuted
normalize-first (`deepCollapse_identifiesKonstNormalForms`); it agrees with the fenced collapse
on the binder-free gap pair.  Honest boundaries: soundness needs the spec's binder-crossing
congruence arm (next brick); shift-1-without-preceding-sibling and shift ≥ 2 children stay
fenced (none live today).  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.collapseUnitVariablesDeep
#assert_no_axioms FX1Poly.Typed.collapseUnitVariablesDeepChildren
#assert_no_axioms FX1Poly.Typed.deepCollapse_crossesBinderFence
#assert_no_axioms FX1Poly.Typed.deepCollapse_identifiesKonstNormalForms
#assert_no_axioms FX1Poly.Typed.deepCollapse_computesGapPair

/-! ### UnitVariableCollapseDeepSound — deep soundness, UNCONDITIONAL (ULC-4 brick C)

The spec gained the binder-crossing congruence arm (`consBinder`, with the SHARED-only
`Option`-threaded children relation — shared threading keeps `sym` provable where left-threading
would break it), and the deep collapse is sound against it: ★
`collapseUnitVariablesDeep_congruent` — every term congruently unit-η-equal to its deep collapse,
ANY context, no wf (the under-binder `unitEta` leaf rides the `var` rule in the extended
context).  The proof composes per cell through the bodies-only intermediate spine with the
spec's `trans` rule (leg 1: heads shared / bodies via `consBinder`; leg 2: heads via `consZero` /
bodies shared).  `ofDeepCollapsesEqual` = the hypothesis-free deep semi-decision; ★
`konstNormalForms_congruentlyEqual` — the binder-fence pair is decided POSITIVELY (the deep
procedure is strictly stronger than every fenced one).  Completeness re-poses next.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.ChildrenUnitEtaCong
#assert_no_axioms FX1Poly.Typed.collapseBinderBodiesOnlyChildren
#assert_no_axioms FX1Poly.Typed.collapseUnitVariablesDeep_congruent
#assert_no_axioms FX1Poly.Typed.collapseBinderBodiesLeg
#assert_no_axioms FX1Poly.Typed.collapseHeadsLeg
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.ofDeepCollapsesEqual

/-! ### UnitCollapseNeutralBoundary — ★ the brick-D verdict: incomplete at compound neutrals

The mandated pre-construction re-analysis, machine-checked: the deep collapse ERASES both prior
refutation witnesses, but completeness fails at a SIMPLER boundary — `x` and `app(f, x)` are
both unit-typed (one `unitEta` leaf, no β, no binder) in `(f : Π(_:Unit).Unit, x : Unit)`, yet
their deep collapses `unitCell` / `app(f, unitCell)` are distinct βη-normal forms that never
join.  VERDICT: completeness of the congruent unit-η decider IS the completeness of
unit-typedness DETECTION at replacement sites — compound neutrals need check-mode against
`unitTypeCell` whose soundness lives only on the route-H wf fragment (an unsound positive would
break collapse SOUNDNESS, not just completeness), or equivalently the full #481 type-directed
readback.  All soundness packages intact.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.unitFunctionContext
#assert_no_axioms FX1Poly.Typed.compoundUnitNeutral
#assert_no_axioms FX1Poly.Typed.compoundUnitNeutralTyped
#assert_no_axioms FX1Poly.Typed.unitVariable_congruentlyEqual_compoundNeutral
#assert_no_axioms FX1Poly.Typed.deepCollapse_compoundUnitNeutral
#assert_no_axioms FX1Poly.Typed.collapsedCompoundNeutral_notBetaEtaConv_unitCell
#assert_no_axioms FX1Poly.Typed.deepCollapseProcedure_isIncompleteAtCompoundNeutrals

/-! ### UnitNeutralSpineDetection — spine-inversion detection of unit-typed neutrals (ULC-5 brick 1)

The route decision post-verdict: NOT the whnf-directed checker (STR-5 — an unsound positive would
break collapse soundness) but SPINE INVERSION: synthesize the type of a variable-headed application
spine by `var` lookups + `piElim` codomain instances on literal Π codes with syntactic domain
matches.  `detectSpineType_sound` is UNCONDITIONAL (any context, no wf) — every positive answer
carries a real grown typing.  The compound-neutral witness is detected by `rfl` and its boundary
pair re-certified from the detector's output alone.  Residual fragment gaps (each a future
widening, soundness statement unchanged): λ/value arguments, Conv-not-equal domain matches,
reducible function types.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.asPiCode?
#assert_no_axioms FX1Poly.Typed.asPiCode?_sound
#assert_no_axioms FX1Poly.Typed.detectSpineType
#assert_no_axioms FX1Poly.Typed.detectSpineType_sound
#assert_no_axioms FX1Poly.Typed.detectsCompoundUnitNeutral
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.ofDetectedUnitSpines
#assert_no_axioms FX1Poly.Typed.compoundNeutralPair_certified

/-! ### UnitSpineDetectionBoundary — ★ the 5th refutation: spine detection misses λ-arguments

The brick-2 pre-construction verdict: `app(g, λ(x:Unit).x)` in `(g : Π(_:Π(_:Unit).Unit).Unit)`
is grown-typed at `unitTypeCell` (wf-free: var + piIntro + piElim) and congruently unit-η-equal
to `unitCell`, yet `detectSpineType` answers `none` on it at EVERY fuel — the spine grammar
demands the argument synthesize, and a λ never does.  Detector-driven deep collapse is
incomplete BEFORE construction.  Widening to λ-arguments = λ-synthesis (piIntro + formation
obligations) = bidirectional checking = the #481 readback.  The unit campaign's elimination
chain is COMPLETE: five refutations, five forced components.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.higherOrderUnitContext
#assert_no_axioms FX1Poly.Typed.unitIdentityFunction
#assert_no_axioms FX1Poly.Typed.lambdaArgumentNeutral
#assert_no_axioms FX1Poly.Typed.unitIdentityFunctionTyped
#assert_no_axioms FX1Poly.Typed.lambdaArgumentNeutralTyped
#assert_no_axioms FX1Poly.Typed.lambdaArgument_congruentlyEqual_unitValue
#assert_no_axioms FX1Poly.Typed.detectSpineType_missesUnitIdentityFunction
#assert_no_axioms FX1Poly.Typed.detectSpineType_missesLambdaArgument
#assert_no_axioms FX1Poly.Typed.spineDetection_isIncompleteAtLambdaArguments
#assert_no_axioms FX1Poly.Typed.readbackAtClassifier
#assert_no_axioms FX1Poly.Typed.readbackSpine
#assert_no_axioms FX1Poly.Typed.readbackAtClassifier_congruent
#assert_no_axioms FX1Poly.Typed.readbackSpine_congruent
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.ofReadbackEqual
#assert_no_axioms FX1Poly.Typed.unitFunctionContextWellFormed
#assert_no_axioms FX1Poly.Typed.higherOrderUnitContextWellFormed
#assert_no_axioms FX1Poly.Typed.betaSurfacingPair_decidedByReadback
#assert_no_axioms FX1Poly.Typed.compoundNeutralPair_decidedByReadback
#assert_no_axioms FX1Poly.Typed.lambdaArgumentPair_decidedByReadback
#assert_no_axioms FX1Poly.Typed.readback_identifiesKonstNormalFormsAtPi
#assert_no_axioms FX1Poly.Typed.readback_etaExpandsNeutralAtPi
#assert_no_axioms FX1Poly.Typed.etaPair_decidedByReadback
#assert_no_axioms FX1Poly.Typed.etaUnitPair_decidedByReadback

/-! ### UnitReadbackArgumentBoundary — ★ the 6th boundary + its RESOLUTION by the spine arm

The brick-3/4 cycle: (Σ) the Σ-η mirror is BLOCKED by engine separation — the expansion emits a
pair and `pairCellHasNoTyping` makes `ofBetaEtaConv`'s both-typed presupposition unsatisfiable
(#361 re-gated on a grown pair-intro rule); (the boundary) in
`(f : Π(_:Π(_:Unit).Unit).Type@0, g : Π(_:Unit).Unit)` the pair `app(f,g)` vs
`app(f, λx.(weaken g)x)` is Cong-related (the η pair at an ARGUMENT position) yet its DEEP
COLLAPSES are distinct never-joining βη-normal forms — every binder-fenced/collapse-mode
procedure fails it; (the resolution) the NEUTRAL-SPINE arm recovers the argument's classifier
from the head variable's looked-up Π code: both sides now read back to the η-long
`app(f, λ(x:Unit).unitCell)` and `ofReadbackEqual` decides the pair at `rfl`.  The spine-arm
soundness chains `invertApp` + `invertVar` + Π-injectivity + `lookupIsTypeDesc` +
`inversionPiCodeComponents` — every hypothesis self-supplied by the wf presuppositions.
Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.appArgumentContext
#assert_no_axioms FX1Poly.Typed.appArgumentContextWellFormed
#assert_no_axioms FX1Poly.Typed.appliedToBareArgument
#assert_no_axioms FX1Poly.Typed.appliedToEtaExpandedArgument
#assert_no_axioms FX1Poly.Typed.appliedToBareArgumentTyped
#assert_no_axioms FX1Poly.Typed.appliedToEtaExpandedArgumentTyped
#assert_no_axioms FX1Poly.Typed.appArgumentPair_congruentlyEqual
#assert_no_axioms FX1Poly.Typed.deepCollapse_appliedToEtaExpanded
#assert_no_axioms FX1Poly.Typed.deepCollapse_appliedToBare
#assert_no_axioms FX1Poly.Typed.collapsedAppArgumentPair_notBetaEtaConv
#assert_no_axioms FX1Poly.Typed.deepCollapseMode_isIncompleteAtApplicationArguments
#assert_no_axioms FX1Poly.Typed.appArgumentPair_decidedByReadback
#assert_no_axioms FX1Poly.Typed.readback_recoversArgumentClassifier

/-! ### UnitReadbackFormerChildBoundary — ★ the 7th boundary: formers hide their children

The post-spine completeness re-analysis: term positions inside TYPE CODES (the identity code's
endpoints) carry unit differences no shipped arm reaches — `Id(Unit, app(f,x), unit)` vs
`Id(Unit, unit, unit)` is Cong-related (one `congGen` through `gen_idCode`, the endpoints by
`unitEta`), yet the readback degrades to the deep collapse at every fuel (an `idCode` head is
not an application) and the collapses are distinct never-joining βη-normal forms — the
compound-neutral phenomenon recurring INSIDE a former.  CORRECTED verdict (brick-5 fact-check):
ENGINE-gated like Σ — `typingRuleDescOf` has no `gen_idCode` row and the `DescTelescope` schema
cannot express value premises (endpoints at the carrier), so the witness is outside the
currently-typeable fragment and typed former children are all TYPES today; the in-fragment
frontier is depth-2+ spines.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.identityCodeOverCompoundNeutral
#assert_no_axioms FX1Poly.Typed.identityCodeOverUnitValue
#assert_no_axioms FX1Poly.Typed.identityCodePair_congruentlyEqual
#assert_no_axioms FX1Poly.Typed.readback_identityCodeNeutral_isDeepCollapse
#assert_no_axioms FX1Poly.Typed.readback_identityCodeValue_isDeepCollapse
#assert_no_axioms FX1Poly.Typed.collapsedIdentityCodeOverCompoundNeutral
#assert_no_axioms FX1Poly.Typed.deepCollapse_identityCodeNeutral
#assert_no_axioms FX1Poly.Typed.deepCollapse_identityCodeValue
#assert_no_axioms FX1Poly.Typed.collapsedIdentityCodePair_notBetaEtaConv
#assert_no_axioms FX1Poly.Typed.readback_isIncompleteAtFormerChildren

/-! ### UnitReadbackDeepSpineBoundary — ★ the 8th boundary, DECIDED by the recursive spine

In `(g : Π(_:Unit).Π(_:Unit).Type@0, f : Π(_:Unit).Unit, x : Unit)`, the pair
`app(app(g, app(f,x)), x)` vs `app(app(g, unit), x)` is Cong-related (nested `congGen`
descents, the inner arguments by `unitEta`), the NEUTRAL side fully grown-typed at `Type@0`
(the value side's whole-spine typing blocked by the standing `unitCell` engine separation).
Against the FROZEN deep-collapse ingredient the boundary stands permanently
(`deepCollapseMode_isIncompleteAtDeepSpines` — the collapses are distinct never-joining
βη-normal forms).  The brick-6 mutual `readbackSpine` recursion DECIDES it: at fuel 4 both
sides compute to the η-long `app(app(g, unit), unit)` (`readback_identifiesDeepSpines`, `rfl`;
fuel 3 insufficient — the inner argument needs the unit ARM, not just the collapse) and the
typed soundness canonicalizes the neutral side directly
(`deepSpine_canonicalizedByReadback`); the substituted-domain wall was never met — app-headed
positions need only `invertApp` (same context), classifier-directed readback stays at
var-headed levels where the domain is a context entry.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.deepSpineContext
#assert_no_axioms FX1Poly.Typed.deepSpineContextWellFormed
#assert_no_axioms FX1Poly.Typed.deepSpineInnerNeutral
#assert_no_axioms FX1Poly.Typed.deepSpineOverNeutral
#assert_no_axioms FX1Poly.Typed.deepSpineOverUnitValue
#assert_no_axioms FX1Poly.Typed.deepSpineInnerNeutralTyped
#assert_no_axioms FX1Poly.Typed.deepSpineOverNeutralTyped
#assert_no_axioms FX1Poly.Typed.deepSpinePair_congruentlyEqual
#assert_no_axioms FX1Poly.Typed.collapsedDeepSpineOverNeutral
#assert_no_axioms FX1Poly.Typed.collapsedDeepSpineOverUnitValue
#assert_no_axioms FX1Poly.Typed.deepCollapse_deepSpineNeutral
#assert_no_axioms FX1Poly.Typed.deepCollapse_deepSpineValue
#assert_no_axioms FX1Poly.Typed.collapsedDeepSpinePair_notBetaEtaConv
#assert_no_axioms FX1Poly.Typed.deepCollapseMode_isIncompleteAtDeepSpines
#assert_no_axioms FX1Poly.Typed.readback_identifiesDeepSpines
#assert_no_axioms FX1Poly.Typed.deepSpine_canonicalizedByReadback

/-! ### UnitReadbackAnnotationBoundary — ★ the 9th boundary, DECIDED by trust-the-classifier

In the EMPTY context, `λ(app(λ(x:Type@0).x, Unit)).x₀` and `λ(Unit).x₀` are BOTH grown-typed at
`Π(_:Unit).Unit` (the redex-annotated side via `conv` through the Π-code congruence step) — the
FIRST boundary pair with both endpoints typed at one formation-typed classifier.  Against the
FROZEN deep-collapse ingredient the boundary stands permanently
(`deepCollapseMode_isIncompleteAtAnnotationMismatch`): the collapse's syntactic lookup test
cannot see unit-typedness BEHIND the redex, and the collapses never βη-join (the
variable-bodied-λ star-chain invariant over `Step.from_lam` + `no_step_from_var` + root-η
refutation).  The brick-7 trust-the-classifier λ arm DECIDES it: both λs read back to the
η-long `λ(Unit).unit` at fuel 1 (`readback_canonicalizesAnnotations`, `rfl`) and
`ofReadbackEqual` closes the pair (`annotationPair_decidedByReadback`).  NOT a
pair-decidability gap — the pair is βη-joinable in ONE congruence step; the boundary was about
CANONICAL-FORM completeness of the #364 normalize-and-compare route.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Typed.redexAnnotation
#assert_no_axioms FX1Poly.Typed.annotatedByRedex
#assert_no_axioms FX1Poly.Typed.annotatedByLiteral
#assert_no_axioms FX1Poly.Typed.redexAnnotation_steps
#assert_no_axioms FX1Poly.Typed.redexAnnotationTyped
#assert_no_axioms FX1Poly.Typed.annotatedByRedexTypedAtRedexPi
#assert_no_axioms FX1Poly.Typed.readback_annotatedByRedex_isEtaLong
#assert_no_axioms FX1Poly.Typed.deepCollapse_annotatedByRedex
#assert_no_axioms FX1Poly.Typed.deepCollapse_annotatedByLiteral
#assert_no_axioms FX1Poly.Typed.readback_annotatedByLiteral_isEtaLong
#assert_no_axioms FX1Poly.Typed.hasVariableBodyUnderLam
#assert_no_axioms FX1Poly.Typed.annotationCollapseForms_notBetaEtaConv
#assert_no_axioms FX1Poly.Typed.deepCollapseMode_isIncompleteAtAnnotationMismatch
#assert_no_axioms FX1Poly.Typed.readback_canonicalizesAnnotations
#assert_no_axioms FX1Poly.Typed.annotationPair_decidedByReadback
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.unitDetection_completeOnFormationClassifiers
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.ofNbeEqual
#assert_no_axioms FX1Poly.Typed.readbackAlone_keepsBetaRedex
#assert_no_axioms FX1Poly.Typed.readbackAtClassifier_constantAtUnit
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.nbeNormalForm_constantAtUnit
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.nbeComplete_atUnit
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.checkNbeEqual_iff_atUnit
#assert_no_axioms FX1Poly.Typed.DefEqUnitEtaCong.decidableAtUnit
-- unit + identity(refl) canonicity via sconing: the last two data types join the generic witness (SN-049 Unit,
-- SN-059/067 identity introduction), completing data-canonicity-via-sconing coverage to ALL data axes. Thin
-- isValue specializations (isUnitValue / isReflValue); #672-free extraction, conditional only on the per-type
-- fundamental (NOT typed SN), so genuinely unblocked.
#assert_no_axioms FX1Poly.Core.unitCanonicityViaSconing
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
#assert_no_axioms FX1Poly.Typed.reduceOnce_unit_halts
#assert_no_axioms FX1Poly.Typed.reduceOnce_nestedRedex_fires
-- The bounded nullary unitCode former membership (the childless data-former analogue of the list/option
-- membership steps): the inert normal leaf Unit is a bound-reducible member of its pinned Type@0 given the output
-- positivity 0 < bound, which the genFormation budget's nullaryBelowBound gate supplies. Used by the unitCode
-- branch of both the formation and grown genFormationPi FT arms.
#assert_no_axioms FX1Poly.Typed.unitFormerMemberAtBounded

-- The GROWN-engine per-derivation budget (BoundExceedsPi.lean, BFT-12a). Mutual inductive Prop over HasTypeDescPi /
-- DescTelescopePi. The grown engine has NO universeFormation leaf, so this carries NO belowBound of its own — the
-- ofFormation ctor carries the embedded BoundExceeds (where the fuel lives), every other ctor threads
-- sub-BoundExceedsPi (conv/piIntro/piElim) or the telescope budget (genFormationPi). Foundation for the BFT-12c
-- grown FT discharge (BoundExceedsPi.rec, ofFormation arm → BFT-11) at a single fixed bound.
#assert_no_axioms FX1Poly.Typed.BoundExceedsPi
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_unit
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_unit
#assert_no_axioms FX1Poly.Typed.semanticTier_unit
#assert_no_axioms FX1Poly.Typed.idTowerCollapsesToCanonicalValue
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_unitCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_unitCode_outputConstant
#assert_no_axioms FX1Poly.Typed.eq_unitCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.unitFormerNotTypedAtPiType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.unitFormerNotTypedAtEmptyType
#assert_no_axioms FX1Poly.Typed.DefEqUnitEta.pairCellOutsideDomain
#assert_no_axioms FX1Poly.Typed.sigmaEtaEquation_underivable

/-! ### EliminatorMotiveShapeRecord — the Phase-Z₀ motive-migration record (Z0-DECIDE + boolElim stage)

The decision record + per-generator shape pins for the Z₀ eliminator-motive migration.  The
`gen_boolElim` stage has SHIPPED: its two pins now assert the motive-carrying shape (arity 4,
binderShifts `[1,0,0,0]`, spine `(motive, thenBranch, elseBranch, scrutinee)`); the remaining
SEVEN eliminator generators are still pinned FLAT — each future migration stage breaks exactly
its own generator's two pins (Route A's regression tripwires).  `HasTypeDescBoolElimDependent`
now expresses DEPENDENT elimination by reading the STORED motive child applied by `subst0` —
decidable checking and uniqueness at neutral scrutinees are exactly what storing the motive
buys (pre-migration this judgment carried the motive EXTRINSICALLY as the Route-B feasibility
spike, with those two limits named).  `subsumesSimpleShape` (constant motive recovers the
simple rule via `weaken_subst_singleton`), a non-vacuous smoke, and by-construction
ι-coherence at the value scrutinee survive the reshape.  The module docstring carries the
costed Route A (staged substrate migration, per-eliminator atomic stages) / Route B
(extrinsic-motive judgments) / Route C (rejected) decision record. -/

#assert_no_axioms FX1Poly.Typed.boolElim_arity_isFlat

/-! ### The η-readback FRAME BOUNDARY (the Σ/modal/cubical verdict)

The advanced η-long readback arms are FRAME-BLOCKED, not unwritten: each
advanced η-expansion (`pair (fst t) (snd t)`, `modIntro (modElim t)`,
`pathLam (...)`, `glueIntro (...) t`) is grown-UNTYPABLE (its head has no
row in any grown rule table), so an η-expanding arm at those classifiers
could never satisfy the readback soundness's `ofBetaEtaConv` obligation.
The shipped behavior at a Σ classifier — neutral-spine delegation — is
pinned by reduction.  The unlock is named in the module docstring (grown
intro rows beyond the binder schema, or a combined-engine frame). -/

#assert_no_axioms FX1Poly.Typed.isUntypableHead_pair
#assert_no_axioms FX1Poly.Typed.isUntypableHead_modIntro
#assert_no_axioms FX1Poly.Typed.isUntypableHead_pathLam
#assert_no_axioms FX1Poly.Typed.isUntypableHead_glueIntro
#assert_no_axioms FX1Poly.Typed.etaPairSource_notGrownTyped
#assert_no_axioms FX1Poly.Typed.etaModIntroSource_notGrownTyped
#assert_no_axioms FX1Poly.Typed.etaPathLamSource_notGrownTyped
#assert_no_axioms FX1Poly.Typed.etaGlueIntroSource_notGrownTyped
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_ne_unitTypeCell
#assert_no_axioms FX1Poly.Typed.asPiCode?_sigma_isNone
#assert_no_axioms FX1Poly.Typed.readbackAtClassifier_sigmaDelegatesToSpine
