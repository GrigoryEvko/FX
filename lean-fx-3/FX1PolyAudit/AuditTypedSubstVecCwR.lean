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
import FX1Poly.Tier0.FxBaseSubstDisplayMap
import FX1Poly.Tier0.FxBaseSubstTypeFormers
import FX1Poly.Typed.DisplayMapDecidableFibration
import FX1Poly.Typed.GluedModelTypeFormers
import FX1Poly.Tier0.FxBaseSubstCanonicityExtraction
import FX1Poly.Typed.NormalizationTransferLedger
import FX1Poly.Typed.ParametricityTransferLedger
import FX1Poly.Typed.BksMetatheoryPackage
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
import FX1Poly.Typed.GluedModelModalFragment
import FX1Poly.Typed.SconingIsEnoughThesis
import FX1Poly.Typed.LiveSignatureSconingCoverage
import FX1Poly.Typed.TypeAxisObligation
import FX1Poly.Typed.UsageAxisObligation
import FX1Poly.Typed.EffectSecurityAxisObligations
import FX1Poly.Typed.RemainingDimensionAxisObligations
import FX1Poly.Modal.GradedCostSemantics
import FX1Poly.Modal.GradedCostRelation
import FX1Poly.Modal.GradedCostFundamental
import FX1Poly.Modal.GradedTermSize
import FX1Poly.Modal.GradedLinearTime
import FX1Poly.Modal.GradedLinearTimeBound
import FX1Poly.Core.NormalizeCost
import FX1Poly.Core.OneStepReducts
import FX1Poly.Typed.UniverseModeGenerators

/-! # FX1PolyAudit/AuditTypedSubstVecCwR — typed-layer zero-axiom gates: the term-carrying CwR substrate (SubstVec, scones, fxBase categories)
   (semantic shard of the typed audit; gates classified by declaration topic, appended
   clusters kept together; full import block retained for namespace-sweep coverage) -/

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
-- The cellular Tm↠Ty display map over the term-carrying base + its comprehension pullback
-- (FxBaseSubstDisplayMap.lean, SN-086 #589 core). SubstActionFamily = the COVARIANT functor
-- fxBaseSubstCategory → Type (a morphism X ⟶ Y is SubstVec Y X, so RawTerm.subst acts sections X → sections Y;
-- GlobalSections is the contravariant twin); identity/composition term-level functor laws lifted from the shipped
-- substitution algebra (subst_identity_apply / subst_compose through subst_pointwise). typeCellFamily = Ty
-- (type-position cells), ClassifiedCell + classifiedCellFamily = Tm (term cells PAIRED with classifiers,
-- componentwise action, structure-eta closure). displayClassifier = THE display map (cell ↦ classifier), naturality
-- rfl. genericClassifiedCell = the comprehension's generic element (fresh var over the weakened type; its display
-- boundary is rfl). displayClassifier_comprehension = ★ the Natural-Model pullback universal property in
-- generalized-element form: unique mediator through the display substitution (existence = SubstVec.cons + p/v laws;
-- uniqueness = cons_unique). Honest scope: the RAW cellular map — the typing refinement lives in the Typed module
-- below; in the renaming RMC the representable class is the isos and weakening is NOT an iso, so representability
-- is THIS comprehension property over the TERM base (as FxBaseRenamingVecGlobalSections predicted). All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity_subst_apply
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose_subst_apply
#assert_no_axioms FX1Poly.Tier0.typeCellFamily
#assert_no_axioms FX1Poly.Tier0.ClassifiedCell.componentsEqual
#assert_no_axioms FX1Poly.Tier0.classifiedCellFamily
#assert_no_axioms FX1Poly.Tier0.displayClassifier
#assert_no_axioms FX1Poly.Tier0.genericClassifiedCell_display
#assert_no_axioms FX1Poly.Tier0.displayClassifier_comprehension
-- The display map's typed refinement is a DECIDABLE fibration (DisplayMapDecidableFibration.lean, SN-086 #589
-- payoff — the #486 reading "representability = the decidable typing fibration"). IsAdmittedByFormation = the
-- judgmental gate over Tm (HasTypeDesc Γ subject classifier); decideAdmittedByFormation = ★ the
-- memberDecidable-shaped witness (membership in the typed refinement of every display fiber is decidable, via the
-- shipped TOTAL formation-engine decider HasTypeDesc.decidableOfWellFormed — honestly the categorical VIEW of the
-- shipped decidable checker #461/#303, not a new decidability result; the grown engine's checking stays
-- bidirectional per-head). displayFiberTypedMembershipDecidable = the fiberwise phrasing.
-- classifiedCellOfTyping + displayClassifier_classifiedCellOfTyping = every grown typing derivation is a point of
-- Tm and the display map sends it to its classifier (rfl). genericClassifiedCell_admittedByFormation/_admittedByGrown
-- = NON-VACUITY: the comprehension's generic element is genuinely typed over the extended context (HasTypeDesc.var
-- + definitional lookup_cons_zero + the SUBSTVEC-3 deep coherence weakening_subst_eq_rename aligning the
-- categorical weakening substitution with the typing context's weakening renaming). All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.ClassifiedCell.IsAdmittedByFormation
#assert_no_axioms FX1Poly.Tier0.ClassifiedCell.decideAdmittedByFormation
#assert_no_axioms FX1Poly.Typed.displayFiberTypedMembershipDecidable
#assert_no_axioms FX1Poly.Typed.classifiedCellOfTyping
#assert_no_axioms FX1Poly.Typed.displayClassifier_classifiedCellOfTyping
#assert_no_axioms FX1Poly.Typed.genericClassifiedCell_admittedByFormation
#assert_no_axioms FX1Poly.Typed.genericClassifiedCell_admittedByGrown
-- Pi/Sigma as concrete type formers (FxBaseSubstTypeFormers.lean, SN-087 #590). SubstVec.liftUnderBinder = the
-- under-binder lift (cons var0 (substVec ∘ weakening)) + the pointwise bridge to the kernel RawTermSubst.lift
-- (rfl at 0; lookup_compose + weakening_subst_eq_rename at successors) + the lift functor laws at the subst
-- level (identity via the pointwise identity + subst_identity_apply; composition via the shipped
-- RawTermSubst.lift_pointwise + lift_compose_pointwise (the polynomial-monad binder pull) + subst_compose).
-- binderParameterFamily = Uemura's Pi/Sigma parameter object (A : U, B : U^A) cellularly (pairs with a
-- binder-scoped codomain; action substitutes the codomain through the lift). piFormerMap/sigmaFormerMap = ★ the
-- concrete Pi/Sigma TYPE FORMERS as natural transformations into Ty — naturality is the genuine
-- substitution-commutes-with-the-former equation (the kernel fold computes the binder child through
-- RawTermSubst.lift, identified with the categorical lift). typeFormer_overRenamingVecRMC_resultIsIsomorphism =
-- the literal-record VERDICT: over fxBaseRenamingVecRMC the representable class is the isos, so every literal
-- TypeFormer's result map is an iso renaming — no genuine Pi can inhabit the literal record there; the honest
-- home is the presheaf level (exactly the natural-transformation side of the Uemura bijection, SN-088's
-- pairing). identityShapedTypeFormer/identityShapedFormerExtension/composedIdentityShapedExtensions = the
-- literal TypeFormer + CwRExtension records inhabited (first NONEMPTY newTypeFormers list; conservativity,
-- faithfulness + CwRExtension.compose exercised) at the only shape the iso class admits, honestly labeled
-- degenerate. Ledger: fxCwRExtensionConstructionLevel advanced extensionComposition →
-- concreteTypeFormerInstances (bijection + conservative-extension theorems remain open, SN-088). All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.SubstVec.liftUnderBinder_toRawTermSubst
#assert_no_axioms FX1Poly.Tier0.SubstVec.liftUnderBinder_subst_apply
#assert_no_axioms FX1Poly.Tier0.SubstVec.liftUnderBinder_identity_subst_apply
#assert_no_axioms FX1Poly.Tier0.SubstVec.liftUnderBinder_compose_subst_apply
#assert_no_axioms FX1Poly.Tier0.binderParameterFamily
#assert_no_axioms FX1Poly.Tier0.piFormer_subst_commutes
#assert_no_axioms FX1Poly.Tier0.sigmaFormer_subst_commutes
#assert_no_axioms FX1Poly.Tier0.piFormerMap
#assert_no_axioms FX1Poly.Tier0.sigmaFormerMap
#assert_no_axioms FX1Poly.Tier0.typeFormer_overRenamingVecRMC_resultIsIsomorphism
#assert_no_axioms FX1Poly.Tier0.identityShapedTypeFormer
#assert_no_axioms FX1Poly.Tier0.identityShapedFormerExtension_isFaithful
#assert_no_axioms FX1Poly.Tier0.composedIdentityShapedExtensions_typeFormerCount
#assert_no_axioms FX1Poly.Tier0.fxCwRExtensionConstructionLevel_eq
#assert_no_axioms FX1Poly.Tier0.fxCwRExtension_hasConcreteTypeFormerInstances
-- BKS preservation: the Pi/Sigma/universe formers lift to the glued model (GluedModelTypeFormers.lean,
-- SN-091 #594, the Phase-1 capstone of the O-NORM sconing ladder). GluedTypeCell = the glued-model type object:
-- a type cell + its computability predicate + the MODEL TIE (isModeled : ReducibleType typeCell computable) —
-- the tie distinguishes a glued point from an arbitrary pairing; candidate-hood is DERIVED from it
-- (GluedTypeCell.isCandidate via the SN-038 capstone ReducibleType.isReducibilityCandidate, at scope+1 for the
-- arrow CR1 variable inhabitant) and every glued type yields a SconingWitness (GluedTypeCell.scone — extraction
-- free by CR1 via reducibilityScone, SN-092). piLift = ★ the BKS lemma at Pi: cell = the SN-087 cellular
-- former's output, scone = the SN-038 dependent function-space predicate, model tie = ONE constructor
-- (ReducibleType.piType); the categorical-twin identifications piLift_typeCell / piLift_computable are rfl —
-- "the sconing of the Pi is the Pi of the sconings", literal. sigmaLift/universeLift route through the model's
-- neutral arm (table-generic formationGenerator_noWeakHeadStep over the gen_sigmaTyCode row;
-- universeCodeCell_noWeakHeadStep) — HONEST: the Sigma scone is the model's NEUTRAL (SN) assignment, not a
-- surjective-pairing predicate (that would be a model refinement). piLift/sigmaLift/universeLift_isCandidate =
-- the preservation payoff (the glued model is closed under the three formers); piLiftScone = the witness-level
-- form the extraction ledgers SN-093/094/095 consume. Categorical PACKAGING of proven content (SN-038 + its
-- capstone carry the mathematics); the new content is the former-by-former closure + the definitional
-- identification with SN-087 + the scone hand-off. All zero-axiom.
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.isCandidate
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.scone
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.piLift
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.piLift_typeCell
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.piLift_computable
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.sigmaLift
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.universeLift
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.piLift_isCandidate
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.sigmaLift_isCandidate
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.universeLift_isCandidate
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.piLiftScone
-- Canonicity extraction is a PER-SCONE property (FxBaseSubstCanonicityExtraction.lean +
-- GluedTypeCell.canonicityTransfer + the InternalSconing ledger advance, SN-093 #596, discharges #212).
-- THE REFUTATION: the GLOBAL CanonicityExtraction record (extract quantified over EVERY scone) is UNINHABITABLE
-- over both shipped GlobalSections — the adversarial emptyDomainScone (PEmpty semantic domain over scope 0,
-- whose sections are PUnit, inhabited) kills any global extract
-- (canonicityExtraction_overSubstBase_isFalse / _overRenamingBase_isFalse). The honest replacement:
-- SconeCanonicityExtraction (per-FIXED-scone, same two fields) with realizationIsSurjective (the choice-free
-- characterization direction) + isFalse_ofUnrealizedSection (the refutation criterion). Instances:
-- tautologicalSconeCanonicityExtraction (generic inhabitation, extract = id) + ★
-- closedTermSconeCanonicityExtraction (GENUINE: the closed-term scone's realization closedTermAsSection is
-- split by sectionAsClosedTerm, round-trip definitional) + emptyValueScone_hasNoCanonicityExtraction (the
-- CONSISTENCY reading: the empty type's predicate-carrying scone rightly refuses extraction — uninhabited
-- domain, inhabited sections). The law-carrying TRANSFER is GluedTypeCell.canonicityTransfer
-- (GluedModelTypeFormers.lean): for every glued type incl. the SN-091 lifts, well-typedness → canonicity (SN)
-- through the scone (SconingWitness.canonicity, extraction free by CR1). LEDGER: fxSconingConstructionLevel
-- advanced extractionRecordInterfaces → canonicityTransferTheorem (the SN-090 honest-scope deferral now
-- performed); fxSconing_hasNoConcretePreservationInstance/hasNoCanonicityTransferTheorem RENAMED to has* true
-- (rg'd: no shard gated the old names); normalization/parametricity/BKS levels remain false (SN-094/095/096).
-- All zero-axiom.
#assert_no_axioms FX1Poly.Tier0.emptyDomainScone
#assert_no_axioms FX1Poly.Tier0.canonicityExtraction_overSubstBase_isFalse
#assert_no_axioms FX1Poly.Tier0.canonicityExtraction_overRenamingBase_isFalse
#assert_no_axioms FX1Poly.Tier0.SconeCanonicityExtraction.realizationIsSurjective
#assert_no_axioms FX1Poly.Tier0.SconeCanonicityExtraction.isFalse_ofUnrealizedSection
#assert_no_axioms FX1Poly.Tier0.tautologicalSconeCanonicityExtraction
#assert_no_axioms FX1Poly.Tier0.closedTermSconeCanonicityExtraction
#assert_no_axioms FX1Poly.Tier0.emptyValueScone_hasNoCanonicityExtraction
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.canonicityTransfer
#assert_no_axioms FX1Poly.Tier0.fxSconingConstructionLevel_eq
#assert_no_axioms FX1Poly.Tier0.fxSconing_hasConcretePreservationInstance
#assert_no_axioms FX1Poly.Tier0.fxSconing_hasCanonicityTransferTheorem
-- The NormalizationExtraction laws carry NO normalization content; the honest reduction-sound form + the typed
-- transfer (NormalizationTransferLedger.lean, SN-094 #597). Unlike CanonicityExtraction (REFUTED, SN-093), the
-- NormalizationExtraction record IS inhabitable — but its ONE law (normalizeIdempotent, on the embedded image
-- only) never ties normalize to REDUCTION: punitNormalizationExtraction is a FULLY LAWFUL instance whose
-- normal-form family is the singleton PUnit at every object (normalize identifies ALL sections —
-- punitNormalizationExtraction_identifiesEverything, rfl), and identityNormalizationExtraction is the lawful
-- other extreme (normal forms = the sections themselves). The honest record: ReductionSoundNormalization domain
-- — the two missing laws, reaches (StepStar to the assigned form) + isNormal — with ★
-- snReductionSoundNormalization the GENUINE instance over the SN fragment (normalFormOf = the shipped
-- RawTerm.normalize, whose Acc parameter IS IsStronglyNormalizing definitionally; soundness = the shipped
-- normalize_reducesTo/normalize_isStepNormalForm; fixed-point on normal inputs =
-- snReductionSoundNormalization_eq_self_ofNormal). Domain restriction essential
-- (curryOmega_notStronglyNormalizing). ★ HasTypeDescPi.normalizationTransfer = the typed transfer (well-typed
-- over wf context ⟹ reaches a normal form, via the SN-043 open form); GluedTypeCell.normalizationTransfer =
-- the glued-model form (completes the canonicity/normalization transfer pair). LEDGER: fxSconingConstructionLevel
-- advanced canonicityTransferTheorem → normalizationTransferTheorem; fxSconing_hasNoNormalizationTransferTheorem
-- RENAMED → has* true (the prior firing's own gate updated — the rename lesson applies to the audit shard's OWN
-- gates too). Follow-on recorded: the full-domain ReductionSoundNormalization refutation needs Ω-not-WN (classic
-- Ω's only reduct is itself, Step inversion), strictly stronger than the shipped not-SN. All zero-axiom.
#assert_no_axioms FX1Poly.Typed.punitNormalizationExtraction
#assert_no_axioms FX1Poly.Typed.identityNormalizationExtraction
#assert_no_axioms FX1Poly.Typed.punitNormalizationExtraction_identifiesEverything
#assert_no_axioms FX1Poly.Typed.snReductionSoundNormalization
#assert_no_axioms FX1Poly.Typed.snReductionSoundNormalization_eq_self_ofNormal
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalizationTransfer
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.normalizationTransfer
#assert_no_axioms FX1Poly.Tier0.fxSconing_hasNormalizationTransferTheorem
-- The ParametricityExtraction record is LAWLESS; the honest type-indexed relational transfer
-- (ParametricityTransferLedger.lean, SN-095 #598). The third extraction-interface verdict: the record states
-- NO law at all (its fundamental's term argument is an underscore in the record itself) — canonicity's was
-- refuted, normalization's had one reduction-blind law, parametricity's has none. punitParametricityExtraction
-- = the constant-singleton-family inhabitant; punitParametricityExtraction_ignoresTerm (rfl) = fundamental
-- never consults the term. The honest content: ★ GluedTypeCell.parametricityTransfer — UNARY parametricity over
-- the glued model (every well-typed term satisfies ITS TYPE'S relational interpretation — the scone, tied to
-- the type by isModeled — and is SN by CR1; the relation family is assigned per type by ReducibleType, not
-- free-floating) + ★ GluedTypeCell.piFreeTheorem — the Reynolds abstraction-theorem shape at Π through the
-- SN-091 lift (a well-typed function maps RELATED arguments to RELATED results; the unfolding is definitional
-- because SN-087/091 made the Π relation literally that predicate). HONEST: this is unary parametricity
-- (exactly what the BKS scone derives); BINARY parametricity is the recorded follow-on (the graded
-- DIM-FUNCTORIAL projection is the dimension-indexed analogue already in the tree). LEDGER:
-- fxSconingConstructionLevel advanced normalizationTransferTheorem → parametricityTransferTheorem;
-- fxSconing_hasNoParametricityTransferTheorem renamed → has* true (own-gate update again). SN-096 (the BKS
-- bundle) is the remaining ledger level. All zero-axiom.
#assert_no_axioms FX1Poly.Typed.punitParametricityExtraction
#assert_no_axioms FX1Poly.Typed.punitParametricityExtraction_ignoresTerm
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.parametricityTransfer
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.piFreeTheorem
#assert_no_axioms FX1Poly.Tier0.fxSconing_hasParametricityTransferTheorem
-- ★ The BKS sconing metatheory package — the SconingConstructionLevel TOP (BksMetatheoryPackage.lean, SN-096
-- #599, completes the Phase-2 extraction-ledger arc). BksGluedMetatheoryPackage = the concrete preservation
-- instance (SN-090) + the three glued-model transfer theorems — canonicity (SN-093), normalization (SN-094),
-- parametricity (SN-095) — each over EVERY GluedTypeCell (hence the SN-091 Π/Σ/universe lifts) with the ONE
-- shared fundamental hypothesis; that sharing IS the BKS thesis (one fundamental feeds all three extractions,
-- the extractions free: CR1 / the normalizer / the membership). fxBksGluedMetatheoryPackage = the inhabitant
-- (direct application of the four shipped pieces; structure-field lambdas need ALL implicits explicitly bound —
-- fun {scope} glued {isWellTyped} … — positional binding grabs implicits otherwise). HONEST: the bundle is the
-- Leg-1 categorical ORGANIZATION of proven content, not an independent second SN proof
-- (sconingSN_eq_taitComposition); the three Tier-0 extraction records' verdicts (refuted / content-free /
-- lawless) are carried by the bundled honest replacements. LEDGER: fxSconingConstructionLevel reaches its TOP
-- level bksMetatheoryPackage; every has* theorem in InternalSconing.lean is now TRUE
-- (fxSconing_hasNoBKSMetatheoryPackage renamed → has*; no shard gated the old name). All zero-axiom.
#assert_no_axioms FX1Poly.Typed.fxBksGluedMetatheoryPackage
#assert_no_axioms FX1Poly.Tier0.fxSconingConstructionLevel_eq
#assert_no_axioms FX1Poly.Tier0.fxSconing_hasBKSMetatheoryPackage

-- ★ The sconing witness extends to the MODAL fragment — the first joint pair beyond MLTT
-- (GluedModelModalFragment.lean, ONORM-M1 #1211). ModalityFormer = the six one-child modality TYPE formers
-- (cohesive shape/flat/sharp, linear bang/whyNot, provability box; payload Unit, binderShifts [0]), enumerated
-- a la DataFormerFamily. ★ GluedTypeCell.modalityLift = the modal former lifts to the glued model through the
-- neutral arm exactly as SN-091's sigmaLift (weak-head normal per former by the cases-rootIota script — no
-- modality root carries a β/ι/scrutinee rule — and non-Π-rooted by nomatch); ONE definition covers all six.
-- ★ jointPair_mlttAndModal_underOnePackage = the headline: the SN-096 package instance
-- fxBksGluedMetatheoryPackage, built with ZERO modal knowledge, discharges canonicity for an MLTT lift (Σ) AND
-- the modal lift in one conjunction — "MLTT and the modal layer under ONE functor", the first genuine O-NORM
-- increment beyond MLTT; the three per-transfer corollaries are one-line applications of the same package.
-- modalBoxValueScone = the #721 categorical twin (SconingWitness over CanonicalFormsPredicate isModIntroValue,
-- canonical phase = reaches a modIntro VALUE — strictly finer than SN); ★ modalSconeConfinement = the semantic
-- O-FIRE confinement (closed well-typed box terms land under a modIntro ROOT with normal payload — the legacy
-- M44-T1 gate's content recovered at the candidate layer); modalCandidate_refinesModalityLiftScone = the
-- two-level coherence (value candidate refines the SN scone by CR1); the three *_preservesModalityLiftScone =
-- modIntro/modElim/subsume scone closure (#721/#722 re-read). HONESTY (the live-signature index):
-- modalTermFragment_isStaticallyUntypedToday + modalityFormers_haveNoFormationRowToday — hasSomeTypingRule is
-- FALSE (rfl) for all nine modal generators; the legacy modal typing died with HT-C, so the fundamental
-- obligations are explicit hypotheses, and wiring modal rule-table rows is the recorded follow-on. The modal
-- eliminator carries no β/ι rule (the collapse is raw η), so eliminator PROGRESS does not transfer — only
-- SN-closure does. All zero-axiom.
#assert_no_axioms FX1Poly.Typed.ModalityFormer
#assert_no_axioms FX1Poly.Typed.ModalityFormer.generator
#assert_no_axioms FX1Poly.Typed.ModalityFormer.formerCell
#assert_no_axioms FX1Poly.Typed.ModalityFormer.formerCell_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.ModalityFormer.formerCell_notPiRooted
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.modalityLift
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.modalityLift_isCandidate
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.modalityLift_canonicityTransfer
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.modalityLift_normalizationTransfer
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.modalityLift_parametricityTransfer
#assert_no_axioms FX1Poly.Typed.jointPair_mlttAndModal_underOnePackage
#assert_no_axioms FX1Poly.Typed.modalBoxValueScone
#assert_no_axioms FX1Poly.Typed.modalSconeConfinement
#assert_no_axioms FX1Poly.Typed.modalCandidate_refinesModalityLiftScone
#assert_no_axioms FX1Poly.Typed.modIntro_preservesModalityLiftScone
#assert_no_axioms FX1Poly.Typed.modElim_preservesModalityLiftScone
#assert_no_axioms FX1Poly.Typed.subsume_preservesModalityLiftScone
#assert_no_axioms FX1Poly.Typed.modalTermFragment_isStaticallyUntypedToday
#assert_no_axioms FX1Poly.Typed.modalityFormers_haveNoFormationRowToday

-- ★★ THE LEG-1 CAPSTONE: sconing is enough — ONE functor yields canonicity + normalization + parametricity
-- (SconingIsEnoughThesis.lean, SN-110 #613, discharges the #463 ONORM-spike GO/NO-GO frontier obligation).
-- ★ GluedTypeCell.sconingIsEnough = the thesis theorem: for EVERY glued type (the SN-091 Π/Σ/universe lifts,
-- the ONORM-M1 modality lifts, any future lift), ONE fundamental obligation yields all three metatheorems as
-- projections — the SN-096 package's three fields applied to the SAME hypothesis. sconingIsEnough_atMembership
-- = non-vacuity (well-typedness := scone membership, fundamental := id — the triple is real for every
-- computable term). ★ HasTypeDescPi.closedSconingTriple = the DISCHARGED instance, zero hypotheses: every
-- closed well-typed grown term is SN (BFT-14) ∧ reaches a normal form (the normalizer) ∧ is a
-- bounded-reducible member of its classifier's interpretation (BFT-13 — discharged unary parametricity).
-- HasTypeDescPi.openSconingPair = the open discharged pair (SN + normalization over any wf context; the open
-- parametricity leg is the recorded follow-on). sconingIsEnough_canonicityIsTaitComposition (rfl) = the
-- honesty pin: the thesis's canonicity projection IS CR1 ∘ fundamental — Leg-1 is the categorical
-- ORGANIZATION of the proven Tait content, not an independent second SN proof (HCAP triangulation
-- discipline). ONORM VERDICT: GO with three named residuals — per-fragment fundamentals (hypotheses outside
-- the engine fragments), STC ladder not consumed (the moonshot cross-check remains separate), and the
-- per-generator live-signature coverage gate (the recorded follow-on admission gate). All zero-axiom.
#assert_no_axioms FX1Poly.Typed.GluedTypeCell.sconingIsEnough
#assert_no_axioms FX1Poly.Typed.sconingIsEnough_atMembership
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSconingTriple
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.openSconingPair
#assert_no_axioms FX1Poly.Typed.sconingIsEnough_canonicityIsTaitComposition

-- ★ THE O-NORM ADMISSION GATE: every semantically-live generator is sconing-covered
-- (LiveSignatureSconingCoverage.lean, ONORM-M2 #1212 — the third SN-110 residual, closed). LiveGenerator =
-- the 40-ctor enumeration of the live signature (14 formers/codes + 15 value constructors + 11 eliminators;
-- LiveGenerator.isLive = 40 semanticTier kernel evaluations; liveSignature_count = 40 pin). ★
-- liveSignature_complete = THE GATE: every classifier-live generator is in the enumeration, by full 198-arm
-- cases — reserved arms refute via absurd + of_decide_eq_true rfl on ¬(semanticTier g = .live) (EAGER, unlike
-- nomatch whose postponed elaboration ESCAPES the first combinator — the new Lean trap this firing), live arms
-- evaluate the Boolean contains by rfl (the List.Mem DECIDABILITY INSTANCE leaks propext — second new trap). A generator going live without an enum ctor + coverage arms BREAKS the theorem. The
-- six-way SconingCoverageRole taxonomy (the uniform "SN-closure for every live generator" is FALSE — untyped
-- Ω — hence per-role coverage): ★ neutralFormerCellHasGluedLift = the NEW lifts (every non-Π former cell, for
-- EVERY payload/children, admits a glued-model SN-scone lift — the ONORM-M1 modalityLift recipe across all 13
-- live formers; the glued model is closed over the ENTIRE live former signature);
-- dependentFormerIsPi + piTyCode_hasConditionalGluedLift = the honest Π asymmetry (lift conditional on
-- modeled-codomain data); constructorFamily + constructorFamilyHasTaitCandidate = each value constructor
-- pinned to ITS DataFormerFamily candidate (indexed, no cross-family discharge);
-- neutralLeafMemberOfEveryCandidate = the variable in every canonical-forms candidate;
-- abstractionConstructorPreservesSn = λ SN-closure (full membership = the shipped abstraction FT arm);
-- eliminatorHasRedexHead = the operational half (semantic half = the SN-058..069 arc, per regime). HONEST:
-- the modal fragment is correctly ABSENT (statically untyped + β/ι-inert; ONORM-M1 covers it semantically,
-- joining this gate when a modal rule-table row lands). All zero-axiom.
#assert_no_axioms FX1Poly.Typed.LiveGenerator
#assert_no_axioms FX1Poly.Typed.LiveGenerator.generator
#assert_no_axioms FX1Poly.Typed.LiveGenerator.isLive
#assert_no_axioms FX1Poly.Typed.LiveGenerator.all
#assert_no_axioms FX1Poly.Typed.liveSignatureList
#assert_no_axioms FX1Poly.Typed.liveSignature_count
#assert_no_axioms FX1Poly.Typed.liveSignature_complete
#assert_no_axioms FX1Poly.Typed.SconingCoverageRole
#assert_no_axioms FX1Poly.Typed.LiveGenerator.sconingRole
#assert_no_axioms FX1Poly.Typed.LiveGenerator.neutralFormerCellHasGluedLift
#assert_no_axioms FX1Poly.Typed.LiveGenerator.dependentFormerIsPi
#assert_no_axioms FX1Poly.Typed.piTyCode_hasConditionalGluedLift
#assert_no_axioms FX1Poly.Typed.LiveGenerator.constructorFamily
#assert_no_axioms FX1Poly.Typed.LiveGenerator.constructorFamilyHasTaitCandidate
#assert_no_axioms FX1Poly.Typed.LiveGenerator.neutralLeafMemberOfEveryCandidate
#assert_no_axioms FX1Poly.Typed.LiveGenerator.abstractionConstructorPreservesSn
#assert_no_axioms FX1Poly.Typed.LiveGenerator.eliminatorHasRedexHead

-- SN-079: the coverage carrier is EXACTLY the M30 semantically-admissible set — soundness
-- (every LiveGenerator member is SemanticallyAdmissible, 40 kernel evaluations) + completeness
-- (every semantically admissible generator is in the live signature, the M30 tier bridge
-- composed with liveSignature_complete). Reducibility only for — and for all of — the
-- semantically-admissible generators.
#assert_no_axioms FX1Poly.Typed.LiveGenerator.memberIsSemanticallyAdmissible
#assert_no_axioms FX1Poly.Typed.liveSignatureMember_of_semanticallyAdmissible

-- ★ The FX type-axis AxisObligation — all eight capabilities flipped, each flip BACKED
-- (TypeAxisObligation.lean, SN-103 #606). fxTypeAxisObligation = the FIRST concrete AxisObligation with
-- non-bottom capabilities: axis id .universe, no Fire-Triangle restriction (the pure type axis; the
-- effect/eval restriction is SN-104's separate axis), capabilities = MetatheoreticCapabilities.top (pinned
-- rfl), precedents = Tait 1967 / Girard 1972 / Atkey 2018 / Wood-Atkey 2022 / Uemura 1904.04097 / BKS
-- 2302.05190. THE HONESTY CONSTRAINT (not a bare flip): eight fxTypeAxis_*_isBacked theorems, each conjoining
-- the ledger field's .available value (rfl) with the SHIPPED metatheorem restated and proved by direct
-- application — canonicity ← closedBoolCanonicalForms; normalization ← HasTypeDescPi.normalizationTransfer;
-- parametricity ← closedBoundedReducibleMember (BFT-13); subject reduction ← HasTypeDescPi.subjectReduction
-- (SR-U4); confluence ← StepStar.rawConfluence; strong normalization ← stronglyNormalizingOfWfContextDesc
-- (OB-5); decidable conversion ← Conv.decidableOfHasTypeDesc; decidable typechecking ←
-- HasTypeDesc.decidableOfWellFormed (both decidability legs through Nonempty since deciders are data).
-- fxTypeAxis_meetPreservesCapabilities = the SN-108 hook: meeting ANY ledger against the type axis is the
-- identity (the discharged base never degrades an extension) — via the new
-- CapabilityStatus.meet_available_right. HONEST: decidability backed on the proven fragments (classifier-Conv
-- of typed subjects; checking over wf contexts); SR over WfContextDescPi, SN/normalization over WfContextDesc
-- — the wf hypotheses quoted exactly as shipped. (The positional-implicit lambda trap recurred: a lambda
-- against ∀ {profile} (env) {subject classifier} (typing) binds {subject} as the typing arg — bind ALL
-- implicits explicitly.) All zero-axiom.
#assert_no_axioms FX1Poly.Typed.fxTypeAxisCapabilities
#assert_no_axioms FX1Poly.Typed.fxTypeAxisCapabilities_eq_top
#assert_no_axioms FX1Poly.Typed.fxTypeAxisObligation
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_canonicity_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_normalization_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_parametricity_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_subjectReduction_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_confluence_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_strongNormalization_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_decidableConversion_isBacked
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_decidableTypechecking_isBacked
#assert_no_axioms FX1Poly.Typed.CapabilityStatus.meet_available_right
#assert_no_axioms FX1Poly.Typed.fxTypeAxis_meetPreservesCapabilities

-- The usage (linearity) AxisObligation: the first honestly PARTIAL ledger + a fully-DISCHARGED sconing
-- witness (UsageAxisObligation.lean, SN-105 #608). usageAxisCapabilities = 5 available / 3 unavailable —
-- the first PROPER capability instance (usageAxisCapabilities_isProper: ≠ top ∧ ≠ bot), witnessing the
-- ledger DISCRIMINATES. Backed flips over the graded λ-calculus (GradedLambda / HasGradeOver
-- fxUsageSemiring): SN ← HasGradeOver.stronglyNormalizing (the DIM2-5 erasure transfer, ANY context);
-- canonicity ← closedReducesToLam (closed well-graded ⟹ reaches a λ-value); normalization ← the graded
-- normalizer + its soundness laws over the transferred SN; SR ← hasGradeOver_reducesStarPreservation
-- (grades INCLUDED, star); confluence ← graded Newman over graded SN. Honest absences (rfl pins, each with
-- a recorded route): parametricity (no usage-indexed relational interpretation; DIM-FUNCTORIAL is a
-- different statement), decidable conversion (normalize-and-compare derivable, not shipped), decidable
-- typechecking (no grade-inference procedure). fxUsageAxisObligation: axis .multiModal, Fire-Triangle
-- restriction some .substitution (linearity restricts substitution — no contraction/weakening), precedents
-- Girard/McBride/Atkey/Wood-Atkey. ★ usageSconingWitness = the GradedSconingWitness with the fundamental
-- DISCHARGED (erasure SN + closedReducesToLam — both theorems, not hypotheses; stronger than the RawTerm
-- data scones); usageSconingWitness_canonicity = the BKS composition; usageGradeArithmetic_oneAddOne (1+1=ω)
-- + _oneMulOne (1*1=1) pin the §6.1 arithmetic the fundamental respects. usageAxis_meetWithTypeAxis = the
-- SN-108 composition breadcrumb. (Lambda-binder rule confirmed: once ANY brace-binder appears, list EVERY
-- binder in order; nomatch swallows a following comma in anonymous constructors — parenthesize.) All
-- zero-axiom.
#assert_no_axioms FX1Poly.Typed.usageAxisCapabilities
#assert_no_axioms FX1Poly.Typed.usageAxisCapabilities_isProper
#assert_no_axioms FX1Poly.Typed.fxUsageAxisObligation
#assert_no_axioms FX1Poly.Typed.usageGradeArithmetic_oneAddOne
#assert_no_axioms FX1Poly.Typed.usageGradeArithmetic_oneMulOne
#assert_no_axioms FX1Poly.Typed.usageAxis_strongNormalization_isBacked
#assert_no_axioms FX1Poly.Typed.usageAxis_canonicity_isBacked
#assert_no_axioms FX1Poly.Typed.usageAxis_normalization_isBacked
#assert_no_axioms FX1Poly.Typed.usageAxis_subjectReduction_isBacked
#assert_no_axioms FX1Poly.Typed.usageAxis_confluence_isBacked
#assert_no_axioms FX1Poly.Typed.usageAxis_parametricity_isHonestlyAbsent
#assert_no_axioms FX1Poly.Typed.usageAxis_decidableConversion_isHonestlyAbsent
#assert_no_axioms FX1Poly.Typed.usageAxis_decidableTypechecking_isHonestlyAbsent
#assert_no_axioms FX1Poly.Typed.GradedSconingWitness
#assert_no_axioms FX1Poly.Typed.isClosedUsageGraded
#assert_no_axioms FX1Poly.Typed.usageSconingWitness
#assert_no_axioms FX1Poly.Typed.usageSconingWitness_canonicity
#assert_no_axioms FX1Poly.Typed.usageAxis_meetWithTypeAxis

-- The security + effect AxisObligations — the graded twin and the honest BOTTOM
-- (EffectSecurityAxisObligations.lean, SN-106 #609; completes the capability-lattice SPAN: type=top,
-- usage=security=proper, effect=bot). SECURITY: securityAxisCapabilities_eq_usageAxisCapabilities (rfl) = the
-- DIM5 orthogonal-composition thesis at the LEDGER level (both ride the ONE generic HasGradeOver engine →
-- identical 5/3 profiles); five backed flips instantiated at fxSecuritySemiring (SN/canonicity/normalization/
-- SR/confluence — same generic theorems); Fire-Triangle restriction some .dependentElimination (branching on a
-- classified scrutinee IS the implicit-flow channel, §12.2); ★
-- securityAxis_parametricityIsAbsent_withFlowHalf = the honest-absence-WITH-partial-content form (the field
-- stays .unavailable — relational noninterference is the route — conjoined with the SHIPPED grade-flow half:
-- securityClassifiedFunctionPoisonsApplication); securitySconingWitness = the discharged witness at the
-- security instance; securityGradeArithmetic_noImplicitDowngrade pins unclassified+classified=classified.
-- EFFECT: effectAxisCapabilities = bot with the REASON a theorem — effectAxis_cannotRideGradedEngine
-- (effectIsNotLawfulOrderedGradeSemiring: the effect join has no annihilator, the semiring engine provably
-- does not instantiate; a lattice-graded judgment is the route); what IS mechanized = the lawful bounded
-- join-semilattice (effectAxis_algebraIsLawfulLattice) + the admissible .effects Fire-Triangle restriction
-- (SN-104 ∂CBPV); effectAxis_meetForcesBot = the negative SN-108 example (composing with the undischarged
-- effect axis zeroes the joint ledger). Precedents Goguen-Meseguer/Volpano/Abadi/Sabelfeld-Myers +
-- Moggi/Plotkin-Power/Levy/Pedrot-Tabareau. All zero-axiom.
#assert_no_axioms FX1Poly.Typed.securityAxisCapabilities
#assert_no_axioms FX1Poly.Typed.securityAxisCapabilities_eq_usageAxisCapabilities
#assert_no_axioms FX1Poly.Typed.fxSecurityAxisObligation
#assert_no_axioms FX1Poly.Typed.securityGradeArithmetic_noImplicitDowngrade
#assert_no_axioms FX1Poly.Typed.securityAxis_strongNormalization_isBacked
#assert_no_axioms FX1Poly.Typed.securityAxis_canonicity_isBacked
#assert_no_axioms FX1Poly.Typed.securityAxis_normalization_isBacked
#assert_no_axioms FX1Poly.Typed.securityAxis_subjectReduction_isBacked
#assert_no_axioms FX1Poly.Typed.securityAxis_confluence_isBacked
#assert_no_axioms FX1Poly.Typed.securityAxis_parametricityIsAbsent_withFlowHalf
#assert_no_axioms FX1Poly.Typed.securityAxis_decidableConversion_isHonestlyAbsent
#assert_no_axioms FX1Poly.Typed.securityAxis_decidableTypechecking_isHonestlyAbsent
#assert_no_axioms FX1Poly.Typed.isClosedSecurityGraded
#assert_no_axioms FX1Poly.Typed.securitySconingWitness
#assert_no_axioms FX1Poly.Typed.effectAxisCapabilities
#assert_no_axioms FX1Poly.Typed.effectAxisCapabilities_eq_bot
#assert_no_axioms FX1Poly.Typed.fxEffectAxisObligation
#assert_no_axioms FX1Poly.Typed.effectAxis_cannotRideGradedEngine
#assert_no_axioms FX1Poly.Typed.effectAxis_algebraIsLawfulLattice
#assert_no_axioms FX1Poly.Typed.effectAxis_fireTriangleAdmissible
#assert_no_axioms FX1Poly.Typed.effectAxis_meetForcesBot

-- The remaining-dimensions AxisObligation batch (RemainingDimensionAxisObligations.lean, SN-107 #610) — the
-- per-dimension gallery COMPLETE in three honesty tiers. ★ gradedAxis_fiveCapabilitiesBacked = the GENERIC
-- five-capability bundle over ANY lawful ordered grade semiring (SN + closed canonicity + normalization + SR +
-- confluence in ONE conjunction — the common generalization the usage/security modules instantiated piecewise;
-- every future semiring dimension discharges by one application). COMPLEXITY = the third graded sibling:
-- complexityAxisCapabilities_eq_usageAxisCapabilities (rfl) extends the orthogonal-composition thesis to a
-- THREE-dimension family; complexityAxis_fiveCapabilitiesBacked = ledger fields + the bundle at
-- fxComplexitySemiring in one theorem. ALGEBRA TIER (bot + cited algebra): trust (cannotRideGradedEngine +
-- lawful weakest-link lattice — the effect-shaped pair), clock + provenance (lawful lattices), lifetime
-- (lifetimeAxis_algebraIsProperPreorder = provably NOT antisymmetric — cannot even be a join-semilattice, the
-- honest structural reason its entry differs). PENDING TIER (bot, NO algebra, non-zero estimatedLinesOfCode —
-- the field's first honest use): refinement (SMT-obligation model, ~4000), representation (layout preorder,
-- ~1500), observability (opaque/transparent two-point lattice — the security recipe, ~1000).
-- remainingDimensionObligations = the 8-record batch + count pin. Composition: complexity meets losslessly;
-- every bot entry forces bot (meet_bot_right) until its judgment ships — the SN-108 inputs. All zero-axiom.
#assert_no_axioms FX1Poly.Typed.gradedAxis_fiveCapabilitiesBacked
#assert_no_axioms FX1Poly.Typed.complexityAxisCapabilities
#assert_no_axioms FX1Poly.Typed.complexityAxisCapabilities_eq_usageAxisCapabilities
#assert_no_axioms FX1Poly.Typed.fxComplexityAxisObligation
#assert_no_axioms FX1Poly.Typed.complexityAxis_fiveCapabilitiesBacked
#assert_no_axioms FX1Poly.Typed.fxTrustAxisObligation
#assert_no_axioms FX1Poly.Typed.trustAxis_cannotRideGradedEngine
#assert_no_axioms FX1Poly.Typed.trustAxis_algebraIsLawfulLattice
#assert_no_axioms FX1Poly.Typed.fxClockAxisObligation
#assert_no_axioms FX1Poly.Typed.clockAxis_algebraIsLawfulLattice
#assert_no_axioms FX1Poly.Typed.fxProvenanceAxisObligation
#assert_no_axioms FX1Poly.Typed.provenanceAxis_algebraIsLawfulLattice
#assert_no_axioms FX1Poly.Typed.fxLifetimeAxisObligation
#assert_no_axioms FX1Poly.Typed.lifetimeAxis_algebraIsProperPreorder
#assert_no_axioms FX1Poly.Typed.fxRefinementAxisObligation
#assert_no_axioms FX1Poly.Typed.fxRepresentationAxisObligation
#assert_no_axioms FX1Poly.Typed.fxObservabilityAxisObligation
#assert_no_axioms FX1Poly.Typed.remainingDimensionObligations
#assert_no_axioms FX1Poly.Typed.remainingDimensionObligations_count

-- ★ The verified COST SEMANTICS for the graded λ-calculus — complexity is honestly CALCULABLE
-- (GradedCostSemantics.lean, COST-1 #1213; the user-directed maximum honest version). The cost MODEL:
-- ReducesInSteps (one unit per β-step) + bridges to ReducesStar. The enumeration: oneStepReducts proven
-- COMPLETE (every Reduces step listed — what the upper bound consumes) AND SOUND (every listed element is a
-- step — what the recursive construction consumes), with HAND-ROLLED membership lemmas (memMapOfMem/
-- memAppendLeft/Right/memMapInv/memAppendInv — core List.mem_* axiom status unaudited, so rolled by list
-- induction with explicit List.Mem ctors). ★ costBound = the computable WORST-CASE cost via Acc.rec
-- (constant-Nat motive, the normalize recipe) over the soundness-THREADED fold costBoundOverReducts (no
-- List.attach; each recursive call justified by a genuine Reduces witness); costBound_isSound = EVERY
-- reduction sequence under ANY strategy is bounded (sum-based per the propext-free Nat.le_add discipline —
-- Nat.le_max_* leaks). ★ normalizeCost = the EXACT attained cost of the canonical normalizer path
-- (normalizeCost_isExact: a genuine chain of exactly that length; normalizeWithCost_reachesNormalize: to THE
-- normal form, by uniqueness; normalizeCost_le_costBound: the sandwich). ★ HasGradeOver.costCalculator +
-- canonicalEvaluationCost: every well-graded term over ANY dimension has a computable sound bound + exact
-- canonical cost; complexityGraded_costIsCalculable = the §6.3 Dim-13 narrative instance. HONEST: cost is
-- computed FROM THE TERM (search + instrumented evaluation), NOT read off the grades — the grade→cost tie is
-- COST-2 (#1214, cost-indexed LR, calf/Danielsson/dlPCF program); the SN-107 complexity docstring now carries
-- this qualifier. All zero-axiom, FIRST-BUILD GREEN.
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesInSteps
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesInSteps.toStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.existsStepCount
#assert_no_axioms FX1Poly.Modal.GradedLambda.memMapOfMem
#assert_no_axioms FX1Poly.Modal.GradedLambda.memAppendLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.memAppendRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.memMapInv
#assert_no_axioms FX1Poly.Modal.GradedLambda.memAppendInv
#assert_no_axioms FX1Poly.Modal.GradedLambda.oneStepReducts
#assert_no_axioms FX1Poly.Modal.GradedLambda.oneStepReducts_complete
#assert_no_axioms FX1Poly.Modal.GradedLambda.oneStepReducts_sound
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBoundOverReducts
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBoundOverReducts_boundsElement
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBound
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBound_isSound
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithCost
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeCost
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeCost_isExact
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithCost_reachesNormalize
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeCost_le_costBound
#assert_no_axioms FX1Poly.Modal.GradedLambda.identityRedex_costsOneStep
#assert_no_axioms FX1Poly.Modal.HasGradeOver.costCalculator
#assert_no_axioms FX1Poly.Modal.HasGradeOver.costCalculator_isSound
#assert_no_axioms FX1Poly.Modal.HasGradeOver.canonicalEvaluationCost
#assert_no_axioms FX1Poly.Modal.HasGradeOver.canonicalEvaluationCost_isExact
#assert_no_axioms FX1Poly.Modal.complexityGraded_costIsCalculable

-- ★ The COST-INDEXED REDUCIBILITY relation at the complexity N-semiring (GradedCostRelation.lean,
-- COST-2 #1214 brick 1 — the calf/Danielsson/dlPCF construction's opening brick). CostReducible: base =
-- bounded normalization (∃ value steps, ReducesInSteps ∧ IsNormalForm ∧ steps ≤ budget); graded arrow =
-- THE APP SCALING AS COST ACCOUNTING — applying to a j-reducible argument is reducible at
-- budget + binderGrade·j + 1 (the §6.1 coeffect law `grades(f a) = grades(f) + r·grades(a)` mirrored into
-- the budget index, plus one unit for the β-step; this is where the grade semiring and the cost model
-- interlock). The carrier gotcha: fxComplexitySemiring.Carrier ≡ Nat definitionally but NOT for TC synthesis
-- (HMul/OfNat fail) — the relation uses explicit Nat.mul and Nat-ascribed grade literals. ★ monotone =
-- budget weakening (upward closure, structural on GTypeOver). ★ headExpansion = the cost-indexed CR3
-- (one backward step costs one unit; arrow arm lifts through congAppLeft, budget shuffle via
-- Nat.add_right_comm + le_of_eq through monotone). ★ applicationBudget = the App interlock DEFINITIONALLY
-- (the arrow case IS the law). ★ Grade honesty in BOTH directions: at binder grade ONE the identity is
-- cost-reducible at budget 0 (genuine β-chain, the algebra computes); at binder grade ZERO it is NOT
-- (the 1-step identityRedex argument defeats budget 0+0·j+1 — exhaustive ≤1-step chain inversion) — the
-- budget index genuinely rejects grade UNDERCLAIMING. HONEST: the FUNDAMENTAL THEOREM (HasGradeOver ⟹
-- CostReducible at a grade-weighted budget — the §6.3 Dim-13 grade→cost tie) is the NAMED OPEN CORE; its
-- λ-arm needs the cost-indexed substitution lemma (the genuinely hard calf/dlPCF step, later bricks).
#assert_no_axioms FX1Poly.Modal.CostReducible
#assert_no_axioms FX1Poly.Modal.CostReducible.extractBoundedNormalization
#assert_no_axioms FX1Poly.Modal.CostReducible.ofNormalForm
#assert_no_axioms FX1Poly.Modal.CostReducible.monotone
#assert_no_axioms FX1Poly.Modal.CostReducible.headExpansion
#assert_no_axioms FX1Poly.Modal.CostReducible.applicationBudget
#assert_no_axioms FX1Poly.Modal.identityLambda_costReducible_atLinearGrade
#assert_no_axioms FX1Poly.Modal.identityLambda_notCostReducible_atZeroGrade

-- ★★ The COST-2 FUNDAMENTAL THEOREM (GradedCostFundamental.lean, #1214 brick 2 — the §6.3 Dim-13
-- grade→cost tie PROVED). HasGradeOver.costFundamental: every complexity-graded term, closed by a
-- cost-reducible substitution, is CostReducible at the GRADE-WEIGHTED budget
-- `weightedBudget grades budgetAssignment + intrinsicWeight` — the §6.2 grade vector contracted against
-- the per-variable environment budgets (a variable consumed at grade r contributes r·its budget) plus a
-- term-intrinsic weight. The quantifier order is the λ-arm's crux: ∃ weight BEFORE ∀ substitution (the
-- lambda commits to ONE body weight for every future argument — possible exactly because the IH's weight
-- is environment-independent). λ-arm = the cost-indexed substitution step: β-reduct rewritten into the
-- extended environment via the σ-algebra composition substAt_zero_applySubstitution_lift, head-expanded
-- at +1, budget shuffle by Nat AC; app arm distributes r·(Wₐ+wₐ) via Nat.left_distrib + the hand-rolled
-- natAddMiddleExchange. ★ weightedBudget + the LINEARITY laws mirroring the §6.2 vector ops the three
-- typing rules use (zero/single-of-lookup/add/scale — add needs the equal-length §6.2 invariant; scale
-- uses the hand-rolled natMulAssoc + clean Nat.left_distrib). ★ CostReducibleSubstitution + cons (the
-- cost-indexed closing environment). ★ Closed corollaries: closedCostReducible (every closed well-graded
-- term cost-reducible) + closedBaseNormalizesWithinBudget (base type ⟹ reaches NF within budget).
-- ★ Smokes on the brick-1 frontier: the linear identity lands via the FT at its grade-ONE arrow; the K
-- combinator lands at a type with a grade-ZERO inner arrow — the zero-grade arrow IS inhabited by honest
-- discarders, contrasting identityLambda_notCostReducible_atZeroGrade (underclaim by a USER rejected).
-- HONEST: budgets are ∃-strategy (optimal discard-early path); the intrinsic weight is existential
-- (HasGradeOver is Prop — no weight computable from it); the grade scaling is the structural content.
#assert_no_axioms FX1Poly.Modal.natAddMiddleExchange
#assert_no_axioms FX1Poly.Modal.weightedBudget
#assert_no_axioms FX1Poly.Modal.weightedBudget_zero
#assert_no_axioms FX1Poly.Modal.weightedBudget_single_of_lookup
#assert_no_axioms FX1Poly.Modal.weightedBudget_add
#assert_no_axioms FX1Poly.Modal.weightedBudget_scale
#assert_no_axioms FX1Poly.Modal.consBudgetAssignment
#assert_no_axioms FX1Poly.Modal.CostReducibleSubstitution
#assert_no_axioms FX1Poly.Modal.CostReducibleSubstitution.cons
#assert_no_axioms FX1Poly.Modal.HasGradeOver.costFundamental
#assert_no_axioms FX1Poly.Modal.HasGradeOver.closedCostReducible
#assert_no_axioms FX1Poly.Modal.HasGradeOver.closedBaseNormalizesWithinBudget
#assert_no_axioms FX1Poly.Modal.linearIdentityCostReducibleViaFundamental
#assert_no_axioms FX1Poly.Modal.kCombinatorCostReducibleViaFundamental

-- ★ Term SIZE + exact occurrence counting + the substitution-size equation (GradedTermSize.lean,
-- COST-2a #1215 brick 1 — the quantitative substrate for the linear-time theorem). GradedLambda.size
-- (node count) + countOccurrencesAt (EXACT Nat-valued — the ω-collapsed usage vector cannot drive size
-- arithmetic) + size_shift (renaming preserves size). ★ size_substAt, the ADDITIVE substitution-size
-- equation: size(t[i := r]) + count i t = size t + count i t · size r — each occurrence trades one var
-- node for a replacement copy; the additive form dodges Nat truncated subtraction entirely. ★ THE β-SIZE
-- LEMMA size_substAt_lt_redex: count 0 body ≤ 1 ⟹ the β-reduct is STRICTLY smaller than the redex (the
-- single-step engine of "linear terms normalize in < size steps under any strategy"). ★ The duplication
-- seed: count 0 (x x) = 2 + its ¬≤1 pin — the witness germ for brick 2's counterexamples. DESIGN FINDING
-- (recorded in #1215 metadata): the task's AFFINE premise is FALSE — binder grade 0 does NOT bound
-- occurrences (0-SCALING LEAKS: λx.(f x) x types at binder grade 0 with x occurring twice over
-- f : A -0-> A -0-> B, and its β DUPLICATES) — the any-strategy theorem holds on the STRICT-linear
-- fragment (all binder grades = 1), brick 2's target; affine gets only ∃-strategy bounds (COST-2).
-- Proof recipe: rw [if_pos/if_neg] consumes ONE instantiated pattern per element — an arm with both a
-- subst-if and count-ifs over the same condition needs the rewrite TWICE; 0 * symbolic is STUCK
-- (Nat.mul recurses on arg 2) — close with Nat.zero_mul, never rfl.
#assert_no_axioms FX1Poly.Modal.GradedLambda.size
#assert_no_axioms FX1Poly.Modal.GradedLambda.countOccurrencesAt
#assert_no_axioms FX1Poly.Modal.GradedLambda.size_pos
#assert_no_axioms FX1Poly.Modal.GradedLambda.size_shift
#assert_no_axioms FX1Poly.Modal.GradedLambda.size_substAt
#assert_no_axioms FX1Poly.Modal.GradedLambda.size_substAt_of_absent
#assert_no_axioms FX1Poly.Modal.GradedLambda.size_substAt_of_linear
#assert_no_axioms FX1Poly.Modal.GradedLambda.size_substAt_lt_redex
#assert_no_axioms FX1Poly.Modal.GradedLambda.countOccurrencesAt_duplicator
#assert_no_axioms FX1Poly.Modal.GradedLambda.duplicatorRedex_count_exceeds_linear

-- ★ The STRICT-LINEAR fragment + the grade→occurrence bound (GradedLinearTime.lean, COST-2a #1215
-- brick 2). HasStrictLinearGrade: HasGradeOver at the usage semiring with EVERY binder grade pinned to
-- one (forgetful toGraded) — the fragment where grades genuinely bound syntactic occurrence counts.
-- ★ countBound: lookupGrade grades i `boundsCount` count i t (zero ⟹ absent, one ⟹ at most once,
-- omega ⟹ unconstrained); the app arm is sound precisely because strict scaling is the identity
-- (lookupGrade_scale_one) and the usage add table never compresses one+one (boundsCount_add's 9-case
-- bash). ★ lamBodyCountBound (the cons-one head read at the binder) → betaShrinks: every strict-linear
-- β-redex STRICTLY decreases size via brick 1's β-size lemma — the single-step engine of steps < size
-- (brick 3). Pointwise lookupGrade + single/add/scale laws (add specialized to the usage semiring whose
-- closed table makes the out-of-range default consistent). ★ THE AFFINE COUNTERWITNESS, COMMITTED:
-- affineDuplicatorLam_typedAtGradeZero — λx.(f x) x types at binder grade ZERO under the FULL graded
-- judgment over f : base -0→ base -0→ base (both applications 0-scale x's grades away while the syntax
-- keeps two occurrences; the whole derivation is built from explicit ctors, vector arithmetic closing
-- by whnf defeq); affineDuplicatorBody_countsTwice (rfl); affineGradeZero_doesNotBoundCount — grade 0
-- does NOT bound occurrences, so the linear-time theorem genuinely needs strictness (the task's affine
-- premise REFUTED as committed theorems, not just metadata).
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_single_other
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_add_usage
#assert_no_axioms FX1Poly.Modal.UsageGrade.one_mul_eq
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_scale_one
#assert_no_axioms FX1Poly.Modal.UsageGrade.boundsCount
#assert_no_axioms FX1Poly.Modal.UsageGrade.boundsCount_add
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.toGraded
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.countBound
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.lamBodyCountBound
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.betaShrinks
#assert_no_axioms FX1Poly.Modal.linearIdentity_strictlyLinear
#assert_no_axioms FX1Poly.Modal.identityApplication_strictlyShrinks
#assert_no_axioms FX1Poly.Modal.affineDuplicatorBody
#assert_no_axioms FX1Poly.Modal.zeroScalingFunctionType
#assert_no_axioms FX1Poly.Modal.affineDuplicatorLam_typedAtGradeZero
#assert_no_axioms FX1Poly.Modal.affineDuplicatorBody_countsTwice
#assert_no_axioms FX1Poly.Modal.affineGradeZero_doesNotBoundCount

-- ★★ COST-2a CLOSED (GradedLinearTimeBound.lean, #1215 brick 3): LINEAR TERMS EVALUATE IN LINEAR TIME,
-- UNDER ANY STRATEGY. HasStrictLinearGrade.linearTime: every ReducesInSteps chain from a strict-linear
-- term — any strategy, any target — is strictly shorter than the term's SIZE (steps < size). Pipeline:
-- strict weakening + substitution (mechanical mirrors of the generic #903/#905 graded metatheory with
-- the binder grade pinned to one; the judgment-free substInto/insertAt vector algebra reused VERBATIM)
-- → betaPreservation (grades preserved EXACTLY: substInto 0 at cons-one is definitionally the strict App
-- grade) → subjectReduction (one-step SR, congruences rebuild) → stepDecreasesSize (β via brick 2's
-- betaShrinks; congruences via inversion + Nat.succ_lt_succ/add_lt_add) → linearTime (chain induction:
-- succ_lt_succ of the tail bound under SR, lt_of_lt_of_le with the head decrease). Smoke: the identity
-- application normalizes in 1 < 5 steps end-to-end through the chain. ★ The β-NON-SHRINK witnesses:
-- duplicatorRedex_betaDoesNotShrink — the SAME syntactic duplicator redex (λx.(f x) x)((λz.z) y) has
-- β-reduct size EQUAL to the redex (11 = 11, Nat.lt_irrefl on the rfl-computed sizes), and it is graded
-- BOTH at binder grade ZERO (brick 2's affine leak) and at OMEGA (omegaDuplicatorLam_typedAtGradeOmega,
-- the same 6-ctor derivation over ω-arrows) — strict decrease fails outside the strict fragment in both
-- gradings, so strictness is exactly the right hypothesis. CASES RECIPE: cases on the strict judgment
-- at a VARIABLE grade/result index CONSUMES the ctor binders that unify with them (outerGrades↦grades,
-- codomain↦resultType) — reference the surviving outer variables, not the ctor's binder names.
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.invertLam
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.invertApp
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.weakening
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.substitution
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.betaPreservation
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.subjectReduction
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.stepDecreasesSize
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.linearTime
#assert_no_axioms FX1Poly.Modal.identityApplication_linearTime
#assert_no_axioms FX1Poly.Modal.duplicatedArgument
#assert_no_axioms FX1Poly.Modal.duplicatorRedex_betaDoesNotShrink
#assert_no_axioms FX1Poly.Modal.omegaFunctionType
#assert_no_axioms FX1Poly.Modal.omegaDuplicatorLam_typedAtGradeOmega

-- ★ The cost-instrumented KERNEL normalizer (Core/NormalizeCost.lean, COST-3 #1216 brick 1 — the COST-1
-- recipe at the 198-generator RawTerm substrate). Step (1) of the COST-3 plan was ALREADY SHIPPED:
-- StepStarN (#368) IS the kernel's step-counted reduction (reflN/transN + both StepStar bridges +
-- trans_compose + rename/subst length-preservation) — no new relation. THIS brick = step (2):
-- RawTerm.normalizeWithCost threads a counter through the shipped Acc.rec normalizer (constant pair
-- motive, rfl unfold handle). ★ normalizeWithCost_isExactChain — the reported cost is attained by a
-- GENUINE StepStarN chain to the reported output (not an estimate). ★ fst identified with
-- RawTerm.normalize via normalForm_unique on the SN fragment — NOT by aligning the two Acc.rec matches
-- (fst's reachability is FREE from the exactness chain via toStepStar; fst's normality by the mirror
-- induction; uniqueness closes). ★ normalizeCost_isExact — every SN kernel term has an EXACT computable
-- evaluation cost reaching THE normal form. Non-vacuity: reduceOnce halts on the closed unit value by
-- KERNEL COMPUTATION (rfl over the 198-generator table), the hand-built Acc.intro witness via
-- isStepNormalForm_blocks_step, and normalizeCost unit = 0 by rfl THROUGH the Acc witness. The typed
-- packaging (HasTypeDescPi ⟹ calculable cost, the FX headline) + costBound (worst-case over
-- oneStepReducts) are the later COST-3 bricks; IsStronglyNormalizing IS Acc StepSuccessor
-- definitionally, so the shipped typed-SN theorems feed this module directly.
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_isExactChain
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_reducesToFst
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_fst_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_fst_eq_normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_isExact
#assert_no_axioms FX1Poly.Core.unitNormalFormFixture
#assert_no_axioms FX1Poly.Core.unitNormalFormFixture_reduceOnce_halts
#assert_no_axioms FX1Poly.Core.unitNormalFormFixture_accessible
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_unit_isZero

-- ★ The kernel ONE-STEP REDUCT ENUMERATION with SOUNDNESS (Core/OneStepReducts.lean, COST-3 #1216
-- brick 2 — the heavy lift's first half). RawTerm.oneStepReducts / RawTermChildren.oneStepChildrenReducts:
-- mutual structural enumeration over the 198-generator table — the root β/ι reduct via fireRootRedex
-- (Option match) ++ every one-child-stepped reassembly (per-position maps over the dependent children
-- spine; the childCons reassemblies keep the binderShifts indices). ★ SOUNDNESS (mutual): every listed
-- element is a genuine Step — root via fireRootRedex_sound, congruence via Step.cong over the mutual
-- StepChildren soundness (here/there per position). Generic hand-rolled membership INVERSION lemmas
-- (listMemAppendInv/listMemMapInv — explicit List.Mem ctors, core mem lemmas unaudited; now GENERIC
-- {α β : Type} unlike COST-1's GradedLambda-specialized ones). split-at on the equation-binderless
-- Option match names the some-arm discharge via `next rootReduct fireEq`. Non-vacuity: the identity-β
-- fixture's enumeration COMPUTES to exactly the singleton β-reduct by kernel evaluation (rfl through
-- fireRootRedex's dite chain — gen_app is the first branch — with all children normal).
-- COMPLETENESS (every Step listed — what costBound's soundness consumes) is brick 3: the congruence
-- half mirrors with FORWARD membership lemmas; the root half needs per-ι fireRootRedex firing equations.
#assert_no_axioms FX1Poly.Core.listMemAppendInv
#assert_no_axioms FX1Poly.Core.listMemMapInv
#assert_no_axioms FX1Poly.Core.RawTerm.oneStepReducts
#assert_no_axioms FX1Poly.Core.RawTermChildren.oneStepChildrenReducts
#assert_no_axioms FX1Poly.Core.RawTerm.oneStepReducts_sound
#assert_no_axioms FX1Poly.Core.RawTermChildren.oneStepChildrenReducts_sound
#assert_no_axioms FX1Poly.Core.identityBetaFixture
#assert_no_axioms FX1Poly.Core.identityBetaFixture_oneStepReducts

/-! ## M24-Z2 (#433) — the four 2LTT universe-mode generators (Z-arc brick 1)

`gen_universeU`/`gen_universeS`/`gen_universeD`/`gen_universeOmega` land as table rows:
LevelExpr x UniverseFlag payload, arity 0, empty child specs, sort .type, tags 198-201,
SupportedGenerator admission, count pin 198 -> 202. The cascade-death architecture absorbed
the addition everywhere except the explicit count sites (count pin + finite polygraph) —
zero new metatheory arms. Smokes: certifier acceptance at sort .type per mode; no-step
normal leaves hence SN; reserved semanticTier pins (no typing/reduction rules yet — the
mode-aware formation rows and per-mode reduction disciplines are LATER Z-arc work);
tag round-trip pins; the honest payload-admission scope (every payload admitted under
fxProfile per the unbounded-universes commitment — the reject-half is the HON-11 /
restricted-profile track). -/
#assert_no_axioms FX1Poly.Core.generatorCount
#assert_no_axioms FX1Poly.Core.generatorCount_lastIndex
#assert_no_axioms FX1Poly.Core.generatorCount_upperBound
#assert_no_axioms FX1Poly.Core.Generator.toNat_lt
#assert_no_axioms FX1Poly.Core.Generator.fromTag_total_on_range
#assert_no_axioms FX1Poly.Core.fxKernelPolygraph
#assert_no_axioms FX1Poly.Typed.universeURaw
#assert_no_axioms FX1Poly.Typed.universeSRaw
#assert_no_axioms FX1Poly.Typed.universeDRaw
#assert_no_axioms FX1Poly.Typed.universeOmegaRaw
#assert_no_axioms FX1Poly.Typed.coverage_universeURaw_sort
#assert_no_axioms FX1Poly.Typed.coverage_universeSRaw_sort
#assert_no_axioms FX1Poly.Typed.coverage_universeDRaw_sort
#assert_no_axioms FX1Poly.Typed.coverage_universeOmegaRaw_sort
#assert_no_axioms FX1Poly.Typed.noStep_universeU
#assert_no_axioms FX1Poly.Typed.noStep_universeS
#assert_no_axioms FX1Poly.Typed.noStep_universeD
#assert_no_axioms FX1Poly.Typed.noStep_universeOmega
#assert_no_axioms FX1Poly.Typed.universeU_isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.universeS_isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.universeD_isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.universeOmega_isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.semanticTier_universeU
#assert_no_axioms FX1Poly.Typed.semanticTier_universeS
#assert_no_axioms FX1Poly.Typed.semanticTier_universeD
#assert_no_axioms FX1Poly.Typed.semanticTier_universeOmega
#assert_no_axioms FX1Poly.Typed.fromTag_universeU
#assert_no_axioms FX1Poly.Typed.fromTag_universeS
#assert_no_axioms FX1Poly.Typed.fromTag_universeD
#assert_no_axioms FX1Poly.Typed.fromTag_universeOmega
#assert_no_axioms FX1Poly.Typed.universeU_payloadAlwaysAdmitted

/-! ## M26-Z1 (#434) — gen_sprop + the mode-bridge reconciliation (Z-arc brick 2)

`gen_sprop` (the definitional-proof-irrelevance universe) lands as a table row: Unit payload,
arity 0, sort .type, tag 202, admission, count pin 202 -> 203. The SProp DISCIPLINE
(subsingleton-target elimination + trivial univalence collapse) is a typing-row obligation
(SN-076 track), not a table property. The M26 LiftDirection-payload bridge design is
SUPERSEDED by the shipped name-encoded pair gen_liftInnerToOuter / gen_lowerOuterToInner
(SN-077 reducibility already proven) — table shapes pinned, direction no-confusion free from
Generator.noConfusion; the directed lift (universeU<->universeD) is the honest unshipped gap. -/
#assert_no_axioms FX1Poly.Typed.spropRaw
#assert_no_axioms FX1Poly.Typed.coverage_spropRaw_sort
#assert_no_axioms FX1Poly.Typed.noStep_sprop
#assert_no_axioms FX1Poly.Typed.sprop_isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.semanticTier_sprop
#assert_no_axioms FX1Poly.Typed.fromTag_sprop
#assert_no_axioms FX1Poly.Typed.liftInnerToOuter_arity
#assert_no_axioms FX1Poly.Typed.liftInnerToOuter_shifts
#assert_no_axioms FX1Poly.Typed.lowerOuterToInner_arity
#assert_no_axioms FX1Poly.Typed.lowerOuterToInner_shifts
#assert_no_axioms FX1Poly.Typed.liftBridges_directionsDistinct
