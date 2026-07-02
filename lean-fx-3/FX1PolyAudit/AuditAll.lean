import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.AuditCore
import FX1PolyAudit.AuditCoreSubstrate
import FX1PolyAudit.Exact.IntMatrix
import FX1PolyAudit.TypeAxisLedger
import FX1PolyAudit.Tier0.Context.AxisObligation
import FX1PolyAudit.Tier0.Context.BeckChevalleyCoherence
import FX1PolyAudit.Tier0.Context.Biequivalence
import FX1PolyAudit.Tier0.Context.ComprehensionCategory
import FX1PolyAudit.Tier0.Context.ComprehensionLaws
import FX1PolyAudit.Tier0.Context.ComprehensionSigma
import FX1PolyAudit.Tier0.Context.Context
import FX1PolyAudit.Tier0.Context.ContextBiInitiality
import FX1PolyAudit.Tier0.Context.ContextCovariantFibration
import FX1PolyAudit.Tier0.Context.ContextDefinitionalUnivalence
import FX1PolyAudit.Tier0.Context.ContextDirectedUnivalence
import FX1PolyAudit.Tier0.Context.ContextDirectedUniverse
import FX1PolyAudit.Tier0.Context.ContextFunctorialGrothendieck
import FX1PolyAudit.Tier0.Context.ContextMarkedComplicial
import FX1PolyAudit.Tier0.Context.ContextOfContextsClassifier
import FX1PolyAudit.Tier0.Context.ContextPolygraphPresentation
import FX1PolyAudit.Tier0.Context.ContextSscCwFPresentation
import FX1PolyAudit.Tier0.Context.ContextStructureIdentity
import FX1PolyAudit.Tier0.Context.ContextSyntheticInfinityCategory
import FX1PolyAudit.Tier0.Context.ContextUnivalentUniverse
import FX1PolyAudit.Tier0.Context.CubicalModel
import FX1PolyAudit.Tier0.Context.CwRExtension
import FX1PolyAudit.Tier0.Context.DemocracyLCC
import FX1PolyAudit.Tier0.Context.ExplicitSubstitution
import FX1PolyAudit.Tier0.Context.FibrationCategory
import FX1PolyAudit.Tier0.Context.Forcing
import FX1PolyAudit.Tier0.Context.GlobalSections
import FX1PolyAudit.Tier0.Context.GroupoidModel
import FX1PolyAudit.Tier0.Context.InftyOneCwF
import FX1PolyAudit.Tier0.Context.Initiality
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingCategory
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecCategory
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecGlobalSections
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecIsomorphism
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecPreimage
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecRMC
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecSconingPreservation
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecTabulate
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxBaseRenamingVecTryTabulate
import FX1PolyAudit.Tier0.Context.Instances.Renaming.FxRenamingCategory
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstCanonicityExtraction
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstCategory
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstColimits
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstComprehension
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstConcreteScone
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstDisplayMap
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstGlobalSections
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstScone
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstSingleton
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstTypeFormers
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstVec
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstWeakening
import FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstWitnessScone
import FX1PolyAudit.Tier0.Context.Instances.ThinScope.FxThinScopeGlobalSections
import FX1PolyAudit.Tier0.Context.Instances.ThinScope.FxThinScopeRMC
import FX1PolyAudit.Tier0.Context.InternalSconing
import FX1PolyAudit.Tier0.Context.IsomorphismCategorical
import FX1PolyAudit.Tier0.Context.ModalLock
import FX1PolyAudit.Tier0.Context.MultimodalNormalization
import FX1PolyAudit.Tier0.Context.PresheafModel
import FX1PolyAudit.Tier0.Context.PushoutContexts
import FX1PolyAudit.Tier0.Context.Realizability
import FX1PolyAudit.Tier0.Context.RenamingInclusion
import FX1PolyAudit.Tier0.Context.Sconing
import FX1PolyAudit.Tier0.Context.SimplicialModel
import FX1PolyAudit.Tier0.Context.SliceCategory
import FX1PolyAudit.Tier0.Context.StandaloneModalRMC
import FX1PolyAudit.Tier0.Context.Strictification
import FX1PolyAudit.Tier0.Context.SubstitutionFree
import FX1PolyAudit.Tier0.Context.SubstitutionTwoGroupoid
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjointStrings
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellWordProblem
import FX1PolyAudit.Tier0.Mode.Cohesion
import FX1PolyAudit.Tier0.Mode.CohesionGlobalSectionsEdge
import FX1PolyAudit.Tier0.Mode.CohesionAdjointString
import FX1PolyAudit.Tier0.Mode.CohesionFlatModality
import FX1PolyAudit.Tier0.Mode.CohesionSharpModality
import FX1PolyAudit.Tier0.Mode.CohesionShapeModality
import FX1PolyAudit.Tier0.Mode.CohesionModalityMetatheory
import FX1PolyAudit.Tier0.Mode.CombineAmalgamation
import FX1PolyAudit.Polygraph.Computad.WordProblem
import FX1PolyAudit.Tier0.Mode.CubicalModal
import FX1PolyAudit.Tier0.Mode.FibrancyMode
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.Model
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.SpineGodement
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SpineReadback
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvDecidable
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.Confluence
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFree
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeConfluence
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeDecidable
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeLocalConfluence
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeNormalize
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.OrientedReducer
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.StrongNormalization
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.TraceDecision
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.WhiskerReconstruction
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.TraceReducer
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedDecision
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcSamePartitionFresh
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.MonotoneFaithful
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCanonicalization
import FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.BlockRotation
import FX1PolyAudit.Polygraph.Computad.Signature
import FX1PolyAudit.Polygraph.Computad.AdjunctionSeed
import FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1PolyAudit.Tier0.Mode.Frontier.ModeOmegaMultiplier
import FX1PolyAudit.Tier0.Mode.Frontier.ModeOmegaWeakGray
import FX1PolyAudit.Tier0.Mode.Frontier.PresentationMultiMode
import FX1PolyAudit.Tier0.Mode.Frontier.ProvabilityGlpRc
import FX1PolyAudit.Tier0.Mode.Frontier.ProvabilityKripke
import FX1PolyAudit.Polygraph.TwoCategory.GlobularSet
import FX1PolyAudit.Tier0.Mode.GradeAlgebra.EffectLatticeClassification
import FX1PolyAudit.Tier0.Mode.GradeAlgebra.ResourceGraded
import FX1PolyAudit.Tier0.Mode.GradeAlgebra.ResourceGradedMore
import FX1PolyAudit.Tier0.Mode.Graded
import FX1PolyAudit.Tier0.Mode.GrayCategory
import FX1PolyAudit.Tier0.Mode.GuardedRecursion
import FX1PolyAudit.Tier0.Mode.Linear
import FX1PolyAudit.Tier0.Mode.ModalFracture
import FX1PolyAudit.Tier0.Mode.ModalInduction
import FX1PolyAudit.Tier0.Mode.Mode
import FX1PolyAudit.Tier0.Mode.ModeOmega
import FX1PolyAudit.Tier0.Mode.ModeRelativeMetatheory
import FX1PolyAudit.Tier0.Mode.MultiplierEndofunctor
import FX1PolyAudit.Tier0.Mode.MultiplierStructureClass
import FX1PolyAudit.Tier0.Mode.Presentation
import FX1PolyAudit.Tier0.Mode.Provability
import FX1PolyAudit.Tier0.Mode.RealCohesion
import FX1PolyAudit.Tier0.Mode.SamenessUnification
import FX1PolyAudit.Polygraph.TwoCategory.Semistrictification
import FX1PolyAudit.Tier0.Mode.Session
import FX1PolyAudit.Tier0.Mode.SessionMore
import FX1PolyAudit.Tier0.Mode.Temporal
import FX1PolyAudit.Tier0.Mode.Transpension
import FX1PolyAudit.Tier0.Mode.TwoCategoryCore
import FX1PolyAudit.Polygraph.TwoCategory.TwoMonad
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionConfluence
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionLocalConfluence
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionReducer
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionSystem
import FX1PolyAudit.Polygraph.OmegacE.Confluence
import FX1PolyAudit.Polygraph.OmegacE.EmptySystem
import FX1PolyAudit.Polygraph.OmegacE.IdempotentConfluence
import FX1PolyAudit.Polygraph.OmegacE.IdempotentReducer
import FX1PolyAudit.Polygraph.OmegacE.IdempotentSystem
import FX1PolyAudit.Polygraph.OmegacE.OmegacEFiniteType
import FX1PolyAudit.Polygraph.OmegacE.ReducerNormalizer
import FX1PolyAudit.Polygraph.OmegacE.Rewrite
import FX1PolyAudit.Polygraph.OmegacE.SortingConfluence
import FX1PolyAudit.Polygraph.OmegacE.SortingReducer
import FX1PolyAudit.Polygraph.OmegacE.SortingSystem
import FX1PolyAudit.Polygraph.OmegacE.SortingTermination
import FX1PolyAudit.Polygraph.OmegacE.TranspositionConfluence
import FX1PolyAudit.Polygraph.OmegacE.TranspositionReducer
import FX1PolyAudit.Polygraph.OmegacE.TranspositionSystem
import FX1PolyAudit.Polygraph.OmegacE.WordFreeMonoid
import FX1PolyAudit.Polygraph.OmegacE.WordFreeMonoidUniversal
import FX1PolyAudit.Polygraph.OmegacE.WordProblem
import FX1PolyAudit.Tier0.RuleFibration
import FX1PolyAudit.Tier0.Term.Action.FoldUniqueness
import FX1PolyAudit.Tier0.Term.Action.InitialAlgebra
import FX1PolyAudit.Tier0.Term.Action.SubstitutionMonoid
import FX1PolyAudit.Tier0.Term.Cell.CellSort
import FX1PolyAudit.Tier0.Term.Codata.CopatternCoverage
import FX1PolyAudit.Tier0.Term.Codata.MixedFixpoint
import FX1PolyAudit.Tier0.Term.Codata.TerminalCoalgebra
import FX1PolyAudit.Tier0.Term.Core.RawTermFoldNonVarCommute
import FX1PolyAudit.Tier0.Term.Core.RawTermFreeVars
import FX1PolyAudit.Tier0.Term.Generator.GeneratorCountPinCoreCellsAudit
import FX1PolyAudit.Tier0.Term.Generator.GeneratorFinitePolygraphCoreCellsAudit
import FX1PolyAudit.Tier0.Term.Generator.GeneratorPolygraphMap
import FX1PolyAudit.Tier0.Term.Generator.GeneratorRedexHead
import FX1PolyAudit.Tier0.Term.Generator.GeneratorSignatureValue
import FX1PolyAudit.Tier0.Term.Generator.GeneratorTagRoundTrip
import FX1PolyAudit.Tier0.Term.Rename.RawTermOccurrenceRename
import FX1PolyAudit.Tier0.Term.Rename.RawTermRenameAsSubst
import FX1PolyAudit.Core.Rewriting.Reduction.Dim1FreePreorder
import FX1PolyAudit.Polygraph.OmegaCategory.FreeStrictOmega
import FX1PolyAudit.Core.Rewriting.LevyOptimality
import FX1PolyAudit.Polygraph.Marked.MarkedComplicial
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.ModularSNBoundary
import FX1PolyAudit.Polygraph.OmegaCategory.PolygraphicResolution
import FX1PolyAudit.Polygraph.OmegaCategory.SquierCoherence
import FX1PolyAudit.Polygraph.Invertibility.WitnessClosure
import FX1PolyAudit.Polygraph.Invertibility.InvertibilitySet
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationBridge
import FX1PolyAudit.Polygraph.Invertibility.FiniteNoGap
import FX1PolyAudit.Core.Rewriting.Word.WordProblem
import FX1PolyAudit.Tier0.Term.Semantics.DenotationalDomain
import FX1PolyAudit.Tier0.Term.Semantics.DifferentialLambda
import FX1PolyAudit.Tier0.Term.Semantics.GameSemantics
import FX1PolyAudit.Tier0.Term.Semantics.GeometryOfInteraction
import FX1PolyAudit.Tier0.Term.Semantics.IntersectionTypes
import FX1PolyAudit.Tier0.Term.Subst.RawTermOccurrenceSubst
import FX1PolyAudit.Tier0.Term.Subst.RawTermOccurrenceSubstLift
import FX1PolyAudit.Tier0.Term.Subst.RawTermSubstLiftWeaken
import FX1PolyAudit.Core.Fib.TermAxis
import FX1PolyAudit.Core.Fib.TermAxisMore
import FX1PolyAudit.Core.Rewriting.Normalize.NbE.LevelExprComplexity
import FX1PolyAudit.Tier0.Type.Level.LevelExprImpredicativeClosure
import FX1PolyAudit.Tier0.Type.Level.LevelExpr
import FX1PolyAudit.Tier0.Type.Level.LevelExprSerialize
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify01
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify02
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify03
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify04
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify05
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify06
import FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify07
import FX1PolyAudit.Tier0.Type.Level.LevelNormalizationTableExclusion
import FX1PolyAudit.Tier0.Type.TypeAxis
import FX1PolyAudit.Tier0.Type.Universe.UniverseFlag
import FX1PolyAudit.Tier0.Type.Universe.UniverseFlagSerialize
import FX1PolyAudit.Tier0.Type.Universe.UniverseFlagStrength
import FX1PolyAudit.Tier0.Type.Universe.UniversePayloadSerialize
import FX1PolyAudit.Core.Unification.PatternUnification
import FX1PolyAudit.Polygraph.Rewriting.Standardization
import FX1PolyAudit.Core.Rewriting.BohmTree
import FX1PolyAudit.Polygraph.Rewriting.RewritingModulo
import FX1PolyAudit.Core.Metatheory.Normalization.IotaSN.RawIotaEtaFullStepSN
import FX1PolyAudit.Core.Metatheory.Normalization.IotaSN.RawIotaFullStepSN
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationCodeFormers
import FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSubterm
import FX1PolyAudit.Core.Metatheory.Reducibility.Candidates.KripkeReducibilityCandidate
import FX1PolyAudit.Core.Metatheory.Reducibility.Core.PointwiseIffAlgebra
import FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleLevelCongr
import FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberNeutral
import FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberStepClosure
import FX1PolyAudit.Core.Metatheory.Reducibility.Types.ReducibleTypeClosed
import FX1PolyAudit.Core.Metatheory.Sconing.SconingSNObjectUnique
import FX1PolyAudit.Core.Metatheory.Sconing.SconingTaitCrossLeg
import FX1PolyAudit.Core.ParityMatrix.CoreCellsParityAudit
import FX1PolyAudit.Polygraph.Rewriting.Confluence.CommutationConfluence
import FX1PolyAudit.Polygraph.Rewriting.Confluence.DecreasingDiagrams
import FX1PolyAudit.Core.Rewriting.Confluence.DeterministicConfluence
import FX1PolyAudit.Polygraph.Rewriting.Confluence.DiamondConfluence
import FX1PolyAudit.Polygraph.Rewriting.Confluence.KnuthBendixCompletion
import FX1PolyAudit.Polygraph.Rewriting.Confluence.ModularConfluence
import FX1PolyAudit.Polygraph.Rewriting.Confluence.Newman
import FX1PolyAudit.Core.Rewriting.Confluence.RawConfluence
import FX1PolyAudit.Core.Rewriting.Confluence.StepStarConfluenceViaTable
import FX1PolyAudit.Polygraph.Rewriting.Confluence.TakahashiTriangle
import FX1PolyAudit.Core.Rewriting.Reduction.Step.StepLamDomainCong
import FX1PolyAudit.Core.Rewriting.RuleTables.Core.UnionStarReflTransBridge
import FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality
import FX1PolyAudit.Core.Rewriting.RuleTables.StepOver.StepTableEquivariance
import FX1PolyAudit.Core.Substrate.Cell.EraseToRoseRenameInvariant
import FX1PolyAudit.Typed.Corpus.Smoke.RawIotaEtaOperationalSN
import FX1PolyAudit.Typed.Metatheory.Canonicity.Core.ConvergentCanonicityBoundary
import FX1PolyAudit.AuditSyntaxAction
import FX1PolyAudit.AuditGen
import FX1PolyAudit.AuditProfile
import FX1PolyAudit.AuditFXProfile
import FX1PolyAudit.AuditNbE
import FX1PolyAudit.AuditUniverse
import FX1PolyAudit.AuditTyped
import FX1PolyAudit.AuditOmegacE
import FX1PolyAudit.AuditModal
import FX1PolyAudit.AuditFX0Poly
import FX1PolyAudit.Typed.CellRuleFibration
import FX1PolyAudit.CapstoneSignoff

/-! # FX1PolyAudit/AuditAll — the authoritative zero-axiom audit umbrella

Pure-import umbrella over every required audit gate module.  This is the
single reviewer- and CI-facing entry point for the strict zero-axiom
sweep: building `FX1PolyAudit.AuditAll` runs the full per-declaration
`#assert_no_axioms` gate set plus the per-namespace axiom sweeps.

## Why an explicit umbrella in addition to the `.submodules` glob

`lake build FX1PolyAudit` builds every file under `FX1PolyAudit/` via the
lakefile's `globs := #[.submodules `FX1PolyAudit]`.  That guarantees every
gate file that EXISTS compiles — but its coverage set is "whatever files
are on disk."  Delete a gate file and the glob silently builds the
remainder and still reports success: the dropped coverage is invisible.

This umbrella inverts that: it names the REQUIRED gate modules explicitly,
so removing a gate file (without also editing this list) becomes a
missing-import build error.  The two mechanisms compose:

* glob      ⟹ "everything present compiles" (no orphaned-but-broken gate),
* umbrella  ⟹ "everything required is present" (no silently-dropped gate).

The second invariant is the one a release gate actually needs.

## Required coverage (the gate modules)

* `DependencyAudit`    — defines the `#assert_no_axioms` primitive (the
  build-failing transitive-dependency axiom check).  Every gate imports it.
* `AuditCore` / `AuditCoreSubstrate` / `AuditCore{Unification,Standardization,
  BohmTree,RewritingModulo,TerminationOrders}` — the `FX1Poly.Core`
  cell-calculus spine + the broad per-namespace axiom sweeps.
* `FX1PolyAudit.Tier0.*` — the Tier0 four-axis ω-category gates
  (Context / Mode / Term / Type / OmegacE), each mirroring its
  `FX1Poly.Tier0.*` source module path.  These replace the former flat
  `AuditTier0{Context,Mode,Term,Type}*` aggregators (relocated into the
  source-mirroring tree); naming each mirror module here keeps the
  deletion-tripwire invariant.
* `TypeAxisLedger` — the type-axis honesty ledger.
* `AuditSyntaxAction` / `AuditGen` / `AuditProfile` / `AuditFXProfile` /
  `AuditNbE` / `AuditUniverse` — syntax-action, generator-table, profile /
  sconing, FX-profile soundness, normalizer, and `LevelExpr` / `UniverseFlag`
  gate sets.
* `AuditTyped` — the typed layer (HasType / weakening / substitution /
  validity / SN / inversion / uniqueness / decidable conv + honesty/decider
  corpora).
* `AuditOmegacE` / `AuditModal` — the Makkai word-problem leg and the
  resource-graded doctrine (usage / security ordered-semiring substrate).
* `AuditFX0Poly` / `AuditCellRuleFibration` / `CapstoneSignoff` — the FX0
  bridge, the cell-rule fibration, and the capstone sign-off.

## Deliberately EXCLUDED — do NOT re-add

`Gates*` budget-ratchet / import-census / naming / parity / debt-dashboard
files and `Summary*` full-namespace-walk reports are deliberately absent.
That machinery is slow, fragile (the namespace sweep silently passes an
under-imported namespace as "ok 0 declarations"; the dependency walk
truncates at a fuel cap with no error), and largely ceremonial.  The
genuine guarantee — "no declaration depends on an axiom" — is delivered by
the per-decl `#assert_no_axioms` gates above, which are both faster and
harder to fool than a coverage-count ratchet.  Do NOT reintroduce the
`Gates*` / `Summary*` infrastructure; add per-decl gates instead.
-/
