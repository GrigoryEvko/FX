import FX1PolyAudit.AuditGen
-- Sink files of the foundational term-substrate slice (importing these
-- transitively loads every FX1Poly.Core declaration).
-- The bespoke-eta cluster (`StepEta` + the eta-rename closure now in
-- `StepEtaRename` + the eta-root classifier carrying the relocated
-- `hasRootStepSource_etaLamSource_smoke`) was severed from the canonical
-- substrate's transitive closure (TABLE-CANON-ETA re-base), so the
-- `FX1Poly.Core` namespace sweep below would otherwise miss their
-- declarations (the silent under-import footgun this gate guards against).
import FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate
import FX1Poly.Core.Equality.Eta.EtaRootClassifier
import FX1Poly.Core.Equality.Gel.GelRelationRetract
import FX1Poly.Core.Substrate.Certifier.CheckResult
import FX1Poly.Core.Substrate.Profile.ConsistencyStrength
import FX1Poly.Core.Substrate.Profile.CoreFxProfile
import FX1Poly.Core.Metatheory.Normalization.Core.FoldShiftGreaterThanOne
import FX1Poly.Tier0.Term.Generator.GenPayloadEvidence
import FX1Poly.Tier0.Term.Generator.GeneratorChildSpecsDim0
import FX1Poly.Tier0.Term.Generator.GeneratorTotalityClass
import FX1Poly.Core.Substrate.Cell.HasEqualDim
import FX1Poly.Core.Substrate.Cell.RawCellCascadeLaws
import FX1Poly.Tier0.Term.Cell.RawCellCode
import FX1Poly.Tier0.Term.Subst.RawTermSubstAction
import FX1Poly.Tier0.Term.Core.RawTermChildrenUnique
import FX1Poly.Core.Rewriting.RuleTables.Core.RuleSpec
import FX1Poly.Core.Substrate.Profile.SiteOpenness
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Rewriting.Reduction.Head.HeadStep
import FX1Poly.Core.Rewriting.Reduction.Head.HeadStepCommute
import FX1Poly.Core.Rewriting.Reduction.Head.HeadStepCommute2
import FX1Poly.Core.Rewriting.Reduction.Head.HeadStepRenameReflect
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStep
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepDeterministic
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepSubsumes
import FX1Poly.Core.Rewriting.Normalize.WeakHeadStepNormalForms
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRename
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepRenameReflect
import FX1Poly.Core.Rewriting.Reduction.Step.StepRenameReflect
import FX1Poly.Core.Rewriting.Reduction.Step.StepRenameReflectAssembly
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepCommute
import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation
import FX1Poly.Core.Rewriting.Normalize.NeutralReflectAlongStep
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst0ArgumentStar
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeForwardClosure
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeForwardStepStar
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeConvInvariance
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DependentArrowReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReachAwareOptionModelCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.UnaryCarrierCombinatorTable
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibleTypeReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Members.ReducibleMember
import FX1Poly.Core.Metatheory.Reducibility.Members.ReducibleMemberNeutral
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeWellFormed
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleType
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeRename
import FX1Poly.Core.Metatheory.Reducibility.Candidates.KripkeCandidateRenameClosure
import FX1Poly.Core.Substrate.Neutral.NeutralTermRename
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeForwardClosure
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeCandidate
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeNeutral
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeConvInvariance
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeHeadExpansion
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMember
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberNeutral
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationReflection
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberAbstraction
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleUniverseDecode
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleMemberNonDependent
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleSmoke
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ArrowCandidateMembership
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
-- Certifier base (CellBoundary / PolyCell + immediate consumers).
import FX1Poly.Core.Substrate.Certifier.CertifiedRawCell
import FX1Poly.Core.Substrate.Certifier.CertifiedTermSpineProjections
import FX1Poly.Core.Substrate.Certifier.CertifyChildSpine
import FX1Poly.Core.Substrate.Profile.PolyCellErasure
import FX1Poly.Core.Substrate.Profile.PolyCellHelpers
-- Certifier spine + exact-cell builders.
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExact
import FX1Poly.Core.Substrate.Certifier.CertifyTermSpine
import FX1Poly.Core.Rewriting.Reduction.Spine.SpineRenameStep
import FX1Poly.Core.Rewriting.Reduction.Spine.SpineSubstStep
-- Certifier coverage / general inference + certified-term to PolyCell.
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactCompHRejects
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactShape
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactSound
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactTermBase
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactWrongChildShape
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactRenameEquiv
import FX1Poly.Core.Substrate.Certifier.CertifyRawCellExactNegativeProbes
import FX1Poly.Core.Substrate.Certifier.CertifyTermExact
import FX1Poly.Core.Substrate.Certifier.CheckRawCellAs
import FX1Poly.Core.Substrate.Certifier.InferRawCellGeneralSound
import FX1Poly.Core.Substrate.Certifier.InferRawCellGeneralAcceptedCellDimensionEq
import FX1Poly.Core.Substrate.Certifier.CertifiedToPolyCell
-- HasCertified intro/composition/projection + subject-reduction iota family
-- + beta-redex preservation + structural-induction primitives + Pair layer.
import FX1Poly.Core.Substrate.Certifier.HasCertifiedHonestyProbes
import FX1Poly.Core.Equality.Eta.SubjectReductionEtaStructural
import FX1Poly.Core.Rewriting.Reduction.Preservation.CompoundRenamePreservation
import FX1Poly.Core.Rewriting.Reduction.Preservation.CompoundSubstPreservation
import FX1Poly.Tier0.Term.Core.RawTermFoldNonVarCommute
import FX1Poly.Core.Rewriting.Reduction.Preservation.BetaRedexDoublingSpike
import FX1Poly.Core.Substrate.Cell.StructuralInductionPrimitives
import FX1Poly.Core.Eliminators.Core.PairEliminatorLayer
-- Reduction machinery: raw NF/free-vars/fresh, Step subst/rename + HCC
-- wrappers + helper smokes, substitution-preservation mutual, Nat/Bool layers.
import FX1Poly.Core.Rewriting.Normalize.RawTermNF
import FX1Poly.Core.Rewriting.Reduction.Step.StepRename
import FX1Poly.Core.Rewriting.Reduction.Step.StepHelperSmokes
import FX1Poly.Core.Rewriting.Reduction.Preservation.SubstPreservationMutual
import FX1Poly.Core.Eliminators.Nat.NatEliminatorLayer
import FX1Poly.Core.Eliminators.Nat.NatElimSuccContractumReductionCongruence
import FX1Poly.Core.Eliminators.Nat.NatElimReductTrackingStrongNormalization
import FX1Poly.Core.Eliminators.List.ListElimConsContractumReductionCongruence
import FX1Poly.Core.Eliminators.List.ListElimReductTrackingStrongNormalization
import FX1Poly.Core.Substrate.Cell.StructuralInductionWrapper
import FX1Poly.Core.Rewriting.Reduction.Step.StepHCCWrappers
-- Confluence + critical pairs + Conv congruence/subst-rename
-- + remaining dim-0 eliminators (Id) + StepStarLength.
import FX1Poly.Core.Rewriting.Conversion.ConvCongruence
import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluence
import FX1Poly.Core.Rewriting.Reduction.Step.StepStarLength
import FX1Poly.Core.Rewriting.Conversion.ConvNormalForm
import FX1Poly.Core.Equality.Eta.SubjectReductionEtaBinder
import FX1Poly.Core.Eliminators.Identity.IdEliminatorLayer
-- Strong normalization (leaves/neutral/constructors/redexes/eta) + beta-eta
-- confluence + iota-eta double strips + concrete neutral predicate.
import FX1Poly.Core.Substrate.Neutral.NeutralTerm
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidateArrow
import FX1Poly.Core.Substrate.Neutral.NeutralStepClosure
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRedexes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationIotaRedexes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.BoolElimStrongNormalization
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSubterm
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSpineExpansion
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.AppWeakHeadFunctionStrongNormalization
import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalRootStability
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Eliminators.Core.BoolElimGeneralCandidateMember
import FX1Poly.Core.Eliminators.Core.OptionMatchGeneralCandidateMember
import FX1Poly.Core.Eliminators.Core.EitherMatchGeneralCandidateMember
import FX1Poly.Core.Eliminators.Core.PairProjectionGeneralCandidateMember
import FX1Poly.Core.Eliminators.Core.IdentityEliminatorGeneralCandidateMember
import FX1Poly.Core.Eliminators.Core.PathApplicationGeneralCandidateMember
import FX1Poly.Core.Metatheory.Reducibility.Candidates.BridgeReducibleCandidate
import FX1Poly.Core.Metatheory.Reducibility.Core.HeadExpansionClosure
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretation
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationDeterminism
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationRename
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationSubst
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationHeadExpansion
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateReducibleSubst
import FX1Poly.Core.Substrate.Semantics.SemanticTypeDomain
import FX1Poly.Core.Rewriting.Normalize.WhnfInterpretation
import FX1Poly.Core.Rewriting.Normalize.WhnfInterpretationDeterminism
import FX1Poly.Core.Rewriting.Normalize.WhnfInterpretationHeadExpansion
import FX1Poly.Core.Rewriting.Normalize.WhnfInterpretationHeadReduce
import FX1Poly.Core.Rewriting.Normalize.WhnfInterpretationRename
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleType
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeHeadExpansion
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibleTypeArrowCandidate
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeAbstraction
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeClosedUnderStep
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeInversion
import FX1Poly.Core.Rewriting.Word.PolygraphConvergentDecision
import FX1Poly.Core.Metatheory.Sconing.SconingWitness
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRename
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRenameForward
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationSmokeCorpus
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationFormerCorpus
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationApplication
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationEta
import FX1Poly.Tier0.Term.Generator.GeneratorCountPin

/-! # FX1PolyAudit.Core.NamespaceSweep — Core / Tier0.Syntax namespace floor sweeps

The two `#audit_namespace` + `#assert_namespace_min_count` floor gates (relocated
verbatim from the former `AuditCoreSubstrateSweeps` monolith).  These depend on the
FULL foundational import closure above so the sweep sees every loaded
`FX1Poly.Core` / `FX1Poly.Tier0.Syntax` declaration; the per-declaration
`#assert_no_axioms` gates that accompanied them now live in the per-kernel-module
mirror shards under `FX1PolyAudit/Core/...`. -/

#audit_namespace FX1Poly.Core
-- Floor re-pinned 3241 → 3144 → 3094 → 3081 after the APPROVED bespoke-iota retirement deletions:
-- (1) CdLemma.lean + CriticalPairs.lean (the per-iota critical-pair matrix, superseded by
--     the table route's StepStar.localJoin / StepStar.tableRouteConfluence);
-- (2) the dead per-iota structural-SR cluster — StepBetaEtaPreservesShape + StepPreservesShape
--     + CongPreservationMutual + SubjectReductionBaseIotas + the 7 SubjectReductionIota* files
--     (the original M2/M3/M4 Step.preservesShape engine, zero consumers, superseded by the
--     typed SR SR-U4 and the table-generic IotaTableStructuralSR.nRedex);
-- (3) the bespoke rename-reflection dispatch — the 16 per-iota Step.reflectIota* arms +
--     Step.reflectBeta (StepRenameReflectEliminatorIota.lean + the StepRenameReflect arm block),
--     superseded by the table-generic StepOverTable.reflectRename harvested across the IOTA-T1
--     adequacy (uniform-table-redex directive).
-- Floor 3081 → 3052 after the APPROVED TABLE-CANON-ETA retirement of the six dead bespoke
-- beta-eta files (StepBetaEtaJoinableConfluence, StrongNormalizationBetaEtaLeaves /
-- StrongNormalizationBetaEtaFormers, BetaEtaWordSystem, NederpeltNonJoinability, StepEtaRename),
-- superseded by the table-native StepTable / StepEtaRootTable / ConvTableBetaEtaRoot relations.
-- Floor 3052 → 2953 after the APPROVED TABLE-CANON-ETA retirement of the now-headless OSN-B /
-- Geser beta-eta chain (EtaPostponementOverBeta, StrongNormalizationBetaEtaUnion,
-- StepBetaEtaConfluence, StepEtaEtaCriticalPairs), whose only external consumer
-- (OpenStronglyNormalizingBetaEta) was retired in a prior unit.
-- Floor 3055 → 2988 after the THEATER-PURGE of the 67 content-free
-- `fxProfile_*Has* = true/false := rfl` PolyProfile smoke pins (status flags
-- re-asserted as `rfl`; the 2 admission-backing stc pins are retained).
-- Floor 2988 → 2987 after the omega-axis deletion dropped the 2 PolyProfile
-- projections (`modeTheory`, `mttNormConstructionLevel`) when the structure
-- shrank from 13 to 11 fields (the retired ModeOmega mode-theory axis).
-- Floor 2987 → 2977: ditched the §3.1-3.6 scaffold axes (10 PolyProfile projections).
#assert_namespace_min_count FX1Poly.Core 2977
#audit_namespace FX1Poly.Tier0.Syntax
#assert_namespace_min_count FX1Poly.Tier0.Syntax 59
