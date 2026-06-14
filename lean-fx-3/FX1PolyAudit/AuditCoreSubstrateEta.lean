import FX1PolyAudit.AuditGen
-- Sink files of the foundational term-substrate slice (importing these
-- transitively loads every FX1Poly.Core declaration).
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
import FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate
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
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeForwardClosure
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeForwardStepStar
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeConvInvariance
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DependentArrowReducibilityCandidate
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
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationFundamental
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
import FX1Poly.Core.Substrate.Certifier.HorizontalCompositeAdmission
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

/-! # FX1PolyAudit/AuditCoreSubstrateEta — foundational term-substrate zero-axiom gates, shard 2 of 2
(split from the AuditCoreSubstrate monolith for parallel gate elaboration; the full import block is preserved verbatim so the `#audit_namespace` sweeps see every loaded Core/Foundation declaration and the per-decl `#assert_no_axioms` gates resolve). -/

-- (The bespoke βη SN leaf/former smoke corpus — noEtaStep_*, the smoke_*BetaEta former witnesses,
-- noStepChildren_*, noStep_lamVar0 — was retired in the TABLE-CANON-ETA deletion along with
-- StrongNormalizationBetaEtaLeaves.lean / StrongNormalizationBetaEtaFormers.lean; the table-native
-- StepTable / StepEtaOverTable SN substrate supersedes it.)

-- Kripke-indexed candidates make arrow rename-closure definitional.  Non-dependent presheaf
-- functoriality + the arrow rename-closure.
#assert_no_axioms FX1Poly.Core.transport_transport_pointwise
#assert_no_axioms FX1Poly.Core.kripkeArrow_transport_pointwise
-- Dependent Kripke arrow (the Pi case): codomain family transport functoriality + dependent rename-closure.
#assert_no_axioms FX1Poly.Core.codFamily_transport_transport_pointwise
#assert_no_axioms FX1Poly.Core.kripkeArrowDep_transport_pointwise
-- CR1 structural ingredient: an application's strong normalization descends to its function (Acc pullback).
#assert_no_axioms FX1Poly.Core.appFunctionCongStep
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_of_appFunction_aux
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_of_appFunction
-- CR1 for the Kripke arrow (non-dependent + dependent): members are strongly normalizing (Tait argument).
#assert_no_axioms FX1Poly.Core.kripkeArrow_stronglyNormalizing
#assert_no_axioms FX1Poly.Core.kripkeArrowDep_stronglyNormalizing
-- CR2 for the Kripke arrow (non-dependent + dependent): forward Step closure.
#assert_no_axioms FX1Poly.Core.kripkeArrow_forwardStep
#assert_no_axioms FX1Poly.Core.kripkeArrowDep_forwardStep
-- CR3 for the non-dependent Kripke arrow: Girard neutral backward closure — the PAUSED brick, now unblocked
-- by the full arbitrary-renaming Step reflection-with-image (Step.reflectRename, StepRenameReflectAssembly).
-- A neutral function all of whose Step-reducts are in the arrow is in the arrow: app of neutral head is
-- neutral, codomain-CR3 closes it, head-steps reflect via Step.reflectRename + the all-reducts hypothesis,
-- arg-steps run the inner Tait accessibility induction on the domain-CR1 strongly-normalizing argument. This
-- COMPLETES the non-dependent Kripke arrow CR bundle (CR1/CR2/CR3) — a prerequisite ingredient for the open
-- Kripke logical relation that the GrownCtxConv-5 (#842) context-conversion piElim residual requires.
#assert_no_axioms FX1Poly.Core.kripkeArrow_neutralBackwardClosure
-- The SN Kripke candidate (the Kripke-model interpretation of a NEUTRAL type code): the index-IGNORING
-- candidate whose members at every renaming index are exactly the strongly-normalizing terms (the
-- `ReducibleTypeStep.neutral` SN candidate lifted to the renaming-indexed family).  Rename-INVARIANT
-- (transport along any renaming is the IDENTITY, `Iff.rfl`) — the semantic reason context conversion is FREE
-- on the neutral-type interpretation of the open GrownCtxConv-5 (#842) type-validity residual — plus CR1 (members are
-- strongly normalizing, definitionally).  Wires the Kripke arrow substrate to the type-level neutral
-- interpretation, the first concrete piece of the open typed logical-relation model.
#assert_no_axioms FX1Poly.Core.snKripkeCand_transport_pointwise
#assert_no_axioms FX1Poly.Core.snKripkeCand_stronglyNormalizing
-- CR3 structural ingredient: neutrality is preserved by renaming (needed so the applied fresh-var head
-- `rename furtherRenaming functionTerm` stays neutral in the Kripke arrow's neutral backward closure).
#assert_no_axioms FX1Poly.Core.IsNeutral.rename
-- A neutral term's one-step reduct is again neutral: a neutral can only step by congruence (no root redex
-- fires, the principal child being neutral never a constructor), and congruence preserves the stuck shape.
-- Discharges the `neutralClosedUnderStep` hypothesis of `CanonicalFormsPredicate.closedUnderStep`.
#assert_no_axioms FX1Poly.Core.IsNeutral.closedUnderStep
-- boolElim s t e is strongly normalizing when its scrutinee and both branches are SN (the branch-SN form,
-- via a triple nested accessibility induction absorbing the iota-redex).  The iota-head-expansion SN
-- foundation for boolElim reducibility and the fundamental theorem's eliminator arm.
#assert_no_axioms FX1Poly.Core.StepStar.boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
-- Identity eliminators: idJ / idStrictRec base witness is SN when base and witness are SN, via the
-- boolElim-style double nested accessibility induction over base and witness.
#assert_no_axioms FX1Poly.Core.StepStar.idJ_isStronglyNormalizing_of_strongly_normalizing_base
#assert_no_axioms FX1Poly.Core.StepStar.idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base

-- Generic non-variable cell commutation for fold traversals: the substrate for subst/rename through an
-- abstract formation cell.  fold_mkGen_of_ne_var exposes the fold non-variable branch for an abstract
-- non-gen_var generator (dsimp [fold] + dif_neg); subst/rename_mkGen_of_ne_var are the traversal corollaries
-- (canonical_algebra_eq_mkGen rebuild).  The payload cast is
-- Generator.payload_scope_invariant_of_not_var (the generator enumeration in one place).  The category-C
-- formation-family consumers (HasTypeDescSubstitution/Weakening + grown twins) discharge their pi/sigma
-- cases through it generically, so a new formation row touches none of them.
#assert_no_axioms FX1Poly.Core.fold_mkGen_of_ne_var
#assert_no_axioms FX1Poly.Core.RawTerm.subst_mkGen_of_ne_var
#assert_no_axioms FX1Poly.Core.RawTerm.rename_mkGen_of_ne_var

-- The bespoke-`Step.eta`-FREE weakening-shape + table-row firing lemmas relocated out of the
-- (now-being-deleted) StepEtaCriticalPairs cluster into the standalone EtaRowFiringSubstrate
-- home; consumed by the table-native childJoin path-lambda join + union subject reduction.
#assert_no_axioms FX1Poly.Core.RawTerm.weaken_lam
#assert_no_axioms FX1Poly.Core.RawTerm.weaken_eq_lam_implies_source_lam
#assert_no_axioms FX1Poly.Core.RawTerm.weaken_pathLam
#assert_no_axioms FX1Poly.Core.RawTerm.weaken_eq_pathLam_implies_source_pathLam
#assert_no_axioms FX1Poly.Core.pathBetaRowFiringDecompose

-- (The bespoke Nederpelt non-joinability witnesses — nederpeltReductsNonJoinable, the three
-- cdLemmaStatement*_isFalse, Step.nederpeltInnerBeta* / Step.eta.not_from_varBodyLam /
-- Step.betaEtaStar.eq_of_blockedSource — and the BECR-1 joinable raw half
-- (BetaEtaPairJoin.*Joinable, Step.betaEtaStar.HereditaryLamJoinable.*) were retired in the
-- TABLE-CANON-ETA deletion along with NederpeltNonJoinability.lean /
-- StepBetaEtaJoinableConfluence.lean — superseded by the table-native ConvTableBetaEtaRoot route.)

-- GENERATOR-COUNT PIN (permanent stale-count guard): the enum has exactly 205 constructors —
-- gen_npComplete attains index 202 (count from below) and every index is < 203 (count from above,
-- the theorem a 204th generator breaks).  Update generatorCount + count-citing docstrings together.
#assert_no_axioms FX1Poly.Core.generatorCount_lastIndex
#assert_no_axioms FX1Poly.Core.generatorCount_upperBound

-- HORIZONTAL-COMPOSITE ADMISSION BOUNDARY: the compH rejection upgraded from behavioral
-- (`certifyRawCellExact?_compH_rejects`) to STRUCTURAL — `PolyCell` deliberately has no
-- horizontalComposite constructor, so the certified layer is provably EMPTY at any compH index
-- and NO profile can inhabit the admission record (`HorizontalCompositeAdmission.unrealizable`).
-- The Gray interchange law is STATED as the Axis 6 blocker shape, never assumed; the decidable
-- dimensional predicate is the necessary-only half of composability; `horizontalCompositeStatus =
-- .stagingOnly` is the honest cell-layer ledger marker (compH sits outside the Generator-based
-- reducibility coverage BY KIND).
#assert_no_axioms FX1Poly.Core.HorizontallyDimComposable
#assert_no_axioms FX1Poly.Core.identityPair_horizontallyDimComposable
#assert_no_axioms FX1Poly.Core.termBasePair_not_horizontallyDimComposable
#assert_no_axioms FX1Poly.Core.GrayInterchangeShape
#assert_no_axioms FX1Poly.Core.HorizontalCompositeAdmission
#assert_no_axioms FX1Poly.Core.PolyCell.horizontalComposite_empty
#assert_no_axioms FX1Poly.Core.CertifiedRawCell.horizontalComposite_empty
#assert_no_axioms FX1Poly.Core.HorizontalCompositeAdmission.unrealizable
#assert_no_axioms FX1Poly.Core.CellCompositeStatus
#assert_no_axioms FX1Poly.Core.verticalCompositeStatus
#assert_no_axioms FX1Poly.Core.horizontalCompositeStatus
#assert_no_axioms FX1Poly.Core.horizontalCompositeStatus_eq_stagingOnly
