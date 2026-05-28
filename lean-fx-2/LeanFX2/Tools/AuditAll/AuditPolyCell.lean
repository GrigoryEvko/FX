import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.StrictHarness.TrustEscape
import LeanFX2.Foundation.PolyCell.Tier0.FireTriangle
import LeanFX2.Foundation.PolyCell.Tier0.InternalSconing
import LeanFX2.Foundation.PolyCell.Core.CellSort
import LeanFX2.Foundation.PolyCell.Core.CheckResult
import LeanFX2.Foundation.PolyCell.Extension.ProfileExtension
import LeanFX2.Foundation.PolyCell.OmegacE.HonestyCheck
import LeanFX2.Foundation.PolyCell.Core.RawCellCode
import LeanFX2.Foundation.PolyCell.Core.GeneratorMetadata
import LeanFX2.Foundation.PolyCell.Core.GeneratorAdmission
import LeanFX2.Foundation.PolyCell.Core.GenPayloadEvidence
import LeanFX2.Foundation.PolyCell.Core.HasEqualDim
import LeanFX2.Foundation.PolyCell.Core.RuleSpec
import LeanFX2.Foundation.PolyCell.Core.CellBoundary
import LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine
import LeanFX2.Foundation.PolyCell.Core.PolyCell
import LeanFX2.Foundation.PolyCell.Core.PolyCellErasure
import LeanFX2.Foundation.PolyCell.Core.PolyCellHelpers
import LeanFX2.Foundation.PolyCell.Core.CertifyChildSpine
import LeanFX2.Foundation.PolyCell.Core.ReconcileChild
import LeanFX2.Foundation.PolyCell.Core.CertifyTermSpine
import LeanFX2.Foundation.PolyCell.Core.CertifyTermExact
import LeanFX2.Foundation.PolyCell.Core.CertifiedRawCell
import LeanFX2.Foundation.PolyCell.Core.BuildGeneratingCellExact
import LeanFX2.Foundation.PolyCell.Core.BuildVerticalCompositeExact
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExact
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneral
import LeanFX2.Foundation.PolyCell.Core.CheckRawCellAs
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactSound
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactCompHRejects
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralAcceptedCellDimensionEq
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralAcceptedRawCellHEq
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralSound
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactCoverage
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactNegativeProbes
import LeanFX2.Foundation.PolyCell.FXProfile.CertifiedViews
import LeanFX2.Foundation.PolyCell.FXProfile.CertifiedViewsSound
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstDefs
import LeanFX2.Foundation.PolyCell.Core.GenAlgebra
import LeanFX2.Foundation.PolyCell.Core.Fold
import LeanFX2.Foundation.PolyCell.Core.RawTermRename
import LeanFX2.Foundation.PolyCell.Core.RawTermWeaken
import LeanFX2.Foundation.PolyCell.Core.LiftsRaw
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstPointwise
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstIdentity
import LeanFX2.Foundation.PolyCell.Core.RawTermRenamePointwise
import LeanFX2.Foundation.PolyCell.Core.RawTermRenameCompose
import LeanFX2.Foundation.PolyCell.Core.RawTermRenameComposeFusion
import LeanFX2.Foundation.PolyCell.Core.RawTermRenameSubstCommute
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstRenameCommute
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstCompose
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0Commute
import LeanFX2.Foundation.PolyCell.Core.RawTermStrengthen
import LeanFX2.Foundation.PolyCell.Core.RawTermFresh
import LeanFX2.Foundation.PolyCell.Core.RawTermFreeVars
import LeanFX2.Foundation.PolyCell.Core.RawTermNF
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstAction
import LeanFX2.Foundation.PolyCell.Core.RawCellRenameSubst
import LeanFX2.Foundation.PolyCell.Core.RawCellCascadeLaws
import LeanFX2.Foundation.PolyCell.Modal.ResourceGraded
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactShape
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactTermBase
import LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpineProjections
import LeanFX2.Foundation.PolyCell.Core.CertifiedToPolyCell
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaBoolTrue
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaBoolFalse
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionBaseIotas
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaProjections
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaEither
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaOption
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaIdRefl
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionIotaNatRec
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionEtaStructural
import LeanFX2.Foundation.PolyCell.Core.SubjectReductionEtaBinder
import LeanFX2.Foundation.PolyCell.Core.StepBetaEtaPreservesShape
import LeanFX2.Foundation.PolyCell.Core.StepEtaCriticalPairs
import LeanFX2.Foundation.PolyCell.Core.StepIotaEtaInsideBinder
import LeanFX2.Foundation.PolyCell.Core.StepIotaEtaDoubleStrips
import LeanFX2.Foundation.PolyCell.Core.StepEtaEtaCriticalPairs
import LeanFX2.Foundation.PolyCell.Core.StepBetaEtaConfluence
import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationEta
import LeanFX2.Foundation.PolyCell.Core.HasCertifiedIntros
import LeanFX2.Foundation.PolyCell.Core.HasCertifiedHonestyProbes
import LeanFX2.Foundation.PolyCell.Core.SubstPreservationProbes
import LeanFX2.Foundation.PolyCell.Core.HasCertifiedComposition
import LeanFX2.Foundation.PolyCell.Core.CompoundRenamePreservation
import LeanFX2.Foundation.PolyCell.Core.CompoundSubstPreservation
import LeanFX2.Foundation.PolyCell.Core.BetaRedexLeafPreservation
import LeanFX2.Foundation.PolyCell.Core.BetaRedexCompoundPreservation
import LeanFX2.Foundation.PolyCell.Core.HasCertifiedProjections
import LeanFX2.Foundation.PolyCell.Core.BetaRedexEndToEnd
import LeanFX2.Foundation.PolyCell.Core.BetaRedexDoublingSpike
import LeanFX2.Foundation.PolyCell.Core.PairEliminatorLayer
import LeanFX2.Foundation.PolyCell.Core.BoolEliminatorLayer
import LeanFX2.Foundation.PolyCell.Core.NatEliminatorLayer
import LeanFX2.Foundation.PolyCell.Core.RemainingDim0Eliminators
import LeanFX2.Foundation.PolyCell.Core.IdEliminatorLayer
import LeanFX2.Foundation.PolyCell.Core.StructuralInductionPrimitives
import LeanFX2.Foundation.PolyCell.Core.StructuralInductionWrapper
import LeanFX2.Foundation.PolyCell.Core.SpineRenameStep
import LeanFX2.Foundation.PolyCell.Core.SpineSubstStep
import LeanFX2.Foundation.PolyCell.Core.SubstPreservationMutual
import LeanFX2.Foundation.PolyCell.Core.CongPreservationMutual
import LeanFX2.Foundation.PolyCell.Core.StepPreservesShape
import LeanFX2.Foundation.PolyCell.Core.CriticalPairs
import LeanFX2.Foundation.PolyCell.Core.CdLemma
import LeanFX2.Foundation.PolyCell.Core.StepStarConfluence
import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationLeaves
import LeanFX2.Foundation.PolyCell.Core.CoreFxProfile
import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactWrongChildShape
import LeanFX2.Foundation.PolyCell.Core.GeneratorTotalityClass
import LeanFX2.Foundation.PolyCell.Core.ConsistencyStrength
import LeanFX2.Foundation.PolyCell.Core.SiteOpenness
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactRenameEquiv
import LeanFX2.Foundation.PolyCell.Core.Step
import LeanFX2.Foundation.PolyCell.Core.StepStar
import LeanFX2.Foundation.PolyCell.Core.StepEta
import LeanFX2.Foundation.PolyCell.Core.StepSubst
import LeanFX2.Foundation.PolyCell.Core.StepRename
import LeanFX2.Foundation.PolyCell.Core.StepInversion
import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationConstructors
import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationNeutral
import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationRedexes
import LeanFX2.Foundation.PolyCell.Core.CertifiedTerm
import LeanFX2.Foundation.PolyCell.Core.GeneratorChildSpecsDim0
import LeanFX2.Foundation.PolyCell.Core.CellNonVarStepRenamer
import LeanFX2.Foundation.PolyCell.Core.CellNonVarStepSubstituter
import LeanFX2.Foundation.PolyCell.Core.SpineConsStep
import LeanFX2.Foundation.PolyCell.Core.StepHCCWrappers
import LeanFX2.Foundation.PolyCell.Core.FoldShiftGreaterThanOne
import LeanFX2.Foundation.PolyCell.Core.StepStarLength
import LeanFX2.Foundation.PolyCell.Core.ConvCongruence
import LeanFX2.Foundation.PolyCell.Core.ConvSubstRename
import LeanFX2.Foundation.PolyCell.NbE.DesignDecision
import LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy
import LeanFX2.Tools.AuditAll.AuditPhaseZ
import LeanFX2.Tools.AuditAll.AuditStrictAxes
import LeanFX2.Foundation.TyWellfoundedness

namespace LeanFX2.Tools

/-! ## AuditPolyCell — PolyCell core and admission-ledger gates. -/

#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellSort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellSort.all
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellSort.toCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellSort.ofCode?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellSort.ofCode?_toCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellSort.all_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqCellSort

-- ═══════════════════════════════════════════════════════════════
-- TCB.9 v1 retirement (2026-05-27): the v1 dim-indexed PolyCell
-- audit gates (originally lines 88-2872 of this file, totalling
-- ~2800 gates over `PolyTerm`, `Check`, `CertifyExact`,
-- `CertifiedFXCell`, etc.) have been removed alongside the v1
-- source files.  The V2 substrate's gates (below) are now the
-- canonical audit surface for the PolyCell kernel.
-- ═══════════════════════════════════════════════════════════════

#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Stratification 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Algebra 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Algebra 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Saturation 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Saturation 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Enrichment 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Enrichment 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Modal 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Modal 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.ProfileFibration 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.ProfileFibration 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Gray 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Gray 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Universe 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Universe 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.SSC 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.SSC 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.STC 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.STC 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Tier0 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Tier0 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.MTTNorm 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.MTTNorm 0
#assert_true_in_result_type_budget LeanFX2.Foundation.PolyCell.Extension 0
#assert_false_in_result_type_budget LeanFX2.Foundation.PolyCell.Extension 0
#assert_inhabited_dependent_budget LeanFX2.Foundation.PolyCell.Core 0
-- ═══════════════════════════════════════════════════════════════
-- V2 RAW SUBSTRATE GATES (Stage 0)
-- ═══════════════════════════════════════════════════════════════
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.arity
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.binderShifts
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.binderShifts_length_eq_arity
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.payload
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.empty
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.single
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.singleUnderBinder
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.pairFlat
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.binderShape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.tripleFlat
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.dim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.size
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.size
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_termBase
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_generatingCell_source
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_generatingCell_target
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_verticalComposite_first
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_verticalComposite_second
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_horizontalComposite_left
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_horizontalComposite_right
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.size_lt_identityCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.size_lt_childCons_head
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.size_lt_childCons_tail
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.decEqPayload
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.decEq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.decEq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqRawTerm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqRawTermChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.decEq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqRawCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.toNat
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.payloadToNat
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.toCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.toCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.toCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.hasSameNatList

-- ═══════════════════════════════════════════════════════════════
-- V2 GENERATOR METADATA GATES (Stage 1)
-- ═══════════════════════════════════════════════════════════════
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.cellSort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.cellDimension
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.scopeShift
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqChildSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.sameScopeDimZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.underOneBinderDimZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.termSameScope
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.termUnderBinder
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.typeSameScope
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.typeUnderBinder
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.cellSort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childSpecs
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childSpecs_length_eq_arity
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childSpecs_scopeShifts_eq_binderShifts

-- ─── V2-L1.4 / V2-L1.5: admission ledger (#139 / #140) ──────────
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.SupportedGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.supportedGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.supportedGenerator?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.supportedGenerator?_isSome

-- ─── V2-L1.6 / V2-L1.7: payload evidence (#141 / #142) ──────────
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.GenPayloadEvidence
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.genPayloadEvidence
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.genPayloadEvidence?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.genPayloadEvidence?_isSome

-- ─── V2-fix-3: unbounded universes design commitment ──────────────
-- genPayloadEvidence?_universeCode_unbounded: for any Nat level,
-- the universeCode payload admits under fxProfile.  Witnesses the
-- explicit commitment to the Tarski-style infinite cumulative
-- universe hierarchy (rather than a bounded maxUniverseLevel).
--
-- A future restricted profile that imposed a level bound would
-- refine GenPayloadEvidence .gen_universeCode level to a Sigma
-- type carrying `level < bound`, and this theorem's proof would
-- fail at sufficiently large `level`.  The audit gate surfaces
-- the design commitment as a machine-checked fact.
--
-- Closes the V2-fix-3 Agent 3 finding H3.3 (decoration GenPayloadEvidence).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.genPayloadEvidence?_universeCode_unbounded

-- ─── V2-L1.8: dim reconciliation predicate (#143) ───────────────
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasEqualDim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.hasEqualDim_decidable
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasEqualDim.refl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasEqualDim.symm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasEqualDim.trans
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasEqualDim.iff_dim_eq

-- ─── V2-L1.9: rule admission ledger (#144) ──────────────────────
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RuleSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RuleSpec.ruleId
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RuleSpec.cellSort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RuleSpec.endpointDimension
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instDecidableEqRuleSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.termStepRuleSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.SupportedRuleSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.SupportedRuleSpec.termStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.lookupRuleSpec?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.supportedRuleSpec?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.lookupRuleSpec?_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.supportedRuleSpec?_termStep

-- ═══════════════════════════════════════════════════════════════════
-- L1c: CERTIFIED LAYER (#146-#155) — the cascade-killing architecture
-- ═══════════════════════════════════════════════════════════════════
--
-- 45 declarations across 5 files, all gated below.  This is the
-- v2 certified layer where the architectural payoff materializes:
-- ONE generic `gen` ctor admits every term-former (vs v1's 5+
-- per-fixture ctors).  Adding a feature = 9 lines of metadata, ZERO
-- new PolyCell ctors.
--
-- File map (in declaration-dependency order):
--   * CellBoundary.lean (#146)        — 5 decls   [dim-dispatch type]
--   * AbstractTermSpine.lean (#147)   — 15 decls  [parametric blueprint]
--   * PolyCell.lean (#148-#152)       — 8 decls   [mutual block: PolyCell+spine]
--   * PolyCellErasure.lean (#153)     — 5 decls   [raw-erasure rfl lemmas]
--   * PolyCellHelpers.lean (#154)     — 12 decls  [CertifiedCell + packageX]
-- ═══════════════════════════════════════════════════════════════════

-- ─── V2-L1c.1: cell boundary data (#146) ─────────────────────────
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellBoundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellBoundary_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellBoundary_succ
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellBoundary.trivial
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CellBoundary.endpoints

-- ─── V2-L1c.2a: abstract spine blueprint + ChildSpec helpers (#147 partial) ─────────────
-- The parametric AbstractTermSpine is the architectural blueprint (cf. v1 CellChildren).
-- The spec-aligned concrete CertifiedTermSpine lives inside the PolyCell mutual block
-- (#148) — gates for that ship there.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope_sameScopeDimZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope_underOneBinderDimZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope_termSameScope
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope_termUnderBinder
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope_typeSameScope
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.expectedScope_typeUnderBinder
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ChildSpec.ExpectedCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine.nil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine.cons
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine.arity
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine.arity_eq_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine.ForGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.AbstractTermSpine.arity_forGenerator_eq

-- ─── V2-L1c.3 through V2-L1c.7: the certified mutual block (#148-#152) ───
-- ONE mutual inductive ships PolyCell + CertifiedTermSpine with all
-- four PolyCell ctors at once (Lean 4 mutual inductives are atomic;
-- ctors cannot be added incrementally).  The headline is `gen`: ONE
-- generic ctor subsumes every v1 per-fixture term ctor.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.gen
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.generatingCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.verticalComposite
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.identityCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.nil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.cons

-- ─── V2-L1c.8: raw-erasure rfl lemmas for PolyCell (#153) ──────
-- Witnesses the "erasure back to raw is definitional" property
-- documented in polycell.md §4.  The extractor projects the rawCell
-- type index; the four per-ctor lemmas restate what each ctor's
-- output type already pins.  All close by rfl.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.raw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.gen_raw_eq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.generatingCell_raw_eq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.verticalComposite_raw_eq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.identityCell_raw_eq

-- ─── V2-L1c.9: package helpers for PolyCell (#154) ─────────────
-- CertifiedCell bundles indices + cell into one struct for use
-- as the certifier's return type.  packageX helpers combine ctor
-- application with packaging in one shot.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.mk
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.dim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.rawCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.boundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.certifiedCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedCell.ofCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.packageGen
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.packageGeneratingCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.packageVerticalComposite
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.packageIdentityCell

-- ═══════════════════════════════════════════════════════════════════
-- L1c sweep complete (#155).  45 decls audited, all axiom-clean.
-- Next stage: L1c.4 certifier (#156+) — certifyRawCellExact? and
-- friends, returning Except CellCheckRejection (CertifiedCell ...)
-- via the package helpers above.
-- ═══════════════════════════════════════════════════════════════════

-- ─── V2-L1cert.1: parametric child-spine certifier (#156) ─────────
-- Generic parallel-walk recursion over (childSpecs, children) with
-- per-child reconciliation delegated to a callback.  The v1
-- screenRawChildDescriptorsWith? equivalent, but constructive
-- (builds a CertifiedTermSpine rather than just yes/no).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedChildAtSpec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedChildAtSpec.mk
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedChildAtSpec.headBoundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedChildAtSpec.headCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyChildSpine?

-- ─── V2-L1cert.2: per-child reconciler (#157) ──────────────────────
-- Bridges general certifier (existential sort/dim/rawCell) to the
-- spec-matched CertifiedChildAtSpec demanded by certifyChildSpine?.
-- Tactic-mode pattern: cases (destructure) + by_cases Decidable +
-- subst (Eq.ndrec) ×3 for sort/dim/raw.  Propext-free per the v1
-- buildTermStepCellExact? recipe.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.reconcileChild

-- ─── V2-L1cert.3: wired term-spine certifier (#158) ────────────────
-- Top-level child-spine certifier produced by wiring
-- certifyChildSpine? (#156) with reconcileChild (#157) as the
-- per-child callback.  One-line function composition; inherits
-- axiom-cleanliness from its two components.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyTermSpine?

-- ─── V2-L1cert.4: generator-dispatch certifier (#159) ──────────────
-- Builds a CertifiedCell from (generator, payload, children) via:
-- admission + payload evidence + spine certification + packageGen.
-- Uses the 'thread coherence as data' pattern: passes
-- (Generator.childSpecs_scopeShifts_eq_binderShifts).symm to
-- certifyTermSpine? as a coherence proof, which absorbs the
-- equation via internal `subst`.  No ▸ chains at this layer.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyTermExact?

-- ─── V2-L1cert.5: raw-indexed package + generating cell builder (#160) ──
-- CertifiedRawCell is the raw-INDEXED package (rawCell as parameter,
-- not field) used by the exact certifier (#162).  Three fields: sort,
-- boundary, certifiedCell (dim is computed via rawCell.dim).
--
-- buildGeneratingCellExact? uses the v1-proven transport recipe:
-- by_cases on ruleId/sourceSort/targetSort/dimEq + subst's + a final
-- generalize+subst dance on target.dim to align with source.dim.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCell.mk
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCell.sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCell.boundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCell.certifiedCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.buildGeneratingCellExact?

-- ─── V2-L1cert.6: vertical composite builder (#161) ─────────────────
-- buildVerticalCompositeExact? extends the v1 transport recipe to
-- the un-indexed v2 raw layer.  v1 took `cdim : CellDim` as a TYPE
-- parameter to pin first/second cells at (cdim+1) definitionally;
-- v2's un-indexed raw cannot do this, so the same constraint travels
-- as DATA: parentDimension : Nat + hFirstDim/hSecondDim witnesses.
--
-- Inside the body:
-- * destructure both certified packages
-- * `if hSort` (constructive Decidable on CellSort)
-- * generalize+subst on firstRaw.dim / secondRaw.dim aligns both
--   children's boundaries/cells to dim parentDimension+1
-- * `cases` on each boundary destructures CellBoundary ... (n+1) ...
--   into Prod components (whnf reduces the def to RawCell × RawCell)
-- * `if hMiddle` (constructive Decidable on RawCell via the L0 #133
--   instance — imported from RawCellDecEq to keep typeclass search
--   from falling back to Classical.propDecidable)
-- * subst hMiddle aligns the middle endpoint
-- * build the verticalComposite cell at dim parentDimension+1
-- * final transport back to firstRaw.dim: boundary via single-motive
--   ▸; cert via explicit Eq.rec with multi-arg motive that captures
--   the dependent boundary in lockstep with the dim.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.buildVerticalCompositeExact?

-- ─── V2-L1cert.7: THE recursive certifier (#162) ────────────────────
-- certifyRawCellExact? is the architectural HEADLINE of the v2
-- certifier: ONE recursion over RawCell that certifies the entire
-- non-horizontalComposite fragment at every dimension.
--
-- ARCHITECTURE: fuel-based mutual recursion.
-- * certifyRawCellExactFueled?: fueled fueled-Nat recursive dispatch
--   on RawCell's five constructors.  Cross-calls into
--   certifyChildrenInlineFueled? for the .termBase case.
-- * certifyChildrenInlineFueled?: walks the children spine + spec
--   list in parallel, cross-calling certifyRawCellExactFueled? on
--   each child wrapped as (.termBase headRaw).  Per-child sort/dim
--   reconciliation via if-Decidable + subst + explicit Eq.rec with
--   multi-arg motive.
-- * certifyRawCellExact?: top-level entry that supplies sufficient
--   fuel (raw.size + 1) so .fuelExhausted is unreachable for
--   well-formed inputs.
--
-- WHY FUEL (not termination_by + decreasing_by):
-- Mutual recursion across RawCell ↔ RawTermChildren (separate
-- inductives) fails Lean 4 v4.29.1's `decreasing_by` substitution:
-- the goal references the function's `children` parameter abstractly
-- even after pattern-matching to .childCons.  Without omega (which
-- leaks propext + Quot.sound per a probe in this session), the
-- `(.childCons head rest).size = children.size` step is not
-- discharable.  Structural recursion on Nat fuel is propext-free and
-- ~50 lines simpler.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExactFueled?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyChildrenInlineFueled?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?

-- ─── V2-L1cert.8: existential wrapper (#163) ────────────────────────
-- inferRawCellGeneral? wraps certifyRawCellExact? into an
-- EXISTENTIAL package (rawCell as field, not type parameter) suitable
-- for higher-level ingress points that don't want to thread the input
-- rawCell through the return type.
--
-- The wrapper adds two `polycell.md` §4 spec fields versus
-- CertifiedRawCell:
-- * inputCode : List Nat (prefix code of input)
-- * hasInputCode : hasSameNatList inputCode rawCell.toCode = true
--   (code-level no-laundering certificate)
--
-- hasSameNatList_self is shipped as a self-contained list+Nat
-- induction proof; CertifiedRawCellResult is a pure structural
-- record; inferRawCellGeneral? is a propext-free Except match +
-- direct struct construction.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.hasSameNatList_self
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.mk
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.cellDimension
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.inputCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.rawCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.cellSort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.cellBoundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.certifiedCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedRawCellResult.hasInputCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inferRawCellGeneral?

-- ─── V2-L1cert.9: expected-shape checker (#164) ─────────────────────
-- checkRawCellAs? is the expected-sort variant of
-- inferRawCellGeneral?.  Takes an expectedSort + raw input,
-- delegates to inferRawCellGeneral?, then checks result.cellSort
-- against the expectation:
--   match → return result
--   mismatch → reject with .wrongSort
--
-- The .wrongSort rejection class is SPECIFIC to expected-shape
-- checking per polycell.md §4.  Bare inference never produces it.
--
-- One-phase design (vs v1's two-phase screen+infer).  Trade-off:
-- mismatched-sort cells get fully certified before the sort check;
-- under fxProfile the cost is negligible since callers usually know
-- the sort they're passing.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.checkRawCellAs?

-- ─── V2-L1cert.10: raw-indexed soundness (#165) ─────────────────────
-- certifyRawCellExact?_sound: every accepted exact certification
-- yields a certified cell whose raw erasure is EXACTLY the input.
-- The no-false-positive guarantee for the raw-indexed ingress.
--
-- Proof: `rfl`.  The raw-indexed return type pins rawCell to the
-- input at the type level; PolyCell.raw is a definitional
-- projection of that type index.  The certifier CANNOT launder a
-- different raw past the input — there is no inhabitant of
-- CertifiedRawCell profile scope raw whose certifiedCell.raw
-- differs from raw.
--
-- The architectural payoff of v2's raw-INDEXED return type made
-- structural: soundness collapses to a one-line rfl.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?_sound

-- ─── V2-L1cert.11: totality off compH (#166) ────────────────────────
-- certifyRawCellExact?_compH_rejects: for any raw input of the
-- form `.horizontalComposite left right`, the certifier rejects with
-- `.unsupportedCompH` at every dimension, scope, and profile.
--
-- Proof: `rfl`.  The top-level wrapper unfolds to
-- certifyRawCellExactFueled? (raw.size + 1) scope raw.  For
-- horizontalComposite, raw.size = left.size + right.size + 1 so
-- raw.size + 1 ≥ 2 — definitionally succ-shaped, matches the fuel
-- function's `fuel' + 1` arm.  The inner match on raw hits the
-- `.horizontalComposite _ _ => .error .unsupportedCompH` arm.
--
-- Closes the totality story: every well-formed input either
-- certifies cleanly OR rejects with one of the seven rejection
-- classes (one of which is .unsupportedCompH, proven here to fire
-- on every compH input).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?_compH_rejects

-- ─── V2-fix-1: behavioral shape pin (identityCell boundary) ─────────
-- certifyRawCellExact?_identityCell_boundary: if the certifier
-- accepts an .identityCell base input, the certified cell's
-- boundary equals (base, base) — the pair of endpoints produced by
-- the dispatcher's identityCell arm.
--
-- Substantively non-vacuous: the proof inspects the acceptance
-- hypothesis via case analysis on the recursive call's result.  A
-- regression that broke the identityCell dispatch arm (e.g., emitting
-- a different boundary value) would invalidate this lemma.
--
-- Complements certifyRawCellExact?_sound (#165, type-level
-- no-laundering) by adding a behavioral dispatch verification.
-- This is the FIRST shape lemma of V2-fix-1; follow-up commits will
-- extend to termBase / generatingCell / verticalComposite arms.
--
-- Pattern: `rfl`-bridge `dispatcherEq` rewrites the wrapper into
-- its expanded match form (avoiding `unfold` on the mutual
-- recursive `certifyRawCellExactFueled?` which would leak
-- Quot.sound), then `cases hRec` on the recursive call result +
-- `injection` on the Except.ok equality.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?_identityCell_boundary

-- ─── V2-fix-1 phase B: "implies inner certs" shape pins ─────────────
-- For dispatcher arms that perform N recursive sub-certifications
-- before delegating to a build* helper, "if accepted, all recursive
-- sub-certifications succeeded" is a substantive shallow shape pin —
-- it verifies the dispatcher's recursion is not short-circuited.
--
-- Two arms covered in this phase:
--
--   .verticalComposite — recurses on first then second, then delegates
--   to buildVerticalCompositeExact? for boundary reconciliation.
--   The pin extracts existential witnesses for both inner certs.
--
--   .generatingCell — symmetric structure: recurses on source then
--   target, delegates to buildGeneratingCellExact?.  Same proof
--   shape, transfers verbatim from the verticalComposite proof.
--
-- Each closes by:
--   1. dispatcherEq `rfl`-bridge (rewrites the wrapper to its match
--      form, avoiding `unfold` on the mutual recursive
--      `certifyRawCellExactFueled?` which would leak Quot.sound).
--   2. `cases hRec1 : ...` on first recursion, `.error` arm closed
--      by `cases accepted`, `.ok` arm pinned.
--   3. `dsimp only at accepted` to iota-reduce the outer match.
--   4. Same pattern for second recursion.
--   5. `exact ⟨⟨witness, rfl⟩, ⟨witness, rfl⟩⟩` — `rfl` closes the
--      existential body because `cases hRec : foo with | ok x =>` has
--      substituted `foo` with `Except.ok x` in the goal context.
--
-- Future phase C (deferred to V2-fix-1 continuation):
--   * `..._verticalComposite_boundary` — actual outer-endpoint shape
--     pin (requires sibling shape pin for buildVerticalCompositeExact?).
--   * `..._generatingCell_boundary` — actual (source, target) pin
--     (same for buildGeneratingCellExact?).
--   * `..._termBase_sort` — pins cert.sort = generator.cellSort.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?_verticalComposite_accepted_implies_inner_certs
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?_generatingCell_accepted_implies_inner_certs

-- ─── V2-L3.1 phase D step 1: termBase shape pin ────────────────────
-- Discharges the missing arm in the dispatcher-shape-pin family.
-- The certifier's `.termBase` arm is the gate every SR-relevant
-- input passes through (Step source/target are RawTerm, wrapped
-- as `.termBase`).  Pattern variant: reducibility-aware dispatcher
-- pin — `supportedGenerator?` and `genPayloadEvidence?` are both
-- `@[reducible]` so they pre-reduce, leaving the spine call as the
-- one non-definitional stage to case-analyze.
--
-- Building block for SR's Certified projection: from `Certified
-- (lam body)` (or any composite generator), extract the spine
-- success witness via this lemma, then projeect into each child.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyRawCellExact?_termBase_accepted_implies_inner_succeeds

-- ─── V2-L3.1 phase D step 2: spine head/tail/nil projections ───────
-- Structural destructors on CertifiedTermSpine — given a spine
-- whose RawTermChildren index is (childCons headRaw restRaws),
-- extract the head certified cell (with its existentially-bound
-- boundary, as a sigma pair) and the tail spine.  Plus the
-- nil-uniqueness lemma deriving spine = .nil from childNil index.
--
-- Building block for SR's Certified projection: combined with the
-- termBase shape pin (phase D step 1), this lets the SR proof
-- descend from a parent's spine success witness to per-child cells.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.headWithBoundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.tail
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.eq_nil_of_childNil

-- V2-L3.1 phase D step 3: dim-0 specialization of headWithBoundary.
-- Collapses the sigma-wrapped boundary to a plain PolyCell at dim 0
-- with CellBoundary.trivial boundary.  Pattern: generalize the
-- field projection (headSpec.cellDimension) to a fresh variable,
-- subst through the dim hypothesis, then use Subsingleton.elim with
-- the explicit `inferInstanceAs (Subsingleton Unit)` bridge to
-- identify the boundary with CellBoundary.trivial.  Closes the
-- SR projection one-liner: `Certified parent` → spine via shape
-- pin → headWithBoundary → headAtDim0 → plain PolyCell.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.headAtDim0

-- ─── V2-L3.1 phase D step 4: Certified → PolyCell bridge ─────────
-- HasCertifiedCellDim0: existential PolyCell at dim 0 over a raw
-- term — the structural target of SR (avoids procedural/fuel
-- reasoning).  Certified.toHasCertifiedCellDim0 ships the bridge
-- from the procedural certifier acceptance to the structural
-- PolyCell witness, collapsing the boundary via the now-canonical
-- inferInstanceAs (Subsingleton Unit) trick.
--
-- This is the load-bearing soundness-direction lemma for SR: with
-- it, the SR proof can unpack `Certified source` into a structural
-- cell and proceed at the PolyCell level (where spine projections
-- and substitution preservation already live).
--
-- The reverse direction (completeness, PolyCell → Certified) is
-- V2-L3.5 and requires fuel monotonicity — deferred.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.toHasCertifiedCellDim0

-- ════════════════════════════════════════════════════════════════════
-- HONESTY NOTICE (2026-05-27, codex audit response)
-- ────────────────────────────────────────────────────────────────────
-- The 16 theorems below named `HasCertifiedCellDim0.preservedByIotaX`
-- prove STRUCTURAL SHAPE PRESERVATION, not type-theoretic Subject
-- Reduction.  Specifically:
--
--   PolyCell.gen admission   = sort/dim/scope/arity/binder-shift OK
--   ChildSpec.termSameScope  = "child has sort .term", NOT
--                              "child has function-type compatible
--                               with the argument"
--   SupportedGenerator       = all 194 generators globally admitted
--   GenPayloadEvidence       = Unit by default for every generator
--
-- So `HasCertifiedCellDim0 (.mkGen .gen_app () [unit, unit])` IS
-- shape-admissible despite being ill-typed (unit is not a function).
-- This is INTENTIONAL: PolyCell is the structural substrate; the
-- semantic typing layer (TypingContext + GeneratorTypingRule +
-- HasType) is future work.
--
-- The 16 arms below prove what they prove honestly: given the
-- structural admission of a source cell, the structural admission
-- holds for the target after Step.  This is foundational for the
-- eventual semantic SR theorem, NOT a substitute for it.
--
-- Codex's full audit recommendations (M-2026-05-27):
--   1. Split certification levels: structural vs semantic.
--   2. Add typed contexts (per-variable types).
--   3. Generator typing rules separate from child-shape specs.
--   4. Restricted SemanticallySupportedGenerator < global.
--   5. Type-preserving Step (real SR over HasType).
--   6. Prove checker ↔ structural-admission equivalence.
--   7. Honesty probes for over-admission (e.g., app(unit,unit) IS
--      shape-admitted, demonstrating the gap).
--
-- ════════════════════════════════════════════════════════════════════

-- ─── V2-L3.1 phase D step 5: FIRST SR arm — iotaBoolTrue ───────────
-- Subject Reduction for the simplest iota: boolElim boolTrue then
-- else → then.  Pure projection (no subst, no rename, no HEq cast
-- through dim-indexed boundary).  Establishes the proof template
-- that pure-projection iota siblings (iotaBoolFalse, iotaFstPair,
-- iotaSndPair, iotaNatElimZero, iotaListElimNil, iotaOptionMatchNone)
-- inherit.
--
-- Proof: destructure HasCertifiedCellDim0 → cases on the
-- PolyCell (single-arm: .gen ctor matches .termBase rawCell) →
-- spine.tail.headAtDim0 rfl projects the then-branch cell → wrap.
-- Combined uses of the V2-L3.1 phase D steps 2 + 4 infrastructure.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaBoolTrue

-- ─── V2-L3.1 phase D step 6: SECOND SR arm — iotaBoolFalse ─────────
-- Symmetric to iotaBoolTrue.  bool-eliminator on boolFalse selects
-- the else-branch (third spine child).  Same proof pattern as
-- iotaBoolTrue with one more tail: spine.tail.tail.headAtDim0 rfl.
-- Validates that the pure-projection iota template transfers
-- verbatim across spine positions.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaBoolFalse

-- ─── V2-L3.1 phase D step 7: BASE-CASE branch-selection iota family ─
-- Four structurally identical SR arms: natElim/natRec on natZero,
-- listElim on listNil, optionMatch on optionNone.  Each: 3-child
-- same-scope spine, target = 2nd child (the base branch).  Proof
-- pattern verbatim from preservedByIotaBoolTrue.
--
-- Total pure-projection iota family after this commit:
--   * 2nd-child target: 5/5 (iotaBoolTrue + 4 here)
--   * 3rd-child target: 1/1 (iotaBoolFalse)
-- Pure projection iotas: COMPLETE.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaNatElimZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaNatRecZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaListElimNil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaOptionMatchNone

-- ─── V2-L3.1 phase D step 8: nested-projection iotas (SR arms 7-8) ─
-- Pair projection iotas: `fst(pair fst snd) ↝ fst` and
-- `snd(pair fst snd) ↝ snd`.  Unlike the 6 pure-projection iotas
-- above (which extract from a 3-child same-scope outer spine), these
-- require unwrapping TWO layers of certified PolyCell:
--   1. Outer cell `(.mkGen .gen_fst () ...)` -> outer spine -> pair cell.
--   2. Inner pair cell `(.mkGen .gen_pair () ...)` -> inner spine
--      -> firstValue/secondValue cell.
-- The dep-elim wall encountered: `cases pairCell with | gen _ _ ...`
-- fails when pairCell's sort index is the concrete `.term` because
-- the matcher cannot solve `.term = generator.cellSort` for a unique
-- free `generator` (100+ generators return `.term`).  Resolved by
-- `generalize hSort : termSameScope.cellSort = innerSort at pairCell`
-- BEFORE the inner cases, replacing the concrete sort with a free
-- variable so the matcher derives the generator from the (concrete)
-- raw cell index via `.mkGen` injectivity alone.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaFstPair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaSndPair

-- ─── V2-L3.1 phase D step 9: compound iotas — eitherMatch (SR arms 9-10)
-- The FIRST family that BUILDS a fresh target cell (rather than
-- projecting an existing child).  Target is `.mkGen .gen_app ()` over
-- [branch, value] -- assembled from the extracted leftBranch (outer
-- spine position 2) and value (inside the eitherInl/eitherInr wrapper).
--
-- Three new techniques over the nested-projection arms:
--   1. Apply the generalize-sort recipe to unwrap eitherInl/eitherInr
--      (same recipe as fstPair/sndPair).
--   2. Construct `SupportedGenerator.gen_app` directly -- it's the
--      global admission inductive's ctor, profile-agnostic.
--   3. Use `genPayloadEvidence` default constructor (returns `()` of
--      Unit) for the payload evidence.
--
-- Final assembly uses CertifiedTermSpine.cons / .nil for the new
-- 2-child spine.  The four remaining compound iotas
-- (iotaOptionMatchSome, iotaNatElimSucc, iotaListElimCons,
-- iotaNatRecSucc) follow this exact template with different
-- wrapper / branch positions.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaEitherMatchInl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaEitherMatchInr

-- ─── V2-L3.1 phase D step 10: optionMatch step iota (SR arm 11) ────
-- Structurally identical to the eitherMatch arms (single-payload
-- wrapper -> app target).  Confirms the template scales.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaOptionMatchSome

-- ─── V2-L3.1 phase D step 11: identity-type iotas on refl (SR arms 12-13)
-- Both are PURE PROJECTION iotas at the substrate level (motive
-- and endpoint information is profile-layer interpretation, not
-- substrate machinery).  Target = head of outer spine; even
-- simpler than iotaBoolTrue (no tail step required).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaIdJRefl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaIdStrictRecRefl

-- ─── V2-L3.1 phase D step 12: nested-app compound iotas (SR arms 14-16)
-- natElimSucc / natRecSucc build a 2-arg app + recursive eliminator
-- in the target.  listElimCons builds a 3-arg app + recursive
-- eliminator.  Demonstrates the compound-iota template scales to
-- arbitrarily-nested gen_app construction with the recursive call
-- as a syntactic sub-term.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaNatElimSucc
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaNatRecSucc
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByIotaListElimCons

-- ─── V2-L3.1 phase D step 13: HasCertifiedCellDim0 nullary intros ──
-- Smart constructors for the 7 nullary generators (var, unit,
-- boolTrue, boolFalse, natZero, listNil, optionNone).  Building
-- blocks for the future cell-level subst-preservation work that
-- unblocks SR-beta + SR-cong.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.var
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolTrue
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolFalse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listNil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionNone

-- ─── V2-L3.1 phase D step 14: HONESTY PROBES (codex audit response) ──
-- Theorems demonstrating that PolyCell's `HasCertifiedCellDim0` is
-- STRUCTURAL admission, NOT type-theoretic well-typedness.  Each
-- probe is a green theorem proving that an ILL-TYPED term IS
-- structurally admitted.  Makes the structural-vs-semantic gap
-- audit-visible.
--
--   * probe_app_unit_unit          — `app unit unit` admitted
--                                     despite unit not being a function
--   * probe_app_boolTrue_unit      — same point with boolTrue
--   * probe_boolElim_natZero_branches — boolElim with Nat scrutinee
--                                       admitted despite ill-typing
--
-- These probes establish that the 16 "SR arms" above prove STRUCTURAL
-- shape preservation, NOT type preservation.  Real Subject Reduction
-- (type-preserving Step over a typed term judgment) is future work
-- requiring a separate semantic layer (TypingContext + HasType +
-- GeneratorTypingRule).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.probe_app_unit_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.probe_app_boolTrue_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.probe_boolElim_natZero_branches

-- ─── V2-L3.1 phase D step 15: rename/subst preservation probes ─────
-- Leaf base cases for the future cell-level rename/subst
-- preservation mutual block.  Each shows that `RawTerm.rename` /
-- `RawTerm.subst` reduce by `rfl` on the simplest closed shapes
-- (var, unit), and that the resulting term is still structurally
-- admitted via the intros from `HasCertifiedIntros.lean`.
--
-- These are the foundation for the eventual mutual block that
-- will discharge structural SR-beta + SR-cong.  Compound cases
-- (gen_app, gen_lam, etc.) are the substantive structural-
-- induction work that follows.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_var_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_unit_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_var_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_unit_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.var_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.unit_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.unit_preservedBySubst

-- Additional nullary leaf reductions and cell-level preservations.
-- Same fold-arm pattern as `unit`; closed terms ignore renamings.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_boolTrue_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_boolFalse_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_natZero_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_listNil_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_optionNone_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolTrue_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolFalse_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natZero_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listNil_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionNone_preservedByRename

-- ─── V2-L3.1 phase D step 30: closed-leaf general-subst preservations
-- The mirror of the rename-direction leaf coverage above, for general
-- `RawTerm.subst`.  Each closed nullary leaf (boolTrue / boolFalse /
-- natZero / listNil / optionNone) carries a `subst σ` reduction probe
-- closing by `rfl`, plus a corresponding `_preservedBySubst` lemma.
-- Combined with `unit_preservedBySubst` (phase D step 15) and
-- `var`'s subst case via the substituent hypothesis, every nullary
-- leaf now has both rename + subst preservation shipped.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_boolTrue_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_boolFalse_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_natZero_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_listNil_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_optionNone_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolTrue_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolFalse_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natZero_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listNil_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionNone_preservedBySubst

-- ─── V2-L3.1 phase D step 31: Generator childSpecs all-dim-0 invariant
-- Bool predicate + universal-true theorem + Prop-valued propagation
-- lemma — provides the `allDim0` witness the mutual structural induction
-- mutual block needs to invoke `CertifiedTermSpine.headAtDim0` inside
-- the non-var arm of the cell renamer / substituter.  Closes by
-- `cases gen <;> rfl` (194-ctor enum) for the Bool side; pure list
-- induction with direct Bool case analysis for the Prop side.  Both
-- propext-free.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.allChildSpecsDim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.allChildSpecsDim0_eq_true
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childSpecs_cellDimension_zero

-- ─── V2-L3.1 phase D step 32: cell-side step renamers (factored body
-- of the eventual mutual block).  Non-recursive — takes the renamed
-- spine as hypothesis (for the non-var case) or works trivially (var).
-- Sibling of `StructuralInductionWrapper.lean` decls but at the cell
-- level rather than HCC.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.rename_dim0_nonVarStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.rename_dim0_varStep

-- ─── V2-L3.1 phase D step 33: cell-side step substituters (subst sibling
-- of step 32 step renamers).  Non-recursive — takes the substituted
-- spine as hypothesis (non-var) or the substituent's cell directly
-- (var).  Completes the cell-side step infrastructure for both
-- rename and subst directions.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.subst_dim0_nonVarStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.subst_dim0_varStep

-- ─── V2-L3.1 phase D step 34: spine-side cons + nil step helpers.
-- Non-recursive cons-step closes the dependent boundary cast on
-- CertifiedTermSpine.cons via generalize + subst + Subsingleton.elim
-- (the trick from headAtDim0).  Direction-agnostic (works for both
-- rename and subst).  With these + cell-step helpers (phase D 32/33),
-- the mutual block's body becomes a thin recursive driver.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.consStep_dim0Trivial
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.nilStep

-- Rename-shaped spine-step wrappers: sibling of the subst-shaped
-- helpers below.  The cons helper records that the head is renamed
-- under `headSpec.scopeShift` binders via `iterateLiftRaw`, while the
-- tail uses the parent renaming.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.renameNilStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.renameConsStep_dim0Trivial

-- Subst-shaped spine-step wrappers: package the future spine-recursion
-- nil/cons cases against `foldChildren GenAlgebra.canonical sigma`.
-- The cons helper records the important de Bruijn discipline: the head
-- is substituted under `headSpec.scopeShift` binders via
-- `iterateLiftRaw`, while the tail uses the parent substitution.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.substNilStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.substConsStep_dim0Trivial

-- ─── M2 / V2-L3.1 phase D: structural rename+subst mutual block.
-- This turns the factored step helpers above into real recursive
-- drivers over `PolyCell.gen` + `CertifiedTermSpine.cons`.
-- The substitution half uses the rename half to certify lifted
-- substitutions under binders; `preservedByBeta` is the SR-beta M2
-- endpoint requested by task #251.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.rename_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.rename_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.liftSubstDim0Cells
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.iterateLiftSubstDim0Cells
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.subst_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.subst_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.singletonSubstDim0Cells
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedBySubst0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByBeta

-- ─── M3 / V2-L3.1 phase D: first congruence-preservation layer.
-- This is the non-circular core of SR-cong: given an exact
-- sort-preserving preserver for the stepped child, recurse over the
-- `StepChildren` witness and rebuild the certified spine / parent.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepCellPreserver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepCellPreserverWitness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByBeta_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaBoolTrue_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaBoolFalse_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaFstPair_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaSndPair_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaNatElimZero_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaNatRecZero_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaListElimNil_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaOptionMatchNone_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaIdJRefl_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaIdStrictRecRefl_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaOptionMatchSome_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaEitherMatchInl_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaEitherMatchInr_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaNatElimSucc_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaNatRecSucc_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PolyCell.exists_preservedByIotaListElimCons_dim0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByCong_via_stepPreserver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserverWitness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByCong_via_stepPreserverWitness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepCellPreserverWitness.polyCell
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpine.exists_preservedByChildStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.preservesShape

-- ─── V2-L3.2 / M6: critical-pair root-rule catalog scaffold ───────
-- RootStepKind enumerates the 17 non-congruence Step rules (beta +
-- the 16 iotas), deliberately separating them from Step.cong because
-- congruence branchings require a parent generator and child position.
-- This is the first M6 slice: root/root critical-pair data is
-- computable and audited; full M6 continues with congruence
-- child-position branchings and diamond fillers.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.all
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sourceGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.hasSourceGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.forSourceGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.RootOverlapShape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.classifyRootOverlap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.RootCriticalPair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.mkRootCriticalPair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.pairLeftWithRightKinds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.pairsForKindLists
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.criticalPairsForSourceGenerators
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.differentRootDisjointPartner?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.RootCriticalPair.hasCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.all_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.forSourceGenerator_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.forSourceGenerator_boolElim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.forSourceGenerator_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.classifyRootOverlap_beta_beta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.classifyRootOverlap_bool_iotas
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.classifyRootOverlap_beta_boolTrue
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness_bool_reverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness_natElim_reverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness_natRec_reverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness_list_reverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness_option_reverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.sameGeneratorDifferentRootPairHasDisjointWitness_either_reverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.boolElimRootPairs_haveCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.natElimRootPairs_haveCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.natRecRootPairs_haveCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.listElimRootPairs_haveCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.optionMatchRootPairs_haveCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RootStepKind.eitherMatchRootPairs_haveCurrentRootResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCriticalPairs
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCriticalPairsEmptyDecision
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCriticalPairs_app_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCriticalPairs_boolElim_boolElim_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCriticalPairs_unit_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.ChildPosition
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childPositionsFromShifts
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childPositions
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.RootCongruenceOrientation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.RootCongruenceBranching
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchingsForPosition
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchingsForRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.RootCongruenceBranching.hasValidChildPosition
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.RootCongruenceBranching.hasCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childPositions_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childPositions_lam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.childPositions_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_app_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_boolElim_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_app_currentResolutionMap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_app_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_boolElim_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_fst_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_snd_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_natElim_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_natRec_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_listElim_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_optionMatch_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_eitherMatch_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_idJ_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.rootCongruenceBranchings_idStrictRec_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.CriticalPair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.CriticalPair.hasCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.CriticalPair.CurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.CriticalPair.currentResolution?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.CriticalPair.currentResolution?_isSome
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairsFromRootPairs
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairsFromRootCongruenceBranchings
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairsEmptyDecision
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.hasCurrentResolutionForCriticalPairs
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.CriticalPairResolutionDispatch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairResolutionDispatch?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairResolutionDispatch?_isSome
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_app_app_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_boolElim_boolElim_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_unit_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_app_app_currentResolutionMap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_app_app_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_boolElim_boolElim_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_fst_fst_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_snd_snd_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_natElim_natElim_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_natRec_natRec_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_listElim_listElim_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_optionMatch_optionMatch_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_eitherMatch_eitherMatch_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_idJ_idJ_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_idStrictRec_idStrictRec_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairs_unit_app_haveCurrentResolution
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.criticalPairResolutionDispatch?_app_app_isSome
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.boolTrue_hasNoStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.boolFalse_hasNoStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.natZero_hasNoStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.listNil_hasNoStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.optionNone_hasNoStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaBeta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaFunctionCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaArgumentCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrueSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalseSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaFstPairSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaSndPairSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimZeroSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecZeroSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimNilSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchNoneSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdJReflSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdStrictRecReflSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrue_iotaBoolFalse_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalse_iotaBoolTrue_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimZero_iotaNatElimSucc_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSucc_iotaNatElimZero_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecZero_iotaNatRecSucc_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSucc_iotaNatRecZero_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimNil_iotaListElimCons_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimCons_iotaListElimNil_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchNone_iotaOptionMatchSome_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSome_iotaOptionMatchNone_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInl_iotaEitherMatchInr_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInr_iotaEitherMatchInl_sourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrueThenCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrueElseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalseThenCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalseElseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaFstPairFirstCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaFstPairSecondCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaSndPairFirstCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaSndPairSecondCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccPredecessorCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccPredecessorCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsHeadCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsTailCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsNilBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsConsBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimNilBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchNoneBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeValueCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeNoneBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeSomeBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlValueCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlLeftBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlRightBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrValueCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrLeftBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrRightBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdJBaseCaseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdJWitnessCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdStrictRecBaseCaseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdStrictRecWitnessCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.sameReduct
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.sameReductOfEq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaBeta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaFunctionCongOfSubst0Replay
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaFunctionCongReverseOfSubst0Replay
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaFunctionCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaFunctionCongReverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaArgumentCongOfSubst0Replay
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaArgumentCongReverseOfSubst0Replay
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaArgumentCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.betaArgumentCongReverse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaBoolTrueSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaBoolFalseSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaFstPairSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaSndPairSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimZeroSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecZeroSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimNilSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchNoneSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaIdJReflSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaIdStrictRecReflSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchSomeSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInlSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInrSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimSuccSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecSuccSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimConsSameRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaBoolTrueThenCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaBoolTrueElseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaBoolFalseThenCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaBoolFalseElseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaFstPairFirstCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaFstPairSecondCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaSndPairFirstCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaSndPairSecondCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimSuccZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimSuccSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecSuccZeroBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecSuccSuccBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatElimSuccPredecessorCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaNatRecSuccPredecessorCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimConsHeadCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimConsTailCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimConsNilBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimConsConsBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimNilBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaListElimConsBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchNoneBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchSomeBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchSomeValueCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchSomeNoneBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaOptionMatchSomeSomeBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInlValueCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInlLeftBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInlRightBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInrValueCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInrLeftBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaEitherMatchInrRightBranchCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaIdJBaseCaseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaIdJWitnessCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaIdStrictRecBaseCaseCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.iotaIdStrictRecWitnessCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CdLemmaStatement
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.ofReductsEqual
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.sameStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.ofCongChildrenJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofHeadJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofIndependentHeadTail
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofIndependentTailHead
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofTailJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofReductsEqual
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.sameStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofStepPairResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenPairJoin.ofSmallerStepPairResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.ofCongCongStepPairResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.ofCongCongSmallerStepPairResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.ofLocalDiamondFromSteps
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepPairJoin.ofLocalDiamondFromSteps_swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.hasJoin_fromSteps
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.HasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.SourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.sourcesDisjoint_noSharedSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.hasJoin_ofReductsEqual
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.hasJoin_swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.congCong_hasJoin_ofStepPairResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.congCong_hasJoin_ofSmallerStepPairResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.toStepPairJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalDiamond.toStepPairJoin_swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaBeta_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaBeta_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaFunctionCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaFunctionCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaFunctionCongReverse_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaFunctionCongReverse_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaArgumentCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaArgumentCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.betaArgumentCongReverse_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaArgumentCongReverse_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_betaRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrueSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalseSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaFstPairSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaSndPairSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimZeroSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecZeroSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimNilSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchNoneSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdJReflSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdStrictRecReflSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolTrueSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolFalseSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaFstPairSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaSndPairSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimZeroSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecZeroSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimNilSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchNoneSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdJReflSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdStrictRecReflSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInlSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInrSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsSameRoot_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrueThenCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrueElseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalseThenCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalseElseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaFstPairFirstCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaFstPairSecondCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaSndPairFirstCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaSndPairSecondCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolTrueThenCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolTrueElseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolTrueLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolTrueRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolFalseThenCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolFalseElseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolFalseLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaBoolFalseRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaFstPairFirstCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaFstPairSecondCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaFstPairLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaFstPairRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaSndPairFirstCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaSndPairSecondCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaSndPairLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaSndPairRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSuccPredecessorCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSuccPredecessorCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccZeroBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccSuccBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccPredecessorCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccPredecessorCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimZeroLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimZeroRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecZeroLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecZeroRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatElimSuccRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaNatRecSuccRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsHeadCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsTailCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsNilBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsConsBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimNilBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimConsBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchNoneBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeValueCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeNoneBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSomeSomeBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlValueCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlLeftBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInlRightBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrValueCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrLeftBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInrRightBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdJBaseCaseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdJWitnessCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdStrictRecBaseCaseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaIdStrictRecWitnessCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsHeadCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsTailCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsNilBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsConsBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimNilBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimNilLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimNilRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaListElimConsRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchNoneBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeValueCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeNoneBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeSomeBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInlValueCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInlLeftBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInlRightBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInrValueCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInrLeftBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInrRightBranchCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdJBaseCaseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdJWitnessCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdStrictRecBaseCaseCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdStrictRecWitnessCong_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchNoneLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchNoneRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaOptionMatchSomeRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInlLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInlRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInrLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaEitherMatchInrRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdJReflLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdJReflRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdStrictRecReflLeft_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_iotaIdStrictRecReflRight_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolTrue_iotaBoolFalse_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaBoolFalse_iotaBoolTrue_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimZero_iotaNatElimSucc_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatElimSucc_iotaNatElimZero_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecZero_iotaNatRecSucc_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaNatRecSucc_iotaNatRecZero_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimNil_iotaListElimCons_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaListElimCons_iotaListElimNil_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchNone_iotaOptionMatchSome_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaOptionMatchSome_iotaOptionMatchNone_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInl_iotaEitherMatchInr_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.iotaEitherMatchInr_iotaEitherMatchInl_hasSourcesDisjoint
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_resolveBranchingBelow_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.fromSteps_resolveBranching_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LocalStepBranching.resolveBranching_hasJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CdLemmaStatement.ofLocalBranchingResolver
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.cd_lemma

-- ─── V2-L3.1 phase D step 35: HCC-level wrappers around the cell-step
-- helpers (phase D 32/33).  Same recipe, .intro-wrapped to land in
-- Prop.  Closes the symmetric HCC + Cell API surface so the SR-cong /
-- SR-beta umbrellas (when the mutual block lands) read uniformly at
-- the HCC level.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.rename_nonVarStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.rename_varStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst_nonVarStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst_varStep

-- ─── V2-L3.1 phase D step 16: compound smart constructors ─────────
-- 9 compound intros for term-shape generators with .term-sorted
-- children.  These take underlying cells (sort .term explicit)
-- rather than HasCertifiedCellDim0 wrappers, enforcing the sort
-- constraint statically.  Composition calculus for the future
-- structural-induction mutual block.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.pair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natSucc
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionSome
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInr
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listCons
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.refl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.lam

-- ─── V2-L3.1 phase D step 17: compound rename preservation ─────────
-- For each compound term-shape generator, two theorems:
--   * `rename_X_reduces`: `RawTerm.rename` distributes over the
--     compound by `rfl` (definitional; fold engine reduces).
--   * `HasCertifiedCellDim0.X_preservedByRename`: compositional
--     form — given renamed-children cells, produce renamed-parent
--     certification.  These are the INDUCTIVE STEPS that the
--     future structural-induction full preservation will
--     compose.
--
-- Crucial discovery: the binder case `gen_lam` also reduces by
-- `rfl` (using `RawRenaming.lift rho` for the body) -- this
-- makes the binder-case induction step tractable without
-- transports.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_app_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_pair_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_listCons_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_natSucc_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_optionSome_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_eitherInl_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_eitherInr_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_refl_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_lam_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.app_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.pair_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listCons_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natSucc_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionSome_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInl_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInr_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.refl_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.lam_preservedByRename

-- ─── V2-L3.1 phase D step 18: compound subst preservation ──────────
-- Symmetric to step 17 (rename) but for substitution.  The fold
-- engine's distributivity is definitional for subst as well,
-- INCLUDING the binder case `gen_lam` (where body uses
-- `RawTermSubst.lift sigma`).  This unblocks the SR-beta path:
-- beta reduces to `subst0 body arg = subst (singleton arg) body`,
-- which structurally needs subst preservation composed with the
-- singleton's pointwise certification.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_app_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_pair_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_listCons_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_natSucc_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_optionSome_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_eitherInl_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_eitherInr_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_refl_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_lam_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.app_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.pair_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listCons_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natSucc_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionSome_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInl_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInr_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.refl_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.lam_preservedBySubst

-- ─── V2-L3.1 phase D step 18: beta-redex leaf preservations ────────
-- Base cases of the future structural subst0-preservation theorem,
-- specialized to the body shapes that appear in beta redexes
-- `(lam body) arg → subst0 body arg`.
--
-- Six closed-nullary bodies (unit / boolTrue / boolFalse / natZero /
-- listNil / optionNone) are invariant under subst0 — the closed
-- term passes through unchanged.  Two variable bodies cover the
-- de Bruijn substitution behavior:
--   * var 0 → arg (the identity lambda)
--   * var (k+1) → var k (higher-indexed variables shift down)
--
-- Each closes by rw [subst0_X_reduces]; exact HCC.X.  Same
-- compositional template as the existing nullary / compound
-- preservations.  Forward-compat: when SR-beta lands as a
-- structural induction on body, THESE lemmas discharge the
-- leaf base cases; the inductive cases recurse on children.
--
-- 6 reduction probes (general var-succ + 5 closed nullary forms)
-- + 8 preservations.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_var_succ_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_boolTrue_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_boolFalse_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_natZero_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_listNil_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_optionNone_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_varZero_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_varSucc_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_unit_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_boolTrue_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_boolFalse_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_natZero_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_listNil_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_optionNone_preservation

-- ─── V2-L3.1 phase D step 19: beta-redex compound preservations ────
-- Compositional inductive step of the future structural SR-beta
-- theorem, covering the 9 compound body shapes.
--
-- For each compound generator (app/pair/listCons/natSucc/optionSome/
-- eitherInl/eitherInr/refl/lam), two theorems:
--   * subst0_X_reduces — distributivity over children by rfl.
--   * subst0_X_preservation — given substituted children's certs,
--     build the parent's cert.
--
-- The lam case is the BINDER case: inner body at scope+2 substitutes
-- with RawTermSubst.lift (RawTermSubst.singleton rawArg) — the
-- standard binder discipline.
--
-- Same compositional template as the rename / subst preservations
-- shipped earlier.  Each closes by rw + exact.  Forward-compat:
-- when the full structural induction lands, these dispatch each
-- compound's inductive step.
--
-- 9 distributivity probes + 9 compositional preservations = 18 new
-- zero-axiom declarations.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_app_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_pair_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_listCons_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_natSucc_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_optionSome_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_eitherInl_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_eitherInr_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_refl_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_lam_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_app_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_pair_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_listCons_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_natSucc_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_optionSome_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_eitherInl_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_eitherInr_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_refl_preservation
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_lam_preservation

-- ─── V2-L3.1 phase D step 20: HasCertifiedCellDim0 child projections ─
-- EXTRACTION half complementing the REBUILD half (steps 18-19).
-- Given a HasCertifiedCellDim0 of a compound shape, project to the
-- certifications of its children.
--
-- Pattern (zero-axiom):
--   obtain ⟨_, cell⟩ := cert
--   cases cell with
--   | gen _ _ spine =>
--     exact ⟨.term, spine.headAtDim0 rfl⟩  -- or spine.tail.headAtDim0
--
-- Free sort from the existential destructure lets `cases` invert
-- the .gen ctor cleanly.  Index unification on the raw
-- .termBase (.mkGen .gen_X () ...) constrains generator = .gen_X
-- and exposes the spine over the specific child shape.
--
-- 12 projections total (one per child position):
--   * Binary: app/pair/listCons → 2 each = 6
--   * Unary, no binder: natSucc/optionSome/eitherInl/eitherInr/refl
--     → 1 each = 5
--   * Unary, 1 binder: lam → body at scope+1 = 1
--
-- Together with the rebuild (steps 18-19), these complete the
-- end-to-end chain for SR-beta of fixture-shaped bodies:
--   source cert → projections to children → recursive certs →
--   composeitional rebuild → target cert
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.app_function_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.app_argument_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.pair_first_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.pair_second_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listCons_head_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listCons_tail_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natSucc_predecessor_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionSome_wrapped_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInl_wrapped_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherInr_wrapped_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.refl_witness_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.lam_body_projection

-- ─── V2-L3.1 phase D step 21: end-to-end SR-beta (var-zero) ────────
-- FIRST concrete end-to-end SR-beta theorem.  Composes the
-- EXTRACTION (step 20 projections) with the REBUILD (step 18 leaf
-- preservations) into a complete chain: source cert → post-beta cert.
--
-- Two theorems:
--   * beta_redex_projection — chained extraction helper.  Given
--     a cert for 'app (lam body) arg', extracts both bodyCert (at
--     scope+1) and argCert (at scope) in one call.  Wraps the
--     three-step projection chain (app → lam → body) plus
--     (app → arg).
--
--   * beta_var_zero_e2e — the simplest meaningful SR-beta:
--     '(λ x. x) arg → arg'.  The ONLY leaf-body case where the
--     source cert contributes — argCert flows through to the
--     result via subst0_varZero_preservation.
--
-- Closed-nullary bodies (unit/boolTrue/etc.) don't get end-to-end
-- variants here because their post-beta term is closed and
-- certified independently of the source cert hypothesis (vacuous);
-- step 18's subst0_X_preservation covers those.
--
-- Forward-compat: when the structural induction lands, this
-- theorem becomes a corollary of
-- HasCertifiedCellDim0.preservedBySubst0 specialized to body =
-- var 0.  Concrete shipping now verifies chain composition at
-- zero axioms.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.beta_redex_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.beta_var_zero_e2e
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.beta_redex_assembly
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.beta_app_self_e2e

-- ─── V2-L3.1 phase D step 22: pair eliminators (fst / snd) ─────────
-- Extends the 16-generator compositional surface to include pair
-- eliminators.  FIRST eliminator generators to get full intros +
-- projections + preservations coverage.  Each generator: 8 decls
-- (intro, projection, rename probe + preservation, subst probe +
-- preservation, subst0 probe + preservation).
--
-- Enables SR-cong for steps inside fst/snd subterms:
--   1. PROJECTION: HCC (fst x) → HCC x
--   2. STEP: x → x' preserves HCC
--   3. REBUILD: HCC x' → HCC (fst x') via intro
--
-- Template scales to other eliminators (boolElim, natElim, natRec,
-- listElim, optionMatch, eitherMatch, idJ, idStrictRec) in future
-- iterations.
--
-- 16 new zero-axiom declarations (8 per generator × 2 generators).
-- fst:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.fst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.fst_pair_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_fst_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.fst_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_fst_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.fst_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_fst_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_fst_preservation
-- snd:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.snd
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.snd_pair_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_snd_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.snd_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_snd_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.snd_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_snd_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_snd_preservation

-- ─── V2-L3.1 phase D step 23: boolean eliminator (boolElim) ────────
-- Sibling of step 22 (PairEliminatorLayer); extends eliminator
-- coverage to the 3-child boolean eliminator gen_boolElim.
--
-- 10 declarations: 1 intro + 3 projections (scrutinee/then/else) +
-- 2 rename (probe + preservation) + 2 subst + 2 subst0.
--
-- Enables SR-cong for steps inside any of boolElim's three
-- subterms (scrutinee, thenBranch, elseBranch).
--
-- Template scales to all 3-child eliminators (natElim/Rec, listElim,
-- optionMatch, eitherMatch).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolElim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolElim_scrutinee_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolElim_thenBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolElim_elseBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_boolElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolElim_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_boolElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.boolElim_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_boolElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_boolElim_preservation

-- ─── V2-L3.1 phase D step 24: nat eliminators (natElim / natRec) ───
-- Sibling of steps 22-23; extends eliminator coverage to the two
-- natural-number eliminators (large-elim natElim and recursor natRec),
-- both 3-child same-scope with layout (scrutinee, zeroBranch, succBranch).
--
-- 20 declarations total (10 per generator).  Same template as
-- boolElim (step 23): intro + 3 projections + rename probe/pres +
-- subst probe/pres + subst0 probe/pres.
--
-- Enables SR-cong for steps inside natElim/natRec subterms (any of
-- the three children).  Template proven to scale across all 3-child
-- eliminators.
-- natElim:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natElim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natElim_scrutinee_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natElim_zeroBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natElim_succBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_natElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natElim_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_natElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natElim_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_natElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_natElim_preservation
-- natRec:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natRec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natRec_scrutinee_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natRec_zeroBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natRec_succBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_natRec_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natRec_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_natRec_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.natRec_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_natRec_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_natRec_preservation

-- ─── V2-L3.1 phase D step 25: remaining 3-child eliminators ────────
-- Completes the 3-child same-scope eliminator family.
-- Ships listElim, optionMatch, eitherMatch (10 declarations each
-- = 30 total).  Same template as boolElim / natElim / natRec.
--
-- Child layouts:
--   * listElim:    (scrutinee, nilBranch, consBranch)
--   * optionMatch: (scrutinee, noneBranch, someBranch)
--   * eitherMatch: (scrutinee, leftBranch, rightBranch)
--
-- After this iteration, 6 of 7 dim-0 eliminators have full
-- compositional coverage (only idJ / idStrictRec remain — higher
-- arity, may need new template variation for 4-5 children).
--
-- Generator surface: 21 -> 24 (3 new eliminators).
-- listElim:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listElim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listElim_scrutinee_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listElim_nilBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listElim_consBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_listElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listElim_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_listElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.listElim_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_listElim_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_listElim_preservation
-- optionMatch:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionMatch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionMatch_scrutinee_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionMatch_noneBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionMatch_someBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_optionMatch_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionMatch_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_optionMatch_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.optionMatch_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_optionMatch_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_optionMatch_preservation
-- eitherMatch:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherMatch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherMatch_scrutinee_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherMatch_leftBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherMatch_rightBranch_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_eitherMatch_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherMatch_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_eitherMatch_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.eitherMatch_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_eitherMatch_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_eitherMatch_preservation

-- ─── V2-L3.1 phase D step 26: identity-type eliminators ────────────
-- Completes ALL dim-0 eliminator coverage (7 of 7).  gen_idJ and
-- gen_idStrictRec are 2-child same-scope (baseCase, identityWitness).
--
-- This is a 2-child template variation (between fst/snd's 1-child
-- and the boolElim family's 3-child).
--
-- 18 declarations total (9 per generator):
--   intro + 2 projections + rename probe/pres + subst probe/pres +
--   subst0 probe/pres.
--
-- Generator surface: 24 -> 26.  Dim-0 eliminators fully covered.
-- idJ:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idJ
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idJ_baseCase_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idJ_identityWitness_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_idJ_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idJ_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_idJ_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idJ_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_idJ_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_idJ_preservation
-- idStrictRec:
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idStrictRec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idStrictRec_baseCase_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idStrictRec_identityWitness_projection
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_idStrictRec_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idStrictRec_preservedByRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_idStrictRec_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.idStrictRec_preservedBySubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_idStrictRec_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst0_idStrictRec_preservation

-- ─── V2-L3.1 phase D step 28: structural induction primitives ──────
-- Foundational building blocks for the future structural induction
-- 'HasCertifiedCellDim0.preservedBySubst' over PolyCell + spine.
--
-- 5 declarations:
--   1. mkGen_shape — every HCC unwraps to .mkGen via PolyCell.gen
--      being the only dim-0 ctor.  This is the destructuring
--      primitive for the structural induction's cell half.
--
--   2. rename_nonVar_reduces — for generator != .gen_var, the
--      fold's dispatch falls into the non-var branch.  Closes via
--      'dsimp only [fold]; rw [dif_neg hNotVar]; rfl' (zero-axiom
--      after the spike confirmed clean).
--
--   3. subst_nonVar_reduces — sibling of (2) for subst.
--
--   4. subst_var_certify — when sigma's substituents are all
--      certified, subst sigma on a var is certified directly.
--      This is the var case of the structural induction.
--
--   5. rename_var_certify — sibling of (4) for rename (var
--      renames to var, certified via HCC.var).
--
-- These compose into the mutual structural induction:
--   * Cell half: destructure via mkGen_shape, dispatch on
--     generator = .gen_var via dite, apply var_certify in var
--     case, apply nonVar_reduces + recursive spine call + intro
--     in non-var case.
--   * Spine half: recurse on cons head + tail (mutual call to
--     cell half).
--
-- The mutual block + spine half remain to ship; this commit locks
-- in the primitive layer at zero axioms.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.mkGen_shape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_nonVar_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_nonVar_reduces
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.subst_var_certify
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.rename_var_certify

-- ─── V2-L3.1 phase D step 29: structural induction wrappers ────────
-- Outer Prop wrappers that factor public-facing HCC preservation
-- through abstract Type-level cell operations.  When the mutual
-- def block (next iteration) ships, plugging those defs in here
-- closes HCC preservation end-to-end.
--
-- 2 declarations: rename + subst wrappers.  Each is a 2-line
-- destructure-and-wrap proof.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByRename_via_renamer
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedBySubst_via_substituter

-- ─── V2-fix-4: restricted-profile admission predicate ──────────────
-- Discharges Agent 3 H3.2 (admission machinery decoration).  Before
-- this commit, `supportedGenerator?` returned `some _` for every
-- one of the 194 Generators under fxProfile — the `.none` rejection
-- branch was structurally unreachable.  The architectural claim
-- "per-profile admission can restrict the supported Generator set"
-- had no machine-witnessed example.
--
-- This commit ships `coreFxProfile`'s admission predicate as a
-- concrete restricted profile.  `Generator.isInCoreFx` returns
-- `false` for the 3 modal generators (`gen_modIntro`, `gen_modElim`,
-- `gen_subsume`) and `true` for everything else — exhibiting the
-- FIRST non-trivial admission decision.
--
-- Six witness theorems pin behavior:
--   * 3 admission witnesses (gen_var / gen_lam / gen_app accepted)
--   * 3 rejection witnesses (3 modal generators rejected)
-- Plus 3 symmetry theorems showing fxProfile-vs-coreFx disagreement
-- on the same Generator (`fxProfile_admits_X_but_coreFx_rejects`).
--
-- Each closes by `rfl` because list-membership on a decidable-
-- equality list reduces definitionally and `@[reducible]` on
-- `Generator.isInCoreFx` unfolds the negation at typecheck time.
--
-- Forward-compat: a future restricted profile (embedded /
-- safety-critical / certified-crypto subtargets) writes its own
-- exclusion list and inherits the same `rfl`-cleanliness.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coreFxExcluded
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.isInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.gen_var_isInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.gen_lam_isInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.gen_app_isInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.gen_modIntro_notInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.gen_modElim_notInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.gen_subsume_notInCoreFx
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.fxProfile_admits_modIntro_but_coreFx_rejects
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.fxProfile_admits_modElim_but_coreFx_rejects
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.fxProfile_admits_subsume_but_coreFx_rejects

-- ─── V2-L2.10: subst0 single substitution + beta-shape ──────────────
-- Ships the convenience wrapper RawTermSubst.singleton +
-- RawTerm.subst0 that the future Step relation's beta-reduction
-- rule will reference.  v2 analog of v1's RawTermSubst.singleton +
-- RawTerm.subst0 (Foundation/RawSubst/SubstDefs.lean:35,200).
--
-- Two definitions:
--   * singleton rawArg : RawTermSubst (scope+1) scope — position 0
--     maps to rawArg, k+1 maps to var k.
--   * subst0 body rawArg := subst (singleton rawArg) body — single-
--     variable substitution at position 0.
-- Both @[reducible] so smoke lemmas close by rfl.
--
-- Five smoke lemmas pin behavior:
--   * singleton_var_zero — position 0 returns rawArg.
--   * singleton_var_succ — position k+1 returns var k (shift-down).
--   * subst0_var_zero — substituting var 0 returns rawArg.
--   * subst0_var_succ_one_smoke — substituting var 1 at scope 1
--     returns var 0 (the de Bruijn shift-down).
--   * subst0_unit_smoke — substituting a closed term ignores rawArg.
--
-- Forward use: V2-L3.1 (subject reduction) will fire beta as
--   Step app(lam(body), arg) ↝ subst0 body arg
-- using subst0 from this file.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.singleton
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.singleton_var_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.singleton_var_succ
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_var_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_var_succ_one_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_unit_smoke

-- ─── V2-fix-6: .wrongChildShape reachability witnesses ──────────────
-- Under fxProfile, every `Generator.childSpecs` entry uses `.term`
-- sort and `cellDimension 0`, so the dispatcher's hSort/hDim checks
-- always succeed under public ingress.  The `.wrongChildShape`
-- rejection branch is structurally unreachable through the
-- generator-driven path.
--
-- Agent 3 of the V2 falsification audit observed that this leaves
-- the BEHAVIORAL CONTENT of `.wrongChildShape` rejection unwitnessed:
-- the soundness-completeness triangulation cannot demonstrate the
-- rejection branch fires at all without an activating fixture.
--
-- This commit ships two reachability witnesses that invoke
-- `certifyChildrenInlineFueled?` directly with handcrafted
-- (childSpec, child) tuples that mismatch:
--
--   * _typeSort_rejects_termChild — typeSameScope spec + unit child
--     triggers the outer hSort failure (sort .type vs .term).
--
--   * _nonZeroDim_rejects_termChild — cellDimension := 1 spec + unit
--     child triggers the inner hDim failure (dim 1 vs dim 0, after
--     the sort check succeeds).
--
-- Together they cover BOTH legs of the dispatch.  Each closes by
-- rfl: the certifier is a pure computation, and concrete inputs
-- reduce via Fin/Nat decidable equality to a definite
-- Except.error .wrongChildShape.
--
-- Forward-compat: a future ProfileExtension adding cross-sort
-- generators (V2-L1.13) would activate the public-ingress
-- reachability of these probes' shapes automatically.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyChildrenInlineFueled?_typeSort_rejects_termChild
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifyChildrenInlineFueled?_nonZeroDim_rejects_termChild

-- ─── V2-SPIKE-2: v1<->v2 agreement spike (seed variable) ────────────
-- Discharges Plan SPIKE-2: prove the v1 and v2 dim-erased existential
-- ingresses agree on the seed-variable fixture (var 0 at scope 1)
-- end-to-end.  Per the plan: "If it needs more than injection/subst/▸,
-- switch the bridge to compare post-erasure rawCellCodes rather than
-- dependent cells."
--
-- The shipped spike avoids the rawCellCode escape hatch entirely:
-- both ingresses agree on .cellSort and .cellDimension by direct
-- rfl-evaluation.  No injection/subst/Eq.rec needed; the certified-
-- result existential's data fields are observable without unpacking
-- the dependent cell inside.
--
-- The spike validates that the bridge architecture (V2-bridge.*) is
-- feasible: v1 and v2 don't disagree on what the certifier observes
-- for the seed variable; the bridge work becomes mechanical
-- translation rather than semantic reconciliation.
--
-- Three agreement theorems:
--   * sort_agree     -- v1 sort projection = v2 sort projection
--   * sort_term      -- both produce specifically some .term
--   * dim_zero       -- both produce cellDimension 0
--
-- Each closes by rfl (the certifiers are pure computations; concrete
-- inputs reduce to definite Except.ok values).  The dim_zero theorem
-- uses full Except enumeration (Ok + Error) rather than wildcard to
-- avoid propext leakage through match equation lemmas.
--
-- Forward-compat: per-fixture agreement extended to all 15 V2
-- coverage fixtures ships at V2-bridge.4 once a translation function
-- (V2-bridge.1/.2) exists.
-- (V1SeedVariable bridge gates removed with v1 retirement.)

-- ─── V2-L1.11: TotalityClass per Generator (Turing boundary) ────────
-- Per polycell.md §11.7.2: every generator carries a Turing-boundary
-- classification that the certifier will (in a future V2-L1.11.B
-- extension) enforce through child-sort constraints.
--
-- Three TotalityClass ctors (suffixed -Class to avoid Std.Total /
-- Lean `partial` keyword conflicts):
--   * totalClass      — always terminates (SN + CR + SR + decidable
--                       Conv hold)
--   * productiveClass — non-terminating but every observation
--                       terminates (codata, reactive systems)
--   * partialClass    — may diverge (general recursion / fixed
--                       point)
--
-- Classification (current, conservative):
--   * partial (2):  gen_natRec (general recursion vs natElim's
--                   primitive), gen_fixedPoint
--   * productive (2):  gen_codataUnfold (stream constructor),
--                      gen_polyNu (greatest fixpoint)
--   * total (190):  all other generators
--
-- Architectural pattern: list-based exclusion via partialGenerators
-- + productiveGenerators (same as V2-fix-4's coreFxExcluded).
-- Avoids the 194-arm match that would either be repetitive (190
-- arms returning .totalClass) or leak propext via Lean's
-- match-equation-lemma path for inductives >100 ctors.
--
-- @[reducible] on totalityClass makes the witness theorems close
-- by rfl: list-membership on a decidable-equality inductive reduces
-- definitionally.  Forward-compat: adding a new partial /
-- productive generator is a list-append, not a 194-arm rewrite.
--
-- Eight witness theorems pin behavior on representative generators
-- across all three classes (gen_var/unit/natElim/codataDest = total,
-- gen_natRec/fixedPoint = partial, gen_codataUnfold/polyNu =
-- productive).
--
-- Forward-compat: V2-L1.11.B (certifier-side enforcement) will
-- extend reconcileChild to check per-child TotalityClass against
-- parent.  That's where this classification becomes load-bearing
-- for the SN/CR/SR/decidable-Conv quartet's structural induction.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.TotalityClass
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.partialGenerators
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.productiveGenerators
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.totalityClass
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_var_total
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_unit_total
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_natElim_total
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_codataDest_total
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_natRec_partial
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_fixedPoint_partial
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_codataUnfold_productive
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.gen_polyNu_productive

-- ─── V2-L1.12: ConsistencyStrength + monotonicity (Gödel's ceiling)
-- Per polycell.md §11.7.1: every profile's certificate carries a
-- ConsistencyStrength TAG that is a LOWER BOUND on what the profile
-- can prove.  ProfileExtensions must be MONOTONE in strength
-- (extending can never DECREASE consistency strength).
--
-- Six-tier inductive following the strength tower:
--   * finitistic     — PRA / bounded arithmetic
--   * predicative    — PA / predicative analysis
--   * impredicative  — Zermelo / power set
--   * inaccessible   — ZFC + inaccessible cardinal
--   * mahlo          — ZFC + Mahlo cardinal
--   * custom n       — user-declared (Nat tag), ordinally above mahlo
--
-- Decidable LE via toRank : ConsistencyStrength -> Nat + Nat.decLe.
-- Seven witness theorems pin the monotonic chain (finitistic <
-- predicative < impredicative < inaccessible < mahlo < custom 0 <
-- custom 1), plus one antisymmetry (¬ predicative ≤ finitistic).
--
-- Why Nat tag instead of Lean.Name: keeps v2 substrate
-- elaborator-independent (no Lean.Name import dragging the
-- elaborator into the audit tree).  Operationally sufficient for
-- monotonicity comparison — a Lean-level proof obligation can map
-- any Name to a fresh Nat at admission time.
--
-- @[reducible] on toRank / le makes every concrete comparison
-- close by `decide`.  The Nat encoding is the cross-verifier ABI:
-- the FX0-PolyCell external verifier (FX0-PC.2+) reads the same
-- Nat tag and applies the same numeric comparison.
--
-- Forward-compat: V2-L1.12 phase B integrates strengthBefore /
-- strengthAfter / strengthMonotone fields into ProfileExtension
-- (Foundation/PolyCell/Extension/ProfileExtension.lean).  Phase A
-- (this commit) ships the OBSERVATIONAL layer; phase B threads it
-- through the existing ProfileExtension calculus.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ConsistencyStrength
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ConsistencyStrength.toRank
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ConsistencyStrength.le
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.finitistic_le_predicative
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.predicative_le_impredicative
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.impredicative_le_inaccessible
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inaccessible_le_mahlo
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.mahlo_le_custom_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.custom_zero_le_custom_one
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.not_predicative_le_finitistic

-- ─── V2-L1.13: SiteOpenness + compatibility (open/closed spectrum) ──
-- Per polycell.md §11.7.3: every profile carries a SiteOpenness tag
-- indicating how open it is to external content.  ProfileExtensions
-- must satisfy opennessCompatible: extension.openness <= base.openness
-- (extensions cannot make a base profile MORE open).
--
-- Four-tier inductive over the openness tower:
--   * sealed     -- no extensions admitted; strongest internal
--                   reasoning (full quartet provable).
--   * extensible -- extensions via ProfileExtension admission contract
--                   (fxProfile default).
--   * reflective -- extensions + Era R ReflTerm self-reference.
--   * oracle     -- external oracle calls with explicit trust
--                   boundaries.
--
-- Decidable LE via toRank: SiteOpenness -> Nat + Nat.decLe.
-- Five witness theorems pin the chain (sealed < extensible <
-- reflective < oracle), plus two antisymmetry cases.
--
-- Note opposite-direction monotonicity from ConsistencyStrength:
--   * Consistency: extensions can only INCREASE strength.
--   * Openness:    extensions can only PRESERVE or NARROW openness.
-- Both disciplines reflect different concerns (strength
-- = lower bound on provability; openness = upper bound on
-- extensibility).
--
-- Pattern: same Nat-rank + Decidable LE shape as V2-L1.12, completing
-- the per-profile-metadata triplet (TotalityClass for generators,
-- ConsistencyStrength + SiteOpenness for profiles).
--
-- Forward-compat: V2-L1.13 phase B integrates openness +
-- opennessCompatible fields into ProfileExtension, plus a separate
-- well-formedness check enforcing "sealed admits no extensions"
-- (the inequality alone allows sealed <= sealed; the semantic rule
-- forbids any extension on a sealed base).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.SiteOpenness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.SiteOpenness.toRank
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.SiteOpenness.le
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.sealed_le_extensible
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.extensible_le_reflective
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.reflective_le_oracle
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.not_extensible_le_sealed
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.not_oracle_le_reflective

-- ─── V2-L2.13 phase A: rename-equivariance (de Bruijn trap) ─────────
-- Per polycell.md §11.6.3: the certifier must be rename-equivariant
-- (renaming a well-formed term yields a well-formed term).
-- Off-by-one in the lift-by-shift vs scope+shift creates a silent
-- de Bruijn bug -- passes on closed terms, fails on open terms.
--
-- Phase A ships FIXTURE-LEVEL witnesses on 4 representative fixtures
-- from the V2-fix-5 coverage suite:
--   * unitTermRaw (closed term, scope 0 -> scope 1)
--   * varZeroRaw (free variable, scope 1 -> scope 2; CRITICAL --
--                 tests the Fin payload index shift)
--   * pairUnitsRaw (spine-recursion, scope 0 -> scope 1)
--   * identityUnitCellRaw (cell-layer .identityCell arm)
--
-- For each: the renamed fixture certifies at the SAME sort
-- (.term) as the original.  Plus one cross-comparison agreement
-- theorem witnessing the equation form of rename-equivariance.
--
-- Each closes by rfl.  The varZero case in particular is the
-- LOAD-BEARING regression sentinel: if fold's lift-by-shift
-- went off-by-one in Fin.succ propagation, the Fin payload
-- mismatch would fail the certification's payload-evidence step,
-- breaking this fixture.
--
-- Phase B (deferred): the universally-quantified structural
-- theorem requires induction over RawTerm + fold + threading
-- through admission + payload-evidence + spine-recursion.
-- Substantive metatheory cascade, real proof work.  Phase A
-- establishes the EMPIRICAL baseline + naming convention.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.unitRenamedToScope1
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.varZeroRenamedToScope2
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.pairUnitsRenamedToScope1
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.identityUnitCellRenamedToScope1
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_unitRaw_renamed_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_varZeroRaw_renamed_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_pairUnitsRaw_renamed_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_identityUnitCellRaw_renamed_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.rename_equiv_unitTerm_sort_agree

-- ─── V2-L3.1 phase A+B+C-1/2/3/4a: Step (beta + cong + 11 iota) ──────
-- Per polycell.md §11.6.1: subject reduction on the v2 substrate
-- requires a Step relation + a theorem that Step preserves
-- certifier acceptance.
--
-- Phase A shipped beta + the identity-lambda smoke.
-- Phase B added the UNIFORM congruence rule via mutual
-- Step + StepChildren.  ONE cong rule covers all 194 generators.
-- Phase C step 1 added branch-selection iota for boolElim.
-- Phase C step 2 added content-projection iota for fst/snd on pair.
-- Phase C step 3 added base-case projection iota for nat/list/
-- option base ctors (natZero, listNil, optionNone).
-- Phase C step 4a (THIS batch) introduces the THIRD iota SHAPE:
-- 1-arg app-chain build for optionSome/eitherInl/eitherInr step
-- ctors.  Reduct is `app branch wrappedValue` (not just `branch`).
-- The Church-encoding payoff: iota recognizes the constructor tag;
-- beta does the variable binding in a SUBSEQUENT reduction step.
--
-- Three iota SHAPES now demonstrated across the standard
-- inductive types:
--   * branch-selection (bool / nat / list / option base cases)
--   * content-projection (pair components)
--   * 1-arg app-chain build (optionSome / eitherInl / eitherInr)
--
-- Thirteen smokes pin operational behavior:
--   identity_lam_applied_to_unit     -- Step.beta on β-redex
--   cong_lam_body_beta               -- Step.cong + StepChildren.here
--   iotaBoolTrue_selects_then        -- bool true selects then
--   iotaBoolFalse_selects_else       -- bool false selects else
--   iotaFstPair_projects_first       -- fst pair projects first
--   iotaSndPair_projects_second      -- snd pair projects second
--   iotaNatElimZero_selects_zero     -- natElim zero selects zero
--   iotaNatRecZero_selects_zero      -- natRec zero selects zero
--   iotaListElimNil_selects_nil      -- listElim nil selects nil
--   iotaOptionMatchNone_selects_none -- optionMatch none selects none
--   iotaOptionMatchSome_builds_app   -- optionMatch some → app
--   iotaEitherMatchInl_builds_app    -- eitherMatch inl → app
--   iotaEitherMatchInr_builds_app    -- eitherMatch inr → app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.identity_lam_applied_to_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.cong_lam_body_beta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaBoolTrue_selects_then
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaBoolFalse_selects_else
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaFstPair_projects_first
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaSndPair_projects_second
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaNatElimZero_selects_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaNatRecZero_selects_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaListElimNil_selects_nil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaOptionMatchNone_selects_none
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaOptionMatchSome_builds_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEitherMatchInl_builds_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEitherMatchInr_builds_app
-- Phase C step 4b: 2-arg app-chain WITH RECURSIVE CALL for
-- natElim/natRec on natSucc.  Reduct is the nested
--   app (app succBranch predecessor) (eliminator predecessor ...)
-- where the recursive call to the same eliminator appears in the
-- reduct as a syntactic sub-term -- this is the SHAPE that gives
-- induction principles their power.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaNatElimSucc_builds_nested_app
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaNatRecSucc_builds_nested_app
-- Phase C step 4c: 3-arg app-chain WITH RECURSIVE CALL for
-- listElim on listCons.  Reduct is the triple-nested
--   app (app (app consBranch head) tail) (listElim tail nil cons)
-- -- one curried argument per cons payload piece (head + tail)
-- plus the recursive call.  Deepest app-chain nesting in the v2
-- iota suite.  All FIVE iota shapes now saturated:
--   branch-selection, content-projection, 1-arg app-chain,
--   2-arg app-chain with recursion, 3-arg app-chain with recursion.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaListElimCons_builds_triple_app
-- Phase C step 5: iota for identity-type elimination.
-- gen_idJ and gen_idStrictRec both have arity 2 (baseCase,
-- witness) -- the motive and dependent-elimination semantics live
-- in the PROFILE layer, not the substrate.  So idJ on refl is
-- SHAPE-1 (pure projection): discard the refl witness, return
-- the base case.  Same iota shape as iotaBoolTrue, applied to
-- the identity-type eliminators.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaIdJRefl_selects_base
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaIdStrictRecRefl_selects_base

-- Eta-M8b: raw structural eta as a sibling relation to beta+iota Step.
-- Clock and parametricity eta slots are intentionally absent here until
-- their Phase Z7/Z8 generators are added to the current Generator enum.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.newestVar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaPairSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaPathLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaModIntroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaGlueIntroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.mapStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.etaLam_weakened_function_strengthens
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.etaLam_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.etaPair_pair_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.etaPathLam_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.etaModIntro_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.etaGlueIntro_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.single
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.trans_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.mapStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.single
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.ofStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.ofEta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.trans_compose

-- Eta-M8c: structural eta subject-reduction arms for current generators.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByEtaPair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByEtaModIntro
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByEtaGlueIntro
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.certifiesBeforeWeakening
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByEtaLam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.HasCertifiedCellDim0.preservedByEtaPathLam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.preservesShape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEta.mapStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEta.preservesShape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.preservesShape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.mapStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.preservesShape
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.ofStepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.ofEtaStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CdLemmaStatementBetaEta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CdLemmaStatementStepEta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CdLemmaStatementEtaStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.ofReductsEqual
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.sameStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.swap
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.ofStepPairJoin
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.ofCdLemmaForStepSteps
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPairFirstCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPairSecondCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPairFirstProjectionIota
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPairSecondProjectionIota
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPairLeftStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPairRightStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaModIntroCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaGlueIntroFirstCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaGlueIntroSecondCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaModIntroLeftStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaModIntroRightStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaGlueIntroLeftStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaGlueIntroRightStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_weaken_then_singleton_newest_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_lam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_eq_lam_implies_source_lam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_lift_weaken_newestVar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamBodyBeta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamFunctionCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPathLamFunctionCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamStrengthenedFunctionCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPathLamStrengthenedFunctionCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamStrengthenedFunctionCongFromUnderStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPathLamStrengthenedFunctionCongFromUnderStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamArbitraryUnderBinderCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPathLamArbitraryUnderBinderCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamLeftStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaLamRightStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPathLamLeftStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.etaPathLamRightStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.cd_lemma_step_eta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.cd_lemma_eta_step
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaLamSource_injective
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaPairSource_injective
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaPathLamSource_injective
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaModIntroSource_injective
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.etaGlueIntroSource_injective
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.from_etaLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.from_etaPairSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.from_etaPathLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.from_etaModIntroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.from_etaGlueIntroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.deterministic
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.CdLemmaStatementEtaEta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.cd_lemma_eta_eta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.BetaEtaPairJoin.cd_lemma_betaEta

-- Eta-M8h partial: conditional Newman bridge for beta+iota+eta.
-- This does not claim global SN; it consumes a future
-- `Step.betaEtaStar.HasStrongNormalization` witness.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaSuccessor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.Join
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.HasConfluence
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.IsStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.HasStrongNormalization
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.localJoin_of_cdLemmaBetaEta
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.joinStepWithReflRight
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.joinStepWithSingleRight
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.confluence_of_localJoin_and_accessible
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.confluence_of_strongNormalization

-- Eta-M8h partial: eta-only size decrease and accessibility.
-- The beta+iota-to-betaEta SN transfer remains blocked by #258.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.size_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.size_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.size_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.size_decreases
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaSuccessor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.IsStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.HasStrongNormalization
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.etaSuccessor_wellFounded
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.hasStrongNormalization
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.etaLam_isStronglyNormalizing_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.etaPair_isStronglyNormalizing_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.etaPathLam_isStronglyNormalizing_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.etaModIntro_isStronglyNormalizing_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.etaGlueIntro_isStronglyNormalizing_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.all
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.sourceGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.hasBetaSourceGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.all_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.sourceGenerator_etaLam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.sourceGenerator_etaPair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.sourceGenerator_etaPathLam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.sourceGenerator_etaModIntro
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.sourceGenerator_etaGlueIntro
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.EtaStepKind.currentEtaRoots_doNotShareBetaSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.all
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.toRootStepKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.sourceGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.all_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.all_maps_to_root_iotas
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.all_sourceGenerators
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderStatus
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderStatus.isCovered
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderStatus.insideBinderDiamond_isCovered
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderCoverage
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderCoverage.rowForIotaKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderCoverage.isComplete
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaInsideBinderCoverage.rowForIotaKind_isComplete
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.etaLamCoverageRows
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.etaLamCoverageComplete
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.etaLamCoverageRows_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.etaLamCoverageComplete_eq_true
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.boolTrue_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.boolFalse_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.fstPair_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.sndPair_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.natElimZero_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.natRecZero_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.listElimNil_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.optionMatchNone_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.optionMatchSome_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.eitherMatchInl_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.eitherMatchInr_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.natElimSucc_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.natRecSucc_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.listElimCons_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.idJRefl_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaRootKind.idStrictRecRefl_etaLam_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_weakened_step
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_inside_etaLam_join
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_etaLam_source_join
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_inside_binder_complete
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_inside_binder_complete_eq_true
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.all
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.phaseMilestone
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.etaKindOption
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.introGeneratorOption
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.eliminatorGeneratorOption
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.hasCurrentStepIota
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.all_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.phaseMilestones
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.currentStepIotas_absent
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripBlocker
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaDoubleStripStatus
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaDoubleStripStatus.isReserved
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaDoubleStripStatus.reserved_isReserved
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStrip
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStrip.blockerForKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStrip.rowForKind
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStrip.isCompleteReservedRow
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStrip.rowForKind_isCompleteReservedRow
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.reservedRows
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.reservedRowsComplete
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.reservedRows_length
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.reservedRowsComplete_eq_true
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.modal_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.path_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.clock_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.parametricity_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.IotaEtaReservedDoubleStripKind.glue_status
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_reserved_doublestrips_complete
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.iotaEta_reserved_doublestrips_complete_eq_true

-- ─── V2-L3.1 phase C step 6 prep: Step inversion lemmas ──────────────
-- Foundational inversion building blocks the SR theorem's cong arm
-- will consume.  Built bottom-up: empty-spine → leaf-ctors →
-- specific-redex inversions (deferred to later atomic iterations).
--
-- StepChildren.no_step_at_empty_spine: foundational uninhabitedness
--   -- StepChildren over .childNil has no inhabitants since both
--   `here` and `there` constructors pattern-match on `.childCons`.
--
-- Step.no_step_from_unit: leaf-term inversion
--   -- the unit term (gen_unit + empty spine) admits no Step.  17
--   ctors auto-discharge via generator mismatch; cong reduces to
--   no_step_at_empty_spine via the empty children spine.
--
-- Leaf inversion suite: every 0-arity ctor with empty spine
-- admits no Step.  Same one-line proof shape as no_step_from_unit
-- because the cong arm reduces uniformly to no_step_at_empty_spine.
-- Boolean leaves (true/false), nat zero, list nil, option none,
-- plus variable references (universal in the de-Bruijn index).
--
-- Future inversions: non-leaf terms (boolElim, lam, app) -- each
-- characterizes which Step ctor could have fired given the source
-- shape.  Built incrementally as the SR cascade requires them.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildren.no_step_at_empty_spine
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_boolTrue
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_boolFalse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_natZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_listNil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_optionNone
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.no_step_from_var
-- Value-constructor inversions: characterize Step (V c) target as
-- target = V c' with Step c c'.  Pattern: value ctors with non-leaf
-- children spines have ONLY cong as their reduction path; the cong
-- arm's StepChildren must be .here (since .there over empty tail is
-- uninhabited).  Result type is existential (NOT False), so these
-- lemmas sit in PolyCell.Core without tripping the False-budget.
--
-- 1-child value ctors covered: lam (body at scope+1), natSucc,
-- pathLam, diffLambda, optionSome, eitherInl/Inr, refl.  All share the same proof
-- structure (cases reduction → cases childStep → here-arm extract).
-- 2-child cases (pair, listCons) deferred to next iteration --
-- they need both here and there arms since the second child can
-- also Step.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_lam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_pathLam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_diffLambda
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_natSucc
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_optionSome
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_eitherInl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_eitherInr
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_refl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_modIntro
-- 2-child value/type-code inversions.  Disjunctive
-- conclusion (first child stepped OR second child stepped), because
-- the cong arm's StepChildren can fire at the head (.here) or
-- descend into the tail (.there then inner .here).  Three inner
-- cases total: head-step, tail-step-via-there-then-here, and
-- absurd-no-spine for there-then-there.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_pair
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_listCons
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_glueIntro
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_arrowCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_productCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_sumCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_eitherCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_equivCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_piTyCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_sigmaTyCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_polyFunctor
-- Eliminator inversions (simplest case: 1-iota + cong, 1-child
-- source spine).  `fst` and `snd` admit a 2-way disjunction:
-- either iota fires (source's child is a literal pair, target is
-- one of the components) OR cong fires (the child stepped to
-- something).  These introduce the iota-arm of the eliminator
-- inversion pattern; more complex eliminators (boolElim, natElim,
-- listElim) will accumulate more iota arms.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_fst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_snd
-- Multi-iota eliminator inversion: from_boolElim.  5-way
-- disjunction: 2 iota arms (boolTrue/boolFalse scrutinee) + 3 cong
-- positions (scrutinee/then/else child stepped).  The cong arm
-- descends through nested here/there cases on StepChildren to
-- reach each child position; the inner-most there reaches childNil
-- which is uninhabited.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_boolElim
-- Multi-iota eliminator inversions with COMPLEX-IOTA disjuncts:
-- from_natElim, from_natRec.  Same 5-way disjunction structure
-- as from_boolElim, but the Succ-iota arm's target is a nested
-- app (the recursive call) requiring an existential witness for
-- the predecessor.  Pattern: `Or.inr (Or.inl ⟨_, rfl, rfl⟩)` lets
-- Lean infer the predecessor from the unified target.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_natElim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_natRec
-- Final 5-way eliminator inversions: listElim, optionMatch,
-- eitherMatch.  All apply established templates -- the cong-arm
-- proof shape is identical to from_boolElim; the iota arms vary
-- in existential count (Cons needs 2, Some/Inl/Inr need 1 each,
-- Nil/None are 0).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_listElim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_optionMatch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_eitherMatch
-- Final inversions completing the suite:
-- * from_idJ / from_idStrictRec: 3-way disjunction (1 refl iota
--   + 2 cong positions over 2-child spine).
-- * from_app: 3-way disjunction (1 beta + 2 cong positions).  THE
--   LOAD-BEARING INVERSION for SR's beta arm -- characterizes
--   "function child is a lambda" with an existential for the
--   lambda body that SR's beta arm threads through V2-L2.12's
--   subst boundary lemma.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_idJ
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_idStrictRec
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.from_app

-- ─── V2-L3.1 phase C step 6: Certified predicate for SR ─────────────
-- The term-level wrapper predicate the SR theorem states about.
-- A raw term is Certified when wrapping it as a dim-0 cell via
-- termBase yields an accepted existential-certifier result.
-- Profile-parametric; bridges Step (term-level relation) to the
-- certifier (cell-level function).  Three trivial helpers
-- (intro/exists_result/ofExistentialOk) provide a stable API so
-- consumers don't need to know Certified unfolds to ∃.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.intro
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.exists_result
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.ofExistentialOk
-- Inhabitation smokes: concrete fixtures demonstrating Certified
-- is non-vacuous.  Both close by ⟨_, rfl⟩ -- the certifier reduces
-- transparently on basic fixtures (unit, var), and Lean's
-- elaborator infers the existential witness from the rfl proof.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.unit_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.varZero_at_scope_one
-- Inhabitation smokes for the standard 0-arity value ctors --
-- bool/nat/list/option base cases.  Each lifts a V2-L1cert.15
-- coverage fixture to the Certified level via ⟨_, rfl⟩.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.boolTrue_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.boolFalse_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.natZero_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.listNil_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.optionNone_at_scope_zero
-- Composite fixture smokes: spine recursion through arity-1 and
-- arity-2 generators (natSucc, optionSome, eitherInl, pair, listCons).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.natSuccZero_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.optionSomeUnit_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.eitherInlUnit_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.pairUnits_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.listConsUnit_at_scope_zero
-- Binder + eliminator fixture smokes: lam, app (beta-redex shape),
-- fst (iota-redex shape), boolElim (3-child eliminator iota-redex).
-- All close by ⟨_, rfl⟩ -- the certifier is UNIFORMLY transparent
-- across the standard MLTT generator family (verified empirically
-- via probe before shipping).  These shapes matter for SR: beta-
-- redex for SR's beta arm, iota-redex for SR's iota arms.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.lamUnit_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.appBetaRedex_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.fstPairUnits_at_scope_zero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Certified.boolElimTrue_at_scope_zero

-- ─── V2-L3.2 phase A: StepStar (reflexive-transitive closure) ───────
-- Reflexive-transitive closure of Step in LEFT-EXTENSION form:
-- a StepStar chain is either .refl (length 0) or a Step followed
-- by a shorter StepStar chain (.trans).
--
-- This is the foundational L3 building block.  Every L3 theorem
-- that talks about "eventually reaches" or "normal-form reduct"
-- routes through StepStar:
--   * SR (V2-L3.1.C): "Step preserves typing, so StepStar does"
--   * Confluence (V2-L3.2): the Church-Rosser theorem.
--   * SN (V2-L3.3): "every term has a StepStar normal form"
--   * Conv (V2-L3.4): defined as the symmetric closure of StepStar
--
-- Two smokes pin operational behavior:
--   refl_unit_smoke      -- reflexivity instance, .refl inhabited
--   identity_lam_beta_unit -- Step.beta + StepStar.refl reaches
--                            unit from the identity-lambda redex
--                            via the standard single-Step pattern
--
-- Phase B (deferred): trans_compose / single / transLast closure
-- properties.  Phase C (V2-L3.2 proper): the diamond / Church-Rosser
-- theorem requiring Tait-Martin-Löf parallel reduction.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.refl_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.identity_lam_beta_unit

-- ─── V2-L3.2 phase B: StepStar closure properties ───────────────────
-- Three closure properties that make StepStar a real reflexive-
-- transitive closure programmatically:
--
--   single        -- Step a b → StepStar a b (length-1 embedding)
--   trans_compose -- StepStar a b → StepStar b c → StepStar a c
--                    (full transitivity; load-bearing for Conv)
--   transLast     -- StepStar a b → Step b c → StepStar a c
--                    (right-extension; symmetric to .trans's
--                    left-extension)
--
-- single is two-ctor construction (Step + refl).
-- trans_compose is induction on the first chain (refl case returns
-- secondChain; trans case re-prepends head step to the recursive
-- composition).
-- transLast is derived (trans_compose + single).
--
-- All three pass #assert_no_axioms — pure structural recursion,
-- no propext leakage.  These are the load-bearing infrastructure
-- for V2-L3.4 (decidable Conv ★ MILESTONE A) and V2-L3.2 phase C
-- (Church-Rosser).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.single
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.trans_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.transLast
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appFunction
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appArgument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.lamBody
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.Join
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.HasConfluence
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.HasStrip
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.StepSuccessor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.IsStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.HasStrongNormalization
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isStronglyNormalizing_of_noStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStepChildren_childNil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_var
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_unit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_boolTrue
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_boolFalse
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_natZero
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_listNil
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_optionNone
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_universeCode
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_interval0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_interval1
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_circleBase
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_circleLoop
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_qubit
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.noStep_hyperreal
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.var_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.unit_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.boolTrue_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.boolFalse_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.natZero_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.listNil_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.optionNone_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.universeCode_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.interval0_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.interval1_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.circleBase_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.circleLoop_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.qubit_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.hyperreal_isStronglyNormalizing
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isStronglyNormalizing_of_oneChildCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isStronglyNormalizing_of_twoChildCong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.lam_isStronglyNormalizing_of_body
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.pathLam_isStronglyNormalizing_of_body
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.diffLambda_isStronglyNormalizing_of_body
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.natSucc_isStronglyNormalizing_of_predecessor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.optionSome_isStronglyNormalizing_of_value
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.eitherInl_isStronglyNormalizing_of_value
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.eitherInr_isStronglyNormalizing_of_value
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.refl_isStronglyNormalizing_of_witness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.modIntro_isStronglyNormalizing_of_value
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.pair_isStronglyNormalizing_of_components
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.listCons_isStronglyNormalizing_of_head_tail
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.glueIntro_isStronglyNormalizing_of_components
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.arrowCode_isStronglyNormalizing_of_domain_codomain
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.productCode_isStronglyNormalizing_of_left_right
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.sumCode_isStronglyNormalizing_of_left_right
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.eitherCode_isStronglyNormalizing_of_left_right
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.equivCode_isStronglyNormalizing_of_source_target
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.piTyCode_isStronglyNormalizing_of_domain_codomain
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.sigmaTyCode_isStronglyNormalizing_of_domain_codomain
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.polyFunctor_isStronglyNormalizing_of_position_type_family
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.IsNeutralApplicationHead
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isNeutralApplicationHead_not_lam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isNeutralApplicationHead_step
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.app_isStronglyNormalizing_of_neutral_head_arg
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.app_isStronglyNormalizing_of_neutral_application_head_arg
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.IsVariableHeadedSpine
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isVariableHeadedSpine_not_lam
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isVariableHeadedSpine_step
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.app_isStronglyNormalizing_of_variable_headed_spine_arg
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.applyRawArgument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.applyRawArgumentsFrom
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_one_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_two_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_three_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.variableHeadedSpineTermFrom
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.variableHeadedSpineTerm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.AllStronglyNormalizingArguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.variableHeadedSpineTermFrom_isVariableHeadedSpine
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.variableHeadedSpineTerm_isVariableHeadedSpine
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.variableHeadedSpineTermFrom_isStronglyNormalizing_of_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.variableHeadedSpineTerm_isStronglyNormalizing_of_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.app_isStronglyNormalizing_of_normal_nonlambda_head_arg
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appVar_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appVarSpine2_isStronglyNormalizing_of_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appVarSpine3_isStronglyNormalizing_of_arguments
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLam_isStronglyNormalizing_of_normal_body_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLam_isStronglyNormalizing_of_normal_body_constant_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamVarZero_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamVarSucc_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamUnit_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamBoolTrue_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamBoolFalse_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamNatZero_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamListNil_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamOptionNone_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamUniverseCode_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamInterval0_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamInterval1_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamCircleBase_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamCircleLoop_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamQubit_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamHyperreal_isStronglyNormalizing_of_argument
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamNatSucc_isStronglyNormalizing_of_predecessor_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamOptionSome_isStronglyNormalizing_of_value_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamEitherInl_isStronglyNormalizing_of_value_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamEitherInr_isStronglyNormalizing_of_value_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamRefl_isStronglyNormalizing_of_witness_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamModIntro_isStronglyNormalizing_of_value_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamTwoChildSecondBinderBody_isStronglyNormalizing_of_children_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamPair_isStronglyNormalizing_of_components_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamListCons_isStronglyNormalizing_of_head_tail_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamGlueIntro_isStronglyNormalizing_of_components_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamArrowCode_isStronglyNormalizing_of_domain_codomain_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamProductCode_isStronglyNormalizing_of_left_right_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamSumCode_isStronglyNormalizing_of_left_right_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamEitherCode_isStronglyNormalizing_of_left_right_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamEquivCode_isStronglyNormalizing_of_source_target_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamPiTyCode_isStronglyNormalizing_of_domain_codomain_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamSigmaTyCode_isStronglyNormalizing_of_domain_codomain_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamPolyFunctor_isStronglyNormalizing_of_position_type_family_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamPathLam_isStronglyNormalizing_of_body_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamLam_isStronglyNormalizing_of_body_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLamDiffLambda_isStronglyNormalizing_of_body_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.appLam_isStronglyNormalizing_of_body_argument_contractum
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.fstPair_isStronglyNormalizing_of_components
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.sndPair_isStronglyNormalizing_of_components
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.boolElimTrue_isStronglyNormalizing_of_branches
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.boolElimFalse_isStronglyNormalizing_of_branches
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.idJRefl_isStronglyNormalizing_of_base_witness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.idStrictRecRefl_isStronglyNormalizing_of_base_witness
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.isStronglyNormalizing_of_twoBranchProjectionRedex
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.natElimZero_isStronglyNormalizing_of_branches
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.natRecZero_isStronglyNormalizing_of_branches
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.natElimSucc_isStronglyNormalizing_of_neutral_succBranch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.natRecSucc_isStronglyNormalizing_of_neutral_succBranch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.listElimNil_isStronglyNormalizing_of_branches
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.listElimCons_isStronglyNormalizing_of_neutral_consBranch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.optionMatchNone_isStronglyNormalizing_of_branches
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.optionMatchSome_isStronglyNormalizing_of_neutral_someBranch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.eitherMatchInl_isStronglyNormalizing_of_neutral_leftBranch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.eitherMatchInr_isStronglyNormalizing_of_neutral_rightBranch
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.localJoin_of_cdLemma
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.joinStepWithReflRight
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.joinStepWithSingleRight
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.confluence_of_localJoin_and_accessible
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.confluence_of_strongNormalization
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.confluence_of_strip
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.refl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.sym
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.fromStepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.fromStep
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.trans_of_confluence
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.trans_of_middle_accessible
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.trans_of_strip
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.trans_of_strongNormalization

-- M6 beta-replay support: one-step reduction commutes with raw
-- substitution, using `subst0_subst_commute` in the beta arm.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildren.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_eq_subst_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.weaken_substTarget
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildren.weaken_substTarget
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.preserves_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.weaken_strengthenTarget
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.PointwiseStepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_pointwiseStepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawTermSubst_pointwiseStepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenStar.trans_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenStar.here
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildrenStar.there
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.ofChildrenStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_pointwise_stepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_pointwise_stepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.subst0Body
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.subst0Argument

-- M-substrate-1 (#365): one-step, child-spine, closure, and eta
-- reductions commute with raw renaming.  The beta+iota proofs factor
-- through `Step.subst`; eta adds explicit eta-source shape lemmas for
-- binder and structural eta sources.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_lift_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_lift_newestVar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_etaLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_etaPairSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_etaPathLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_etaModIntroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_etaGlueIntroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepChildren.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.eta.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.etaStar.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEta.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Step.betaEtaStar.rename

-- ─── M-substrate-4 (#368): StepStarN counted parallel of StepStar ───
-- Nat-indexed counted variant of StepStar.  Since StepStar is
-- Prop-valued, a direct StepStar.length : StepStar a b → Nat function
-- is impossible without large elimination from Prop (banned without
-- Classical.choice / propext).  The counted variant exposes the chain
-- length as an explicit Nat index that downstream complexity / NbE-
-- soundness / strip-property work induct on.
--
-- API surface:
--   * StepStarN inductive (reflN + transN)
--   * toStepStar : StepStarN n a b → StepStar a b (forget count)
--   * StepStar.exists_N : StepStar a b → ∃ n, StepStarN n a b
--     (recover count existentially via Prop-to-Prop induction)
--   * single, trans_compose (length-1, length addition)
--   * rename, subst (length-preserving monotonicity)
--   * identity_lam_beta_unit_smoke (concrete fixture)
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN.toStepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStar.exists_N
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN.single
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN.trans_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.StepStarN.identity_lam_beta_unit_smoke

-- ─── M-Conv-cong (#369): generic Conv congruence lifter ─────────────
-- The 5-agent gap audit found ZERO per-generator Conv-cong rules
-- exist (only 3 hand-coded StepStar-level cong helpers for 194
-- generators).  This block ships:
--
--   * ConvChildren: pointwise Conv on a child spine (inductive).
--   * ConvChildren.symm: pointwise symmetry.
--   * ConvChildren.exists_join: bridge to children-level Join via
--     StepChildrenStar.here + .there + .trans_compose.
--   * Conv.ofChildren: ONE generic congruence lifter covering all
--     194 generators (the PolyCell uniformity payoff).
--   * 11 per-generator congruence corollaries (app, lam, pair,
--     fst, snd, natSucc, listCons, optionSome, eitherInl, eitherInr,
--     gen_refl).
--
-- Unblocks M46 #295 ★ Typed SR + M47 #296 typed weakening + M-Conv-
-- subst-rename #370 + M-Conv-equivalence #371 + M55a #364 typed
-- β+η Decidable Conv.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ConvChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ConvChildren.symm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ConvChildren.exists_join
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.ofChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.app_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.lam_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.pair_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.fst_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.snd_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.natSucc_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.listCons_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.optionSome_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.eitherInl_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.eitherInr_cong
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.gen_refl_cong

-- ─── M-Conv-subst-rename (#370): Conv preservation laws ─────────────
-- Substitution / renaming / weakening / subst0 preservation for the
-- raw `Conv` relation.  Required by M46 #295 ★ Typed SR (cites
-- Conv.subst when traversing typing derivations) and M47 #296 typed
-- weakening (cites Conv.weaken under context extension).
--
-- API:
--   * Conv.subst σ : Conv a b → Conv (subst σ a) (subst σ b)
--   * Conv.rename ρ : Conv a b → Conv (rename ρ a) (rename ρ b)
--   * Conv.weaken : single-binder weakening specialization
--   * Conv.subst0 : two-arg β-redex congruence
--
-- Plus bridging helper:
--   * RawTermSubst.singleton_pointwise_stepStar — promotes a StepStar
--     on the arg to a PointwiseStepStar on the singleton substitutions.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.singleton_pointwise_stepStar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Conv.subst0

-- ─── M11-pre (#372): NbE design choice committed to HYBRID ──────────
-- Resolves the spec/task contradiction surfaced by Agent 3 + Agent 4
-- of the 5-agent gap audit:
--
--   M11 #260 task wording: HOAS ValueTerm semantic domain (Design A).
--   polycell.md §3 P3.6/P3.7: values = NF predicates on RawTerm (B).
--
-- HYBRID commitment:
--   * Raw layer follows polycell vision (Design B): eval = fold,
--     values = NF predicates on RawTerm, quote = identity.
--   * Typed layer with η adds a SEPARATE type-directed readback pass
--     (M15a-e #359-#363), not a new semantic domain.
--
-- This collapses M13 (quote = id) and preserves polycell's "one
-- inductive, one fold" uniformity at the raw layer while still
-- supporting the typed-η requirement at M55a #364.
--
-- M11 #260 / M12 #261 / M13 #262 / M14 #263 task descriptions are
-- updated via TaskUpdate to match.
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.NbEDesignChoice
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.NbEDesign.committed
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.NbEDesign.committed_is_hybrid

-- ─── M12-pre (#373): NbE reduction strategy committed to CBN ────────
-- Resolves the strategy ambiguity Agent 3 surfaced — three reducers
-- in the codebase each use a different strategy (CBN WHNF, CBV iota,
-- structural fold).  Commits to call-by-name (CBN) for M12 NbE eval.
--
-- CBN matches:
--   * The M11-pre #372 hybrid design (eval returns RawTerm in β-NF).
--   * Abel-Coquand-Dybjer 2007 NbE-for-MLTT reference.
--   * FX's effect-tracking discipline (no spurious arg evaluation).
--
-- Memoization (lazy CBN) deferred to M19 #268 STRICT-COMPLEXITY work.
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy.committed
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy.committed_is_cbn
#assert_no_axioms LeanFX2.Foundation.PolyCell.NbE.ReductionStrategy.compatible_with_hybrid_design

-- ─── M-phaseZ-strict-gates (#380): honest phase-Z STRICT ledgers ────
-- 10 honest ledger entries (Z0-Z9) tracking phase-Z STRICT audit
-- gate state — explicitly at .notStarted today, advances as phase-Z
-- work ships.  The summary theorem enforces lockstep between per-
-- gate state values and the aggregate snapshot: when any gate
-- advances, the audit build breaks until the summary is updated to
-- match.
--
-- Pattern: HONEST LEDGERS, not passing placeholder gates.  Each
-- state value is declared explicitly at its current honest level;
-- no `def gate : Bool := true` placeholder that pretends coverage.
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.PhaseZLedgerState
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z0_MOTIVE_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z1_CTX_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z2_CONV_TYPE_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z3_DECIDABLE_CONV_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z4_CUBICAL_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z5_HIT_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z6_IRT_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z7_GUARDED_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z8_MODAL_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_Z9_SMT_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.phaseZ_current_summary
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.phaseZ_notStarted_count
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.phaseZ_fullyShipped_count
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.phaseZ_counts_honest

-- ─── M-strict-axes-CS-TC-SO-DF (#381): cross-cutting STRICT ledger ──
-- 4 honest ledger entries (CS/TC/SO/DF) tracking cross-cutting
-- STRICT audit axes per polycell.md §11.7.5.  Today's snapshot:
--
--   CS scaffoldShipped — ConsistencyStrength.lean ships scaffold.
--   TC scaffoldShipped — GeneratorTotalityClass.lean ships scaffold.
--   SO scaffoldShipped — SiteOpenness.lean ships scaffold.
--   DF notStarted      — DecidabilityStatus not yet implemented.
--
-- Same pattern as M-phaseZ-strict-gates #380: per-axis state values
-- pinned by a summary theorem via rfl-conjunction.  When any axis
-- advances, summary stops elaborating until updated.
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.StrictAxisLedgerState
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_CS_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_TC_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_SO_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.STRICT_DF_state
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.strictAxes_current_summary
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.strictAxes_scaffoldShipped_count
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.strictAxes_notStarted_count
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.strictAxes_fullyShipped_count
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.strictAxes_counts_honest
#assert_no_axioms LeanFX2.Tools.AuditAll.Audit.strictAxes_total_count

-- ─── M-Ty-wf (#383): Ty.size well-foundedness measure ──────────────
-- 25-ctor structural size measure for typed recursion in M15a-e
-- (typed η-long quote) and M9-Tait (Tait reducibility predicate).
--
-- Counts ONLY Ty-substructure (RawTerm payloads / Nat / Fin
-- payloads do not contribute) — the recursion-friendly shape for
-- type-directed traversal.
--
-- Ships: Ty.size (25 arms), Ty.size_pos (25-arm positivity),
-- 23 per-ctor size_lt_X structural-decrease lemmas covering
-- piTy / sigmaTy / arrow / eitherType / equiv / codata / listType /
-- optionType / record / modal / glue / refine / effect / id / path /
-- oeq / idStrict.
#assert_no_axioms LeanFX2.Ty.size
#assert_no_axioms LeanFX2.Ty.size_pos
#assert_no_axioms LeanFX2.Ty.size_lt_piTy_codomain
#assert_no_axioms LeanFX2.Ty.size_lt_piTy_domain
#assert_no_axioms LeanFX2.Ty.size_lt_sigmaTy_second
#assert_no_axioms LeanFX2.Ty.size_lt_sigmaTy_first
#assert_no_axioms LeanFX2.Ty.size_lt_arrow_domain
#assert_no_axioms LeanFX2.Ty.size_lt_arrow_codomain
#assert_no_axioms LeanFX2.Ty.size_lt_eitherType_left
#assert_no_axioms LeanFX2.Ty.size_lt_eitherType_right
#assert_no_axioms LeanFX2.Ty.size_lt_equiv_domain
#assert_no_axioms LeanFX2.Ty.size_lt_equiv_codomain
#assert_no_axioms LeanFX2.Ty.size_lt_codata_state
#assert_no_axioms LeanFX2.Ty.size_lt_codata_output
#assert_no_axioms LeanFX2.Ty.size_lt_listType_element
#assert_no_axioms LeanFX2.Ty.size_lt_optionType_element
#assert_no_axioms LeanFX2.Ty.size_lt_record_singleField
#assert_no_axioms LeanFX2.Ty.size_lt_modal_carrier
#assert_no_axioms LeanFX2.Ty.size_lt_glue_base
#assert_no_axioms LeanFX2.Ty.size_lt_refine_base
#assert_no_axioms LeanFX2.Ty.size_lt_effect_carrier
#assert_no_axioms LeanFX2.Ty.size_lt_id_carrier
#assert_no_axioms LeanFX2.Ty.size_lt_path_carrier
#assert_no_axioms LeanFX2.Ty.size_lt_oeq_carrier
#assert_no_axioms LeanFX2.Ty.size_lt_idStrict_carrier

-- ─── V2-L1cert.12: existential preserves dim (#167) ─────────────────
-- inferRawCellGeneral?_accepted_cellDimension_eq: when the
-- existential wrapper accepts a raw input, the result's stored
-- cellDimension field equals raw.dim.  First of three existential-
-- variant soundness theorems.
--
-- Proof shape: unfold inferRawCellGeneral? + cases on underlying
-- certifyRawCellExact? + injection + subst + rfl.  No omega, no
-- propext, no Classical.
--
-- Rules out the existential wrapper laundering a different dim past
-- the input — the dim it forgot (when going from raw-indexed to
-- existential) is provably the dim it was given.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inferRawCellGeneral?_accepted_cellDimension_eq

-- ─── V2-L1cert.13: existential preserves rawCell HEq (#168) ─────────
-- inferRawCellGeneral?_accepted_rawCell_heq: when the existential
-- wrapper accepts a raw input, the result's stored rawCell field is
-- heterogeneously equal to the input.  Second of three existential-
-- variant soundness theorems.
--
-- Under v2's un-indexed RawCell scope, both sides of the HEq have
-- the same type, so this is technically reducible to Eq.  HEq is
-- shipped for v1 API compatibility and to compose cleanly with #169
-- (the existential _sound theorem chains this HEq with the cert's
-- raw-erasure HEq).
--
-- Proof shape: same 5-step skeleton as #167 (unfold + cases +
-- injection + subst + rfl).  Lean's rfl tactic produces HEq.refl _
-- when the types match definitionally.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inferRawCellGeneral?_accepted_rawCell_heq

-- ─── V2-fix-7: Eq companion for HEq raw-preservation theorem ────────
-- Under v2's un-indexed RawCell scope, both sides of the HEq
-- relation above have the same type (RawCell scope), so the
-- relation collapses to definitional Eq.  The HEq form is kept for
-- v1 API compatibility; the Eq companion ships the tightened form
-- for v2-LOCAL callers (L3 metatheory, NbE, confluence proofs).
--
-- Plus a derivation theorem witnessing that the HEq form follows
-- from the Eq form via heq_of_eq.  In V2-mig phase B (when v1 is
-- retired), the HEq form can be retired in favor of the Eq form
-- via this derivation.
--
-- All three theorems pass #assert_no_axioms.  Proof shape for each:
-- same 5-step skeleton as #168 (unfold + cases + injection + subst
-- + rfl).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inferRawCellGeneral?_accepted_rawCell_eq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inferRawCellGeneral?_accepted_rawCell_heq_of_eq

-- ─── V2-L1cert.14: existential no-laundering keystone (#169) ────────
-- inferRawCellGeneral?_sound: KEYSTONE of the existential-variant
-- soundness trio.  Every cell accepted by the existential wrapper
-- has its certified-cell's raw erasure heterogeneously equal to the
-- input raw.  Closes the NO-LAUNDERING guarantee on the existential
-- ingress.
--
-- Proof: 2-step HEq composition.
--   (1) result.certifiedCell.raw = result.rawCell  by rfl
--       (PolyCell.raw projects the implicit rawCell index, which
--       is result.rawCell by the struct's field type)
--   (2) HEq result.rawCell raw                     from #168
--   (composition) HEq result.certifiedCell.raw raw  via HEq.trans
--
-- Combined with #165 (raw-indexed _sound) and #166 (_compH_rejects),
-- this CLOSES the FULL no-false-positives guarantee on the entire
-- L1cert.4 ingress (raw-indexed + existential).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.inferRawCellGeneral?_sound

-- ─── V2-L1cert.15: positive coverage suite (#170) ───────────────────
-- Per-fixture acceptance theorems demonstrating the certifier DOES
-- accept well-formed fxProfile fixtures with the expected sort.  The
-- DUAL of the soundness tier: where #165-#169 prove the certifier
-- never accepts badly, this layer proves it does accept rightly.
--
-- Initial catalog (2 fixtures):
--   * unitTermRaw — gen_unit (Unit payload, arity 0, sort .term)
--   * varZeroRaw  — gen_var at scope 1 (Fin payload, arity 0, sort .term)
--
-- Plus the certifiedResultSort? helper (sort extractor from Except).
--
-- All theorems close by `rfl`: each fixture's certification chain
-- (fuel → admission → payload evidence → nil-spine → packaging →
-- sort projection) reduces definitionally to the expected sort.
--
-- This layer is intentionally minimal — establishes the pattern; per-
-- generator exhaustive coverage lives in later tasks.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifiedResultSort?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.unitTermRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.varZeroRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_unitTermRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_varZeroRaw_sort

-- ─── V2-fix-5: certifier coverage backfill (2 -> 15 fixtures) ───────
-- Agent 3 of the V2 falsification audit observed that the original
-- coverage suite (2 fixtures: unitTermRaw + varZeroRaw) gated rfl-
-- evaluation of the certifier on only TWO out of 194 generators -
-- insufficient to demonstrate the certifier exercises distinct
-- payload paths across the generator table.
--
-- This commit expands the catalog to 15 fixtures (one cell-layer +
-- 14 termBase fixtures spanning 14 distinct generator ctors), with
-- each fixture audited individually as both data + acceptance theorem
-- (26 new gates = 13 fixtures + 13 acceptance theorems).
--
-- Coverage distribution by arity:
--   * Arity 0 (9 generators):  gen_unit, gen_var, gen_boolTrue,
--     gen_boolFalse, gen_natZero, gen_listNil, gen_optionNone,
--     gen_interval0, gen_interval1
--   * Arity 1 (3 generators):  gen_natSucc, gen_optionSome,
--     gen_eitherInl - exercises 1-element spine recursion
--   * Arity 2 (2 generators):  gen_pair, gen_listCons - exercises
--     2-element spine recursion
--   * Cell layer (1 fixture):  identityCell wrapping termBase -
--     exercises the cell-layer .identityCell dispatch arm
--
-- All fixtures close acceptance by rfl: the certifier is a pure
-- computation, and concrete inputs reduce via admission + payload-
-- evidence + spine recursion + structural packaging to a definite
-- Except.ok value with cellSort = .term.
--
-- 14 of the 194 generators is still small coverage in absolute terms,
-- but each new fixture exercises a DISTINCT payload + child-spine
-- shape, gating the structural reduction chain in a way the original
-- 2-fixture suite did not.  Per-generator exhaustive coverage is
-- deferred to a follow-up (V2-fix-5 phase B if needed).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.boolTrueRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.boolFalseRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.natZeroRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.listNilRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.optionNoneRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.interval0Raw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.interval1Raw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.natSuccZeroRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.optionSomeUnitRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.eitherInlUnitRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.pairUnitsRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.listConsUnitRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Coverage.identityUnitCellRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_boolTrueRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_boolFalseRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_natZeroRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_listNilRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_optionNoneRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_interval0Raw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_interval1Raw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_natSuccZeroRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_optionSomeUnitRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_eitherInlUnitRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_pairUnitsRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_listConsUnitRaw_sort
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.coverage_identityUnitCellRaw_sort

-- ─── V2-L1cert.16: negative-probe suite (#171) ──────────────────────
-- Rejection-side coverage: per-fixture rejection theorems demonstrating
-- the certifier DOES reject malformed fixtures with the EXPECTED
-- rejection reason.  The DUAL of #170's positive coverage and the
-- counterpart to #165-#169's no-laundering soundness.
--
-- Under fxProfile (194 generators admitted), three rejection branches
-- are runtime-reachable from the public ingress:
--   * .unsupportedCompH — every .horizontalComposite _ _ rejects
--   * .badVerticalBoundary — .verticalComposite with first.dim = 0
--   * .wrongSort — checkRawCellAs? with expected != inferred sort
--
-- The remaining 7 rejection variants (.unknownGenerator, .badPayload,
-- .wrongChildShape, .fuelExhausted, .badBoundaryEndpoint,
-- .unsupportedCertification) are forward-compat dead code under
-- fxProfile — exercisable only under restricted-profile test suites.
--
-- All theorems close by `rfl`: each malformed fixture's rejection
-- chain reduces definitionally to the expected `.error <reason>`.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.certifiedResultRejection?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.NegativeProbes.horizontalCompositeUnitRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.NegativeProbes.verticalCompositeUnitRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.negative_horizontalCompositeUnit_rejects_unsupportedCompH
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.negative_verticalCompositeUnit_rejects_badVerticalBoundary
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.negative_unitTerm_as_type_rejects_wrongSort

-- ─── V2-L1cert.17: FX-profile views (#172) ──────────────────────────
-- FX-profile-fixed entry points over the v2 certifier infrastructure:
-- both wrappers ARE the canonical ingress for callers working in the
-- default fxProfile (currently the only profile under v2).
--
-- Two wrappers (each a one-liner delegation):
--   * certifyFXCellExact? — raw-indexed certifier, profile := fxProfile
--   * certifyFXCell?      — existential ingress, profile := fxProfile
--
-- Semantic equivalence to the general API is by definition; ergonomic
-- difference (no profile to thread) is significant for FX-kernel
-- callers.  Soundness theorems are #173, per-fixture FX-profile
-- packages are migration-deferred to V2-mig.4 (#195).
#assert_no_axioms LeanFX2.Foundation.PolyCell.FXProfile.certifyFXCellExact?
#assert_no_axioms LeanFX2.Foundation.PolyCell.FXProfile.certifyFXCell?

-- ─── V2-L1cert.18: FX-profile soundness theorems (#173) ─────────────
-- Four delegating theorems pinning the FX-profile entry points
-- (#172) to the same no-laundering, dim-preservation, and
-- compH-rejection guarantees the general v2 API enjoys (#165, #166,
-- #167, #169).
--
-- Each proof is a single function application against an already
-- audited zero-axiom theorem; no new reasoning is introduced.  The
-- FX-profile wrappers being DEFINITIONAL equalities to the general
-- API (with profile fixed at fxProfile) makes the delegations work
-- without rewriting.
--
--   * _compH_rejects → certifyRawCellExact?_compH_rejects (#166)
--   * _sound (raw-indexed) → certifyRawCellExact?_sound (#165)
--   * _accepted_cellDimension_eq → inferRawCellGeneral?_accepted_cellDimension_eq (#167)
--   * _sound (existential, HEq) → inferRawCellGeneral?_sound (#169)
--
-- Together with #172's entry points, this closes the L1cert.4
-- soundness story for the FX-profile (profile-fixed) API surface.
#assert_no_axioms LeanFX2.Foundation.PolyCell.FXProfile.certifyFXCellExact?_compH_rejects
#assert_no_axioms LeanFX2.Foundation.PolyCell.FXProfile.certifyFXCellExact?_sound
#assert_no_axioms LeanFX2.Foundation.PolyCell.FXProfile.certifyFXCell?_accepted_cellDimension_eq
#assert_no_axioms LeanFX2.Foundation.PolyCell.FXProfile.certifyFXCell?_sound

-- ─── V2-L1cert.19: Stage-3 audit gates final-sweep verification (#174) ──
-- End-of-stage verification that the Stage-3 certifier infrastructure
-- (#156-#173) has comprehensive named-gate coverage in this file.
--
-- The named #assert_no_axioms gates above complement the kernel-wide
-- `#audit_namespace_strict LeanFX2` sweep in Tools/AuditAll/GatesNsSweepStrict.lean
-- (which walks every decl under LeanFX2.* automatically).  Named gates
-- provide diagnostic anchors: a regression on a specific Stage-3 decl
-- fails THIS file's elaboration with a clear gate name, before the
-- namespace sweep runs.
--
-- ┌─ Coverage matrix (36 named gates, all verified ───────────────────┐
-- │  this commit at 720 jobs green on partial target):                │
-- │                                                                   │
-- │  L1cert.1-6 Spine/term certifier infrastructure (#156-#161):  6   │
-- │    CertifiedChildAtSpec, certifyChildSpine?, reconcileChild,│
-- │    certifyTermSpine?, certifyTermExact?,                      │
-- │    buildGeneratingCellExact?, buildVerticalCompositeExact?    │
-- │                                                                   │
-- │  L1cert.7-9 Top-level ingress (#162-#164):                    5   │
-- │    certifyRawCellExact?, certifyChildrenInlineFueled?,        │
-- │    certifyRawCellExactFueled?, inferRawCellGeneral?,          │
-- │    checkRawCellAs?                                              │
-- │                                                                   │
-- │  L1cert.10-14 Soundness suite (#165-#169):                    6   │
-- │    certifyRawCellExact?_sound, _compH_rejects,                  │
-- │    inferRawCellGeneral?_accepted_cellDimension_eq,              │
-- │    _accepted_rawCell_heq, _sound (HEq)                            │
-- │    + helper: hasSameNatList_self                                  │
-- │                                                                   │
-- │  L1cert.15 Positive coverage (#170):                          5   │
-- │    certifiedResultSort?, Coverage.{unitTermRaw, varZeroRaw},  │
-- │    coverage_{unitTermRaw, varZeroRaw}_sort                        │
-- │                                                                   │
-- │  L1cert.16 Negative coverage (#171):                          6   │
-- │    certifiedResultRejection?,                                   │
-- │    NegativeProbes.{horizontalCompositeUnitRaw,                  │
-- │      verticalCompositeUnitRaw}, negative_*_rejects (3 theorems)   │
-- │                                                                   │
-- │  L1cert.17-18 FX-profile views + soundness (#172-#173):       6   │
-- │    certifyFXCellExact?, certifyFXCell?,                       │
-- │    certifyFXCellExact?_{compH_rejects, sound},                  │
-- │    certifyFXCell?_{accepted_cellDimension_eq, sound}            │
-- │                                                                   │
-- │  Plus structures with auto-gated projections via namespace sweep: │
-- │    CertifiedRawCellResult (8 projections),                      │
-- │    CertifiedChildAtSpec (3 projections),                        │
-- │    PolyCell (3 ctor gates + raw_eq theorems)                    │
-- │                                                                   │
-- │  Total: 36/36 Stage-3 decls gated, 0 ungated.                     │
-- └───────────────────────────────────────────────────────────────────┘
--
-- ┌─ Pre-existing unrelated failures (NOT Stage-3, out-of-scope) ─────┐
-- │  Full `lake build LeanFX2Audit` is pre-red on TWO orphan smokes   │
-- │  that predate Stage-3 work and trace to earlier kernel passes:    │
-- │                                                                   │
-- │  * Smoke/AuditTacticsRawCd.lean — imports deleted                 │
-- │    LeanFX2.Tools.Tactics.RawCd (removed in commit c2efaccf        │
-- │    "bulldoze: cascade fake cluster — RawCd/RawCdLemma/RawCdRename │
-- │     + orphan smokes").  The bulldoze commit's own message lists   │
-- │    multiple orphan smokes it deleted; this one was missed.        │
-- │    All references in the file (RawTerm.cd, .cdGlueElimCase,       │
-- │    fx_rw_raw_cd_rename, fx_rw_cd_glue_elim_case_rename) point     │
-- │    to deleted definitions.  Safe to delete; deferred from #174    │
-- │    scope as it's bulldoze-followup hygiene, not Stage-3 work.     │
-- │                                                                   │
-- │  * Smoke/ImportSurface.lean — unexpected '#' token at line 33     │
-- │    (#assert_production_layer_imports_clean macro).  Distinct      │
-- │    issue from STRICT-FX1Core import-surface tooling.              │
-- │                                                                   │
-- │  Per memory entry `project_audit_importeverywhere_prered`:        │
-- │  verify Stage-3 work via per-decl #assert_no_axioms gates (this   │
-- │  file's mechanism), NOT via the full LeanFX2Audit target.  The    │
-- │  partial target `lake build LeanFX2 LeanFX2.Tools.AuditAll.AuditPolyCell`
-- │  IS green at 720 jobs, and all 36 named gates report 'axiom audit ok'.
-- └───────────────────────────────────────────────────────────────────┘
--
-- L1cert.4 layer (Stage-3 certifier): 19/19 tasks closed.  Ready to
-- advance to L2 (Allais ops layer, #175-#185) — the generic
-- fold/rename/subst infrastructure that turns v2's substrate into a
-- productive base for `cd_lemma`/`Conv`/derived rewrite work.

-- ─── V2-L2.1: Action / Semantics infrastructure for RawTerm (#175) ──
-- L2 kickoff: ship the variable-bridge typeclass + Container type that
-- fold (#177) will consume.  Splits the Allais two-typeclass
-- architecture cleanly:
--   * Foundation/Action.lean (already shipped) — Container-side: lift,
--     compose, identity, generic structure.
--   * ActsOnRawTermVar (this commit) — Target-bridge: how a Container
--     produces a RawTerm from a Fin position.
--
-- Two Container instances:
--   * RawRenaming (reused from v1's RawSubst/RenameDefs) — purely
--     positional, profile-agnostic.  Variable bridge: wrap renamed
--     Fin in .mkGen .gen_var pos .childNil.
--   * RawTermSubst (new) — Fin source → RawTerm target.  Variable
--     bridge: direct lookup.
--
-- Deferred to later L2 sub-tasks (require fold):
--   * Full Action instance for RawTermSubst (compose/laws) → #181
--   * RawTermSubst.lift through binders → #179/#180
--   * RawTerm.act / fold recursion engine → #177
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.identity
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ActsOnRawTermVar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ActsOnRawTermVar.varToRawTerm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.identity_lookup_eq_genVar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ActsOnRawTermVar.rawRenaming_varToRawTerm_eq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.ActsOnRawTermVar.rawTermSubst_varToRawTerm_eq

-- ─── V2-L2.2: GenAlgebra fold algebra record (#176) ────────────────
-- The Allais-style "Semantics" algebra for the v2 fold engine.  ONE
-- record + ONE field + ONE canonical algebra value.  Captures the
-- per-generator children-combination function that fold (#177)
-- consumes when traversing a RawTerm.
--
-- Architectural property: algebra signature uses ONE scope (no
-- source/target distinction), making the canonical "rebuild .mkGen"
-- algebra a literal ONE-LINE body that handles all 194 generators
-- uniformly.  No per-generator pattern match.  This is the L2
-- cascade-tax killer made concrete: in v1's dim-indexed era the
-- analog work for a single traversal required a 74-arm match.
--
-- Container threading (variable lookup, binder lifting) is fold's
-- responsibility, not the algebra's.  The algebra is purely a
-- children-combinator.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.GenAlgebra
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.GenAlgebra.algebra
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.GenAlgebra.canonical
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.GenAlgebra.canonical_algebra_eq_mkGen
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.GenAlgebra.canonical_algebra_gen_unit_smoke

-- ─── V2-L2.3: fold + foldChildren generic fold engine (#177) ────
-- The L2 workhorse: mutual structural recursion over RawTerm +
-- RawTermChildren, consuming the Action typeclass (#175) +
-- ActsOnRawTermVar bridge (#175) + GenAlgebra record (#176).
--
-- Three load-bearing pieces:
--   * iterateLiftRaw — iterate Action.liftForRaw N times
--   * Generator.payload_scope_invariant_of_not_var — 194-arm
--     enumeration in ONE place (cases generator + all_goals rfl)
--   * fold / foldChildren — mutual structural recursion engine
--
-- The dispatch on variable-vs-non-variable uses `if h : generator =
-- .gen_var then _ else _` with DecidableEq Generator (#122).  No
-- wildcard match, no 194-arm match in the recursion itself.  The
-- non-variable arm uses the scope-invariance helper to cast payload
-- from sourceScope to targetScope.
--
-- Together with #178-#180, this engine derives rename/weaken/subst
-- as one-line fold instantiations — the L2 cascade-tax killer.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.payload_scope_invariant_of_not_var
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.fold
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.foldChildren

-- ─── V2-L2.4: rename via fold (#178) ──────────────────────────────
-- THE FIRST L2 PAYOFF IN ACTION.  RawTerm.rename is a ONE-LINE
-- fold instantiation; in v1's era this would be a 74-arm pattern
-- match cascade.  The cascade-tax killer made concrete.
--
-- Composition of four prior commits:
--   * RawRenaming Action instance (v1's RawSubst/ActionInstances)
--   * ActsOnRawTermVar RawRenaming instance (#175)
--   * GenAlgebra.canonical (#176)
--   * fold engine (#177)
-- → RawTerm.rename, ONE LINE.
--
-- Both smoke tests (gen_unit and gen_var paths) close by `rfl` —
-- empirical confirmation that fold's full dispatch chain reduces
-- on closed inputs, including the Eq.rec motive trick (memory
-- feedback_lean_eq_rec_motive) and the DecidableEq Generator
-- dispatch.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_eq_fold
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.rename_eq_foldChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_identity_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_identity_var_smoke

-- ─── V2-L2.5: weaken via fold (#179) ──────────────────────────────
-- THE SECOND L2 PAYOFF.  RawTerm.weaken factors through rename:
--   weaken term := rename RawRenaming.weaken term
--
-- Two delegations deep (weaken → rename → fold).  Each step is
-- ONE LINE; the 74-arm cascade lives in neither — eliminated entirely
-- by the L2 architecture.
--
-- Smoke tests close by `rfl`:
--   * gen_unit weakening preserves shape at the next scope
--   * gen_var ⟨0,_⟩ weakening produces var (Fin.succ ⟨0,_⟩) — the
--     position is correctly shifted by Fin.succ via RawRenaming.weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_eq_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.weaken_eq_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_var_zero_smoke

-- ─── V2-L2.6: subst via fold + LiftsRaw refactor (#180) ───────────
-- THE THIRD L2 PAYOFF + an architectural refactor.
--
-- Refactor: extract LiftsRaw as the minimal binder-lift typeclass
-- (just liftForRaw).  fold (#177) now requires [LiftsRaw Container]
-- instead of [Action Container].  Auto-derive bridge means existing
-- Action-instanced types (RawRenaming) automatically satisfy LiftsRaw.
--
-- Resolution: subst-via-fold's chicken-and-egg dissolves because
-- RawTermSubst ships LiftsRaw (just lift, no compose) here, while
-- the full Action instance (with subst-based compose) ships at #181.
--
-- Subst ships as ONE LINE:
--   def RawTerm.subst sigma term := fold GenAlgebra.canonical sigma term
--
-- Both smoke tests close by `rfl` — full dispatch chain reduces on
-- closed inputs, just like rename (#178) and weaken (#179).  The
-- rename/weaken/subst trio is now complete; ONE engine, three
-- one-line operations.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LiftsRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.LiftsRaw.liftForRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instLiftsRawOfAction
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instLiftsRawRawTermSubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_eq_fold
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_eq_foldChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_identity_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_identity_var_zero_smoke

-- V2-L2.7a: Allais extensionality (apply_ext / pointwise) — the FIRST
-- of three Action laws.  Pointwise-equal substitutions act equally on
-- terms.  In v1 this was a 74-arm per-ctor structural induction; in v2
-- it collapses to a 4-arm mutual induction over RawTerm /
-- RawTermChildren because the 194-generator dispatch is amortized
-- into fold.  Adding a new Generator requires NO new arm — the
-- empirical L2 cascade-tax demonstration.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.PointwiseEq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.PointwiseEq.refl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawTermSubst_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_pointwise_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_pointwise_var_smoke

-- V2-L2.7b: identity_apply / subst_identity — the SECOND of three
-- Action laws.  Substituting by the identity substitution returns
-- the term unchanged.  Consumes #181a's subst_pointwise to bridge
-- the `iterateLiftRaw identity n` ≢ `identity` mismatch.  In v1
-- this was another 74-arm structural induction; in v2 the mutual
-- induction reuses the fold-based collapse.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_identity_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_identity_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_identity_apply
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_identity_apply
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_identity_apply_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_identity_apply_var_smoke

-- V2-L2.7c1: rename-side Allais extensionality (RawRenaming.PointwiseEq).
-- First piece of the cross-direction fusion ladder leading to
-- subst_compose.  In v1 this was a 74-arm structural induction on
-- RawTerm; in v2 it collapses to a 4-arm mutual induction over
-- RawTerm / RawTermChildren, mirroring #181a's subst_pointwise
-- with RawRenaming's variable bridge (.mkGen .gen_var (rho pos)
-- .childNil) instead of substitution's (sigma pos directly).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.PointwiseEq
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.PointwiseEq.refl
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.lift_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawRenaming_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.rename_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_pointwise_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_pointwise_var_smoke

-- V2-L2.7c2: rename-side lift-compose fusion (binder-level).
-- Pure Fin / Nat reasoning; no RawTerm induction yet.  Both
-- branches of `lift_compose_pointwise` close by `rfl` (renamings'
-- `lift` and `compose` are @[reducible] and reduce uniformly under
-- both Fin pattern arms).  The iterated form does Nat induction
-- using #181c1's lift_pointwise + this file's single-binder fusion.
-- Foundation for #181c3 RawTerm.rename_compose.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.lift_compose_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawRenaming_compose_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.lift_compose_pointwise_zero_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawRenaming_compose_pointwise_zero_smoke

-- V2-L2.7c3: term-level renaming fusion (rename_compose).
-- The KEYSTONE helper `Generator.payload_cast_compose` proves that
-- chained payload-scope-invariance casts equal single casts (193-arm
-- `all_goals rfl` after the `gen_var` arm is discharged via absurd).
-- This unblocks ALL term-level cross-direction fusion.
-- The mutual `rename_compose` uses it for the cast subgoal and the
-- mutual children IH for the spine subgoal, with the iterLiftBridge
-- (from #181c2) converting `compose (lift r1) (lift r2)` to
-- `lift (compose r1 r2)` at each binder descent.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.Generator.payload_cast_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.rename_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_compose_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_compose_var_smoke

-- V2-L2.7c4: rename-then-subst commute (first cross-direction lemma).
-- `RawRenaming.thenSubst rho sigma pos = sigma (rho pos)` is the
-- pre-composed bridge substitution.  `lift_thenSubst_pull` is the
-- binder-level pull (both Fin cases close by `rfl` because all the
-- defs are @[reducible]).  The iterated form chains lift_pointwise
-- (#181a) with lift_thenSubst_pull.  The mutual term theorem reuses
-- the now-established 4-arm template + payload_cast_compose keystone
-- (#181c3) + children IH + iter-bridge.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.thenSubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.lift_thenSubst_pull
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawRenaming_thenSubst_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_subst_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.rename_subst_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_subst_commute_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_subst_commute_var_smoke

-- V2-L2.7c5: subst-then-rename commute (second cross-direction).
-- `RawTermSubst.postRename sigma rho pos = rename rho (sigma pos)`
-- is the post-composed bridge substitution.
-- `weaken_lift_commute` is the trivial Fin commute (`fun _ => rfl`).
-- `lift_then_rename_lift_pull` is the binder pull — the FIRST place
-- in the ladder where the binder helper does substantive work
-- (uses rename_compose from #181c3 twice + rename_pointwise from
-- #181c1 + weaken_lift_commute).  The mutual term commute uses the
-- now-standard 4-arm template.
-- This closes the cross-direction pair; next is subst's
-- lift_compose_pointwise + subst_compose (the headline third
-- Action law).
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawRenaming.weaken_lift_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.postRename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_then_rename_lift_pull
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawTermSubst_postRename_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_rename_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_rename_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_rename_commute_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_rename_commute_var_smoke

-- V2-L2.7c6: THE HEADLINE THIRD ACTION LAW (compose_assoc / subst_compose).
-- The polynomial monad's multiplication law at the term layer.
-- `RawTermSubst.compose sigma1 sigma2 pos = subst sigma2 (sigma1 pos)`
-- is the homogeneous substitution composition.
-- `lift_compose_pointwise` is the binder pull — the FIRST place in
-- the ladder that uses BOTH cross-direction commutes (#181c4 +
-- #181c5) plus subst_pointwise (#181a) in a single proof.
-- The mutual `subst_compose` reuses the now-standard 4-arm template.
-- This closes the three Action laws V2-L2.7 needs (apply_ext +
-- identity_apply + compose_assoc).  Next is the typeclass instance.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_compose_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawTermSubst_compose_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_compose_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_compose_var_smoke

-- M6 beta-replay support: singleton/weakening cancellation plus the
-- beta-contractum reshape `(subst0 body arg).subst sigma =
-- subst0 (body.subst sigma.lift) (arg.subst sigma)`.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.weaken_then_singleton_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_subst_singleton
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst_iterateLiftRaw_singleton_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.subst_iterateLiftRaw_singleton_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.weaken_subst_singleton
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.subst0_subst_commute

-- Eta-M8a: raw strengthening substrate for structural eta.
-- `RawTerm.strengthen` is a lifted partial renaming that drops the
-- newest parent-scope variable when it is unused.  Binder descent goes
-- through `iterateLiftRaw`, so eta rules can state their side condition
-- computationally instead of smuggling a freshness proof.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.lift
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.dropNewest
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.instLiftsRawPartialRawRenaming
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.dropNewest_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.lift_rename_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.iterateLiftRaw_rename_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.dropNewest_renamingInjectsBack
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.lift_renamingInjectsBack
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRawRenaming.iterateLiftRaw_renamingInjectsBack
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_RawRenaming_identity_pointwise
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameTermResult
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameTermResult.hasSucceeded
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameTermResult.term
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameTermResult.toOption
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameTermResult.toOption_eq_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameChildrenResult
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameChildrenResult.hasSucceeded
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameChildrenResult.children
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameChildrenResult.toOption
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.PartialRenameChildrenResult.toOption_eq_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.partialRenameResult
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.partialRenameResult
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.partialRename?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.partialRename?
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.strengthen
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_identity_apply
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.rename_identity_apply
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.partialRenameResult_rename_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.partialRenameResult_rename_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.partialRename?_rename_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.partialRename?_rename_some
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.partialRename?_imp_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.partialRename?_imp_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_iterateLiftRaw_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.strengthen_iterateLiftRaw_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.strengthen_weaken
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_sound
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_iterateLiftRaw_sound
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.strengthen_sound
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.strengthen_iterateLiftRaw_sound
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.weaken_subst0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_weakened_subst0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_commutes_rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_commutes_subst0
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.childNil_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isFreshFor_nonVar_of_children_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.childCons_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.single_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.double_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.triple_isFreshFor
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.rename_subst0_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.strengthen_eq_subst_of_isFreshFor_singleton

-- M-substrate-2: first-principles free-variable support.
-- Avoids host Finset/Std set infrastructure by representing raw
-- variable sets as boolean characteristic functions over `Fin scope`.
-- This gives later closure/NF/Conv-substrate tasks a small kernel-local
-- API with a structural soundness/completeness theorem against
-- `UsesPosition`.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.empty
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.singleton
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.union
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.contains
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.instDecidableContains
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.raiseParentPosition
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.fromChild
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.contains_empty_false
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.contains_singleton_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.contains_union_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.freeVars
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.freeVars
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.UsesPosition
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.UsesPosition
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.freeVars_nonVar
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.usesPosition_nonVar_iff
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.freeVars_iff_uses
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.freeVars_iff_uses
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.freeVars_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.freeVars_var_self_smoke

-- M-substrate-3: precise raw beta+iota NF + closedness substrate.
-- The root detector intentionally excludes eta; beta+eta consumers use
-- `Step.betaEta` instead of overloading raw Step normality.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.isEmpty
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawVarSet.isEmpty_empty
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isLamSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isBoolTrueSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isBoolFalseSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isPairSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isNatZeroSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isNatSuccSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isListNilSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isListConsSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isOptionNoneSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isOptionSomeSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isEitherInlSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isEitherInrSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isReflSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.castToGenerator
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasAppBetaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasBoolElimIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasPairProjectionIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasNatElimIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasListElimIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasOptionMatchIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasEitherMatchIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.hasIdElimIotaRoot
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.hasRootStepSource
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalFormBool
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.areStepNormalFormsBool
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isClosed
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.instDecidableIsStepNormalForm
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.instDecidableIsClosed
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.areStepNormalForms
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.instDecidableAreStepNormalForms
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm_blocks_step
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermChildren.areStepNormalForms_blocks_stepChildren
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isClosed_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.isStepNormalForm_unit_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.hasRootStepSource_beta_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.not_isStepNormalForm_beta_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.hasRootStepSource_fst_pair_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTerm.hasRootStepSource_etaLamSource_smoke

-- V2-L2.7d: THE `Action RawTermSubst` TYPECLASS INSTANCE.
-- Closes V2-L2.7 entirely.  Cites the three Action laws shipped
-- across #181a (apply_ext / subst_pointwise), #181b
-- (identity_apply / subst_identity_apply), and #181c6
-- (compose_assoc / subst_compose).
-- Resolves the chicken-and-egg from #180: at that time,
-- `RawTermSubst.compose` needed `RawTerm.subst`, but `subst`
-- was being defined.  The LiftsRaw refactor (#180) sidestepped
-- this for fold; now with compose shipped (#181c6) and the laws
-- proven, the full Action instance lands.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.instActionRawTermSubst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.identity_eq_action
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_eq_actionForTy
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.lift_eq_actionForRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.compose_eq_action
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.action_identity_headIndex_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawTermSubst.action_compose_identity_left_smoke

-- V2-L2.8: cell-layer rename/subst lift.  RawCell.rename and
-- RawCell.subst are 5-arm structural recursions that delegate
-- to the term-layer fold-backed RawTerm.rename / RawTerm.subst
-- at termBase leaves and recurse structurally on composite/identity
-- ctors.  Dimension preservation theorems plus per-arm reduction
-- smokes round out the gate.  The cell layer has no binder shifts
-- (composition doesn't bind variables), so no fold abstraction
-- is needed — direct match-form structural recursion suffices.
-- (Import lives at the file head per Lean import-position discipline.)
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_preserves_dim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_preserves_dim
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_termBase_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_termBase_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_generatingCell_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_verticalComposite_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_horizontalComposite_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_identityCell_unfolds

-- ─── V2-L2.12: subst push-through (cell-level boundary preservation)
-- Per polycell.md §11.6.2: cell-level subst is HOMOMORPHIC over every
-- cell constructor (subst pushes through to the sub-cells).  The
-- termBase arm was already gated above; this section completes the
-- family for the four remaining ctors.
--
-- Each theorem closes by rfl because RawCell.subst is a direct
-- 5-arm structural recursion (RawCellRenameSubst.lean:111).  The
-- ctor pattern match unfolds definitionally on concrete inputs.
--
-- Together with subst_termBase_unfolds, these five theorems witness
-- that cell-level substitution preserves the boundary structure of
-- every cell ctor — the "boundary preservation" obligation that
-- §11.6.2 names as load-bearing.
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_generatingCell_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_verticalComposite_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_horizontalComposite_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_identityCell_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_preserves_dim_generatingCell_smoke

-- V2-L2.9: cascade-deletion demonstration (the L2 payoff, quantified).
-- Five cell-layer cascade lemmas as 5-arm structural recursions, each
-- citing the corresponding term-layer Allais law at the termBase arm.
-- Per cascade: v1 needed (5 cell arms + 78 term arms) = 83
-- constructor-arm proofs; v2 needs (5 cell arms + 4 term arms) = 9
-- arms — a ~9.2x reduction.  Across the five cascades shipped here,
-- 45 arms in v2 replace 415 arms in v1.  Three smokes witness that
-- the cell-layer cascade genuinely delegates to the term-layer
-- Action laws at the `termBase` arm (no hidden cell-layer
-- computation).  Closes #183.
-- (Import lives at the file head per Lean import-position discipline.)
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_compose
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_identity_apply
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_subst_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_rename_commute
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.rename_compose_termBase_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_compose_termBase_smoke
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.RawCell.subst_identity_apply_termBase_smoke

-- V2-fix-8: foldV2 shift greater-than-one property smoke.  Pins the
-- fold engine's binder-shift behavior ahead of Phase Z₀'s commitment
-- to add eliminator motive children at shift > 1 (per polycell.md
-- §11.8.3 + §3.16.6).  Two sections: (1) `iterateLiftRaw` equational
-- smokes at depths 0/1/2/3 + the recursive `succ` equation; (2)
-- `foldChildren` over synthetic shift-list spines `[2]` and `[0,2,1]`
-- with identity renaming.  Each theorem closes by `rfl` because the
-- engine is shift-polymorphic by construction.  Closes #249.
-- (Import lives at the file head per Lean import-position discipline.)
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_depth_zero_eq_self
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_depth_one_eq_liftForRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_depth_two_eq_double_liftForRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_depth_three_eq_triple_liftForRaw
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.iterateLiftRaw_succ_unfolds
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.rename_identity_synthetic_shift_two_spine_eq_self
#assert_no_axioms LeanFX2.Foundation.PolyCell.Core.rename_identity_synthetic_shifts_zero_two_one_spine_eq_self

#assert_inhabited_dependent_budget LeanFX2.Foundation.PolyCell.FXProfile 0
#assert_inhabited_dependent_budget LeanFX2.Foundation.PolyCell.Saturation 0
#assert_inhabited_dependent_budget LeanFX2.Foundation.PolyCell.Extension 0

end LeanFX2.Tools
