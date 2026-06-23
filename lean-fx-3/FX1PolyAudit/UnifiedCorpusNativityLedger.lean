import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.NativityLedger
import FX1PolyAudit.MetatheoryParityLedger
import FX1PolyAudit.MilestoneAParityMatrix
import FX1PolyAudit.FX0CrossCheckUnionCorpus

/-! # FX1PolyAudit/UnifiedCorpusNativityLedger — the one-engine corpus capstone bundle

The kernel finished collapsing to ONE typing engine (the union judgment `HasTypeUnion`, whose
static semantics is the pure table classifier `hasSomeTypingRule`) and ONE reduction relation
(`StepOver fxBundle`, the canonical βιη bundle).  Three independent certificates already witness the
distinct facets of that collapse — but no SINGLE named object had previously bundled them.  This
module ships that bundle.

## What this certificate ties together (by CITATION — it re-proves nothing)

  * **Nativity completeness** — `FX1Poly.Typed.nativityLedgerHolds : NativityLedger`
    (`FX1Poly/Typed/NativityLedger.lean`): every generator the semantic-tier classifier brands
    `.live` has its STATIC semantics carried by a typing-table row (`hasSomeTypingRule`) OR its
    OPERATIONAL semantics by a reduction-table redex row (`hasRedexHead`).  No bespoke per-generator
    arm carries any live generator's semantics; the tables do.

  * **FX0 cross-check of the unified corpus** —
    `FX1Poly.FX0CrossCheck.unionCrossCheckCoverageWitness :
       UnionCrossCheckCoverage profile UniverseFlag.standard`
    (`FX1PolyAudit/FX0CrossCheckUnionCorpus.lean`): the three flagship subjects typed BY THE UNION
    JUDGMENT (the recursive data-intro numeral tower, the λ-over-data composition, the path-endpoint
    eliminator redex) are each accepted by the independent minimal external verifier, are strongly
    normalizing, AND carry their `HasTypeUnion` derivation.  The byte channel is cross-checked against
    a genuinely union-typed term, not a docstring claim.

  * **Parity consistency** — the still-holding formation↔grown reduction-metatheory parity facts
    (`FX1Poly/Typed/MetatheoryParityLedger.lean`: `weakening_atFullParity`,
    `substitution_atFullParity`, `strongNormalization_grownNeedsWfContext`,
    `subjectReduction_grownConditionalOnBundle`) and the honest 3-leg Milestone-A status
    (`FX1Poly/Typed/MilestoneAParityMatrix.lean`: `capstone_currentlyClosedOneWay`, `legBreakdown`).
    The one-engine collapse did not silently flip any parity cell: weakening / substitution stay at
    full parity, grown SN keeps its benign well-formed-context presupposition, grown SR's master stays
    honestly conditional on the GrownCtxConv bundle, and exactly one of the three SN legs (Tait) is
    fully + independently proven.

## The bundle inhabitant's reading

`unifiedCorpusNativityCertificate` certifies: **the unified (one-engine) corpus is
nativity-complete AND FX0-cross-checked AND parity-consistent.**  Its inhabitant
`unifiedCorpusNativityCertificateHolds` constructs each field from the shipped named decl above —
the file fails to compile if any cited theorem is renamed or deleted, so the bundle cannot silently
decay.

## Layering note

This bundle lives in the AUDIT layer (`FX1PolyAudit/`), not the kernel layer (`FX1Poly/`), because
its FX0-cross-check field cites `unionCrossCheckCoverageWitness`, which is itself an audit-layer
declaration (the FX0 re-checker is the audit-side independent verifier).  The kernel library never
imports the audit library — keeping the fast inner-loop `lake build FX1Poly` free of the cross-check
dependency — so the bundle that joins kernel-side nativity/parity with audit-side cross-check must sit
on the audit side.

## Zero-axiom verification

`UnifiedCorpusNativityCertificate` is a `Prop` structure whose every field is the type of a shipped
zero-axiom theorem; the inhabitant is `⟨nativityLedgerHolds, unionCrossCheckCoverageWitness, …⟩` with
the parity facts threaded in.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated below in this same file. -/

namespace FX1PolyAudit

open FX1Poly.Core (PolyProfile)
open FX1Poly.Universe (UniverseFlag)
open FX1Poly.Typed
  (NativityLedger nativityLedgerHolds MetatheoryProperty EngineParityStatus
   weakening_atFullParity substitution_atFullParity strongNormalization_grownNeedsWfContext
   subjectReduction_grownConditionalOnBundle)
open FX1Poly.Core.ParityMatrix
  (capstone_currentlyClosedOneWay legBreakdown fullyIndependentlyProvenLegCount
   legFullyIndependent MilestoneLeg)
open FX1Poly.FX0CrossCheck (UnionCrossCheckCoverage unionCrossCheckCoverageWitness)

/-- **The unified one-engine corpus capstone certificate.**  One `Prop` whose three groups of fields
bundle, by citation, the distinct facets of the one-engine / one-reduction collapse: nativity
completeness, FX0 cross-check of the union-typed flagship corpus, and reduction-metatheory parity
consistency.  An inhabitant certifies the unified corpus is nativity-complete AND FX0-cross-checked
AND parity-consistent. -/
structure UnifiedCorpusNativityCertificate (profile : PolyProfile) : Prop where
  /-- Nativity completeness: every live generator's semantics is a rule-table row (the nativity
  ledger holds). -/
  corpusIsNativityComplete : NativityLedger
  /-- FX0 cross-check of the unified corpus: the three flagship UNION-typed subjects are accepted by
  the independent external verifier, are strongly normalizing, and carry their `HasTypeUnion`
  derivation. -/
  unionCorpusIsCrossChecked : UnionCrossCheckCoverage profile UniverseFlag.standard
  /-- Parity consistency (reduction metatheory): weakening and substitution stay at full
  formation↔grown parity. -/
  weakeningAndSubstitutionStayAtFullParity :
    MetatheoryProperty.weakening.parityStatus = EngineParityStatus.bothUnconditional ∧
      MetatheoryProperty.substitution.parityStatus = EngineParityStatus.bothUnconditional
  /-- Parity consistency: grown strong normalization keeps the benign well-formed-context
  presupposition (NOT conflated with a blocker), and grown subject reduction's master stays honestly
  conditional on the GrownCtxConv bundle. -/
  strongNormalizationAndSubjectReductionStayHonest :
    MetatheoryProperty.strongNormalization.parityStatus = EngineParityStatus.grownNeedsWfContext ∧
      MetatheoryProperty.subjectReduction.parityStatus =
        EngineParityStatus.grownConditionalOnBundle
  /-- Parity consistency: exactly one of the three Milestone-A SN legs (Tait) is fully + independently
  proven across all three endpoints — the honest capstone status is unchanged by the collapse. -/
  exactlyOneSnLegFullyIndependent : fullyIndependentlyProvenLegCount = 1
  /-- Parity consistency: the per-leg breakdown holds (Tait fully independent; sconing's SN bridged to
  Tait; the RPO leg a fragment only). -/
  snLegBreakdownHolds :
    legFullyIndependent MilestoneLeg.taitReducibility = true ∧
      legFullyIndependent MilestoneLeg.sconingViaSTC = false ∧
        legFullyIndependent MilestoneLeg.rpoWordRewriting = false

/-- **★ The unified one-engine corpus capstone HOLDS.**  Every field is the shipped named carrier:
`nativityLedgerHolds`, `unionCrossCheckCoverageWitness`, the four `MetatheoryParityLedger` ledger
facts, and the two `MilestoneAParityMatrix` honest-status facts.  The unified (one-engine) corpus is
nativity-complete AND FX0-cross-checked AND parity-consistent — one checked object. -/
theorem unifiedCorpusNativityCertificateHolds {profile : PolyProfile} :
    UnifiedCorpusNativityCertificate profile where
  corpusIsNativityComplete := nativityLedgerHolds
  unionCorpusIsCrossChecked := unionCrossCheckCoverageWitness
  weakeningAndSubstitutionStayAtFullParity :=
    ⟨weakening_atFullParity, substitution_atFullParity⟩
  strongNormalizationAndSubjectReductionStayHonest :=
    ⟨strongNormalization_grownNeedsWfContext, subjectReduction_grownConditionalOnBundle⟩
  exactlyOneSnLegFullyIndependent := capstone_currentlyClosedOneWay
  snLegBreakdownHolds := legBreakdown

end FX1PolyAudit

-- ===== Per-declaration zero-axiom audit gates =====
-- ★ the unified one-engine corpus capstone bundle + its inhabitant
#assert_no_axioms FX1PolyAudit.UnifiedCorpusNativityCertificate
#assert_no_axioms FX1PolyAudit.unifiedCorpusNativityCertificateHolds
-- the cited carriers, re-verified zero-axiom at the bundle site (the §27.3-L3 cross-reference idiom)
#assert_no_axioms FX1Poly.Typed.nativityLedgerHolds
#assert_no_axioms FX1Poly.FX0CrossCheck.unionCrossCheckCoverageWitness
#assert_no_axioms FX1Poly.Typed.weakening_atFullParity
#assert_no_axioms FX1Poly.Typed.substitution_atFullParity
#assert_no_axioms FX1Poly.Typed.strongNormalization_grownNeedsWfContext
#assert_no_axioms FX1Poly.Typed.subjectReduction_grownConditionalOnBundle
#assert_no_axioms FX1Poly.Core.ParityMatrix.capstone_currentlyClosedOneWay
#assert_no_axioms FX1Poly.Core.ParityMatrix.legBreakdown
