import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.TypedBySomeEngine
import FX1Poly.Typed.Engine.Classifier.NativityLedger
import FX1Poly.Typed.Engine.Classifier.UnionStaticTypingSoundness
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms
import FX1PolyAudit.UnifiedCorpusNativityLedger

/-! # FX1PolyAudit/OneEngineSignoff — FX has exactly ONE typing engine, table-driven, fully covered

After the NATIVE-42..45 endgame the kernel's typed layer collapsed to a SINGLE typing judgment: the
union judgment `HasTypeUnion`, whose static admission is decided by the pure table classifier
`hasSomeTypingRule` (NATIVE-40: a `isSome` over the rule tables, zero `decide`s).  The ~23 standalone
bespoke engines (boolElim / natElim / pair / either / list / … intro+elim engines, BaseType /
DataIntro / Flat, the bridge) were retired; their data / former / eliminator families are now the 25
arms of the one union judgment.

This module is the ONE-ENGINE sign-off: a single named certificate bundling, BY CITATION (it re-proves
nothing), the facts that make "FX has exactly one typing engine" machine-checked.

## What this certificate ties together

  * **The union IS the typing engine, table-driven** —
      - `FX1Poly.Typed.nativityLedgerHolds : NativityLedger` (`FX1Poly/Typed/NativityLedger.lean`):
        every `.live` generator's static semantics is a typing-table row (`hasSomeTypingRule`) — the
        classifier IS the engine's admission test.
      - `FX1Poly.Typed.HasTypeUnion.reservedHeadUntyped`
        (`FX1Poly/Typed/UnionStaticTypingSoundness.lean`): the classifier's negative verdicts are
        TRUTHFUL — a subject whose head is reserved by the union eliminator table heads no union-typed
        cell.  One judgment, one refutation.

  * **Its shipped metatheory over `HasTypeUnion`** —
      - subject reduction: `FX1Poly.Typed.unionRootStepSubjectReduction` (the root-redex SR master) +
        `FX1Poly.Typed.nativeUnionRootRedexSubjectReductionCoverageWitness` (NATIVE-37: the
        nine-family root-redex SR coverage gate, so the exercised SR property set cannot silently
        shrink);
      - canonicity: `FX1Poly.Typed.HasTypeUnion.closedNormalLaneCanonicalForms` (NATIVE-38: the
        single-union canonicity master) and its Nat instance
        `FX1Poly.Typed.HasTypeUnion.closedNormalNatCanonicalForms`;
      - honesty inversions: `FX1Poly.Typed.nativeUnionInversionCoverageWitness` (NATIVE-37: the
        inversion coverage gate — pathLam-head refutation, the per-head inversions, the union-wide
        affine-grade rejection).

  * **The unified-corpus certificate from Stage 1** —
    `FX1PolyAudit.unifiedCorpusNativityCertificateHolds`
    (`FX1PolyAudit/UnifiedCorpusNativityLedger.lean`): the unified corpus is nativity-complete AND
    FX0-cross-checked AND parity-consistent.

## The bundle inhabitant's reading

`oneEngineSignoff` certifies: **FX has exactly one typing engine — the table-driven union judgment
`HasTypeUnion`, whose static admission is the table classifier `hasSomeTypingRule`, and which is fully
metatheoretically covered (subject reduction + canonicity + honesty inversions) and joined to the
unified-corpus capstone.**  The inhabitant `oneEngineSignoffHolds` constructs each field from a shipped
named declaration, so the sign-off cannot silently decay.

## Layering note

Lives in the AUDIT layer because it cites `unifiedCorpusNativityCertificateHolds`, itself an
audit-layer bundle (it joins kernel-side nativity/parity with the audit-side FX0 cross-check).

## Zero-axiom verification

`OneEngineSignoff` is a `Prop` structure whose every field is the type of a shipped zero-axiom
theorem; the inhabitant threads those shipped terms in.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated below in this same file. -/

namespace FX1PolyAudit

open FX1Poly.Core (PolyProfile RawTerm Generator Conv Step StepChildren RawTermChildren)
open FX1Poly.Universe (UniverseFlag)
open FX1Poly.Typed
  (NativityLedger nativityLedgerHolds HasTypeUnion TypingContext
   hasUnionEliminatorTypingRule natTypeCell natZeroCell natSuccCell
   unionRootStepSubjectReduction nativeUnionRootRedexSubjectReductionCoverageWitness
   NativeUnionRootRedexSubjectReductionCoverage nativeUnionInversionCoverageWitness
   NativeUnionInversionCoverage IsDeferredRootRedexShape)
open FX1PolyAudit
  (UnifiedCorpusNativityCertificate unifiedCorpusNativityCertificateHolds)

/-- **The ONE-ENGINE sign-off certificate.**  One `Prop` whose fields bundle, by citation: the union
judgment is THE typing engine (table classifier + nativity + reserved-head truthfulness), its shipped
metatheory over `HasTypeUnion` (subject reduction, canonicity, honesty inversions), and the
unified-corpus capstone from Stage 1.  An inhabitant certifies FX has exactly one typing engine,
table-driven and fully covered. -/
structure OneEngineSignoff (profile : PolyProfile) : Prop where
  /-- The union is the typing engine, table-driven: every live generator's static semantics is a
  typing-table row (the nativity ledger holds). -/
  unionIsTheTableDrivenEngine : NativityLedger
  /-- The table classifier's negative verdicts are truthful: a reserved-head subject heads no
  union-typed cell (`HasTypeUnion.reservedHeadUntyped`). -/
  reservedHeadsAreUntyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeUnion profile context subject classifier →
    hasUnionEliminatorTypingRule (FX1Poly.Typed.RawTerm.headGenerator subject) = false → False
  /-- Subject reduction over the one engine: a root `Step` from a union-typed redex lands at a
  reclassifiable union typing, a congruence reduct, or a deferred-shape redex
  (`unionRootStepSubjectReduction`). -/
  engineHasSubjectReduction : ∀ {scope : Nat} {context : TypingContext profile scope}
    {redex reduct classifier : RawTerm scope},
    HasTypeUnion profile context redex classifier → Step redex reduct →
    (∃ pinnedClassifier : RawTerm scope,
        HasTypeUnion profile context reduct pinnedClassifier ∧ Conv pinnedClassifier classifier)
    ∨ (∃ (generator : Generator) (payload : generator.payload scope)
         (childrenBefore childrenAfter : RawTermChildren generator.binderShifts scope),
        redex = RawTerm.mkGen generator payload childrenBefore ∧
        reduct = RawTerm.mkGen generator payload childrenAfter ∧
        StepChildren childrenBefore childrenAfter)
    ∨ IsDeferredRootRedexShape redex
  /-- Subject-reduction coverage gate over the one engine (NATIVE-37): the nine-family root-redex SR
  property set cannot silently shrink. -/
  engineSubjectReductionCovered : NativeUnionRootRedexSubjectReductionCoverage profile
  /-- Canonicity over the one engine (NATIVE-38, Nat instance): a closed normal union-typed term at
  `Nat` on the core fragment is `natZero` or a `natSucc`
  (`HasTypeUnion.closedNormalNatCanonicalForms`). -/
  engineHasCanonicity : ∀ {subject : RawTerm 0},
    HasTypeUnion profile (TypingContext.empty : TypingContext profile 0) subject natTypeCell →
    RawTerm.isStepNormalForm subject →
    RawTerm.containsGeneratorBool .gen_pathApp subject = false →
    RawTerm.containsGeneratorBool .gen_pathLam subject = false →
    subject = natZeroCell ∨ ∃ predecessor : RawTerm 0, subject = natSuccCell predecessor
  /-- Honesty inversions over the one engine (NATIVE-37): the inversion coverage gate is inhabited. -/
  engineHonestyInversionsCovered : NativeUnionInversionCoverage profile
  /-- The unified-corpus capstone (Stage 1): nativity-complete AND FX0-cross-checked AND
  parity-consistent. -/
  unifiedCorpusIsCertified : UnifiedCorpusNativityCertificate profile

/-- **★ The ONE-ENGINE sign-off HOLDS.**  Every field is the shipped named carrier: `nativityLedgerHolds`,
`HasTypeUnion.reservedHeadUntyped`, `unionRootStepSubjectReduction`,
`nativeUnionRootRedexSubjectReductionCoverageWitness`, `HasTypeUnion.closedNormalNatCanonicalForms`,
`nativeUnionInversionCoverageWitness`, and the Stage 1 `unifiedCorpusNativityCertificateHolds`.  FX has
exactly one typing engine, table-driven, fully metatheoretically covered — one checked object. -/
theorem oneEngineSignoffHolds {profile : PolyProfile} : OneEngineSignoff profile where
  unionIsTheTableDrivenEngine := nativityLedgerHolds
  reservedHeadsAreUntyped typed reserved := typed.reservedHeadUntyped reserved
  engineHasSubjectReduction typed step := unionRootStepSubjectReduction typed step
  engineSubjectReductionCovered := nativeUnionRootRedexSubjectReductionCoverageWitness
  engineHasCanonicity typed normal pathAppFree pathLamFree :=
    typed.closedNormalNatCanonicalForms normal pathAppFree pathLamFree
  engineHonestyInversionsCovered := nativeUnionInversionCoverageWitness
  unifiedCorpusIsCertified := unifiedCorpusNativityCertificateHolds

end FX1PolyAudit

-- ===== Per-declaration zero-axiom audit gates =====
-- ★ the one-engine sign-off bundle + its inhabitant
#assert_no_axioms FX1PolyAudit.OneEngineSignoff
#assert_no_axioms FX1PolyAudit.oneEngineSignoffHolds
-- the cited carriers, re-verified zero-axiom at the bundle site
#assert_no_axioms FX1Poly.Typed.nativityLedgerHolds
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.reservedHeadUntyped
#assert_no_axioms FX1Poly.Typed.unionRootStepSubjectReduction
#assert_no_axioms FX1Poly.Typed.nativeUnionRootRedexSubjectReductionCoverageWitness
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNormalNatCanonicalForms
#assert_no_axioms FX1Poly.Typed.nativeUnionInversionCoverageWitness
#assert_no_axioms FX1PolyAudit.unifiedCorpusNativityCertificateHolds
