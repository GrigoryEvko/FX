import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.ConsistencyTargetSignature

/-! # FX1Poly/Typed/MilestoneASpineValueLayer
    — the Milestone-A VALUE-LAYER spine: SN + consistency + value-layer canonicity bundled, zero-axiom

Milestone A's three metatheoretic pillars for the grown typed kernel `HasTypeDescPi` are each now
UNCONDITIONAL (modulo the benign empty-context well-formedness presupposition `WfContextDesc.emptyIsWellFormed`,
which is itself shipped).  This file bundles them into ONE honest capstone record so the joint claim is a single
checked theorem rather than three scattered ones:

  1. **Strong normalization** (SN-043) — every closed grown-typed term strongly normalizes
     (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, the OB-5 / BFT route through the reducibility
     fundamental theorem).
  2. **Consistency** (SN-050) — nothing closed is grown-typed at `emptyType`
     (`emptyConsistencyViaCandidateBridge`; the candidate bridge discharges it, and the syntactic-validity
     route confirms it — both unconditional, zero-axiom).
  3. **Value-layer canonicity** (SN-047) — every closed term typed at `boolType` by any of the three
     value-and-formation engines (`HasTypeDescDataIntro` / `HasTypeDescBaseType` / grown `HasTypeDescPi`)
     reduces to `boolTrue` or `boolFalse` (`closedBoolCanonicalForms`, via grown SN + SR-U4 — the SYNTACTIC
     route, NO §5 candidate bridge).

## Honest scope — what this is NOT

This is the **value-layer** spine, and the record's docstring is deliberate about its boundary:

  * **Canonicity is over the VALUE layer.**  `boolCanonicity` covers closed terms typed at `boolType` by the
    three engines whose canonical-forms/vacuity facts are shipped.  It does NOT yet cover ELIMINATOR-typed
    bools (`boolElim …` typed by the fourth engine `HasTypeDescDataElim`): fully-non-vacuous
    eliminator-computing canonicity is the follow-on (CANON-1, needs `HasTypeDescDataElim` folded into the
    grown table, GTL-18, plus combined SN/SR over eliminator redexes).  Eliminator-computing canonicity is
    separately established as an operational fact (ELIM-CANON); its INTEGRATION into this typed spine is the
    open frontier.
  * **This is NOT the joint-decidability apex.**  Per the milestone-ledger correction, decidable typed Conv
    and decidable typed checking are established PER FRAGMENT; the joint decidable kernel (O-NORM) is open
    research.  This spine bundles the three SOUNDNESS pillars (SN / consistency / canonicity), not the
    decidability apex.
  * **Three-ways triangulation is separate.**  The candidate-bridge sconing leg (now de-risked via
    `emptyTaitCandidate` / `dataTaitCandidate`) and the Makkai word-equality leg are cross-checks toward the
    "closed three ways" capstone (SN-150), not part of this single-route spine.

So this is the honest value-layer Milestone-A sign-off: the three pillars hold jointly, unconditionally,
zero-axiom, for the grown typed kernel — with the eliminator-layer and the joint apex explicitly named as the
remaining frontier.

## Zero-axiom verification

`milestoneAValueLayerSpineHolds` is a three-field record whose fields are the shipped
`stronglyNormalizingOfWfContextDesc` / `emptyConsistencyViaCandidateBridge` / `closedBoolCanonicalForms` at the
empty context.  Confirmed `#print axioms`-clean.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The Milestone-A value-layer spine.**  The three unconditional soundness pillars of the grown typed
kernel bundled as one record: strong normalization of every closed grown-typed term, consistency (no closed
grown inhabitant of `emptyType`), and value-layer canonicity (a closed bool reduces to `boolTrue`/`boolFalse`).
A `Prop` record — the joint Milestone-A soundness claim as a single object. -/
structure MilestoneAValueLayerSpine (profile : PolyProfile) : Prop where
  /-- SN-043: every closed grown-typed term strongly normalizes. -/
  stronglyNormalizing : ∀ {subject classifier : RawTerm 0},
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier →
      StepStar.IsStronglyNormalizing subject
  /-- SN-050: nothing closed is grown-typed at `emptyType`. -/
  consistency : ∀ {subject : RawTerm 0},
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject emptyTypeCell → False
  /-- SN-047 (value layer): a closed term typed at `boolType` by any of the three value/formation engines
  reduces to `boolTrue` or `boolFalse`. -/
  boolCanonicity : ∀ {subject : RawTerm 0},
    (HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
     HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell ∨
     HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell) →
      ∃ value : RawTerm 0, StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell)

/-- **★ The Milestone-A value-layer spine holds, unconditionally, zero-axiom.**  Each pillar is the shipped
unconditional theorem at the empty context: `stronglyNormalizingOfWfContextDesc` (SN), the candidate-bridge
`emptyConsistencyViaCandidateBridge` (consistency), and `closedBoolCanonicalForms` (value-layer canonicity).
The benign empty-context well-formedness is `WfContextDesc.emptyIsWellFormed`.  The joint Milestone-A
soundness claim for the grown typed kernel, as one checked object — with the eliminator-layer canonicity and
the joint-decidability apex the named remaining frontier (see the file docstring). -/
theorem milestoneAValueLayerSpineHolds {profile : PolyProfile} :
    MilestoneAValueLayerSpine profile where
  stronglyNormalizing typed :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed
  consistency typed := emptyConsistencyViaCandidateBridge _ typed
  boolCanonicity typed := closedBoolCanonicalForms typed

end FX1Poly.Typed
