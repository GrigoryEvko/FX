import FX1Poly.Tier0.Mode.Mode
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TwoCellWordProblemDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCongruenceProved
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCanonicalization
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedDecision

/-! # DecidableCeilingLedger — the honest boundary of the 2-cell word problem (CEIL rung map)

The mechanized theory sits on a three-rung decidability ladder, and this ledger is the
machine-checked statement of exactly where each rung stands.  Every field of the ledger
value is PINNED to the source honesty marker of the file that shipped (or refuted) it —
a marker drift breaks a `rfl` here, so the ledger cannot silently rot.

**Rung 1 — FREE, decided GENERICALLY.**  Over ANY mode signature, `TwoCellConvFull`
(the relation-free Godement/whisker congruence) is characterized by atomic trace
equivalence of spines and decided by the class-saturation search
(`decideTwoCellConvFull?`, `FreeTwoCell/TwoCellWordProblemDecision`).  The decision is
FUEL-GATED: the honest front door returns `none` when the frontier-exhaustion check
fails, and the computed sufficient fuel (the class-size pigeonhole) is still owed.
This is the free-2-category instance of the Mazurkiewicz trace word problem.

**Rung 2 — SATURATED (presentation relations), decided PER-PRESENTATION.**  Adding
relations (the walking adjunction's triangle identities) breaks every generic invariant:
generator count is not preserved (`saturatedConv_doesNotPreserveGeneratorCount`), and
cell reconstruction from the matching invariant is REFUTED at general signatures
(`fxMode_hasArcCellReconstructionRefutedAtGeneralSignature`, the parallel-pair
counterexample) — so each presentation needs its own model.  For the walking adjunction
the model is the arc matching: soundness is unconditional
(`fxMode_hasMatchingSaturatedCongruence`); completeness (the Schanuel–Street
monotone-map reconstruction) and hence the decision are in flight.  This mirrors the
`mode-8` framing (the free 2-category word problem routed through an engine) made
honest: the engine is per-presentation, not universal.

**Rung 3 — ARBITRARY finite presentations, UNDECIDABLE.**  No generic procedure exists
above rung 2: already 1-cell convertibility under the 2-cells of a ONE-OBJECT
2-polygraph is the word problem of the finitely presented monoid it presents, which is
undecidable (Markov 1947, Post 1947; the polygraphic framing is Burroni's).  The wall
is CITED here, not mechanized — the reduction into the kernel's polygraph substrate is
tracked as its own arc, and the marker below stays `false` until it lands.  This is the
same undecidability-frontier discipline the term axis uses: state the wall as a marker
with the citation, never as an unproved theorem.

Lives in `Tier0/Mode/` (not `Polygraph/`) although its declarations stay in the
`FX1Poly.Polygraph` namespace: the rung-1 and ceiling pins reference the Tier0 mode-floor
markers (`FX1Poly.Tier0.fxMode_hasDecidable*`), and the layer DAG forbids Polygraph → Tier0
imports — a cross-layer ledger must live in the LATER layer.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The wall marker (rung 3's mechanization status) -/

/-- **Honesty marker.**  The undecidability REDUCTION for rung 3 — embedding a finitely
presented monoid with undecidable word problem (Markov 1947 / Post 1947) as a one-object
2-polygraph whose 1-cell convertibility decides it — is NOT mechanized; the wall stands
on the citation.  `= false` until the reduction lands. -/
def fxMode_hasArbitraryTwoCellUndecidabilityReduction : Bool := false

/-! ## The ledger -/

/-- The three-rung decidability ledger for the 2-cell word problem.  Each field is
pinned to its source marker by a `rfl` theorem below. -/
structure DecidableCeilingLedger where
  /-- Rung 1: the FREE word problem is decided generically over any signature. -/
  hasGenericFreeDecision : Bool
  /-- Rung 1 honesty: the generic free decision is fuel-gated (the computed
  sufficient fuel from the class-size pigeonhole is still owed). -/
  isFreeDecisionFuelGated : Bool
  /-- Rung 2: saturated soundness at the walking adjunction (the matching invariant
  respects the triangle relations), unconditional. -/
  hasSaturatedSoundness : Bool
  /-- Rung 2: saturated completeness (equal matchings reconstruct a saturated
  convertibility) — the monotone-map reconstruction, in flight. -/
  hasSaturatedCompleteness : Bool
  /-- Rung 2 honesty: GENERIC saturated completeness is refuted — reconstruction from
  the matching fails at general signatures, forcing the per-presentation discipline. -/
  wasGenericSaturatedCompletenessRefuted : Bool
  /-- Rung 2: the assembled saturated decision at the walking adjunction. -/
  hasSaturatedDecision : Bool
  /-- Rung 3: the undecidability reduction, mechanized (the wall is cited either way). -/
  hasUndecidabilityReductionMechanized : Bool

/-- ★ The current ledger value — the honest boundary as of the free-decision landing. -/
def fxDecidableCeiling : DecidableCeilingLedger where
  hasGenericFreeDecision := true
  isFreeDecisionFuelGated := true
  hasSaturatedSoundness := true
  hasSaturatedCompleteness := false
  wasGenericSaturatedCompletenessRefuted := true
  hasSaturatedDecision := false
  hasUndecidabilityReductionMechanized := false

/-! ## The pins — ledger fields match the source markers definitionally -/

/-- Rung 1 pin: the free rung matches the Tier0 free-fragment marker. -/
theorem fxDecidableCeiling_freeRung_matchesMarker :
    fxDecidableCeiling.hasGenericFreeDecision
      = FX1Poly.Tier0.fxMode_hasDecidableFreeTwoCellEquality := rfl

/-- Rung 2 pin: saturated soundness matches the matching-congruence marker. -/
theorem fxDecidableCeiling_saturatedSoundness_matchesMarker :
    fxDecidableCeiling.hasSaturatedSoundness = fxMode_hasMatchingSaturatedCongruence := rfl

/-- Rung 2 pin: saturated completeness matches the canonicalization marker. -/
theorem fxDecidableCeiling_saturatedCompleteness_matchesMarker :
    fxDecidableCeiling.hasSaturatedCompleteness
      = fxMode_hasSaturatedMatchingCanonicalization := rfl

/-- Rung 2 pin: the generic-completeness refutation matches the arc-reconstruction
refutation marker (the parallel-pair counterexample). -/
theorem fxDecidableCeiling_genericSaturatedRefutation_matchesMarker :
    fxDecidableCeiling.wasGenericSaturatedCompletenessRefuted
      = fxMode_hasArcCellReconstructionRefutedAtGeneralSignature := rfl

/-- Rung 2 pin: the saturated decision matches the monotone-map decision marker. -/
theorem fxDecidableCeiling_saturatedDecision_matchesMarker :
    fxDecidableCeiling.hasSaturatedDecision
      = fxMode_hasSaturatedTwoCellMonotoneMapDecision := rfl

/-- Rung 3 pin: the mechanization status matches the wall marker above. -/
theorem fxDecidableCeiling_undecidabilityWall_matchesMarker :
    fxDecidableCeiling.hasUndecidabilityReductionMechanized
      = fxMode_hasArbitraryTwoCellUndecidabilityReduction := rfl

/-- The ceiling itself: the GENERAL mode-3 marker (relations + ungated) sits ABOVE
every shipped rung and correctly stays `false` — flipping it requires the saturated
decision (rung 2 completed at the walking adjunction) plus the ungated free fuel
bound, and can never be generic past rung 2 (rung 3 is the wall). -/
theorem fxDecidableCeiling_generalMarkerSitsAboveLedger :
    FX1Poly.Tier0.fxMode_hasDecidableTwoCellEquality = false := rfl

end FX1Poly.Polygraph
