import FX1Poly.Tier0.Mode.Mode
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TwoCellWordProblemDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TotalWordProblemDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCongruenceProved
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCanonicalization
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingDecisionAssembly
import FX1Poly.Tier0.Mode.TierBThinDecision
import FX1Poly.Tier0.Mode.ExhibitedConvergentDecision

/-! # DecidableCeilingLedger — the honest boundary of the 2-cell word problem (CEIL rung map)

The mechanized theory sits on a three-rung decidability ladder, and this ledger is the
machine-checked statement of exactly where each rung stands.  Every field of the ledger
value is PINNED to the source honesty marker of the file that shipped (or refuted) it —
a marker drift breaks a `rfl` here, so the ledger cannot silently rot.

**Rung 1 — FREE, decided GENERICALLY and UN-GATED.**  Over ANY mode signature,
`TwoCellConvFull` (the relation-free Godement/whisker congruence) is characterized by
atomic trace equivalence of spines and decided by the class-saturation search.  The
class-size fuel is now DISCHARGED (`FreeTwoCell/TotalWordProblemDecision`,
`fxMode_hasUngatedFreeTwoCellDecision = true`): a boundary-chained seed's whole
`AtomicTraceEquiv` class lives inside the computable list `chainedSeedClassList`
(`chainedSeedClassList_isComplete`), and a complete class list forces the saturation
frontier to exhaust within the computed fuel `classSaturationFuel` — the stabilization
theorem `didExhaustFrontier_ofCompleteClassList`, itself the strict-potential-descent
argument `saturationPotentialStep` (Kleene/Knaster–Tarski least-fixpoint on the finite
trace class; Mazurkiewicz trace theory, Diekert–Rozenberg *Book of Traces* 1995).  So
`decideTwoCellConvFull` is total — no fuel hypothesis, no `Option`, no exhaustion gate.
This is the free-2-category instance of the Mazurkiewicz trace word problem, decided
outright.

**Rung 2 — SATURATED (presentation relations), decided PER-PRESENTATION.**  Adding
relations (the walking adjunction's triangle identities) breaks every generic invariant:
generator count is not preserved (`saturatedConv_doesNotPreserveGeneratorCount`), and
cell reconstruction from the matching invariant is REFUTED at general signatures
(`fxMode_hasArcCellReconstructionRefutedAtGeneralSignature`, the parallel-pair
counterexample) — so each presentation needs its own model.  For the walking adjunction
the model is the boundary ARC MATCHING `matchingOf` (Joyal–Street `DiagramType`), the
variance-correct carrier: soundness is unconditional
(`fxMode_hasMatchingSaturatedCongruence`), completeness is discharged through the
matching reconstruction + Track-B spine-trace join
(`fxMode_hasSaturatedMatchingCanonicalization`, term
`saturatedMatchingCanonicalization_holds`), and the assembled decision has LANDED
(`fxMode_hasSaturatedMatchingDecisionAssembled`, term `decideSaturatedTwoCellConv_ofSeed`)
— rung 2 is COMPLETE at the walking adjunction, all zero-axiom.  Note: the earlier
Schanuel–Street MONOTONE-MAP reconstruction route is RETIRED for this decision — its
`monotoneMapOf` fold is refuted as a canonicalization map by
`covariantMonotoneMapOf_notSound` (variance flips by mode); its files are kept only for
the refutation theorems cited here.  This mirrors the `mode-8` framing (the free
2-category word problem routed through an engine) made honest: the engine is
per-presentation, not universal.

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
  /-- Rung 1 honesty: is the generic free decision still fuel-gated?  Now `false` — the
  sufficient fuel is DISCHARGED (`decideTwoCellConvFull`, total over any signature; backed
  by `chainedSeedClassList_isComplete` + `didExhaustFrontier_ofCompleteClassList`). -/
  isFreeDecisionFuelGated : Bool
  /-- Rung 2: saturated soundness at the walking adjunction (the matching invariant
  respects the triangle relations), unconditional. -/
  hasSaturatedSoundness : Bool
  /-- Rung 2: saturated completeness (equal matchings reconstruct a saturated
  convertibility) — LANDED via the matching-route spine-trace JOIN
  (`saturatedMatchingCanonicalization_holds`); the retired monotone-map route is dead. -/
  hasSaturatedCompleteness : Bool
  /-- Rung 2 honesty: GENERIC saturated completeness is refuted — reconstruction from
  the matching fails at general signatures, forcing the per-presentation discipline. -/
  wasGenericSaturatedCompletenessRefuted : Bool
  /-- Rung 2: the assembled saturated decision at the walking adjunction. -/
  hasSaturatedDecision : Bool
  /-- Tier B (Gratzer): thin / poset-enriched decision — 2-cell conv = kernel of a decidable classifier,
  exhibited at the walking involution (Z/2 parity).  Sits between the free rung and the wall. -/
  hasTierBThinDecision : Bool
  /-- Tier C (Squier / Knuth-Bendix): exhibited-convergent decision — a hand-exhibited convergent
  presentation decides its word problem, exhibited at the involution presentation `s.s -> id`. -/
  hasExhibitedConvergentDecision : Bool
  /-- Rung 3: the undecidability reduction, mechanized (the wall is cited either way). -/
  hasUndecidabilityReductionMechanized : Bool

/-- ★ The current ledger value — the honest boundary as of the SATURATED matching-decision
landing, now with the two Wave-2 decidable BANDS between the saturated rung and the wall.  Rung 2 is
COMPLETE at the walking adjunction (soundness, completeness, and the assembled decision), all zero-axiom via
the matching carrier; Tier B (Gratzer thin) and Tier C (Squier/KB exhibited-convergent) are both DECIDED at
the walking involution (`hasTierBThinDecision`, `hasExhibitedConvergentDecision` — the same object from two
directions, tied by `equationalTheory_iff_involutionOneCellConv`); rung 1 stays ungated and rung 3 stays
walled. -/
def fxDecidableCeiling : DecidableCeilingLedger where
  hasGenericFreeDecision := true
  isFreeDecisionFuelGated := false
  hasSaturatedSoundness := true
  hasSaturatedCompleteness := true
  wasGenericSaturatedCompletenessRefuted := true
  hasSaturatedDecision := true
  hasTierBThinDecision := true
  hasExhibitedConvergentDecision := true
  hasUndecidabilityReductionMechanized := false

/-! ## The pins — ledger fields match the source markers definitionally -/

/-- Rung 1 pin: the free rung matches the Tier0 free-fragment marker. -/
theorem fxDecidableCeiling_freeRung_matchesMarker :
    fxDecidableCeiling.hasGenericFreeDecision
      = FX1Poly.Tier0.fxMode_hasDecidableFreeTwoCellEquality := rfl

/-- Rung 1 pin: the fuel-gate honesty field is the NEGATION of the ungated-decision
marker.  `isFreeDecisionFuelGated = false` holds ONLY because
`fxMode_hasUngatedFreeTwoCellDecision = true` (backed by `decideTwoCellConvFull` on the
complete class list `chainedSeedClassList_isComplete` with the stabilization theorem
`didExhaustFrontier_ofCompleteClassList`) — flip the marker back and this `rfl` breaks, so
the ledger cannot claim ungated without the backing term. -/
theorem fxDecidableCeiling_freeDecisionUngated_matchesMarker :
    fxDecidableCeiling.isFreeDecisionFuelGated
      = not fxMode_hasUngatedFreeTwoCellDecision := rfl

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

/-- Rung 2 pin: the saturated decision matches the assembled MATCHING-route decision marker.
The monotone-map route (`fxMode_hasSaturatedTwoCellMonotoneMapDecision`) is RETIRED — its
`monotoneMapOf` carrier is refuted by `covariantMonotoneMapOf_notSound` — so the pin binds to
the live matching route `fxMode_hasSaturatedMatchingDecisionAssembled`, backed by
`decideSaturatedTwoCellConv_ofSeed` on the inhabited `saturatedMatchingCanonicalization_holds`. -/
theorem fxDecidableCeiling_saturatedDecision_matchesMarker :
    fxDecidableCeiling.hasSaturatedDecision
      = fxMode_hasSaturatedMatchingDecisionAssembled := rfl

/-- Tier B pin: the thin/poset-enriched decision matches the Tier-B thin marker (backed by
`decideThinTwoCellConv` on `fxInvolutionThinModeTheory`, itself pinned to
`fxInvolution_hasOneCellWordProblemDecided`). -/
theorem fxDecidableCeiling_tierBThin_matchesMarker :
    fxDecidableCeiling.hasTierBThinDecision = fxMode_hasTierBThinDecision := rfl

/-- Tier C pin: the exhibited-convergent decision matches the Tier-C marker (backed by
`decideInvolutionEquationalTheory` via the shipped KB engine on the convergent involution presentation, tied
to Tier B by `equationalTheory_iff_involutionOneCellConv`). -/
theorem fxDecidableCeiling_exhibitedConvergent_matchesMarker :
    fxDecidableCeiling.hasExhibitedConvergentDecision = fxMode_hasExhibitedConvergentDecision := rfl

/-- Rung 3 pin: the mechanization status matches the wall marker above. -/
theorem fxDecidableCeiling_undecidabilityWall_matchesMarker :
    fxDecidableCeiling.hasUndecidabilityReductionMechanized
      = fxMode_hasArbitraryTwoCellUndecidabilityReduction := rfl

/-- The ceiling itself: the GENERAL mode-3 marker (relations + ungated) sits ABOVE
every shipped rung and correctly stays `false`.  Both lower ingredients are now
DISCHARGED — rung 2 saturated decision (`hasSaturatedDecision = true`) and rung 1's free
fuel bound (`isFreeDecisionFuelGated = false`, `fxMode_hasUngatedFreeTwoCellDecision`) —
yet the marker STILL stays `false`: it is the GENERAL cross-signature claim WITH
presentation relations, which can never be generic past rung 2 (rung 3 is the
undecidability wall, FLAG A).  The walking-adjunction saturated decision and the ungated
free decision are necessary ingredients, not the general marker. -/
theorem fxDecidableCeiling_generalMarkerSitsAboveLedger :
    FX1Poly.Tier0.fxMode_hasDecidableTwoCellEquality = false := rfl

/-! ## fib-3 honest status ledger (marker + tracker reconciliation, CEIL-1 close point)

A single reconciliation of every fib-3 / mode-3 decidability marker against its live value
and the tracker.  No theorem here — a status map so the honest boundary reads in one place.
The mode-3 decision splits into TWO general flags, each with a DIFFERENT wall; the
per-presentation saturated instance sits BELOW both and is TRUE+backed.

FLAG A — `FX1Poly.Tier0.fxMode_hasDecidableTwoCellEquality = false` (`Mode.lean`).
  WALL: rung-3 undecidability of ARBITRARY finite presentations.  A one-object f.p.
  2-polygraph encodes a f.p. monoid; its 1-cell convertibility is the monoid word problem,
  undecidable (Markov 1947 / Post 1947; Burroni polygraphic framing).  PERMANENT — no
  procedure can be generic past rung 2.  Mechanization status of the reduction:
  `fxMode_hasArbitraryTwoCellUndecidabilityReduction = false` (wall CITED, not mechanized).

FLAG B — `FX1Poly.Tier0.fxMode_hasModeRelativeConvDecision = false`
  (`ModeRelativeMetatheory.lean`).  WALL: a RELATION MISMATCH, NOT undecidability and NOT an
  owed decision.  Its parameter is the FINER free BARE `TwoCellConv` over ANY computad (the
  snakes provably do NOT collapse, `leftSnakeSaturatedButNotFree`), owed
  `(traceDecision, reconstruct)` of `AdjunctionTwoCellWordProblem`.  BOTH natural readback
  carriers are machine-witnessed to MISS the over-fine bare relation, from opposite sides: the
  `traceDecision` is DISCHARGED ungated (`adjunctionSpineTraceDecision`, via
  `decideAtomicTraceEquivOfChainedSeed` + FREE-5), yet the SPINE-carried `reconstruct` into
  BARE `TwoCellConv` is provably FALSE — now MECHANIZED as
  `adjunctionSpineTraceReconstruction_refuted` (FREE-2, via the bare-conv invariant
  `RawTwoCellExpr.whiskerSum`, scoring `2` vs `0` on the identity-1-cell whisker), the `¬`
  earlier passes only argued; and the finer interchange-free `nfCell` carrier OVER-separates —
  a `TwoCellConv` pair with distinct normal forms
  (`interchangeFreeNormalForm_notCompleteInvariantForBareConv`), so "normalize + compare" gives
  false negatives.  The categorically-FAITHFUL
  `TwoCellConvFull` decision IS unconditional (`adjunctionDecideTwoCellConvFull`,
  `fxMode_hasFaithfulTwoCellDecisionModuloTrace = true`), and the SATURATED modulo-triangles
  relation the MTT fibration consumes is decided too
  (`fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction`) — so fib-3 is NOT blocked on
  FLAG B.  The arc route (`ArcReconstruction`, `fxMode_hasArcStructureReconstruction` /
  `fxMode_hasArcGodementIndependenceProof`, both `false`) is now a NON-BLOCKING geometry-native
  alternative for the faithful decision, not this flag's gate.  fib-3 Wave-1(b) TERMINAL: bare
  `TwoCellConv` is kept honestly live as an over-fine relation whose decidability is GENUINELY
  OPEN (the interchange critical-pair convergence) — re-openable, NOT walled by undecidability
  (that is FLAG A).  The owed statement is unchanged; the flag stays `false` as a
  permanent-as-stated disposition, both readback routes now mechanized-refuted.

SATURATED (per-presentation, below both flags) — TRUE+backed, zero-axiom:
  * `fxMode_hasSaturatedMatchingCanonicalizationCarrier = true` — carrier `matchingOf`.
  * `fxMode_hasSaturatedMatchingCanonicalization = true` — term
    `saturatedMatchingCanonicalization_holds` (`SaturatedMatchingDecisionAssembly`).
  * `fxMode_hasSaturatedMatchingDecisionAssembled = true` — term
    `decideSaturatedTwoCellConv_ofSeed`.
  * `fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction = true`
    (`ModeRelativeMetatheory`) — SCOPED to the adjunction WITH triangle identities; does
    NOT flip FLAG B (finer free relation) nor FLAG A (general undecidability).
  * `fxMode_hasDecidableFreeTwoCellEquality = true` (`Mode.lean`) — the FREE fragment
    (`TwoCellConvFull`) decided generically (rung 1), now UN-GATED:
    `fxMode_hasUngatedFreeTwoCellDecision = true` (`TotalWordProblemDecision`), term
    `decideTwoCellConvFull`, so `isFreeDecisionFuelGated = false`.

RETIRED-FOR-DECISION (monotone route, #1975/#1999) — KEPT, NOT deleted; terminal markers
  all `false`: `fxMode_hasSaturatedTwoCellMonotoneMapDecision`,
  `…MonotoneMapGodementSoundness`, `…MonotoneMapFaithfulness`,
  `fxMode_hasMonotoneRouteFaithfulnessReconstructed`.  The `monotoneMapOf` fold is refuted
  as a canonicalization map by `covariantMonotoneMapOf_notSound` /
  `covariantFold_notACanonicalizationMap` (variance flips by mode).  `MonotoneMap` /
  `MonotoneFaithful` are kept because they HOST those refutation theorems, cited by this
  ledger (`fxDecidableCeiling_saturatedDecision_matchesMarker` pin) and imported by the live
  carrier file.  Re-aimable at the walking MONAD.  See the quarantine note atop
  `WalkingAdjunction/MonotoneMap.lean`.

CEIL-1 TIERING (this ledger): rung 1 free-generic (UN-GATED, total decider) < rung 2
  saturated per-presentation (COMPLETE at the walking adjunction) < { Tier B thin, Tier C
  exhibited-convergent } < rung 3 arbitrary undecidable (FLAG A's wall).  Every `fxDecidableCeiling` field
  is `rfl`-pinned to its source marker above, so this status map cannot drift from the mechanized values.

WAVE-2 DECIDABLE BANDS (both TRUE+backed, zero-axiom, strictly below the rung-3 wall):
  * `fxMode_hasTierBThinDecision = true` (`TierBThinDecision`) — Gratzer: MTT conversion is decidable when
    the mode theory decides its modalities/2-cells; for a THIN theory (<= one 2-cell per parallel pair) that
    is a decidable-classifier comparison (`decideThinTwoCellConv`).  Instance: the walking involution as
    `fxInvolutionThinModeTheory` (classifier = Z/2 parity), citing `fxInvolution_hasOneCellWordProblemDecided`.
    Gratzer, arXiv:2106.01414 / 2301.11842.  CAVEAT: a NON-thin f.p. mode theory can encode an undecidable
    word problem — that is FLAG A's wall; do not generalize past thin.
  * `fxMode_hasExhibitedConvergentDecision = true` (`ExhibitedConvergentDecision`) — Squier/Knuth-Bendix: a
    HAND-EXHIBITED convergent presentation decides its word problem via the shipped KB engine
    (`ConvergentNormalizer.decidableEquationalTheory`, term `decideInvolutionEquationalTheory`).  Instance:
    the involution presentation `s.s -> id` IS convergent (terminating: length drops by 2; confluent: the
    parity-NF funnel, no critical pairs), and its `EquationalTheory` COINCIDES with the Tier-B thin relation
    (`equationalTheory_iff_involutionOneCellConv`), tying Tiers B and C on the SAME object.  CAVEATS:
    convergence is EXHIBITED, not COMPLETED (the completion algorithm/fairness is not mechanized; the
    normalizer is data); by Squier {finite convergent presentation} is a PROPER subclass of {decidable word
    problem} (arXiv:1402.2587), so this is not a decidability criterion; does not lift past this presentation. -/
end FX1Poly.Polygraph
