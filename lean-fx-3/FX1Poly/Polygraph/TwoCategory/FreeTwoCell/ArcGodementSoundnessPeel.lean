import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # mode-3 floor — the Godement arc soundness CLOSED at the walking adjunction, via the shipped peel

`FreeTwoCellArcPartitionCommute` REFUTED (`not_arcGodementSamePartition`) the over-quantified Godement arc
residual and re-stated the true, freshness-conditioned residual `ArcGodementSamePartitionFresh`, marked the "one
remaining soundness obligation" (`fxMode_hasArcGodementSamePartitionFreshProof = false`).  The whole FreeTwoCell
edifice then routed soundness through that residual (taken as a HYPOTHESIS in
`arcStructureOf_sound_of_arcGodementSamePartitionFresh`).

This file discharges the soundness side OUTRIGHT for the walking adjunction — with NO dependence on that residual
— by composing a chain that was shipped in the `WalkingAdjunction` layer but never wired to the top:

  ★ `twoCellConvFull_spineTraceEquiv` : `TwoCellConvFull … → SpineTraceEquiv` on the spines (whisker layer);
  ★ `SpineTraceEquiv.toAtomicTraceEquiv` : the block-level Godement equivalence IS an ATOMIC (single-swap) trace
    equivalence — the bubble-lift `SpineGodementStep.toAtomicTraceEquiv` under the closure operators;
  ★ `extractArc_eq_of_atomicTraceEquiv` (the shipped **peel**) : along ANY atomic trace equivalence over the
    walking adjunction, the arc extraction is invariant — from every state that is fresh, forest-rooted, has
    positive `nextFresh` bounding the boundary, and whose open-wire count tracks the spine's chained boundary;
  ★ `RawTwoCellExpr.spineBoundaryChained_spine` + `arcStateFresh_initial` + `isUnionFindForest_nil` : the
    fresh-initial fold state `mk (range n) [] n 0 [] []` (from which `arcStructureOf` reads) meets EVERY peel
    hypothesis but one — `0 < n`, the empty-boundary positivity.

So `arcStructureOf` is sound under the COMPLETE `TwoCellConvFull` at the walking adjunction whenever the source
boundary is non-empty (`0 < sourcePath.length`), and the freshness-conditioned residual is NOT needed at all: the
peel already carries it (the atomic swap dispatcher is the disjoint-support independence, freshness supplied by
the reachable fold).  The refuted `∀`-state markers (`fxMode_hasArcPartitionCommuteProof`,
`fxMode_hasArcBlockCommuteProof` in `GodementIndependence`) STAY `false` — they name over-quantified Props that
are machine-refuted and can never be flipped; this file makes them MOOT, closing the soundness they guarded via
the freshness-carrying peel instead.

## What is honest-DEFERRED

  * The **empty-boundary** case `sourcePath.length = 0` — the peel needs `0 < nextFresh` (its fresh-block
    transposition fixes the zero fallback and the cap-read sentinel is `0`), which fails at `nextFresh = 0`.
  * **General signatures** — `extractArc_eq_of_atomicTraceEquiv` is `adjunctionModeSignature`-hardcoded through
    its 2×2 cup/cap swap dispatcher; `ArcGodementSamePartitionFresh signature` (general) remains open as stated.
  * The **completeness / reconstruction** side (the `isTrue` branch of the decision — `arcStructureOf` equality
    forces convertibility) is a SEPARATE obligation, taken here as a hypothesis exactly as the ungated decision
    corollary does.

Raw Lean 4 + Init; the range-length helper is hand-rolled off `List.range.loop` (core `List.length_range` leaks
`propext`); the assembly is definitional unfolding of `arcStructureOf` / `arcStructureOfSpineList` onto the peel's
conclusion.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## `propext`-free `(List.range n).length = n` -/

/-- `List.range.loop count acc` lists `count` new elements in front of `acc`, so its length is `count + acc.length`
— hand-rolled (core `List.length_range` leaks `propext`). -/
private theorem rangeLoopLengthPeel : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [rangeLoopLengthPeel count (count :: accumulated)]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count` — the initial fold state's open-wire count. -/
private theorem rangeLengthPeel (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthPeel count []]
  exact Nat.add_zero count

/-! ## The soundness side, closed at the walking adjunction (non-empty boundary) -/

/-- ★ **`arcStructureOf` is sound under the COMPLETE `TwoCellConvFull` at the walking adjunction, with NO
freshness residual.**  From `TwoCellConvFull firstCell secondCell` the two cells' spines are trace-equivalent
(`twoCellConvFull_spineTraceEquiv`), hence ATOMIC-trace-equivalent (`SpineTraceEquiv.toAtomicTraceEquiv`, the
bubble-lift of the Godement block move to single swaps), and the shipped peel
`extractArc_eq_of_atomicTraceEquiv` reads equal arc extracts from the fresh-initial fold state
`mk (range n) [] n 0 [] []` — which is fresh (`arcStateFresh_initial`), forest-rooted (`isUnionFindForest_nil`),
open-wire-counted `n` (`rangeLengthPeel`), boundary-chained at `n` (`spineBoundaryChained_spine`), with
`n ≤ n` — provided `0 < n = sourcePath.length` (the empty-boundary positivity the peel needs).  This closes the
soundness side WITHOUT the residual `ArcGodementSamePartitionFresh`: the peel already carries the
disjoint-support independence, freshness supplied by the reachable fold. -/
theorem arcStructureOf_sound_of_convFull_adjunction
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (sourcePositive : 0 < sourcePath.length)
    (convFull : TwoCellConvFull adjunctionModeSignature firstCell secondCell) :
    arcStructureOf firstCell = arcStructureOf secondCell := by
  have atomicEquiv : AtomicTraceEquiv adjunctionModeSignature firstCell.spine secondCell.spine :=
    (twoCellConvFull_spineTraceEquiv convFull).toAtomicTraceEquiv
  show arcStructureOfSpineList sourcePath.length firstCell.spine
      = arcStructureOfSpineList sourcePath.length secondCell.spine
  show extractArc sourcePath.length
        (processArcSpine (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])
          firstCell.spine)
      = extractArc sourcePath.length
        (processArcSpine (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])
          secondCell.spine)
  exact extractArc_eq_of_atomicTraceEquiv atomicEquiv
    (ArcWireState.mk (List.range sourcePath.length) [] sourcePath.length 0 [] [])
    sourcePath.length sourcePath.length
    (arcStateFresh_initial sourcePath.length)
    isUnionFindForest_nil
    sourcePositive
    (Nat.le_refl _)
    (rangeLengthPeel sourcePath.length)
    firstCell.spineBoundaryChained_spine

/-- ★ **The walking-adjunction free-2-cell convertibility decision, with the soundness side fully discharged.**
Mirrors `decidableTwoCellConvFull_of_fresh` but DROPS the `ArcGodementSamePartitionFresh` residual: the `isFalse`
branch is the unconditional (modulo `0 < sourcePath.length`) `arcStructureOf_sound_of_convFull_adjunction`.  Only
the completeness/reconstruction direction (`isTrue`) remains a hypothesis — the separate `arcStructureOf`
reconstruction obligation, exactly as the ungated corollary takes it. -/
def decidableTwoCellConvFull_of_adjunction
    (reconstruct : ∀ {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
        {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
        {firstCell secondCell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath},
        arcStructureOf firstCell = arcStructureOf secondCell →
          TwoCellConvFull adjunctionModeSignature firstCell secondCell)
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (sourcePositive : 0 < sourcePath.length)
    (firstCell secondCell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConvFull adjunctionModeSignature firstCell secondCell) :=
  if structuresEqual : arcStructureOf firstCell = arcStructureOf secondCell
  then isTrue (reconstruct structuresEqual)
  else isFalse (fun convFull =>
    structuresEqual (arcStructureOf_sound_of_convFull_adjunction sourcePositive convFull))

/-! ## Honesty markers -/

/-- **Honesty marker — the Godement arc SOUNDNESS side is CLOSED at the walking adjunction via the peel.**
`arcStructureOf_sound_of_convFull_adjunction` proves `arcStructureOf` invariant under the COMPLETE
`TwoCellConvFull` at `adjunctionModeSignature` whenever `0 < sourcePath.length`, with NO freshness residual: it
composes `twoCellConvFull_spineTraceEquiv` → `SpineTraceEquiv.toAtomicTraceEquiv` (the shipped bubble-lift) →
`extractArc_eq_of_atomicTraceEquiv` (the shipped peel) at the fresh-initial fold state.
`decidableTwoCellConvFull_of_adjunction` packages it into the decision, the `isFalse` branch owing nothing beyond
`0 < sourcePath.length`.  The refuted `∀`-state markers `fxMode_hasArcPartitionCommuteProof` /
`fxMode_hasArcBlockCommuteProof` stay `false` (they name over-quantified Props that are machine-refuted) and are
thereby made MOOT — the soundness they guarded is closed by the freshness-carrying peel, not by flipping them.
`= true`. -/
def fxMode_hasArcGodementSoundnessViaPeel : Bool := true

/-- **Honesty marker — the peel closure is walled at the empty boundary and off the walking adjunction.**  The
soundness closure requires `0 < sourcePath.length` (the peel's `0 < nextFresh`, needed because its fresh-block
transposition fixes the zero fallback and the cap-read sentinel is `0`), so the empty-boundary case
`sourcePath.length = 0` is honestly deferred.  `extractArc_eq_of_atomicTraceEquiv` is
`adjunctionModeSignature`-hardcoded through its 2×2 cup/cap swap dispatcher, so the general-signature
`ArcGodementSamePartitionFresh signature` remains open as stated.  The completeness/reconstruction direction is a
separate obligation, taken as a hypothesis in `decidableTwoCellConvFull_of_adjunction`.  `= false`. -/
def fxMode_hasArcGodementSoundnessPeelEmptyBoundary : Bool := false

end FX1Poly.Polygraph
