import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # mode-3 floor — the freshness+FOREST-gated Godement arc residual, reduced from the LIVE count route

`FreeTwoCellArcSamePartitionFresh` (leg B) reduced the freshness-conditioned residual `ArcGodementSamePartitionFresh`
to the renaming existence `ArcGodementSwapRenameable`, and `WalkingAdjunctionArcSwapRenameable` (W9/W10) built the
LIVE, satisfiable count route to that: `arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` proves the two
Godement run orders are `ArcRenameRel`-related from the CORRECTED obligation `ArcGodementCoreSwapSimCount` — but only
on a state that is fresh AND a union-find FOREST AND non-degenerate (`0 < nextFresh`).

`ArcFreshnessInvariant` truth-probed the exact gap this exposes: `ArcStateFresh` does NOT imply
`isUnionFindForest links` (a fresh state can be cyclic — `arcFreshCyclicState`).  So the standalone leg-B residual
`ArcGodementSamePartitionFresh` (quantified over ALL fresh states, no forest / non-degeneracy) is STRICTLY STRONGER
than what the count route can supply: `ArcGodementCoreSwapSimCount → ArcGodementSamePartitionFresh` does NOT hold
over the cyclic fresh states.  This file lands the additive fix — the residual STATED at exactly the hypothesis
strength the count route provides:

  ★ `ArcGodementSamePartitionFreshForest` — `ArcGodementSamePartitionFresh` strengthened with the two reachable-state
    invariants the count route consumes: `isUnionFindForest state.links` and `0 < state.nextFresh`.  (These are NOT
    extra assumptions on the DECISION — every state reachable from the fold seed `mk (range n) [] n 0 [] []` is a
    forest, `isUnionFindForest_initialLinks` / `isUnionFindForest_runArcCell`, with `nextFresh = n ≥ 1` at any
    non-empty boundary; the empty boundary is handled by the counter-shift proxy, `ArcGodementSoundnessPeelEmptyBoundary`.)

  ★ `arcGodementSamePartitionFreshForest_of_coreSwapSimCount` — the reduction, ASSEMBLED from shipped, zero-axiom
    pieces: `arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` (the LIVE count-route pointwise parent
    reduction) emits the renaming witness `∃ σ, ArcRenameRel …` at each fresh forest non-degenerate state, and
    `sameArcPartition_of_renameRel` (the renaming-invariance of the partition view) turns it into the
    `SameArcPartition` the residual demands.

## What is honest-DEFERRED (unchanged: residual (2))

The SOLE hypothesis of `arcGodementSamePartitionFreshForest_of_coreSwapSimCount` is `ArcGodementCoreSwapSimCount`
— residual (2), the explicit block-swap `σ` over arbitrary cells (the geometric Mazurkiewicz fitting invariant),
`fxMode_hasArcGodementSwapRenameableProof2 = false`.  This file does NOT construct it and does NOT flip it; it only
removes the false generality from the fresh residual, so the reduction now bottoms out in EXACTLY the one open
obligation.  `fxMode_hasArcGodementSamePartitionFreshProof` (the parent's leg-B marker) stays `false`.

Raw Lean 4 + Init; the reduction is a direct assembly of two shipped lemmas (no new recursion / decide).
Per-declaration `#assert_no_axioms` + independent `#print axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The freshness+forest-gated residual -/

/-- ★ **The freshness+FOREST-conditioned Godement arc residual.**  Identical to `ArcGodementSamePartitionFresh`
(`FreeTwoCellArcPartitionCommute`) except the starting `state` is additionally required to be a union-find FOREST
(`isUnionFindForest state.links`) and non-degenerate (`0 < state.nextFresh`) — the two reachable-state invariants
the LIVE count route (`arcGodementSwapRenameable_pointwise_of_coreSwapSimCount`) actually consumes, and which
`ArcStateFresh` alone does NOT imply (`arcFreshCyclicState` is fresh but cyclic).  Under these hypotheses the two
Godement run orders land `SameArcPartition`.  This is the residual at exactly the strength the count route provides
— the standalone `ArcGodementSamePartitionFresh` is strictly stronger and NOT reducible to
`ArcGodementCoreSwapSimCount`. -/
def ArcGodementSamePartitionFreshForest (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : ArcWireState),
    ArcStateFresh state → bottomCount ≤ state.nextFresh →
      isUnionFindForest state.links → 0 < state.nextFresh →
    SameArcPartition bottomCount
      (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processArcSpine
        (runArcCell (runArcCell (runArcCell
            (runArcCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-! ## The reduction from the LIVE count route -/

/-- ★ **The reduction.**  `ArcGodementCoreSwapSimCount` (residual (2), the count-level block-swap obligation)
IMPLIES the freshness+forest-gated residual `ArcGodementSamePartitionFreshForest`.  At each fresh, forest,
non-degenerate starting state the LIVE pointwise reduction
`arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` emits the renaming witness `∃ σ, ArcRenameRel …` between
the two Godement run orders, and `sameArcPartition_of_renameRel` (the renaming-invariance of the partition view)
turns it into the `SameArcPartition` the residual demands.  Both inputs are shipped and zero-axiom, so this
reduction bottoms out in EXACTLY the one open obligation — nothing weaker is being smuggled in. -/
theorem arcGodementSamePartitionFreshForest_of_coreSwapSimCount {signature : ModeSignature}
    (coreSwapSimCount : ArcGodementCoreSwapSimCount signature) :
    ArcGodementSamePartitionFreshForest signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state stateFresh bottomLe stateForest nfPos
  obtain ⟨sigma, rel⟩ := arcGodementSwapRenameable_pointwise_of_coreSwapSimCount coreSwapSimCount
    cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount state
    stateFresh bottomLe stateForest nfPos
  exact sameArcPartition_of_renameRel bottomCount sigma _ _ rel

/-! ## Honesty markers -/

/-- **Honesty marker — the freshness+forest residual is BUNDLED and REDUCED from the count route (zero-axiom).**
`ArcGodementSamePartitionFreshForest` states the Godement commute at exactly the hypothesis strength the LIVE count
route provides (`ArcStateFresh ∧ bottomCount ≤ nextFresh ∧ isUnionFindForest links ∧ 0 < nextFresh`), and
`arcGodementSamePartitionFreshForest_of_coreSwapSimCount` reduces it to residual (2)
`ArcGodementCoreSwapSimCount` via the shipped `arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` +
`sameArcPartition_of_renameRel`.  This removes the false generality the truth-probes surfaced (`ArcStateFresh` does
NOT imply forest, `arcFreshCyclicState`), so the standalone `ArcGodementSamePartitionFresh` is strictly stronger
than what is reducible to the count route.  `= true`. -/
def fxMode_hasArcForestFreshResidualBundled : Bool := true

/-- **Honesty marker — residual (2) is the SOLE remaining obligation, and it is NOT closed here.**  The hypothesis
of `arcGodementSamePartitionFreshForest_of_coreSwapSimCount` is `ArcGodementCoreSwapSimCount` — the explicit
block-swap `σ` over arbitrary cells (the geometric Mazurkiewicz fitting invariant),
`fxMode_hasArcGodementSwapRenameableProof2 = false`.  This file bundles the residual at count-route strength but
does NOT construct that `σ`, so it flips NOTHING: `fxMode_hasArcGodementSamePartitionFreshProof` (the parent's
leg-B marker) stays `false`, and the orchestrator must not present the forest residual as closed.  `= false`. -/
def fxMode_hasArcForestFreshResidualClosed : Bool := false

end FX1Poly.Polygraph
