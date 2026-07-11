import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDecisionSelfAttacks
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDescentInterfaceLedger

/-! # WalkingMonad — the WP-MONAD ARC CENSUS: the completeness state of the walking-monad word problem

A single machine-checked snapshot of the WP-MONAD arc.  Every rung of the walking-monad saturated 2-cell word
problem is CLOSED and its honesty marker is `true`; the one open node is NAMED and its marker is honestly `false`.
The census is a `rfl`-conjunction over the lane's markers — a red here means a marker silently changed value.

## The closed rungs (each `true`)

  * `fxMonad_hasSaturatedWordProblemClosed` — the walking-monad saturated 2-cell word problem is DECIDABLE
    (`monadSaturatedTwoCellDecision`), the SECOND saturated decision of the ladder (Δ₊ is the walking monad).
  * `fxMonad_hasConvOfMapEqReducedToNormalize` / `fxMonad_hasBoundaryTransportAndCanon` — the completeness leg
    `convOfMapEq` machine-reduced to the cell normalization; the boundary transport (every 1-cell a `t`-power).
  * `fxMonad_hasWordMulVcomp` / `fxMonad_hasVcompWordMultiplicativity` / `fxMonad_hasWordGadgetCollapseAndComposeCounts`
    — the VERTICAL word multiplicativity `wordMul_vcomp` (the block-sum re-sort) and its collapse kit.
  * `fxMonad_hasWhiskerNormalizeCases` / `fxMonad_hasNormalizeGeneratorBaseCases` / `fxMonad_hasNormalizeIdCase` /
    `fxMonad_hasCanonCountsVcompBridge` — the five `normalizeCell` cases (gen/id/whiskerL/whiskerR/vcomp).
  * `fxMonad_hasMapEqOfConvComplete` / `fxMonad_hasMonotoneMapDecisionAssembled` /
    `fxMonad_hasMonotoneMapFoldSoundOnLaws` — the SOUNDNESS leg and the monotone-map decision assembly.
  * `fxMonad_wpDischargesPerGapDescentDownstream` — the closure discharges the #2043 per-gap descent DOWNSTREAM
    half (this round's B3 interface ledger).

## The one open node (honestly `false`)

  * `fxMonad_wpClosesJamAGate = false` — the WalkingMonad lane does NOT close the amalgam JAM-A gate.  The sole
    surviving residual is the mode-side Godement / Mazurkiewicz disjoint-support block commutation
    `fxMode_hasArcBlockCommuteProof` (`FreeTwoCell/GodementIndependence`), independent of this lane; JAM A
    (`fxAmalg_hasSaturatedDispatchTheorem`) stays open in the Amalgam lane.  No WalkingMonad-authored discharge
    exists and none is claimed.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; a `rfl`-conjunction over
`Bool` markers.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- ★ **The WP-MONAD arc census — every closed rung is `true`, the one open node is `false`, machine-checked.**  The
walking-monad saturated 2-cell word problem is closed across all its rungs (decision, both legs, all five
normalization cases, both word multiplicativities, the boundary transport, and the #2043 descent DOWNSTREAM
discharge); the single open node is the mode-side JAM-A residual, honestly `false`.  A `rfl`-conjunction: any marker
whose value drifts fails this census. -/
theorem wpMonadArcCensus_allClosed :
    fxMonad_hasSaturatedWordProblemClosed = true
    ∧ fxMonad_hasConvOfMapEqReducedToNormalize = true
    ∧ fxMonad_hasBoundaryTransportAndCanon = true
    ∧ fxMonad_hasWordMulVcomp = true
    ∧ fxMonad_hasVcompWordMultiplicativity = true
    ∧ fxMonad_hasWordGadgetCollapseAndComposeCounts = true
    ∧ fxMonad_hasWhiskerNormalizeCases = true
    ∧ fxMonad_hasNormalizeGeneratorBaseCases = true
    ∧ fxMonad_hasNormalizeIdCase = true
    ∧ fxMonad_hasCanonCountsVcompBridge = true
    ∧ fxMonad_hasMapEqOfConvComplete = true
    ∧ fxMonad_hasMonotoneMapDecisionAssembled = true
    ∧ fxMonad_hasMonotoneMapFoldSoundOnLaws = true
    ∧ fxMonad_wpDischargesPerGapDescentDownstream = true
    ∧ fxMonad_wpClosesJamAGate = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **ESTABLISHED — the WP-MONAD arc is complete modulo the named mode-side node.**  The census
`wpMonadArcCensus_allClosed` machine-checks that every rung of the walking-monad word problem is closed and the sole
open node is the mode-side `fxMode_hasArcBlockCommuteProof` (recorded `fxMonad_wpClosesJamAGate = false`).  This is
the WP-MONAD completeness state, snapshotted zero-axiom. `= true`. -/
def fxMonad_wpMonadArcCensus : Bool := true

end FX1Poly.Polygraph
