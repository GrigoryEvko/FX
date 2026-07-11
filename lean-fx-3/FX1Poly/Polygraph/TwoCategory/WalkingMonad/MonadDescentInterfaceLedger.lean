import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

/-! # WalkingMonad — the DESCENT-INTERFACE ledger: what the closed word problem delivers to the #2043 JAM-A gate

This ledger records, from the WALKING-MONAD side, the exact adjudication of how the now-closed saturated word problem
bears on the amalgam pushout dispatch gate JAM A (`fxAmalg_hasSaturatedDispatchTheorem`, `Amalgam/SaturatedDispatch`,
currently `false`).  It is ADDITIVE and lives in the WalkingMonad lane by design: the Amalgam dispatch ledgers are an
actively-worked lane, and the honest WalkingMonad-side fact is decoupled from their churn — this file imports ONLY
`MonadWordProblem` (whose transitive closure is Amalgam-free), so its verdict cannot be silently invalidated by an
Amalgam edit.

## The adjudication (verdict: JAM A does NOT close from the WalkingMonad closure; the wall is now sharper)

The #2043 per-gap descent demand splits into a DOWNSTREAM half and an UPSTREAM half:

  * **DOWNSTREAM — the per-gap comparison, once descended, is the reconstructed monad word problem.**  The amalgam
    r20 verdict cited this half as "the reconstructed monad word problem (WalkingMonad lane, fib-3-coupled)".  It is
    now DISCHARGED: `monadSaturatedTwoCellDecision` decides every parallel pair of free monad 2-cells
    (`fxMonad_hasSaturatedWordProblemClosed = true`), and the Amalgam right-image reflection
    `pushoutRightImageConvReflect` (`Amalgam/PushoutRightImageReflect`, `fxAmalg_hasFullRightImageReflection = true`)
    ALREADY consumes the completeness leg through `reconstructed_convOfArityEq`.  So a PURE right-coprojection gap
    payload descends and decides — this ledger's `fxMonad_wpDischargesPerGapDescentDownstream` records exactly that.

  * **UPSTREAM — the disjoint-support block commutation — is the SOLE surviving residual, and it is MODE-SIDE.**  To
    descend a MIXED (interleaved cross-wall) whole-cell conv you must first commute the horizontally-disjoint middle
    blocks apart into pure per-gap sub-cells; that is the Godement / Mazurkiewicz disjoint-support independence
    `fxMode_hasArcBlockCommuteProof` (= `fxMode_ln`, `FreeTwoCell/GodementIndependence`, `false`, further reduced to
    `fxMode_hasArcPartitionCommuteProof`).  It is a FreeTwoCell / mode-side obstruction, INDEPENDENT of the
    WalkingMonad word problem — owning the WalkingMonad lane does NOT author it.

Hence the WalkingMonad closure RETIRES the r20 verdict's "fib-3-coupled per-gap comparison" downstream half and
confirms the right-image reflection is now unconditional, WITHOUT flipping any Amalgam master: JAM A
(`fxAmalg_hasSaturatedDispatchTheorem`) stays `false`, machine-checked in the owning lane by the Amalgam
`recon…JamA_perGapDescentOpen` theorems; `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` stay `false`; `pushoutDispatchCloseCriterion` stays `false`.  NO discharge of
JAM A is attempted this round — the honest final ceiling for #2043 is the mode-side disjoint-support block
commutation, NOT the monad word problem.  (Adjudication attributed to the WP-MONAD r9 recon; Amalgam residual values
read at HEAD prior to this commit.)

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; the ledger theorems are
`rfl` on WalkingMonad-lane markers.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- **The WalkingMonad word-problem closure DISCHARGES the downstream half of the #2043 per-gap descent.**  The
per-gap comparison, once descended, is the reconstructed monad word problem — now decided unconditionally by
`monadSaturatedTwoCellDecision` (`fxMonad_hasSaturatedWordProblemClosed = true`) and consumed by the Amalgam
right-image reflection `pushoutRightImageConvReflect` through `reconstructed_convOfArityEq`.  This marker records the
DOWNSTREAM discharge only; it makes NO claim on JAM A itself (which stays open on the mode side — see below).
`= true`. -/
def fxMonad_wpDischargesPerGapDescentDownstream : Bool := true

/-- **The JAM-A gate does NOT close from the WalkingMonad closure — the sole surviving residual is MODE-SIDE.**  This
marker records that the walking-monad word problem, though closed, is NOT the remaining wall for #2043: after the
downstream discharge, the standing obligation is the Godement / Mazurkiewicz disjoint-support block commutation
`fxMode_hasArcBlockCommuteProof` (`FreeTwoCell/GodementIndependence`), a FreeTwoCell / mode-side independence law
independent of this lane.  So `fxAmalg_hasSaturatedDispatchTheorem` stays `false` and this marker is `false` — no
WalkingMonad-authored discharge of JAM A exists, and none is attempted this round. `= false`. -/
def fxMonad_wpClosesJamAGate : Bool := false

/-- ★ **The descent-interface ledger, machine-checked on the WalkingMonad lane.**  The word problem is CLOSED
(`fxMonad_hasSaturatedWordProblemClosed`), which discharges the per-gap descent's DOWNSTREAM half
(`fxMonad_wpDischargesPerGapDescentDownstream`); yet the WalkingMonad lane does NOT close the JAM-A gate
(`fxMonad_wpClosesJamAGate = false`) — the surviving residual is the mode-side disjoint-support block commutation.
Exactly what the WalkingMonad closure delivers to #2043, and exactly what it does not. -/
theorem reconWpMonad_perGapDescentDownstreamClosed :
    fxMonad_hasSaturatedWordProblemClosed = true
    ∧ fxMonad_wpDischargesPerGapDescentDownstream = true
    ∧ fxMonad_wpClosesJamAGate = false :=
  ⟨rfl, rfl, rfl⟩

end FX1Poly.Polygraph
