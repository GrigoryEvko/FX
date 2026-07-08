import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerReconstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellWordProblem
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction

/-! # mode-3 floor — the seed's FAITHFUL 2-cell decision reduced to the SINGLE trace residual

`AdjunctionTwoCellWordProblem` reduced the seed's **bare** `TwoCellConv` decision to TWO obligations,
`(traceDecision, reconstruct)`.  A later machine-checked pass then relocated the `reconstruct` obstruction: the
spine→cell readback is UNSOUND on the bare `TwoCellConv` (the per-atom `atomFrame` wraps identity-1-cell whiskers
that no `TwoCellStep` strips — the FREE-2 finding), so the bare `reconstruct`
(`AdjunctionSpineTraceReconstruction`) is provably FALSE, and the bare-`TwoCellConv` flag cannot be flipped
through the trace route at all.  The categorically-FAITHFUL relation is the COMPLETED convertibility
`TwoCellConvFull` (bare `TwoCellConv` + whisker FUNCTORIALITY + congruence closure), for which the readback IS
sound.  Over that faithful relation the whole YES-direction is already SHIPPED
(`RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv`, the reconstruction; `twoCellConvFull_spineTraceEquiv`, the
soundness).  This file discharges `reconstruct` at the seed and assembles the faithful decision modulo the
SINGLE remaining residual — the list-level trace decision.

## What this file ships (each piece zero-axiom)

  ★ `adjunctionSpineTraceReconstructionFull` — the seed's FAITHFUL readback reconstruction, DISCHARGED (not a
    hypothesis): the abbrev `AdjunctionSpineTraceReconstructionFull` is inhabited directly by the shipped free
    reconstruction `RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv`.  This is the honest statement that the
    `reconstruct` leg is DONE over the faithful relation — the FREE-2 obstruction that killed the bare form is
    exactly what whisker functoriality dissolves.
  ★ `adjunctionDecideTwoCellConvFullViaTrace` — decide `TwoCellConvFull cellFirst cellSecond` at the seed from a
    LIST-level `traceDecision` (`Decidable (SpineTraceEquiv … cellFirst.spine cellSecond.spine)`) ALONE.  Both
    directions are shipped theorems: trace-equivalent spines ⟹ `isTrue` via the discharged reconstruction;
    trace-INequivalent spines ⟹ `isFalse` because `twoCellConvFull_spineTraceEquiv` (soundness) would force the
    spines trace-equivalent.  The `reconstruct` obligation of the bare route is GONE — nothing cell-level remains.
  ★ `adjunctionTwoCellConvFullDecisionModuloTrace` — the family form: supplying `traceDecision` decides EVERY
    parallel pair of free 2-cells at the seed against the faithful convertibility.  This is precisely the faithful
    analogue of `adjunctionTwoCellWordProblemModuloTraceRoute`, with the second obligation (`reconstruct`)
    eliminated, so the whole residual is the ONE list-level trace decision (route (a)).
  ★ `adjunctionParallelUnits_convFull` — smoke: the Eckmann–Hilton witness (two parallel units in the two orders)
    is `TwoCellConvFull` via the discharged reconstruction on its shipped trace equivalence.

## What is DEFERRED — the single genuine residual (flag stays `false`)

The FAITHFUL decision is now owed ONLY `traceDecision` : an UNCONDITIONAL `Decidable (SpineTraceEquiv …)` — the
Mazurkiewicz / partially-commutative-monoid word problem on the whiskered-atom spine.  The shipped
`decidableSpineTraceEquiv_of` supplies it GATED on `fxMode_hasArcGodementIndependenceProof` (the union-find
Godement independence) and `fxMode_hasArcStructureReconstruction` (the Joyal–Street planar-arc completeness) —
both still `false`, the genuine cup-merge arc geometry (route (a)).  That is the SOLE remaining wall for the
faithful relation; the `reconstruct` leg is no longer part of the residual.

Two honesty points, kept sharp:

  * The general/free `fxMode_hasModeRelativeConvDecision` names the **bare** `TwoCellConv` parameter, whose
    `reconstruct` leg is provably FALSE (FREE-2).  This file does NOT flip it: it reduces the residual of the
    FAITHFUL relation, which is the categorically-correct target, but the bare flag's parameter is a strictly
    finer relation that the trace route cannot decide (equal-spine cells that are not bare-`TwoCellConv` exist).
    So the bare flag stays `false` for a genuine reason — a relation mismatch, not a missing lemma.
  * No fuel gate is introduced here: `traceDecision` is taken as an abstract `Decidable (SpineTraceEquiv …)`
    parameter, so this reduction is exact (the shipped `decideTwoCellConvFull?` gates on a computable
    frontier-exhaustion check; this states the clean abstract reduction the arc route must inhabit).

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the reconstruction is the shipped free term; the decision is a `match` on the supplied `Decidable`, the
NO-branch a `fun convFull => …` through soundness; the smoke is the discharged reconstruction on the shipped
trace equivalence).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The faithful reconstruction at the seed, discharged -/

/-- ★ **The seed's FAITHFUL readback reconstruction, DISCHARGED.**  The abbrev
`AdjunctionSpineTraceReconstructionFull` — a spine-level trace equivalence lifts to a cell-level
`TwoCellConvFull` at the seed — is inhabited directly by the shipped free reconstruction
`RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv` (any signature, hence the seed).  This is the `reconstruct`
leg of the trace route, completed over the relation faithful to the free strict 2-category. -/
def adjunctionSpineTraceReconstructionFull : AdjunctionSpineTraceReconstructionFull :=
  fun cellFirst cellSecond equiv =>
    RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv cellFirst cellSecond equiv

/-! ## The faithful trace-route decision (both directions shipped) -/

/-- ★ **Decide `TwoCellConvFull` via the trace route, modulo `traceDecision` ALONE.**  Given the list-level trace
decision, decide faithful cell convertibility at the seed: trace-equivalent spines ⟹ `isTrue` via the discharged
reconstruction `adjunctionSpineTraceReconstructionFull`; trace-INequivalent spines ⟹ `isFalse`, because
`twoCellConvFull_spineTraceEquiv` (soundness) would force the spines trace-equivalent.  BOTH directions are
shipped theorems — the `reconstruct` obligation of the bare route is fully discharged, so nothing cell-level is
owed. -/
def adjunctionDecideTwoCellConvFullViaTrace
    (traceDecision : AdjunctionSpineTraceDecision)
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConvFull adjunctionModeSignature cellFirst cellSecond) :=
  match traceDecision cellFirst cellSecond with
  | isTrue tracesEquiv => isTrue (adjunctionSpineTraceReconstructionFull cellFirst cellSecond tracesEquiv)
  | isFalse tracesDiffer => isFalse (fun convFull => tracesDiffer (twoCellConvFull_spineTraceEquiv convFull))

/-- ★ **The seed's faithful 2-cell decision, modulo the SINGLE trace residual.**  The family form: supplying
`traceDecision` decides EVERY parallel pair of free 2-cells at the seed against `TwoCellConvFull`.  This is the
faithful analogue of `adjunctionTwoCellWordProblemModuloTraceRoute`, with the second obligation (`reconstruct`)
ELIMINATED — the whole residual is the one list-level trace decision (route (a)). -/
def adjunctionTwoCellConvFullDecisionModuloTrace
    (traceDecision : AdjunctionSpineTraceDecision)
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConvFull adjunctionModeSignature cellFirst cellSecond) :=
  adjunctionDecideTwoCellConvFullViaTrace traceDecision cellFirst cellSecond

/-! ## Smoke: the Eckmann–Hilton witness is faithfully convertible -/

/-- Smoke: the non-degenerate Eckmann–Hilton witness — the two parallel units inserted in the two orders,
related by ONE `interchange` step — is `TwoCellConvFull`, obtained by the DISCHARGED reconstruction
`adjunctionSpineTraceReconstructionFull` on its shipped trace equivalence
(`adjunctionParallelUnits_spineTraceEquiv`).  The genuine Godement case the residual isolates is thereby
decided `isTrue` by the faithful route once the spines are seen trace-equivalent. -/
theorem adjunctionParallelUnits_convFull :
    TwoCellConvFull adjunctionModeSignature
      adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct :=
  adjunctionSpineTraceReconstructionFull
    adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct
    adjunctionParallelUnits_spineTraceEquiv

/-! ## Honesty marker -/

/-- **Honesty marker — the faithful decision is reduced to the SINGLE trace residual; the bare flag stays
walled.**  Over the categorically-faithful `TwoCellConvFull`, the seed's 2-cell decision is now owed ONLY the
list-level `traceDecision` (`Decidable (SpineTraceEquiv …)`): the `reconstruct` leg is DISCHARGED here
(`adjunctionSpineTraceReconstructionFull`, from the shipped free `twoCellConvFull_ofSpineTraceEquiv`), and the
NO-direction is the shipped soundness (`twoCellConvFull_spineTraceEquiv`).  `traceDecision` remains the genuine
cup-merge arc geometry — `decidableSpineTraceEquiv_of` gated on `fxMode_hasArcGodementIndependenceProof` /
`fxMode_hasArcStructureReconstruction`, both `false`.  This does NOT flip `fxMode_hasModeRelativeConvDecision`:
that flag names the BARE `TwoCellConv` parameter, whose `reconstruct` leg is provably FALSE (FREE-2, the
identity-path-whisker); the trace route cannot decide the bare relation (equal-spine non-bare-convertible cells
exist), a relation mismatch rather than a missing lemma.  `= false`. -/
def fxMode_hasFaithfulTwoCellDecisionModuloTrace : Bool := false

end FX1Poly.Polygraph
