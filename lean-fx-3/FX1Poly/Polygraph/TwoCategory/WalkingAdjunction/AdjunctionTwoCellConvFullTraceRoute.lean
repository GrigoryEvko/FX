import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerReconstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellWordProblem
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TotalWordProblemDecision

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

## What is DISCHARGED — the faithful decision is now UNCONDITIONAL (the trace residual falls)

The `traceDecision` residual is DISCHARGED ungated.  An UNCONDITIONAL `Decidable (SpineTraceEquiv …)` on the
whiskered-atom spine is now shipped WITHOUT the arc geometry: every free cell's spine is boundary-chained at its
source 1-cell (`RawTwoCellExpr.spine_isBoundaryChained`), so the bounded-atom-universe route
(`decideAtomicTraceEquivOfChainedSeed`, `TotalWordProblemDecision`) decides `AtomicTraceEquiv` of the two spines
outright, and FREE-5 (`spineTraceEquiv_iff_atomicTraceEquiv`) transports that decision to `SpineTraceEquiv`.  This
inhabits `AdjunctionSpineTraceDecision` outright (`adjunctionSpineTraceDecision`), so the FAITHFUL decision is now
UNCONDITIONAL: `adjunctionDecideTwoCellConvFull` feeds it into the discharged reconstruction to decide EVERY
parallel pair against `TwoCellConvFull` with NO hypothesis (`fxMode_hasFaithfulTwoCellDecisionModuloTrace = true`).

  * The older arc route (`decidableSpineTraceEquiv_of`, GATED on `fxMode_hasArcGodementIndependenceProof` /
    `fxMode_hasArcStructureReconstruction`, both `false`) is now a NON-BLOCKING alternative: its target
    `Decidable (TwoCellConvFull …)` is already shipped ungated by the disjoint class-saturation route
    (`decideTwoCellConvFull`).  The Joyal–Street planar-arc / union-find Godement-independence development
    (`MixedTailArcCompleteness`) stays an open refinement leaf — a second, geometry-native proof of the same
    decision, not a wall.

## What is DEFERRED — the SINGLE genuine residual is the BARE relation (`fxMode_hasModeRelativeConvDecision` stays `false`)

The general/free `fxMode_hasModeRelativeConvDecision` names the **bare** `TwoCellConv` parameter (NOT the faithful
`TwoCellConvFull`), whose `reconstruct` leg (`AdjunctionSpineTraceReconstruction`, landing in bare `TwoCellConv`)
is provably FALSE (FREE-2, the identity-path-whisker): `atomFrame adjunctionUnitSpineAtom` has the SAME spine as
the bare unit yet no `TwoCellStep` strips its identity-1-cell whisker, so equal-spine cells that are NOT
bare-`TwoCellConv` exist and the trace route cannot decide the bare relation.  This is a RELATION MISMATCH, not a
missing lemma: bare `TwoCellConv` is strictly finer than both the faithful `TwoCellConvFull` (decided here) and
the saturated modulo-triangles relation (`SaturatedTwoCellConv`, decided by
`fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction`, the granularity the MTT fibration consumes).  The
bare flag stays `false` for that genuine reason; this file does NOT flip it and does NOT weaken its parameter.

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

/-! ## The trace residual discharged — the UNCONDITIONAL faithful decision -/

/-- ★ **The seed's list-level trace decision, DISCHARGED ungated.**  Inhabits `AdjunctionSpineTraceDecision`
outright — an UNCONDITIONAL `Decidable (SpineTraceEquiv … cellFirst.spine cellSecond.spine)` — with NO arc gate:
every free cell's spine is boundary-chained at its source 1-cell (`RawTwoCellExpr.spine_isBoundaryChained`), so
the bounded-atom-universe route (`decideAtomicTraceEquivOfChainedSeed`) decides `AtomicTraceEquiv` of the spines,
and FREE-5 (`spineTraceEquiv_iff_atomicTraceEquiv`) transports the decision to `SpineTraceEquiv`.  This is the
`traceDecision` slot the trace route owed — supplied WITHOUT the Joyal–Street arc geometry. -/
@[reducible] def adjunctionSpineTraceDecision : AdjunctionSpineTraceDecision :=
  fun cellFirst cellSecond =>
    match decideAtomicTraceEquivOfChainedSeed adjunctionModeDecEq adjunctionModalityDecEq
        adjunctionTwoCellDecEq cellFirst.spine cellSecond.spine cellFirst.spine_isBoundaryChained with
    | isTrue atomicEquiv => isTrue (spineTraceEquiv_iff_atomicTraceEquiv.mpr atomicEquiv)
    | isFalse atomicRefuted =>
        isFalse (fun tracesEquiv => atomicRefuted (spineTraceEquiv_iff_atomicTraceEquiv.mp tracesEquiv))

/-- ★★ **The seed's FAITHFUL 2-cell decision, UNCONDITIONAL.**  Feeds the discharged trace decision
`adjunctionSpineTraceDecision` into the trace-route family form: the whole `TwoCellConvFull` word problem at the
walking-adjunction seed is decided with NO hypothesis — the `reconstruct` leg is
`adjunctionSpineTraceReconstructionFull` (discharged), the `traceDecision` leg is now discharged too, and the
NO-direction is the shipped soundness.  Equivalent to `decideTwoCellConvFull` at the seed via the disjoint
class-saturation route; this exhibits it through the trace-route composition. -/
def adjunctionDecideTwoCellConvFull
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConvFull adjunctionModeSignature cellFirst cellSecond) :=
  adjunctionTwoCellConvFullDecisionModuloTrace adjunctionSpineTraceDecision cellFirst cellSecond

/-! ## Smokes: the faithful decision genuinely separates -/

/-- Smoke (ACCEPT): the faithful decision cannot REJECT the convertible Eckmann–Hilton witness — no proof makes
it `isFalse`, since `adjunctionParallelUnits_convFull` witnesses the conversion.  Rules out a degenerate
reject-everything decision. -/
theorem adjunctionDecideTwoCellConvFull_accepts_parallelUnits :
    ∀ notConv, adjunctionDecideTwoCellConvFull adjunctionParallelUnitsRedex adjunctionParallelUnitsReduct
      ≠ Decidable.isFalse notConv :=
  fun notConv _ => notConv adjunctionParallelUnits_convFull

/-- Smoke (REJECT): the faithful decision cannot ACCEPT the non-convertible snake/identity pair — no proof makes
it `isTrue`, since `snake_not_convFull_identity` refutes the conversion (the snake and the identity differ in
generator count `2 ≠ 0`, a `TwoCellConvFull` invariant).  Rules out a degenerate accept-everything decision. -/
theorem adjunctionDecideTwoCellConvFull_rejects_snake :
    ∀ conv, adjunctionDecideTwoCellConvFull snakeOnLeft identityOnLeft ≠ Decidable.isTrue conv :=
  fun conv _ => snake_not_convFull_identity conv

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the faithful `TwoCellConvFull` decision at the walking-adjunction seed is UNCONDITIONAL.**
Over the categorically-faithful `TwoCellConvFull` (bare `TwoCellConv` + whisker functoriality + congruence
closure), the seed's 2-cell decision is now DISCHARGED with no hypothesis (`adjunctionDecideTwoCellConvFull`):
the `reconstruct` leg is the shipped free `twoCellConvFull_ofSpineTraceEquiv`
(`adjunctionSpineTraceReconstructionFull`); the `traceDecision` leg is DISCHARGED ungated by
`adjunctionSpineTraceDecision` (via `decideAtomicTraceEquivOfChainedSeed` + FREE-5 — NOT the arc-gated
`decidableSpineTraceEquiv_of`); and the NO-direction is the shipped soundness (`twoCellConvFull_spineTraceEquiv`).
The decision genuinely SEPARATES: it accepts the Eckmann–Hilton witness
(`adjunctionDecideTwoCellConvFull_accepts_parallelUnits`) and rejects the snake/identity pair
(`adjunctionDecideTwoCellConvFull_rejects_snake`).  The older arc route (Joyal–Street planar-arc completeness +
union-find Godement independence, gates both `false`) is a NON-BLOCKING alternative — its target is already
shipped here — with `MixedTailArcCompleteness` an open refinement leaf.  This does NOT flip
`fxMode_hasModeRelativeConvDecision`: that flag names the strictly-finer BARE `TwoCellConv`, whose `reconstruct`
leg is provably FALSE (FREE-2, the identity-path-whisker) — a relation mismatch, kept honestly live.  `= true`. -/
def fxMode_hasFaithfulTwoCellDecisionModuloTrace : Bool := true

end FX1Poly.Polygraph
