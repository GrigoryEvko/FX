import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvDecidable

/-! # mode-3 floor — the seed's 2-cell word problem, reduced to the trace route (residual sharpened)

`AdjunctionTwoCellConvDecidable` reduced the FULL `TwoCellConv` decision at the affine walking-adjunction seed
to a SINGLE opaque `residual` (decide `TwoCellConv` for two cells of EQUAL generator count whose interchange-free
normal forms DIFFER — the genuine Godement/Eckmann–Hilton case, machine-checked non-empty).
`FreeTwoCellSpineGodement` then proved the SOUND half of the trace-monoid characterization of `TwoCellConv`
(`TwoCellConv.spineTraceEquiv` : convertible ⟹ trace-equivalent spines).  This file uses that soundness to
SHARPEN the residual into two STRUCTURED, textbook-shaped obligations, with the whole NO-direction DISCHARGED.

## The trace route (each piece zero-axiom)

  ★ `adjunctionDecideTwoCellConvViaTrace` — decide `TwoCellConv cellFirst cellSecond` from:
      * a `traceDecision` — `Decidable (SpineTraceEquiv … cellFirst.spine cellSecond.spine)`, the LIST-level
        Mazurkiewicz / trace word problem (a self-contained, reusable, decidable-in-principle list canonicalization);
      * a `reconstruct` — `SpineTraceEquiv … cellFirst.spine cellSecond.spine → TwoCellConv … cellFirst cellSecond`,
        the readback past the `spine` quotient (the YES-direction).
    The NO-direction is FREE: when `traceDecision` says the spines are NOT trace-equivalent,
    `TwoCellConv.spineTraceEquiv` (soundness) turns a hypothetical conversion into the contradiction.  So the
    decision is `isTrue ∘ reconstruct` / `isFalse ∘ (soundness ▷ ¬trace)` — NO opaque cell-level NO-reasoning
    remains.
  ★ `adjunctionTwoCellWordProblemModuloTraceRoute` — packaged as `DecidableTwoCellConvFor adjunctionModeSignature`
    (the `mode-3` interface) modulo the SAME two obligations.  It decides ALL parallel cells (not merely the
    equal-count distinct-normal-form residual), because soundness handles every NO-case uniformly.
  ★ `adjunctionTwoCellConvResidualFromTraceRoute` — exhibits the trace route as a term of the EXACT
    `residual`-hypothesis type of `adjunctionDecidableTwoCellConvModuloResidual`: supplying `(traceDecision,
    reconstruct)` discharges the predecessors' single `residual`.  So the keystone residual is now PROVABLY
    reduced to `(traceDecision, reconstruct)` — a strict refinement (the opaque cell-level NO-direction is gone;
    what remains is a list-level decidability + a focused YES-reconstruction).

## What is DEFERRED (the precise two remaining obligations) — gates stay `false`

  * `traceDecision`: the DECIDABILITY of `SpineTraceEquiv` on the whiskered-atom spine — the source-anchored
    canonical (Foata / lexicographic) normal form over the dependently-typed, context-shifting atoms.  A
    self-contained list-combinatorics development (the genuine Gratzer confluence-modulo-interchange core).
  * `reconstruct`: realizing a list-level trace equivalence as a cell-level `TwoCellConv` — the readback through
    the `spine` quotient (a single Godement spine transposition lifted to one `interchange` `TwoCellConv` on the
    reconstructed normal forms).

Neither is discharged here; `fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay
`false`; the convergent-3-polygraph route stays blocked (interchange non-confluence is real —
`adjunctionInterchangeIsNonDegenerate`).  What this file adds is the machine-checked REDUCTION of the keystone
residual to those two named, well-shaped pieces, with the NO-direction proven.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the decision is a `match` on the supplied `Decidable`, the NO-branch a `fun conv => …` through soundness; the
smoke is the soundness theorem on the shipped Eckmann–Hilton witness).  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The two deferred obligations, named -/

/-- The seed's **list-level trace word problem**: decide `SpineTraceEquiv` of two cells' spines — the
Mazurkiewicz / partially-commutative-monoid decision (the deferred source-anchored canonicalization). -/
abbrev AdjunctionSpineTraceDecision : Type :=
  {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
  {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
  (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
  Decidable (SpineTraceEquiv adjunctionModeSignature cellFirst.spine cellSecond.spine)

/-- The seed's **readback reconstruction**: a spine-level trace equivalence lifts to a cell-level `TwoCellConv`
(the deferred YES-direction, past the `spine` quotient). -/
abbrev AdjunctionSpineTraceReconstruction : Prop :=
  {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
  {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
  (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
  SpineTraceEquiv adjunctionModeSignature cellFirst.spine cellSecond.spine →
  TwoCellConv adjunctionModeSignature cellFirst cellSecond

/-! ## The trace-route decision (NO-direction from soundness) -/

/-- ★ **Decide `TwoCellConv` via the trace route.**  Given the list-level trace decision and the readback
reconstruction, decide cell convertibility: trace-equivalent spines ⟹ `isTrue` (via `reconstruct`);
trace-INequivalent spines ⟹ `isFalse`, because `TwoCellConv.spineTraceEquiv` (soundness) would force the
spines trace-equivalent.  The whole NO-direction is discharged by soundness — no opaque obligation remains
there. -/
def adjunctionDecideTwoCellConvViaTrace
    (traceDecision : AdjunctionSpineTraceDecision)
    (reconstruct : AdjunctionSpineTraceReconstruction)
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConv adjunctionModeSignature cellFirst cellSecond) :=
  match traceDecision cellFirst cellSecond with
  | isTrue tracesEquiv => isTrue (reconstruct cellFirst cellSecond tracesEquiv)
  | isFalse tracesDiffer => isFalse (fun conv => tracesDiffer conv.spineTraceEquiv)

/-- ★ **The seed's 2-cell word problem, via the trace route.**  Packages `adjunctionDecideTwoCellConvViaTrace`
as a `DecidableTwoCellConvFor adjunctionModeSignature` (the `mode-3` decidability interface) modulo the two
trace obligations.  Decides ALL parallel cells uniformly — soundness handles every NO-case — so supplying
`(traceDecision, reconstruct)` is PRECISELY what flips `fxMode_hasModeRelativeConvDecision`. -/
def adjunctionTwoCellWordProblemModuloTraceRoute
    (traceDecision : AdjunctionSpineTraceDecision)
    (reconstruct : AdjunctionSpineTraceReconstruction) :
    DecidableTwoCellConvFor adjunctionModeSignature :=
  fun cellFirst cellSecond =>
    adjunctionDecideTwoCellConvViaTrace traceDecision reconstruct cellFirst cellSecond

/-- ★ **The trace route discharges the predecessors' `residual`.**  This has the EXACT type of the `residual`
hypothesis of `adjunctionDecidableTwoCellConvModuloResidual` (equal generator count + distinct interchange-free
normal forms ⟹ `Decidable (TwoCellConv …)`), realized by the trace route — which in fact decides every parallel
pair, so the equal-count / distinct-normal-form premises are not even needed.  Hence the single opaque keystone
residual is provably REDUCED to `(traceDecision, reconstruct)`. -/
def adjunctionTwoCellConvResidualFromTraceRoute
    (traceDecision : AdjunctionSpineTraceDecision)
    (reconstruct : AdjunctionSpineTraceReconstruction)
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (_countsAgree : cellFirst.generatorCount = cellSecond.generatorCount)
    (_normalFormsDiffer :
      (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellFirst ≠
        (interchangeFreeNormalizer adjunctionModeSignature sourcePath targetPath).normalize cellSecond) :
    Decidable (TwoCellConv adjunctionModeSignature cellFirst cellSecond) :=
  adjunctionDecideTwoCellConvViaTrace traceDecision reconstruct cellFirst cellSecond

/-- ★ **The full keystone decision, via the trace route.**  Feeds the residual realization above into the
predecessors' assembly `adjunctionDecidableTwoCellConvModuloResidual`: supplying `(traceDecision, reconstruct)`
inhabits the full `Decidable (TwoCellConv …)` at the seed.  This is the concrete witness that the keystone
residual is now exactly `(traceDecision, reconstruct)` — nothing else is owed. -/
def adjunctionDecidableTwoCellConvModuloTraceRoute
    (traceDecision : AdjunctionSpineTraceDecision)
    (reconstruct : AdjunctionSpineTraceReconstruction)
    {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (TwoCellConv adjunctionModeSignature cellFirst cellSecond) :=
  adjunctionDecidableTwoCellConvModuloResidual
    (adjunctionTwoCellConvResidualFromTraceRoute traceDecision reconstruct) cellFirst cellSecond

/-! ## Smoke: the Eckmann–Hilton witness has trace-equivalent spines -/

/-- The non-degenerate Eckmann–Hilton witness — the two parallel units inserted in the two orders
(`adjunctionParallelUnitsRedex` / `…Reduct`, related by ONE `interchange` step) — has TRACE-EQUIVALENT spines,
via soundness (`TwoCellConv.spineTraceEquiv`) on the shipped one-step conversion.  So the genuine Godement case
the residual isolates is exactly a `SpineTraceEquiv` of distinct interchange-free normal forms — the trace route
applies to it, as intended. -/
theorem adjunctionParallelUnits_spineTraceEquiv :
    SpineTraceEquiv adjunctionModeSignature
      adjunctionParallelUnitsRedex.spine adjunctionParallelUnitsReduct.spine :=
  adjunctionParallelUnitsConv.spineTraceEquiv

/-! ## Honesty marker -/

/-- **Honesty marker.**  The seed's full `TwoCellConv` decision is NOT realized: the trace route reduces it to
`(traceDecision, reconstruct)` — the list-level `SpineTraceEquiv` decidability (source-anchored canonicalization)
and the readback reconstruction — both deferred.  The SOUND NO-direction IS shipped
(`adjunctionDecideTwoCellConvViaTrace`'s `isFalse` branch, via `TwoCellConv.spineTraceEquiv`).  Hence
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasAdjunctionTwoCellWordProblem : Bool := false

end FX1Poly.Tier0
