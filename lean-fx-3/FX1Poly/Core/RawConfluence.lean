import FX1Poly.Core.ParStepTriangle
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle

/-! # FX1Poly/Core/RawConfluence
    — UNCONDITIONAL raw confluence of the FX reduction relation (`#420`, the M8-S1 payoff).

This file closes the `#420` pipeline.  `StepStarConfluence.lean` supplied `StepStar.HasConfluence` only
CONDITIONALLY (the shipped `cd_lemma` is a single-step LOCAL join, and raw β+ι is NOT strongly normalizing,
so Newman's lemma cannot promote local to global confluence).  The Tait/Martin-Löf/Takahashi parallel-
reduction route bypasses termination entirely:

* `ParallelReduction.lean` shipped the parallel reduction `ParStep` with the sandwich
  `Step ⊆ ParStep ⊆ StepStar` (`Step.toParStep`, `ParStep.toStepStar`);
* `CompleteDevelopment.lean` shipped the Takahashi complete development `completeDevelopment`;
* `ParStepTriangle.lean` proved the triangle `ParStep.triangle : ParStep a b → ParStep b (completeDevelopment a)`;
* `TakahashiTriangle.lean` turns a triangle into a `DiamondProperty` (`DiamondProperty.ofTriangle`);
* `StepParallelConfluence.lean` turns a sandwiched parallel diamond into `StepStar.HasConfluence`
  (`StepStar.hasConfluence_of_parallelDiamond`, route A).

This file instantiates that pipeline at the concrete FX `ParStep`:

* `ParStep.diamond` — the `ParStep` diamond, from the triangle;
* `StepStar.rawConfluence` — global Church-Rosser for the raw `StepStar`, UNCONDITIONALLY.

`StepStar.rawConfluence` is exactly `#420`: any two `StepStar`-reducts of a common source `Join` (reduce to
a common term).  No termination hypothesis — the prize strong normalization cannot supply, since raw β+ι is
not SN (`gen_natRec`/`gen_fixedPoint` give non-terminating raw reductions).

## Zero-axiom verification

Both theorems are direct instantiations of shipped, separately-gated lemmas (`DiamondProperty.ofTriangle`,
`StepStar.hasConfluence_of_parallelDiamond`) at the concrete `ParStep` / `Step.toParStep` /
`ParStep.toStepStar` / `ParStep.triangle`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **The `ParStep` diamond property.**  Two diverging single parallel steps reconverge at the complete
development of their common source — the Takahashi triangle (`ParStep.triangle`) sends each reduct there in
one further parallel step.  No quadratic redex-pair case split, no termination. -/
theorem ParStep.diamond {scope : Nat} : DiamondProperty (@ParStep scope) :=
  DiamondProperty.ofTriangle (@ParStep.triangle scope)

/-- **Unconditional raw confluence (`#420`).**  The FX raw reduction relation `StepStar` is globally
Church-Rosser: any two `StepStar`-reducts of a common source join at a common term.  Discharged through the
parallel-reduction sandwich `Step ⊆ ParStep ⊆ StepStar` and the `ParStep` diamond — with NO strong-
normalization assumption (raw β+ι is not SN).  This closes the M8-S1 confluence pipeline. -/
theorem StepStar.rawConfluence : StepStar.HasConfluence :=
  StepStar.hasConfluence_of_parallelDiamond
    (@ParStep) (@Step.toParStep) (@ParStep.toStepStar) (@ParStep.diamond)

end FX1Poly.Core
