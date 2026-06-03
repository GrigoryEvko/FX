import FX1Poly.Core.ParStepTriangle
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.NormalFormUnique

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

/-! ### Raw conversion is an equivalence relation — the unconditional harvest of confluence.

`Conv` (`StepStarConfluence.lean`) is *defined* as `StepStar.Join` — joinability via a common reduct.
`Conv.refl` and `Conv.sym` are structural (a term joins itself; a join is symmetric).  Transitivity,
however, is exactly Church-Rosser: chaining `a ~ b` (join at `c`) and `b ~ d` (join at `e`) needs `c` and
`e` — both reducts of `b` — to rejoin, which is confluence at `b`.  `StepStarConfluence.lean` could only
offer `Conv.trans_of_confluence` (a confluence hypothesis), `trans_of_strip`, or
`trans_of_strongNormalization` (global SN — UNAVAILABLE for raw β+ι).  `StepStar.rawConfluence` now
discharges the confluence hypothesis, so raw `Conv` is an UNCONDITIONAL equivalence relation — the
foundation the raw-layer conversion checker rests on. -/

/-- **Unconditional transitivity of raw conversion**, by discharging `Conv.trans_of_confluence` with the
shipped `StepStar.rawConfluence`. -/
theorem Conv.trans {scope : Nat} {firstTerm middleTerm lastTerm : RawTerm scope}
    (firstMiddle : Conv firstTerm middleTerm) (middleLast : Conv middleTerm lastTerm) :
    Conv firstTerm lastTerm :=
  Conv.trans_of_confluence StepStar.rawConfluence firstMiddle middleLast

/-- **Raw conversion is an equivalence relation** — unconditionally.  Reflexivity/symmetry are structural
(`Conv.refl` / `Conv.sym`); transitivity is `Conv.trans` via raw confluence (`#420`). -/
theorem Conv.equivalence {scope : Nat} : Equivalence (@Conv scope) where
  refl := Conv.refl
  symm := Conv.sym
  trans := Conv.trans

/-- `calc`-enabling homogeneous `Trans` instance for raw conversion, backed by the unconditional
`Conv.trans`.  Lets downstream conversion reasoning chain `Conv` steps with `calc` / `Trans.trans`. -/
instance Conv.instTrans {scope : Nat} : Trans (@Conv scope) (@Conv scope) (@Conv scope) where
  trans := Conv.trans

/-! ### Normal forms are unique — without any termination hypothesis.

`NormalFormUnique.lean`'s `normalForm_unique` joins two normal reducts via
`confluence_of_localJoin_and_accessible`, which needs the source to be strongly normalizing
(`StepStar.IsStronglyNormalizing sourceTerm`) — the only confluence available before `#420`.  Global
`rawConfluence` removes that need: it joins ANY two reductions of a common source, so two normal reducts
coincide whether or not the source terminates.  This makes "the normal form of a raw term" a well-defined
*partial* function on ALL raw terms (a possibly-diverging term may reach no normal form, but if it reaches
one, that form is unique). -/

/-- **Uniqueness of normal forms, unconditionally.**  Two structurally-normal `StepStar`-reducts of one
common source coincide — with NO strong-normalization hypothesis.  `rawConfluence` joins the two reduction
chains; normality makes each endpoint rigid (`isStepNormalForm_blocks_step`), so the shared reduct equals
both.  This strengthens `normalForm_unique` (which threads `IsStronglyNormalizing sourceTerm`) by dropping
the termination premise — the canonical harvest of unconditional global confluence. -/
theorem normalForm_unique_of_confluence {scope : Nat}
    {sourceTerm normalForm1 normalForm2 : RawTerm scope}
    (chain1 : StepStar sourceTerm normalForm1)
    (firstIsNormal : RawTerm.isStepNormalForm normalForm1)
    (chain2 : StepStar sourceTerm normalForm2)
    (secondIsNormal : RawTerm.isStepNormalForm normalForm2) :
    normalForm1 = normalForm2 :=
  Conv.eq_of_noStep
    (fun reduct firstStep => RawTerm.isStepNormalForm_blocks_step firstIsNormal reduct firstStep)
    (fun reduct secondStep => RawTerm.isStepNormalForm_blocks_step secondIsNormal reduct secondStep)
    (StepStar.rawConfluence chain1 chain2)

end FX1Poly.Core
