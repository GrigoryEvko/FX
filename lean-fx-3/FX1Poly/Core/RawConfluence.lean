import FX1Poly.Core.ParStepTriangle
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.NormalFormUnique
import FX1Poly.Core.RawTermDecEq

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

/-! ### Conv = normal-form equality, with NO strong-normalization hypothesis.

`StronglyNormalizingConvDecision.lean`'s `Conv.iff_normalForms_eq_of_isStronglyNormalizing` decides
`Conv` as normal-form equality but threads BOTH endpoints' `IsStronglyNormalizing` witnesses — used only to
supply per-term confluence (`confluence_of_localJoin_and_accessible`) for the forward direction.  Global
`rawConfluence` + `normalForm_unique_of_confluence` discharge those, so the iff holds for ANY two terms
that HAPPEN to reduce to normal forms — SN or not.  This separates the two ingredients of decidable
conversion cleanly: **existence** of normal forms / termination of a normalizer is the SN obligation (the
gated part), whereas the **correctness** of "compare the normal forms" is pure confluence (now
unconditional). -/

/-- **Conv = normal-form equality (no SN hypothesis).**  For any two terms with normal forms in hand
(reduction chains + normality), conversion is exactly equality of those normal forms.  Forward: the
conversion's common reduct and the left normal form are both reducts of `leftTerm`, so `rawConfluence`
joins them; rigidity collapses the apex onto the left normal form, so `rightTerm` also reaches it, and
`normalForm_unique_of_confluence` equates the two normal forms.  Backward: equal normal forms expose a
shared reduct.  Strengthens `Conv.iff_normalForms_eq_of_isStronglyNormalizing` by dropping both SN
premises. -/
theorem Conv.iff_normalForms_eq_of_confluence {scope : Nat}
    {leftTerm rightTerm leftNormalForm rightNormalForm : RawTerm scope}
    (leftReducesToNF : StepStar leftTerm leftNormalForm)
    (leftIsNormal : RawTerm.isStepNormalForm leftNormalForm)
    (rightReducesToNF : StepStar rightTerm rightNormalForm)
    (rightIsNormal : RawTerm.isStepNormalForm rightNormalForm) :
    Conv leftTerm rightTerm ↔ leftNormalForm = rightNormalForm := by
  constructor
  · intro convertibility
    obtain ⟨commonTerm, leftToCommon, rightToCommon⟩ := convertibility
    -- The left term reaches both the conversion's common reduct and the left normal form; GLOBAL
    -- confluence joins them, and the normal form is rigid, so the apex collapses onto the left normal
    -- form: the common reduct itself reduces to the left normal form.
    obtain ⟨apexTerm, commonToApex, normalToApex⟩ := StepStar.rawConfluence leftToCommon leftReducesToNF
    have apexIsNormalForm : apexTerm = leftNormalForm :=
      StepStar.eq_of_noStep
        (fun reduct stepFromNF => RawTerm.isStepNormalForm_blocks_step leftIsNormal reduct stepFromNF)
        normalToApex
    have commonToNormalForm : StepStar commonTerm leftNormalForm := apexIsNormalForm ▸ commonToApex
    have rightToNormalForm : StepStar rightTerm leftNormalForm :=
      StepStar.trans_compose rightToCommon commonToNormalForm
    -- The right term now reaches both the left and right normal forms; confluence uniqueness equates them.
    exact normalForm_unique_of_confluence rightToNormalForm leftIsNormal
      rightReducesToNF rightIsNormal
  · intro normalFormsEqual
    exact ⟨rightNormalForm, normalFormsEqual ▸ leftReducesToNF, rightReducesToNF⟩

/-- **Decidable Conv from normal forms (no SN hypothesis).**  Given two terms together with their normal
forms (reduction chains + normality), conversion is decidable — it is normal-form equality, decided by the
propext-free `instDecidableEqRawTerm`.  No global-confluence assumption (discharged by `rawConfluence`) and
no SN premise; a normalizer function supplying the normal-form witnesses makes this a parameter-free
decision on whatever fragment it normalizes. -/
def Conv.decidableOfNormalForms {scope : Nat}
    {leftTerm rightTerm leftNormalForm rightNormalForm : RawTerm scope}
    (leftReducesToNF : StepStar leftTerm leftNormalForm)
    (leftIsNormal : RawTerm.isStepNormalForm leftNormalForm)
    (rightReducesToNF : StepStar rightTerm rightNormalForm)
    (rightIsNormal : RawTerm.isStepNormalForm rightNormalForm) :
    Decidable (Conv leftTerm rightTerm) :=
  decidable_of_iff _
    (Conv.iff_normalForms_eq_of_confluence
      leftReducesToNF leftIsNormal rightReducesToNF rightIsNormal).symm

end FX1Poly.Core
