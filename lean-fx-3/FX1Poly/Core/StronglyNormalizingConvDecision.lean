import FX1Poly.Core.NormalFormUnique
import FX1Poly.Core.RawTermDecEq

/-! # FX1Poly/Core/StronglyNormalizingConvDecision
    — Conv = normal-form equality on the *strongly-normalizing* fragment, confluence discharged per-term.

`PolygraphConvergentDecision.lean` ships the Path-B decider core `Conv.iff_normalForm_eq` /
`Conv.decidableOfNormalizer`, but parameterized by TWO unproved hypotheses: a `Normalizer` *function* and
GLOBAL `StepStar.HasConfluence`.  At the raw layer global confluence is NOT available as a theorem —
raw `Step` is not strongly normalizing in general (`gen_natRec`/`gen_fixedPoint` are partial), so
`HasConfluence` would have to be assumed.

This file ships the HONEST refinement: on the strongly-normalizing fragment the global-confluence
hypothesis is DISCHARGED.  Per-term confluence comes from `confluence_of_localJoin_and_accessible` (which
needs only `IsStronglyNormalizing` of the source, supplied by the caller), so the only inputs are the two
terms' SN witnesses together with their normal forms and reduction chains — every one of which is provable
for an actual SN term, no global axiom-shaped assumption.

* `Conv.iff_normalForms_eq_of_isStronglyNormalizing` — for two SN terms with normal forms in hand,
  conversion is exactly equality of those normal forms.  Forward: the conversion's common reduct and the
  left normal form join under left-SN confluence, and rigidity collapses the apex onto the left normal
  form, so the right term also reaches the left normal form; right-SN `normalForm_unique` then equates the
  two normal forms.  Backward: equal normal forms expose a shared reduct, hence a conversion.
* `Conv.decidableOfNormalForms_of_isStronglyNormalizing` — the decision, `decidable_of_iff` over the
  propext-free `instDecidableEqRawTerm`.  The remaining input is the normal-form witnesses; a normalizer
  *function* (eval/quote, #261/#480) supplies them, at which point this becomes a parameter-free decider.

## Zero-axiom verification

A `Join` destructure, `confluence_of_localJoin_and_accessible` (`Acc`-recursion, zero-axiom), rigidity via
`StepStar.eq_of_noStep` fed by `isStepNormalForm_blocks_step`, `normalForm_unique`, `StepStar.trans_compose`,
a clean `▸` along a `StepStar`-typed motive, and `decidable_of_iff` over `instDecidableEqRawTerm`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Conv = normal-form equality on the SN fragment** (global confluence discharged).  For two
strongly-normalizing terms whose normal forms are in hand, conversion is exactly equality of those normal
forms — no `StepStar.HasConfluence` hypothesis, confluence supplied per-term by the SN witnesses. -/
theorem Conv.iff_normalForms_eq_of_isStronglyNormalizing {scope : Nat}
    {leftTerm rightTerm leftNormalForm rightNormalForm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm)
    (leftReducesToNF : StepStar leftTerm leftNormalForm)
    (leftIsNormal : RawTerm.isStepNormalForm leftNormalForm)
    (rightReducesToNF : StepStar rightTerm rightNormalForm)
    (rightIsNormal : RawTerm.isStepNormalForm rightNormalForm) :
    Conv leftTerm rightTerm ↔ leftNormalForm = rightNormalForm := by
  constructor
  · intro convertibility
    obtain ⟨commonTerm, leftToCommon, rightToCommon⟩ := convertibility
    -- The left term reaches both the conversion's common reduct and the left normal form; left-SN
    -- confluence joins them, and the normal form is rigid, so the join's apex collapses onto the left
    -- normal form: the common reduct itself reduces to the left normal form.
    have joinedLeft : StepStar.Join commonTerm leftNormalForm :=
      StepStar.confluence_of_localJoin_and_accessible leftTerminates leftToCommon leftReducesToNF
    obtain ⟨apexTerm, commonToApex, normalToApex⟩ := joinedLeft
    have apexIsNormalForm : apexTerm = leftNormalForm :=
      StepStar.eq_of_noStep
        (fun reduct stepFromNF => RawTerm.isStepNormalForm_blocks_step leftIsNormal reduct stepFromNF)
        normalToApex
    have commonToNormalForm : StepStar commonTerm leftNormalForm := apexIsNormalForm ▸ commonToApex
    have rightToNormalForm : StepStar rightTerm leftNormalForm :=
      StepStar.trans_compose rightToCommon commonToNormalForm
    -- The right term now reaches both the left and right normal forms; right-SN uniqueness equates them.
    exact normalForm_unique rightTerminates rightToNormalForm leftIsNormal
      rightReducesToNF rightIsNormal
  · intro normalFormsEqual
    exact ⟨rightNormalForm, normalFormsEqual ▸ leftReducesToNF, rightReducesToNF⟩

/-- **Decidable Conv on the SN fragment.**  Given two strongly-normalizing terms together with their normal
forms (and the reduction chains), conversion is decidable — it is normal-form equality, decided by the
propext-free `instDecidableEqRawTerm`.  No global confluence, no Normalizer-function assumption; a
normalizer function (eval/quote, #261/#480) is what supplies the normal-form witnesses to make this a
parameter-free decision. -/
def Conv.decidableOfNormalForms_of_isStronglyNormalizing {scope : Nat}
    {leftTerm rightTerm leftNormalForm rightNormalForm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm)
    (leftReducesToNF : StepStar leftTerm leftNormalForm)
    (leftIsNormal : RawTerm.isStepNormalForm leftNormalForm)
    (rightReducesToNF : StepStar rightTerm rightNormalForm)
    (rightIsNormal : RawTerm.isStepNormalForm rightNormalForm) :
    Decidable (Conv leftTerm rightTerm) :=
  decidable_of_iff _
    (Conv.iff_normalForms_eq_of_isStronglyNormalizing leftTerminates rightTerminates
      leftReducesToNF leftIsNormal rightReducesToNF rightIsNormal).symm

end FX1Poly.Core
