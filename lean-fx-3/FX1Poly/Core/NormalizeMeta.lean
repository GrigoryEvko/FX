import FX1Poly.Core.Normalize

/-! # FX1Poly/Core/NormalizeMeta
    — metatheory of the normalizer: fixed point at normal forms, idempotence, and the normal form as a
      complete conversion invariant.

`Normalize.lean` shipped the normalizer `RawTerm.normalize` with its reaches-its-output (`reducesTo`) and
output-is-normal (`isStepNormalForm`) correctness.  This file rounds out the standard normalizer metatheory:

* `normalize_eq_self_of_isStepNormalForm` — a structurally-normal term is a fixed point (one unfold:
  `reduceOnce` halts immediately, so the `none` branch returns the term unchanged);
* `normalize_idempotent` — re-normalizing is the identity (the output is already normal);
* `conv_normalize` — a term converts to its normal form (its reduction chain lifts to `Conv`);
* `normalize_eq_iff_conv` — the headline: two terms convert IFF their normal forms coincide, so the normal
  form is a complete invariant for conversion on the strongly-normalizing fragment (this is exactly the
  characterization `Conv.decidableOfStronglyNormalizing` decides, now stated as an explicit biconditional
  over the normalizer).

## Zero-axiom verification

`normalize_eq_self_of_isStepNormalForm` is a single `normalize_unfold` + `split`, discharging the impossible
fired branch via `reduceOnce_eq_none_iff_isStepNormalForm` + `nomatch`; the rest are direct compositions of
the shipped correctness theorems with `Conv.fromStepStar` and
`Conv.iff_normalForms_eq_of_isStronglyNormalizing`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Normal forms are fixed points.**  A structurally-normal term normalizes to itself — the reducer halts
on the first step, returning the term unchanged. -/
theorem RawTerm.normalize_eq_self_of_isStepNormalForm {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term)
    (normalForm : RawTerm.isStepNormalForm term) :
    RawTerm.normalize term accessible = term := by
  cases accessible with
  | intro _currentTerm accStep =>
      rw [RawTerm.normalize_unfold term accStep]
      split
      · rfl
      · next reduct hReduce =>
          rw [RawTerm.reduceOnce_eq_none_iff_isStepNormalForm.mpr normalForm] at hReduce
          nomatch hReduce

/-- **Idempotence.**  Re-normalizing a normalized term is the identity — the normalizer's output is already
structurally normal. -/
theorem RawTerm.normalize_idempotent {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term)
    (accessibleNormalForm : Acc (@StepStar.StepSuccessor scope) (RawTerm.normalize term accessible)) :
    RawTerm.normalize (RawTerm.normalize term accessible) accessibleNormalForm =
      RawTerm.normalize term accessible :=
  RawTerm.normalize_eq_self_of_isStepNormalForm (RawTerm.normalize term accessible)
    accessibleNormalForm (RawTerm.normalize_isStepNormalForm term accessible)

/-- **A term converts to its normal form.**  The normalizer's reduction chain lifts to `Conv`. -/
theorem RawTerm.conv_normalize {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    Conv term (RawTerm.normalize term accessible) :=
  Conv.fromStepStar (RawTerm.normalize_reducesTo term accessible)

/-- **The normal form is a complete conversion invariant.**  Two strongly-normalizing terms convert iff
their normal forms coincide — the explicit biconditional behind `Conv.decidableOfStronglyNormalizing`. -/
theorem RawTerm.normalize_eq_iff_conv {scope : Nat} (leftTerm rightTerm : RawTerm scope)
    (leftAccessible : Acc (@StepStar.StepSuccessor scope) leftTerm)
    (rightAccessible : Acc (@StepStar.StepSuccessor scope) rightTerm) :
    Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm leftAccessible = RawTerm.normalize rightTerm rightAccessible :=
  Conv.iff_normalForms_eq_of_isStronglyNormalizing leftAccessible rightAccessible
    (RawTerm.normalize_reducesTo leftTerm leftAccessible)
    (RawTerm.normalize_isStepNormalForm leftTerm leftAccessible)
    (RawTerm.normalize_reducesTo rightTerm rightAccessible)
    (RawTerm.normalize_isStepNormalForm rightTerm rightAccessible)

end FX1Poly.Core
