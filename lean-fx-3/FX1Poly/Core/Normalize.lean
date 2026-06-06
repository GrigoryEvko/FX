import FX1Poly.Core.ReduceOnceComplete
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.StronglyNormalizingConvDecision

/-! # FX1Poly/Core/Normalize
    — the normalizer FUNCTION on the strongly-normalizing fragment, and the parameter-free decidable
      conversion it unlocks.  The culmination of the weak-normalization grind.

Every prior file built one ingredient:
* `fireRootRedex` + soundness/completeness — fire a root redex, exactly when one exists;
* `reduceOnce` + soundness/completeness — one leftmost-outermost step, halting exactly at normal forms;
* `exists_normalForm_of_isStronglyNormalizing` (∃) / `normalForm_unique` — an SN term has a unique normal form;
* `Conv.decidableOfNormalForms_of_isStronglyNormalizing` — given the normal forms, conversion is decidable.

This file ties them off.  `RawTerm.normalize` IS the normal-form *function* (the computational form, not the
existential `exists_normalForm_of_isStronglyNormalizing`): it
iterates `reduceOnce` along the accessibility witness `Acc StepSuccessor` until the reducer halts.  Because
`reduceOnce` is sound (each step is a real `Step`, so the successor stays accessible — the descent) and
complete (it halts only at a structural normal form — the right place to stop), the two correctness
theorems hold:

* `normalize_reducesTo : StepStar term (normalize term acc)` — the output is reached by a reduction chain;
* `normalize_isStepNormalForm : isStepNormalForm (normalize term acc)` — the output is structurally normal.

Feeding those to the SN-fragment decider gives `Conv.decidableOfStronglyNormalizing`: for two
strongly-normalizing terms, conversion is decidable — normalize each and compare.  No NF witnesses passed
in, no `Normalizer` structure assumed, no global `StepStar.HasConfluence` hypothesis.  The whole path from
raw redex detection to a real decision procedure is closed on the SN fragment.

## Why `Acc.rec` and not the equation compiler

`reduceOnce` is NOT size-decreasing (β/ι can grow a term), so the recursion is on the accessibility proof,
not a structural/`Nat` measure.  The equation compiler's `brecOn` cannot eliminate the `Prop`-valued `Acc`
into the `Type`-valued `RawTerm`, so `normalize` is written directly with `Acc.rec` (the well-founded
recursion primitive, which large-eliminates `Acc`).  `normalize term (Acc.intro term accStep)` then unfolds
by `rfl` (`normalize_unfold`), and the correctness proofs are `Acc`-induction + `split` on the `reduceOnce`
result.

## Zero-axiom verification

`Acc.rec` (a recursor, axiom-free), `Acc`-induction, `split` on the reducer result, the shipped
soundness/completeness lemmas, `StepStar.trans`/`refl`, and `decidableOfNormalForms_of_isStronglyNormalizing`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per
declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **The normalizer.**  Iterate `reduceOnce` along the accessibility witness until it halts; the result is
the (unique) normal form of `term`.  Written with `Acc.rec` because the descent shrinks the accessibility
proof, not the term. -/
def RawTerm.normalize {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) : RawTerm scope :=
  Acc.rec
    (motive := fun _currentTerm _acc => RawTerm scope)
    (fun currentTerm _accStep normalizeRec =>
      match hReduce : RawTerm.reduceOnce currentTerm with
      | none => currentTerm
      | some reduct => normalizeRec reduct (RawTerm.reduceOnce_sound hReduce))
    accessible

/-- One-step unfolding of `normalize` at an `Acc.intro` witness (holds by `rfl`; the proof handle for the
correctness theorems). -/
theorem RawTerm.normalize_unfold {scope : Nat} (term : RawTerm scope)
    (accStep : ∀ later, StepStar.StepSuccessor later term → Acc StepStar.StepSuccessor later) :
    RawTerm.normalize term (.intro term accStep) =
      (match hReduce : RawTerm.reduceOnce term with
        | none => term
        | some reduct =>
            RawTerm.normalize reduct (accStep reduct (RawTerm.reduceOnce_sound hReduce))) := rfl

/-- **The normalizer reaches its output by a reduction chain.**  By `Acc`-induction: a halted step is the
reflexive chain; a fired step prepends `reduceOnce_sound` to the inductive chain. -/
theorem RawTerm.normalize_reducesTo {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    StepStar term (RawTerm.normalize term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalize_unfold currentTerm accStep]
      split
      · exact StepStar.refl _
      · next reduct hReduce =>
          exact StepStar.trans (RawTerm.reduceOnce_sound hReduce)
            (ih reduct (RawTerm.reduceOnce_sound hReduce))

/-- **The normalizer's output is structurally normal.**  By `Acc`-induction: a halted step gives a normal
form by `reduceOnce_complete`; a fired step defers to the inductive hypothesis. -/
theorem RawTerm.normalize_isStepNormalForm {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.isStepNormalForm (RawTerm.normalize term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalize_unfold currentTerm accStep]
      split
      · next hReduce => exact RawTerm.reduceOnce_complete hReduce
      · next reduct hReduce => exact ih reduct (RawTerm.reduceOnce_sound hReduce)

/-- **Parameter-free decidable conversion on the strongly-normalizing fragment.**  Two SN terms — normalize
each, compare the normal forms.  No NF witnesses, no `Normalizer` structure, no global confluence: the
normalizer supplies the witnesses `Conv.decidableOfNormalForms_of_isStronglyNormalizing` needs. -/
def Conv.decidableOfStronglyNormalizing {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Decidable (Conv leftTerm rightTerm) :=
  Conv.decidableOfNormalForms_of_isStronglyNormalizing
    leftTerminates rightTerminates
    (RawTerm.normalize_reducesTo leftTerm leftTerminates)
    (RawTerm.normalize_isStepNormalForm leftTerm leftTerminates)
    (RawTerm.normalize_reducesTo rightTerm rightTerminates)
    (RawTerm.normalize_isStepNormalForm rightTerm rightTerminates)

/-- **Conv = normalize-equality on the strongly-normalizing fragment** (the NbE soundness+completeness
characterization).  Two SN terms are convertible iff `RawTerm.normalize` maps them to the SAME term —
the semantic core underlying `Conv.decidableOfStronglyNormalizing` (which is `decidable_of_iff` over this).
Sharper than `Conv.iff_normalForms_eq_of_isStronglyNormalizing` (which takes the normal forms and their
reduction chains as opaque arguments): here the normal forms ARE the normalizer's outputs, supplied by
`normalize_reducesTo` / `normalize_isStepNormalForm`, so the right-hand side is a literal `RawTerm` equality
decided by `instDecidableEqRawTerm`.  No global confluence — confluence is discharged per-term by the two SN
witnesses. -/
theorem Conv.iff_normalize_eq_of_isStronglyNormalizing {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm leftTerminates = RawTerm.normalize rightTerm rightTerminates :=
  Conv.iff_normalForms_eq_of_isStronglyNormalizing
    leftTerminates rightTerminates
    (RawTerm.normalize_reducesTo leftTerm leftTerminates)
    (RawTerm.normalize_isStepNormalForm leftTerm leftTerminates)
    (RawTerm.normalize_reducesTo rightTerm rightTerminates)
    (RawTerm.normalize_isStepNormalForm rightTerm rightTerminates)

end FX1Poly.Core
