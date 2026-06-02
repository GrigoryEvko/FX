import FX1Poly.Core.ExistsStepOfNotNormal
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/WeakNormalization
    — weak normalization: a strongly-normalizing raw term reaches a structural normal form.

The two preceding ingredients combine here into weak normalization:

* `StepStar.IsStronglyNormalizing source` is `Acc StepSuccessor source` — the term admits no infinite
  `Step` chain (`StepStarConfluence.lean`).
* `exists_step_of_not_isStepNormalForm` (`ExistsStepOfNotNormal.lean`) exhibits a `Step` at every
  *non-normal* term.

Descending the accessibility proof, at each node we ask the decidable structural-normality test
`RawTerm.isStepNormalFormBool`: a `true` answer means the node *is* a normal form, reached by the
reflexive chain; a `false` answer feeds the extraction lemma, which produces a genuine `Step` to an
accessible successor, and the accessibility induction hypothesis supplies a normal form below it — prepend
the step with `StepStar.trans`.  The descent terminates exactly because the term is strongly normalizing.

This is the `StepStar`-existence half of normalization (a normal form is *reachable*); paired with global
confluence (`confluence_of_localJoin_and_accessible`, also keyed on `IsStronglyNormalizing`) that normal
form is unique, giving decidable conversion on the strongly-normalizing fragment (#267) and underwriting
the WHNF migration (#374).

## Zero-axiom verification

`Acc`-induction (large elimination into the existential `Prop`), a boolean `cases` on the decidable
normality test, an `Eq`-rewrite plus `decide` on the closed boolean residue, and the productive extraction
lemma.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` — in
particular the descent uses the boolean normality test directly rather than a classical `by_cases`.  Gated
per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Weak normalization.**  A strongly-normalizing term `StepStar`-reduces to a structural normal form.
The reduction chain is produced by descending the accessibility witness: each non-normal node takes a real
`Step` (via `exists_step_of_not_isStepNormalForm`) to an accessible successor, and the descent halts at the
first structurally-normal node it reaches. -/
theorem exists_normalForm_of_isStronglyNormalizing {scope : Nat} {sourceTerm : RawTerm scope}
    (sourceTerminates : StepStar.IsStronglyNormalizing sourceTerm) :
    ∃ normalForm : RawTerm scope,
      StepStar sourceTerm normalForm ∧ RawTerm.isStepNormalForm normalForm := by
  induction sourceTerminates with
  | intro currentTerm _accStep currentIH =>
      cases normalValue : RawTerm.isStepNormalFormBool currentTerm with
      | true =>
          exact ⟨currentTerm, StepStar.refl _, normalValue⟩
      | false =>
          have currentNotNormal : ¬ RawTerm.isStepNormalForm currentTerm := by
            show ¬ (RawTerm.isStepNormalFormBool currentTerm = true)
            rw [normalValue]; exact (by decide)
          obtain ⟨nextTerm, currentStep⟩ :=
            exists_step_of_not_isStepNormalForm currentNotNormal
          obtain ⟨normalForm, tailChain, normalProof⟩ := currentIH nextTerm currentStep
          exact ⟨normalForm, StepStar.trans currentStep tailChain, normalProof⟩

end FX1Poly.Core
