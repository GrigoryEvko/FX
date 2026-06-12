import FX1Poly.Core.ReduceOnce
import FX1Poly.Core.ExistsStepOfNotNormal

/-! # FX1Poly/Core/ReduceOnceComplete
    — completeness of `reduceOnce`: it halts (returns `none`) exactly at structural normal forms.

`ReduceOnce.lean` ships the table-backed one-step reducer plus SOUNDNESS (a firing is a real
`Step`).  This file ships COMPLETENESS: a term `reduceOnce` cannot reduce is structurally normal.
Combined with soundness this pins `reduceOnce`'s halting set to exactly `isStepNormalForm` — the
precise spec the weak-normalization normalizer FUNCTION needs to terminate at a *genuine* normal
form.

Since the IOTA-T11 reducer rebase the proof routes through the TABLE: a `none` result means no
legacy-table step exists (`reduceOnceOverTable_eq_none_blocks_step`, generic); a non-normal term
would witness a bespoke `Step` (`exists_step_of_not_isStepNormalForm`), which the IOTA-T1 forward
adequacy (`Step.toLegacyTableStep`) turns into exactly such a legacy-table step — contradiction.
The per-iota `hasRootStepSource` boolean recombination is no longer in this chain.

* `reduceOnce_complete` / `reduceOnceSpine_complete` — `reduceOnce term = none → isStepNormalForm
  term` (and the spine companion).
* `reduceOnce_eq_none_iff_isStepNormalForm` — the biconditional; the backward leg is soundness
  against `isStepNormalForm_blocks_step` (a normal term blocks every `Step`, so it cannot reduce).
* `not_isStepNormalForm_imp_reduceOnce_isSome` — the descent guarantee: a non-normal term *does*
  reduce, so the `Acc StepSuccessor` normalizer always has a successor to step to until it reaches
  a normal form.

## Zero-axiom verification

A `Bool` case split on the normality detector, the shipped redex-extraction witnesses
(`exists_step_of_not_isStepNormalForm` / the spine twin), the generic table blocking completeness,
and the legacy adequacy.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Completeness of `reduceOnce`.**  A term the reducer cannot step is structurally normal: were
it not, redex extraction would witness a bespoke `Step`, whose legacy-table image contradicts the
generic blocking completeness of the failed walk. -/
theorem RawTerm.reduceOnce_complete {scope : Nat} {term : RawTerm scope}
    (irreducible : RawTerm.reduceOnce term = none) :
    RawTerm.isStepNormalForm term := by
  cases normalityValue : RawTerm.isStepNormalFormBool term with
  | true => exact normalityValue
  | false =>
      have notNormal : ¬ RawTerm.isStepNormalForm term := fun isNormal =>
        Bool.noConfusion (normalityValue.symm.trans isNormal)
      obtain ⟨reduct, bespokeStep⟩ := exists_step_of_not_isStepNormalForm notNormal
      exact (reduceOnceOverTable_eq_none_blocks_step (table := legacyIotaRuleTable)
        irreducible bespokeStep.toLegacyTableStep).elim

/-- **Completeness of `reduceOnceSpine`.**  A spine the reducer cannot step is structurally
normal — the spine companion of `reduceOnce_complete`. -/
theorem RawTermChildren.reduceOnceSpine_complete {binderShifts : List Nat} {scope : Nat}
    {children : RawTermChildren binderShifts scope}
    (irreducible : RawTermChildren.reduceOnceSpine children = none) :
    RawTermChildren.areStepNormalForms children := by
  cases normalityValue : RawTermChildren.areStepNormalFormsBool children with
  | true => exact normalityValue
  | false =>
      have notNormal : ¬ RawTermChildren.areStepNormalForms children := fun areNormal =>
        Bool.noConfusion (normalityValue.symm.trans areNormal)
      obtain ⟨reducedChildren, childrenStep⟩ :=
        exists_stepChildren_of_not_areStepNormalForms notNormal
      exact (reduceOnceSpineOverTable_eq_none_blocks_step (table := legacyIotaRuleTable)
        irreducible (StepChildren.toLegacyTableStepChildren childrenStep)).elim

/-- **`reduceOnce` halts exactly at normal forms.**  Forward is completeness; backward is soundness
against `isStepNormalForm_blocks_step` (a normal term admits no `Step`, hence no reduct). -/
theorem RawTerm.reduceOnce_eq_none_iff_isStepNormalForm {scope : Nat} {term : RawTerm scope} :
    RawTerm.reduceOnce term = none ↔ RawTerm.isStepNormalForm term := by
  constructor
  · exact RawTerm.reduceOnce_complete
  · intro normalForm
    cases hReduce : RawTerm.reduceOnce term with
    | none => rfl
    | some reduct =>
        exact absurd (RawTerm.reduceOnce_sound hReduce)
          (RawTerm.isStepNormalForm_blocks_step normalForm reduct)

/-- **Descent guarantee.**  A non-normal term genuinely reduces — the successor the `Acc StepSuccessor`
normalizer steps to.  The computable, function-valued counterpart of `exists_step_of_not_isStepNormalForm`. -/
theorem RawTerm.not_isStepNormalForm_imp_reduceOnce_isSome {scope : Nat} {term : RawTerm scope}
    (notNormal : ¬ RawTerm.isStepNormalForm term) :
    (RawTerm.reduceOnce term).isSome = true := by
  cases hReduce : RawTerm.reduceOnce term with
  | some reduct => rfl
  | none =>
      exact absurd (RawTerm.reduceOnce_eq_none_iff_isStepNormalForm.mp hReduce) notNormal

end FX1Poly.Core
