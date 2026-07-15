import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst

/-! # FX1Poly/Core/StepSubst0ArgumentStar
    — the `StepStar` lift of the `subst0` argument-congruence (the dependent-eliminator branch-conversion crux)

`Step.subst0Argument` (StepSubst.lean) replays a SINGLE argument step through `subst0` with a fixed body,
yielding a `StepStar` (the body may duplicate variable 0).  The dependent data-eliminator fundamental-theorem
bridges need the MULTI-step version: when a scrutinee REDUCES — a `StepStar`, e.g. `scrutinee ↠ boolTrueCell`
on the way to a canonical value — the eliminator's dependent result type `subst0 motive scrutinee` reduces in
lockstep to `subst0 motive value`.  That lockstep reduction is exactly the conversion `Conv (subst0 motive
scrutinee) (subst0 motive value)` along which a branch typed at `subst0 motive value` transfers into the
result type.

`StepStar.subst0Argument`: induction on the argument's `StepStar`, threading `Step.subst0Argument` (itself a
`StepStar`) through `StepStar.trans_compose`.

## Zero-axiom verification

A 2-case `StepStar.rec` (`refl` → `StepStar.refl`; `trans` → `Step.subst0Argument` composed with the inductive
hypothesis via `StepStar.trans_compose`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Swept by `#audit_namespace FX1Poly.Core`. -/

namespace FX1Poly.Core

open FX1Poly.Axis.Syntax

/-- **`StepStar` lift of `Step.subst0Argument`.**  When the argument reduces by `StepStar`, `subst0 body`
reduces in lockstep: `StepStar argument updatedArgument → StepStar (subst0 body argument) (subst0 body
updatedArgument)`.  Each single argument step is replayed by `Step.subst0Argument` (already a `StepStar`,
since `body` may duplicate variable 0), and the per-step chains are assembled by `StepStar.trans_compose`.
The dependent-eliminator bridges read the result type's lockstep reduction off this lemma. -/
theorem StepStar.subst0Argument {scope : Nat} (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentReduction : StepStar argument updatedArgument) :
    StepStar (RawTerm.subst0 body argument) (RawTerm.subst0 body updatedArgument) := by
  induction argumentReduction with
  | refl _ => exact StepStar.refl _
  | trans firstStep _restReduction restInductiveHypothesis =>
      exact StepStar.trans_compose (Step.subst0Argument body firstStep) restInductiveHypothesis

end FX1Poly.Core
