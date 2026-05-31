import FX1Poly.Core.HeadStep
import FX1Poly.Core.WeakHeadStep

/-! # Foundation/PolyCell/Core/WeakHeadStepSubsumes
    — `HeadStep` and `IotaHeadStep` embed into `WeakHeadStep`

`WeakHeadStep` (`WeakHeadStep.lean`) is the COMPLETE weak-head reduction; the two partial substrates it
unifies — `HeadStep` (β at the head / function-spine congruence) and `IotaHeadStep` (root-ι) — are
sub-relations of it.  This file records those embeddings and their immediate corollary: a
`WeakHeadStep`-normal term is both `HeadStep`-normal and `IotaHeadStep`-normal.

The embeddings make the consolidated `ReducibleType.neutral` guard (`¬ WeakHeadStep`) bridge to the
older β/ι vocabulary: a code stuck for the complete weak-head reduction is, in particular, stuck for β
and for root-ι, so any lemma phrased against `HeadStep` / `IotaHeadStep` normality applies to a
`WeakHeadStep`-neutral type.  (The CONVERSE fails — `¬ HeadStep ∧ ¬ IotaHeadStep` does NOT imply
`¬ WeakHeadStep`, because an eliminator with a reducible scrutinee is `WeakHeadStep`-reducible via
scrutinee-congruence while being neither `HeadStep`- nor root-ι-reducible; that asymmetry is exactly why
the complete `WeakHeadStep` was needed.)

## Zero-axiom verification

`HeadStep.toWeakHeadStep` by induction (β ↦ `beta`, congruence ↦ `appCongruence` with the induction
hypothesis); `IotaHeadStep.toWeakHeadStep` is the `rootIota` constructor; the normality corollaries are
contrapositives.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **β weak-head reduction embeds into the complete weak-head reduction.**  `HeadStep ⊆ WeakHeadStep`:
the head β-redex is `WeakHeadStep.beta`; function-spine congruence is `WeakHeadStep.appCongruence` (the
induction hypothesis supplies the recursive `WeakHeadStep`). -/
theorem HeadStep.toWeakHeadStep {scope : Nat} {term reduct : RawTerm scope}
    (headStep : HeadStep term reduct) : WeakHeadStep term reduct := by
  induction headStep with
  | beta => exact WeakHeadStep.beta
  | appCongruence _functionStep functionToWeakHeadStep =>
      exact WeakHeadStep.appCongruence functionToWeakHeadStep

/-- **Root-ι reduction embeds into the complete weak-head reduction.**  `IotaHeadStep ⊆ WeakHeadStep`
via the `rootIota` constructor. -/
theorem IotaHeadStep.toWeakHeadStep {scope : Nat} {term reduct : RawTerm scope}
    (iotaStep : IotaHeadStep term reduct) : WeakHeadStep term reduct :=
  WeakHeadStep.rootIota iotaStep

/-- A `WeakHeadStep`-normal term is `HeadStep`-normal (contrapositive of `HeadStep.toWeakHeadStep`).  The
bridge from the consolidated `¬ WeakHeadStep` neutral guard to β-normality. -/
theorem HeadStep.absent_of_weakHeadStep_absent {scope : Nat} {term : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep term reduct) :
    ∀ reduct : RawTerm scope, ¬ HeadStep term reduct :=
  fun reduct headStep => noWeakHeadStep reduct headStep.toWeakHeadStep

/-- A `WeakHeadStep`-normal term is `IotaHeadStep`-normal (contrapositive of
`IotaHeadStep.toWeakHeadStep`).  The bridge from the consolidated `¬ WeakHeadStep` neutral guard to
root-ι normality. -/
theorem IotaHeadStep.absent_of_weakHeadStep_absent {scope : Nat} {term : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep term reduct) :
    ∀ reduct : RawTerm scope, ¬ IotaHeadStep term reduct :=
  fun reduct iotaStep => noWeakHeadStep reduct iotaStep.toWeakHeadStep

end FX1Poly.Core
