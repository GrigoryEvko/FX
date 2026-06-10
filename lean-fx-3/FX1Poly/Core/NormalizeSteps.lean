import FX1Poly.Core.Normalize
import FX1Poly.Core.StepStarLength

/-! # FX1Poly/Core/NormalizeSteps
   — the EXACT step counter for the SN normalizer (SN-145, the STRICT-COMPLEXITY witness)

`RawTerm.normalize` (the `Acc.rec` normalizer) fires `reduceOnce` until it halts.  This file ships
its cost instrumentation: `normalizeSteps`, the `Acc.rec` TWIN that counts exactly how many
`reduceOnce` firings the normalizer performs, with the three facts that make it a complexity
witness rather than a slogan:

  * `normalizeSteps_chainExact` — the normalizer's run IS a counted reduction chain:
    `StepStarN (normalizeSteps t acc) t (normalize t acc)`.  The counter is not an estimate; it is
    the length of the leftmost-outermost chain the normalizer walks.
  * `normalizeSteps_eq_zero_iff` — the counter is `0` exactly on structural normal forms (the
    correctness anchor: zero cost ⟺ nothing to do).
  * `reduceOnce_eq_none_of_isStepNormalForm` — the halting half made explicit (the converse of
    `reduceOnce_complete`).

## What is HONESTLY claimed about the bound — and what is not

The §11.8.7 STRICT-COMPLEXITY discipline asks every decision procedure for a verified cost bound.
For the term normalizer the truthful answer is:

  * EXACT cost: `normalizeSteps`, tied to the run by `normalizeSteps_chainExact` (this file).
  * NO size-polynomial bound is claimed: β-reduction length is not elementary in term size
    (Statman 1979 — typed λ-calculus normalization is non-elementary), so the polynomial-shape
    `StrictNormalizer` contract CANNOT be truthfully instantiated with a size-based bound for the
    term normalizer.  It is deliberately left uninstantiated; the machine-checked boundary brick
    in `Typed/NormalizeStepsTower.lean` (`normalizeSteps_unbounded`) shows the counter is not
    bounded by any constant, realized exactly by the identity-tower family.
  * The non-elementary LOWER bound itself is literature-cited, NOT mechanized — a named open
    formalization target, not absorbed.

## Zero-axiom verification

`Acc.rec` (axiom-free large elimination), `Acc`-induction, `split` on the reducer result,
`Option.noConfusion`/`Option.some.inj` cross-branch reconciliation, the shipped
`reduceOnce_sound`/`reduceOnce_complete`, and the `StepStarN` counted-chain constructors.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **The normalizer's exact step counter** — the `Acc.rec` twin of `RawTerm.normalize`: same
scrutinee (`reduceOnce`), same descent (`reduceOnce_sound`), but accumulating one unit per fired
step instead of rebuilding the term.  Mirror-faithful by construction (identical control flow). -/
def RawTerm.normalizeSteps {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) : Nat :=
  Acc.rec
    (motive := fun _currentTerm _acc => Nat)
    (fun currentTerm _accStep stepsRec =>
      match hReduce : RawTerm.reduceOnce currentTerm with
      | none => 0
      | some reduct => stepsRec reduct (RawTerm.reduceOnce_sound hReduce) + 1)
    accessible

/-- One-step unfolding of `normalizeSteps` at an `Acc.intro` witness (holds by `rfl`). -/
theorem RawTerm.normalizeSteps_unfold {scope : Nat} (term : RawTerm scope)
    (accStep : ∀ later, StepStar.StepSuccessor later term → Acc StepStar.StepSuccessor later) :
    RawTerm.normalizeSteps term (.intro term accStep) =
      (match hReduce : RawTerm.reduceOnce term with
        | none => 0
        | some reduct =>
            RawTerm.normalizeSteps reduct
              (accStep reduct (RawTerm.reduceOnce_sound hReduce)) + 1) := rfl

/-- Unfolding of `normalizeSteps` at an OPAQUE accessibility witness: the recursive call's witness
is recovered by `Acc.inv`, and definitional proof irrelevance closes the gap to the `Acc.intro`
form.  This is the equation consumers use when the witness is a theorem-supplied `Acc` (e.g. from
typed SN), not a literal `Acc.intro`. -/
theorem RawTerm.normalizeSteps_eq {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.normalizeSteps term accessible =
      (match hReduce : RawTerm.reduceOnce term with
        | none => 0
        | some reduct =>
            RawTerm.normalizeSteps reduct
              (accessible.inv (RawTerm.reduceOnce_sound hReduce)) + 1) := by
  induction accessible with
  | intro currentTerm accStep _ih =>
      rw [RawTerm.normalizeSteps_unfold currentTerm accStep]

/-- The halting half made explicit: the reducer returns `none` on every structural normal form
(the converse of `reduceOnce_complete`; a fired step would contradict normality via
`reduceOnce_sound`). -/
theorem RawTerm.reduceOnce_eq_none_of_isStepNormalForm {scope : Nat} {term : RawTerm scope}
    (termNormal : RawTerm.isStepNormalForm term) :
    RawTerm.reduceOnce term = none := by
  cases hReduce : RawTerm.reduceOnce term with
  | none => rfl
  | some reduct =>
      exact absurd (RawTerm.reduceOnce_sound hReduce)
        (RawTerm.isStepNormalForm_blocks_step termNormal reduct)

/-- **The counter is exact: the normalizer's run IS a counted chain.**
`normalize t acc` is reached from `t` by a `StepStarN`-chain of length EXACTLY
`normalizeSteps t acc`.  By `Acc`-induction with a double `split` (both `Acc.rec` twins
scrutinize the same `reduceOnce` result; cross branches are `Option.noConfusion`-impossible). -/
theorem RawTerm.normalizeSteps_chainExact {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    StepStarN (RawTerm.normalizeSteps term accessible) term
      (RawTerm.normalize term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeSteps_unfold currentTerm accStep,
          RawTerm.normalize_unfold currentTerm accStep]
      split
      · next hReduceSteps =>
          split
          · exact StepStarN.reflN currentTerm
          · next reduct hReduceNorm =>
              cases hReduceSteps.symm.trans hReduceNorm
      · next reduct hReduceSteps =>
          split
          · next hReduceNorm =>
              cases hReduceNorm.symm.trans hReduceSteps
          · next reductNorm hReduceNorm =>
              have hSameReduct : reduct = reductNorm :=
                Option.some.inj (hReduceSteps.symm.trans hReduceNorm)
              subst hSameReduct
              exact StepStarN.transN (RawTerm.reduceOnce_sound hReduceSteps)
                (ih reduct (RawTerm.reduceOnce_sound hReduceSteps))

/-- **Zero cost exactly at normal forms** — the counter's correctness anchor: `normalizeSteps`
returns `0` iff the input is already a structural normal form. -/
theorem RawTerm.normalizeSteps_eq_zero_iff {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.normalizeSteps term accessible = 0 ↔ RawTerm.isStepNormalForm term := by
  induction accessible with
  | intro currentTerm accStep _ih =>
      constructor
      · intro hZeroSteps
        rw [RawTerm.normalizeSteps_unfold currentTerm accStep] at hZeroSteps
        split at hZeroSteps
        · next hReduce => exact RawTerm.reduceOnce_complete hReduce
        · next reduct hReduce => exact Nat.noConfusion hZeroSteps
      · intro termNormal
        rw [RawTerm.normalizeSteps_unfold currentTerm accStep]
        split
        · rfl
        · next reduct hReduce =>
            cases (RawTerm.reduceOnce_eq_none_of_isStepNormalForm termNormal).symm.trans hReduce

end FX1Poly.Core
