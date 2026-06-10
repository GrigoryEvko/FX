import FX1Poly.Core.FireRootEtaRedex
import FX1Poly.Core.StepBetaEtaConfluence

/-! # FX1Poly/Core/NormalizeBetaEta
    — the βη normalizer FUNCTION on the βη-strongly-normalizing fragment (the ETA-2 harvest, raw half)

`Core/Normalize` iterates `reduceOnce` (β/ι) along an `Acc StepStar.StepSuccessor` witness; this file
is its exact βη twin: iterate `reduceOnceBetaEta` (β/ι anywhere, then the root η-firer) along an
`Acc Step.betaEtaSuccessor` witness.  The two correctness theorems mirror the β/ι pair:

  * `normalizeBetaEta_reducesTo` — the output is reached by a `Step.betaEtaStar` chain;
  * `normalizeBetaEta_isBetaEtaNormalForm` — the output admits NO `Step.betaEta` step at all
    (β/ι-normal everywhere AND root-η-free; since `Step.eta` is root-only by construction, that is
    full βη-normality).

The accessibility hypothesis is supplied on the well-typed fragment by typed βη-SN
(`HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc`, OSN-1) — the raw relation is NOT
globally βη-SN, so the witness is a real hypothesis here, exactly as in `Core/Normalize`.

## Why `Acc.rec` and not the equation compiler

Same reason as `Core/Normalize`: `reduceOnceBetaEta` is not size-decreasing (β/ι can grow a term),
so the recursion descends on the accessibility proof; the equation compiler's `brecOn` cannot
large-eliminate the `Prop`-valued `Acc` into `RawTerm`, so the function is written directly with
`Acc.rec` and unfolds by `rfl` at an `Acc.intro` witness.

## Zero-axiom verification

`Acc.rec`, `Acc`-induction, `split` on the reducer result, and the shipped
`reduceOnceBetaEta_sound`/`reduceOnceBetaEta_complete`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **The βη normalizer.**  Iterate `reduceOnceBetaEta` along the βη accessibility witness until it
halts; the output is a full βη-normal form of `term`.  `Acc.rec` because the descent shrinks the
accessibility proof, not the term. -/
def RawTerm.normalizeBetaEta {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@Step.betaEtaSuccessor scope) term) : RawTerm scope :=
  Acc.rec
    (motive := fun _currentTerm _acc => RawTerm scope)
    (fun currentTerm _accStep normalizeRec =>
      match hReduce : RawTerm.reduceOnceBetaEta currentTerm with
      | none => currentTerm
      | some reduct => normalizeRec reduct (RawTerm.reduceOnceBetaEta_sound hReduce))
    accessible

/-- One-step unfolding of `normalizeBetaEta` at an `Acc.intro` witness (holds by `rfl`). -/
theorem RawTerm.normalizeBetaEta_unfold {scope : Nat} (term : RawTerm scope)
    (accStep : ∀ later, Step.betaEtaSuccessor later term → Acc Step.betaEtaSuccessor later) :
    RawTerm.normalizeBetaEta term (.intro term accStep) =
      (match hReduce : RawTerm.reduceOnceBetaEta term with
        | none => term
        | some reduct =>
            RawTerm.normalizeBetaEta reduct
              (accStep reduct (RawTerm.reduceOnceBetaEta_sound hReduce))) := rfl

/-- **The βη normalizer reaches its output by a `Step.betaEtaStar` chain.**  `Acc`-induction: a
halted step is the reflexive chain; a fired step prepends `reduceOnceBetaEta_sound`. -/
theorem RawTerm.normalizeBetaEta_reducesTo {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@Step.betaEtaSuccessor scope) term) :
    Step.betaEtaStar term (RawTerm.normalizeBetaEta term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeBetaEta_unfold currentTerm accStep]
      split
      · exact Step.betaEtaStar.refl _
      · next reduct hReduce =>
          exact Step.betaEtaStar.trans (RawTerm.reduceOnceBetaEta_sound hReduce)
            (ih reduct (RawTerm.reduceOnceBetaEta_sound hReduce))

/-- **The βη normalizer's output is fully βη-normal**: it admits no `Step.betaEta` step (the
β/ι half by `reduceOnce` completeness, the η half by the root-only firer's completeness — both
folded into `reduceOnceBetaEta_complete`). -/
theorem RawTerm.normalizeBetaEta_isBetaEtaNormalForm {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@Step.betaEtaSuccessor scope) term) :
    ∀ reduct : RawTerm scope,
      ¬ Step.betaEta (RawTerm.normalizeBetaEta term accessible) reduct := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeBetaEta_unfold currentTerm accStep]
      split
      · next hReduce => exact RawTerm.reduceOnceBetaEta_complete hReduce
      · next reduct hReduce => exact ih reduct (RawTerm.reduceOnceBetaEta_sound hReduce)

end FX1Poly.Core
