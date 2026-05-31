import FX1Poly.Core.WeakHeadStep
import FX1Poly.Core.RawTermSubst0Commute

/-! # Foundation/PolyCell/Core/WeakHeadStepSubst
    — the complete weak-head reduction commutes with substitution

`HeadStep.subst` (`HeadStepCommute`) shows the β-only weak-head step commutes with a parallel
substitution.  The dependent reducibility relation dispatches on the COMPLETE weak-head reduction
`WeakHeadStep` (β + root-ι + scrutinee-congruence), and the fundamental theorem — interpreting a
well-typed term under a reducible closing substitution — reasons about how the substituted term reduces.
This file lifts substitution-commutation to the full relation.

  * `IotaHeadStep.subst` — root-ι commutes with substitution.  Every ι contractum is Church-encoded (a
    reshuffling of the redex's children into nested applications, NO `subst0`; see the redex/contractum
    pairs in `IotaHeadStep`), so substitution distributes through both redex and contractum definitionally
    and each of the sixteen rules transports by a bare constructor application.

  * `WeakHeadStep.subst` — the complete weak-head reduction commutes with substitution.  `beta` reshapes
    its contractum by `RawTerm.subst0_subst_commute` (the head β-redex's `subst0` interacts with the outer
    substitution); `appCongruence` and the ten `scrutineeCong` rules transport by the induction hypothesis
    under the substituted application / eliminator; `rootIota` delegates to `IotaHeadStep.subst`.

This is a reduction-substrate prerequisite for the fundamental theorem (and for any substitution lemma on
the dependent reducibility relation).

## Zero-axiom verification

`induction` on the ι / weak-head derivation; the β contractum rewritten by `RawTerm.subst0_subst_commute`,
every other arm a constructor on the induction hypothesis (or `IotaHeadStep.subst`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Root-ι reduction commutes with substitution.**  Each ι contractum is a Church-encoded reshuffling
of the redex's children (no `subst0`), so substitution distributes through both sides and every rule
transports by its own constructor. -/
theorem IotaHeadStep.subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (iotaStep : IotaHeadStep term reduct) :
    IotaHeadStep (RawTerm.subst substitution term) (RawTerm.subst substitution reduct) := by
  induction iotaStep with
  | iotaBoolTrue => exact IotaHeadStep.iotaBoolTrue
  | iotaBoolFalse => exact IotaHeadStep.iotaBoolFalse
  | iotaFstPair => exact IotaHeadStep.iotaFstPair
  | iotaSndPair => exact IotaHeadStep.iotaSndPair
  | iotaNatElimZero => exact IotaHeadStep.iotaNatElimZero
  | iotaNatRecZero => exact IotaHeadStep.iotaNatRecZero
  | iotaListElimNil => exact IotaHeadStep.iotaListElimNil
  | iotaOptionMatchNone => exact IotaHeadStep.iotaOptionMatchNone
  | iotaOptionMatchSome => exact IotaHeadStep.iotaOptionMatchSome
  | iotaEitherMatchInl => exact IotaHeadStep.iotaEitherMatchInl
  | iotaEitherMatchInr => exact IotaHeadStep.iotaEitherMatchInr
  | iotaNatElimSucc => exact IotaHeadStep.iotaNatElimSucc
  | iotaNatRecSucc => exact IotaHeadStep.iotaNatRecSucc
  | iotaListElimCons => exact IotaHeadStep.iotaListElimCons
  | iotaIdJRefl => exact IotaHeadStep.iotaIdJRefl
  | iotaIdStrictRecRefl => exact IotaHeadStep.iotaIdStrictRecRefl

/-- **The complete weak-head reduction commutes with substitution.**  `beta` reshapes its `subst0`
contractum by `RawTerm.subst0_subst_commute`; `appCongruence` / `scrutineeCong` transport by the induction
hypothesis; `rootIota` by `IotaHeadStep.subst`. -/
theorem WeakHeadStep.subst {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (weakHeadStep : WeakHeadStep term reduct) :
    WeakHeadStep (RawTerm.subst substitution term) (RawTerm.subst substitution reduct) := by
  induction weakHeadStep with
  | beta => rw [RawTerm.subst0_subst_commute]; exact WeakHeadStep.beta
  | appCongruence _functionStep functionInductiveHypothesis =>
      exact WeakHeadStep.appCongruence functionInductiveHypothesis
  | rootIota iotaStep => exact WeakHeadStep.rootIota (iotaStep.subst substitution)
  | scrutineeBoolElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeBoolElim scrutineeInductiveHypothesis
  | scrutineeFst _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeFst scrutineeInductiveHypothesis
  | scrutineeSnd _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeSnd scrutineeInductiveHypothesis
  | scrutineeNatElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeNatElim scrutineeInductiveHypothesis
  | scrutineeNatRec _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeNatRec scrutineeInductiveHypothesis
  | scrutineeListElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeListElim scrutineeInductiveHypothesis
  | scrutineeOptionMatch _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeOptionMatch scrutineeInductiveHypothesis
  | scrutineeEitherMatch _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeEitherMatch scrutineeInductiveHypothesis
  | scrutineeIdJ _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeIdJ scrutineeInductiveHypothesis
  | scrutineeIdStrictRec _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeIdStrictRec scrutineeInductiveHypothesis

end FX1Poly.Core
