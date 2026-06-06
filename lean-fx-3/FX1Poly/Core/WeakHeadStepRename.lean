import FX1Poly.Core.WeakHeadStep
import FX1Poly.Core.RawTermFresh

/-! # Foundation/PolyCell/Core/WeakHeadStepRename
    — the complete weak-head reduction commutes with renaming

`WeakHeadStepSubst` shows the complete weak-head reduction `WeakHeadStep` (β + root-ι +
scrutinee-congruence) commutes with a parallel substitution.  The reducibility-under-renaming development
needs the renaming analogue: renaming a weak-head redex by `rawRenaming` weak-head-steps to the
renamed contractum.  This is the `whnfExpand`-arm ingredient of the stratified `ReducibleTypeStep`
rename-closure (the SN-preserving neutral-leaf ingredient `isStronglyNormalizing_rename_of_leftInverse`
landed alongside).

The proof mirrors `WeakHeadStep.subst` exactly, swapping the substitution lemmas for their renaming twins:

  * `IotaHeadStep.rename` — root-ι commutes with renaming.  Every ι contractum is a Church-encoded
    reshuffling of the redex children (NO `subst0`), so renaming distributes through both redex and
    contractum definitionally and each of the sixteen rules transports by a bare constructor.

  * `WeakHeadStep.rename` — `beta` reshapes its `subst0` contractum by `RawTerm.rename_subst0_commute`;
    `appCongruence` and the ten `scrutineeCong` rules transport by the induction hypothesis; `rootIota`
    delegates to `IotaHeadStep.rename`.

## Zero-axiom verification

`induction` on the ι / weak-head derivation; the β contractum rewritten by `RawTerm.rename_subst0_commute`,
every other arm a constructor on the induction hypothesis (or `IotaHeadStep.rename`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Root-ι reduction commutes with renaming.**  Each ι contractum is a Church-encoded reshuffling of the
redex children (no `subst0`), so renaming distributes through both sides and every rule transports by its
own constructor. -/
theorem IotaHeadStep.rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (iotaStep : IotaHeadStep term reduct) :
    IotaHeadStep (RawTerm.rename rawRenaming term) (RawTerm.rename rawRenaming reduct) := by
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

/-- **The complete weak-head reduction commutes with renaming.**  `beta` reshapes its `subst0` contractum by
`RawTerm.rename_subst0_commute`; `appCongruence` / `scrutineeCong` transport by the induction hypothesis;
`rootIota` by `IotaHeadStep.rename`. -/
theorem WeakHeadStep.rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {term reduct : RawTerm sourceScope} (weakHeadStep : WeakHeadStep term reduct) :
    WeakHeadStep (RawTerm.rename rawRenaming term) (RawTerm.rename rawRenaming reduct) := by
  induction weakHeadStep with
  | beta => rw [RawTerm.rename_subst0_commute]; exact WeakHeadStep.beta
  | appCongruence _functionStep functionInductiveHypothesis =>
      exact WeakHeadStep.appCongruence functionInductiveHypothesis
  | rootIota iotaStep => exact WeakHeadStep.rootIota (iotaStep.rename rawRenaming)
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
