import FX1Poly.Core.WeakHeadStep
import FX1Poly.Core.RawTermFresh
import FX1Poly.Core.StepTableRenameReflection
import FX1Poly.Core.RawTermFoldNonVarCommute

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

/-- **The two-binder succ-iota contractum commutes with an outer renaming.**

The renaming twin of `RawTerm.natSuccElim_subst_commute`: pushing a renaming `rawRenaming` through the
Phase-Z natElim/natRec succ-iota contractum lifts the renaming twice for the two-binder succ-branch and
renames each substituent.

  `rename rho (subst (cons recCall (singleton pred)) succBranch)
     = subst (cons (rename rho recCall) (singleton (rename rho pred)))
             (rename (iterateLiftRaw rho 2) succBranch)`.

Proved by the same `subst_rename_commute` + `rename_subst_commute` + `subst_pointwise` template as
`RawTerm.rename_subst0_commute`; the pointwise residual closes by `rfl` at every position (renamings are
positional, so the lift / weakening cancellations are definitional). -/
theorem RawTerm.natSuccElim_rename_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (recursiveCall predecessor : RawTerm sourceScope)
    (succBranch : RawTerm (sourceScope + 2)) :
    RawTerm.rename rawRenaming
        (RawTerm.subst
          (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
          succBranch) =
      RawTerm.subst
        (RawTermSubst.cons
          (RawTerm.rename rawRenaming recursiveCall)
          (RawTermSubst.singleton (RawTerm.rename rawRenaming predecessor)))
        (RawTerm.rename (iterateLiftRaw rawRenaming 2) succBranch) := by
  rw [RawTerm.subst_rename_commute]
  rw [RawTerm.rename_subst_commute]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨_priorValue + 2, _⟩ => rfl

/-- **Root-ι reduction commutes with renaming.**  Most ι contracta are Church-encoded reshufflings of the
redex children (no `subst0`), so renaming distributes through both sides and those rules transport by their
own constructor.  The two substituting succ-iotas (`iotaNatElimSucc` / `iotaNatRecSucc`) rewrite by
`RawTerm.natSuccElim_rename_commute` first. -/
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
  | iotaNatElimSucc =>
      rw [RawTerm.natSuccElim_rename_commute]; exact IotaHeadStep.iotaNatElimSucc
  | iotaNatRecSucc =>
      rw [RawTerm.natSuccElim_rename_commute]; exact IotaHeadStep.iotaNatRecSucc
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
  | pathAppCongruence _functionStep functionInductiveHypothesis =>
      exact WeakHeadStep.pathAppCongruence functionInductiveHypothesis
  | scrutineeQuotRec _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeQuotRec scrutineeInductiveHypothesis
  | scrutineeQuotElim _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeQuotElim scrutineeInductiveHypothesis
  | scrutineeTruncRec _scrutineeStep scrutineeInductiveHypothesis =>
      exact WeakHeadStep.scrutineeTruncRec scrutineeInductiveHypothesis
  | @pathBeta spine _reduct fires =>
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming
        (fun contra => Generator.noConfusion contra)]
      have renamedFires := pathBetaIotaRow.firesOn?_rename rawRenaming
        (iotaRuleTable_isScopeUniform _ pathBetaIotaRow_memTable) () spine
      rw [fires] at renamedFires
      exact WeakHeadStep.pathBeta renamedFires
  | @quotRecMk spine _reduct fires =>
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming
        (fun contra => Generator.noConfusion contra)]
      have renamedFires := quotRecMkIotaRow.firesOn?_rename rawRenaming
        (iotaRuleTable_isScopeUniform _ quotRecMkIotaRow_memTable) () spine
      rw [fires] at renamedFires
      exact WeakHeadStep.quotRecMk renamedFires
  | @quotElimMk spine _reduct fires =>
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming
        (fun contra => Generator.noConfusion contra)]
      have renamedFires := quotElimMkIotaRow.firesOn?_rename rawRenaming
        (iotaRuleTable_isScopeUniform _ quotElimMkIotaRow_memTable) () spine
      rw [fires] at renamedFires
      exact WeakHeadStep.quotElimMk renamedFires
  | @truncRecIntro truncationLevel spine _reduct fires =>
      rw [RawTerm.rename_mkGen_of_ne_var rawRenaming
        (fun contra => Generator.noConfusion contra)]
      have renamedFires := truncRecIntroIotaRow.firesOn?_rename rawRenaming
        (iotaRuleTable_isScopeUniform _ truncRecIntroIotaRow_memTable)
        truncationLevel spine
      rw [fires] at renamedFires
      exact WeakHeadStep.truncRecIntro renamedFires

end FX1Poly.Core
