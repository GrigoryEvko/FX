import LeanFX2.Foundation.RawSubst

/-! # Foundation/RawTermInjective — rename injectivity (D2.5.5 prerequisite)

Foundation lemmas for the cd-cascade rename helper that fires when
the dispatcher detects `piTyCode A A.weaken` shapes.  Without these,
the `decide (A = B)` test inside `cdTranspPathLamBody` is not
rename-equivariant under non-injective renamings.

Strict zero-axiom verified per declaration.  CRITICAL: proofs use
DIRECT pattern-match style (matching the propext-clean precedent of
`RawRenaming.lift_pointwise` in `RawSubst.lean`), NOT `by ... match`
tactic mode (which leaks propext through Lean 4 v4.29.1's match
compiler).

## Root status

* Layer: foundation (above `RawSubst`, below `Confluence/RawCdRename`)
* Load-bearing for: D2.5.5+ cd-cascade rename helpers
* Axiom budget: zero
-/

namespace LeanFX2

/-- A renaming is injective when distinct source positions map to
distinct target positions. -/
def RawRenamingInjective {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) : Prop :=
  ∀ (positionA positionB : Fin sourceScope),
    rawRenaming positionA = rawRenaming positionB →
    positionA = positionB

/-- `RawRenaming.weaken` (= `Fin.succ`) is injective.  Pure
val-level reasoning via `Nat.succ.inj`; no Fin pattern matching. -/
theorem RawRenamingInjective.weaken {scope : Nat} :
    RawRenamingInjective (RawRenaming.weaken (scope := scope)) := by
  intro positionA positionB succEq
  apply Fin.ext
  have valEq : (RawRenaming.weaken positionA).val =
               (RawRenaming.weaken positionB).val :=
    congrArg Fin.val succEq
  exact Nat.succ.inj valEq

/-- `RawRenaming.lift` preserves injectivity through binders.

DIRECT pattern-match style on `(positionA, positionB)` Fin pairs —
matches `RawRenaming.lift_pointwise`'s propext-clean precedent.
NOT `by ... match positionA with ...` (tactic-mode match leaks propext). -/
theorem RawRenamingInjective.lift {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    (rhoInjective : RawRenamingInjective rho) :
    RawRenamingInjective rho.lift
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨0, _⟩, ⟨kB + 1, ltB⟩, liftEq => by
      exfalso
      have valLiftEq : (rho.lift ⟨0, Nat.zero_lt_succ _⟩).val =
                       (rho.lift ⟨kB + 1, ltB⟩).val :=
        congrArg Fin.val liftEq
      exact Nat.noConfusion valLiftEq
  | ⟨kA + 1, ltA⟩, ⟨0, _⟩, liftEq => by
      exfalso
      have valLiftEq : (rho.lift ⟨kA + 1, ltA⟩).val =
                       (rho.lift ⟨0, Nat.zero_lt_succ _⟩).val :=
        congrArg Fin.val liftEq
      exact Nat.noConfusion valLiftEq
  | ⟨kA + 1, ltA⟩, ⟨kB + 1, ltB⟩, liftEq => by
      have valLiftEq : (rho.lift ⟨kA + 1, ltA⟩).val =
                       (rho.lift ⟨kB + 1, ltB⟩).val :=
        congrArg Fin.val liftEq
      have rhoValEq : (rho ⟨kA, Nat.lt_of_succ_lt_succ ltA⟩).val =
                      (rho ⟨kB, Nat.lt_of_succ_lt_succ ltB⟩).val :=
        Nat.succ.inj valLiftEq
      have rhoEq : rho ⟨kA, Nat.lt_of_succ_lt_succ ltA⟩ =
                   rho ⟨kB, Nat.lt_of_succ_lt_succ ltB⟩ :=
        Fin.ext rhoValEq
      have abEq : (⟨kA, Nat.lt_of_succ_lt_succ ltA⟩ : Fin sourceScope) =
                  ⟨kB, Nat.lt_of_succ_lt_succ ltB⟩ :=
        rhoInjective _ _ rhoEq
      apply Fin.ext
      have valAB : kA = kB := congrArg Fin.val abEq
      show kA + 1 = kB + 1
      exact congrArg (· + 1) valAB

end LeanFX2
