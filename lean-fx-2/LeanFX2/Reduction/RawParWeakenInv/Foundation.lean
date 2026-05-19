import LeanFX2.Reduction.RawParInversion
import LeanFX2.Foundation.RawPartialRename

/-! # Reduction/RawParWeakenInv/Foundation — injectivity of weaken and lift

Foundational injectivity lemmas threaded through the cascade:
`RawRenaming.weaken_injective` (used to specialize the headline
`rename_inj_inv` to the canonical weaken case) and
`RawRenaming.lift_injective` (propagates injectivity into binder
recursion).

## Root status

Kernel `theorem`s with bodies, zero-axiom. -/

namespace LeanFX2

/-- `RawRenaming.weaken` is injective: `weaken a = weaken b → a = b`.

Used by `weaken_inv` to specialize the general `rename_inj_inv` to
the weaken case.  Standalone-useful. -/
theorem RawRenaming.weaken_injective {scope : Nat} :
    ∀ (a b : Fin scope), RawRenaming.weaken a = RawRenaming.weaken b → a = b := by
  intro a b h
  cases a with
  | mk aVal aLt =>
    cases b with
    | mk bVal bLt =>
      simp only [RawRenaming.weaken, Fin.succ] at h
      have hValSucc : aVal + 1 = bVal + 1 := Fin.mk.inj h
      have hVal : aVal = bVal := Nat.succ.inj hValSucc
      cases hVal
      rfl

/-- Lifting an injective renaming preserves injectivity:
if `rho` is injective on `Fin sourceScope`, then `rho.lift` is
injective on `Fin (sourceScope + 1)`.

Used by `rename_inj_inv` to recurse on binder cases: the body of
`lam`, `pathLam`, `piTyCode`, `sigmaTyCode` lives at scope+1 and we
need an injective renaming there. -/
theorem RawRenaming.lift_injective {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (rhoInj : ∀ a b, rho a = rho b → a = b) :
    ∀ a b, rho.lift a = rho.lift b → a = b := by
  intro a b h
  cases a with
  | mk aVal aLt =>
    cases b with
    | mk bVal bLt =>
      cases aVal with
      | zero =>
        cases bVal with
        | zero => rfl
        | succ bPred =>
            simp only [RawRenaming.lift, Fin.succ] at h
            cases h
      | succ aPred =>
        cases bVal with
        | zero =>
            simp only [RawRenaming.lift, Fin.succ] at h
            cases h
        | succ bPred =>
            have aPredLt : aPred < sourceScope := Nat.lt_of_succ_lt_succ aLt
            have bPredLt : bPred < sourceScope := Nat.lt_of_succ_lt_succ bLt
            simp only [RawRenaming.lift, Fin.succ] at h
            have hValSucc : (rho ⟨aPred, aPredLt⟩).val + 1 = (rho ⟨bPred, bPredLt⟩).val + 1 :=
              Fin.mk.inj h
            have hVal : (rho ⟨aPred, aPredLt⟩).val = (rho ⟨bPred, bPredLt⟩).val :=
              Nat.succ.inj hValSucc
            have hRho : rho ⟨aPred, aPredLt⟩ = rho ⟨bPred, bPredLt⟩ :=
              Fin.eq_of_val_eq hVal
            have hPred := rhoInj _ _ hRho
            have : aPred = bPred := Fin.mk.inj hPred
            cases this
            rfl


end LeanFX2
