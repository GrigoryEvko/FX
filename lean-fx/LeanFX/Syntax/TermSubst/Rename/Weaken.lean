import LeanFX.Syntax.TermSubst.Rename.Compose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.rename_weaken_commute_HEq`.

Term-level analogue of `Ty.rename_weaken_commute`:

  Term.rename (lift ρt X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.rename ρ) (Term.rename ρt t)

Both sides factor into double-rename forms because `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`.  By v1.37 each side
collapses to a single rename along a composed TermRenaming; the two
underlying renamings (`compose Renaming.weaken ρ.lift` and `compose
ρ Renaming.weaken`) are pointwise equal — both reduce to `Fin.succ ∘ ρ`
modulo Fin proof-irrelevance.  The bridge is `Term.rename_HEq_pointwise`
(v1.36) over the trivial pointwise witness. -/
theorem Term.rename_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.rename (TermRenaming.lift ρt newType) (Term.weaken newType t))
        (Term.weaken (newType.rename ρ) (Term.rename ρt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.rename (TermRenaming.lift ρt newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.rename ρ))
      (Term.rename ρt t))
  -- Collapse LHS via v1.37 to a single composed rename.
  apply HEq.trans
    (Term.rename_compose_HEq
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType)
      t)
  -- Same for RHS, in symm orientation so it lands on the right of HEq.
  apply HEq.symm
  apply HEq.trans
    (Term.rename_compose_HEq
      ρt
      (TermRenaming.weaken Δ (newType.rename ρ))
      t)
  apply HEq.symm
  -- The two composed underlying renamings agree pointwise — `fun _ => rfl`.
  exact Term.rename_HEq_pointwise rfl
    (TermRenaming.compose
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType))
    (TermRenaming.compose ρt
      (TermRenaming.weaken Δ (newType.rename ρ)))
    (fun _ => rfl)
    t



end LeanFX.Syntax
