import LeanFX.Syntax.TermSubst.Commute.RenameSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.subst_weaken_commute_HEq`.

Term-level analogue of `Ty.subst_weaken_commute`:

  Term.subst (σt.lift X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.subst σ) (Term.subst σt t)

Direct corollary of v1.40 + v1.42 — no fresh structural induction.
Both sides factor into rename/subst forms (since `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`).  v1.42 collapses
LHS to `Term.subst (precompose (weaken Γ X) (σt.lift X)) t`; v1.40
collapses RHS to `Term.subst (renameAfter σt (weaken Δ (X.subst σ))) t`.
The two underlying Substs (`precompose Renaming.weaken σ.lift` and
`renameAfter σ Renaming.weaken`) are pointwise rfl-equal — both
reduce to `(σ i).weaken`.  `Term.subst_HEq_pointwise` (v1.24)
bridges them.

This subsumes the v1.28–v1.33 standalone closed-context case
lemmas (`Term.subst_weaken_commute_HEq_{var,unit,boolTrue,boolFalse,
app,boolElim,fst,snd,pair,appPi}`); the binder cases (`lam`,
`lamPi`) that were missing in those layered theorems are now
covered by the same corollary.  Mirrors v1.38 exactly. -/
theorem Term.subst_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.subst (σt.lift newType) (Term.weaken newType t))
        (Term.weaken (newType.subst σ) (Term.subst σt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.subst (σt.lift newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.subst σ))
      (Term.subst σt t))
  -- Collapse LHS via v1.42 to a single composed subst.
  apply HEq.trans
    (Term.rename_subst_commute_HEq
      (TermRenaming.weaken Γ newType)
      (σt.lift newType)
      t)
  -- Same for RHS via v1.40, in symm orientation.
  apply HEq.symm
  apply HEq.trans
    (Term.subst_rename_commute_HEq
      σt
      (TermRenaming.weaken Δ (newType.subst σ))
      t)
  apply HEq.symm
  -- The two composed underlying Substs agree pointwise — `fun _ => rfl`.
  -- The pointwise HEq between the term-level composed TermSubsts
  -- follows from the cast-strip identity: at each i both reduce
  -- (modulo casts) to `Term.weaken (newType.subst σ) (σt i)`.
  exact Term.subst_HEq_pointwise rfl
    (TermSubst.precompose
      (TermRenaming.weaken Γ newType) (σt.lift newType))
    (TermSubst.renameAfter σt
      (TermRenaming.weaken Δ (newType.subst σ)))
    (Subst.precompose_weaken_lift_equiv_renameAfter_weaken σ)
    (fun _ => by
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact eqRec_heq _ _)
    t



end LeanFX.Syntax
