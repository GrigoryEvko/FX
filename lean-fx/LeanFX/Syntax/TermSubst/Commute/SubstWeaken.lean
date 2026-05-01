import LeanFX.Syntax.TermSubst.Commute.RenameSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.subst_weaken_commute_HEq`.

Term-level analogue of `Ty.subst_weaken_commute`:

  Term.subst (termSubstitution.lift X) (Term.weaken X term)
    ≃HEq≃
  Term.weaken (X.subst typeSubstitution)
              (Term.subst termSubstitution term)

Direct corollary of v1.40 + v1.42 — no fresh structural induction.
Both sides factor into rename/subst forms (since `Term.weaken X term`
is `Term.rename (TermRenaming.weaken Γ X) term`).  v1.42 collapses
LHS to `Term.subst (precompose (weaken Γ X) (termSubstitution.lift X))
term`; v1.40 collapses RHS to `Term.subst (renameAfter termSubstitution
(weaken Δ (X.subst typeSubstitution))) term`.
The two underlying Substs (`precompose Renaming.weaken typeSubstitution.lift`
and `renameAfter typeSubstitution Renaming.weaken`) are pointwise
rfl-equal — both reduce to `(typeSubstitution i).weaken`.
`Term.subst_HEq_pointwise` bridges them.

This subsumes the v1.28–v1.33 standalone closed-context case
lemmas (`Term.subst_weaken_commute_HEq_{var,unit,boolTrue,boolFalse,
app,boolElim,fst,snd,pair,appPi}`); the binder cases (`lam`,
`lamPi`) that were missing in those layered theorems are now
covered by the same corollary.  Mirrors v1.38 exactly. -/
theorem Term.subst_weaken_commute_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution :
      TermSubst sourceContext targetContext typeSubstitution)
    (newType : Ty level sourceScope)
    {tyValue : Ty level sourceScope} (term : Term sourceContext tyValue) :
    HEq (Term.subst (termSubstitution.lift newType)
          (Term.weaken newType term))
        (Term.weaken (newType.subst typeSubstitution)
          (Term.subst termSubstitution term)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.subst (termSubstitution.lift newType)
      (Term.rename (TermRenaming.weaken sourceContext newType) term))
    (Term.rename (TermRenaming.weaken targetContext
                  (newType.subst typeSubstitution))
      (Term.subst termSubstitution term))
  -- Collapse LHS via v1.42 to a single composed subst.
  apply HEq.trans
    (Term.rename_subst_commute_HEq
      (TermRenaming.weaken sourceContext newType)
      (termSubstitution.lift newType)
      term)
  -- Same for RHS via v1.40, in symm orientation.
  apply HEq.symm
  apply HEq.trans
    (Term.subst_rename_commute_HEq
      termSubstitution
      (TermRenaming.weaken targetContext (newType.subst typeSubstitution))
      term)
  apply HEq.symm
  -- The two composed underlying Substs agree pointwise — `fun _ => rfl`.
  -- The pointwise HEq between the term-level composed TermSubsts
  -- follows from the cast-strip identity: at each i both reduce
  -- (modulo casts) to `Term.weaken (newType.subst typeSubstitution)
  -- (termSubstitution i)`.
  exact Term.subst_HEq_pointwise rfl
    (TermSubst.precompose
      (TermRenaming.weaken sourceContext newType)
      (termSubstitution.lift newType))
    (TermSubst.renameAfter termSubstitution
      (TermRenaming.weaken targetContext (newType.subst typeSubstitution)))
    (Subst.precompose_weaken_lift_equiv_renameAfter_weaken typeSubstitution)
    (fun _ => by
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact eqRec_heq _ _)
    term



end LeanFX.Syntax
