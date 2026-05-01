import LeanFX.Syntax.TermSubst.Rename.Compose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.rename_weaken_commute_HEq`.

Term-level analogue of `Ty.rename_weaken_commute`:

  Term.rename (lift termRenaming X) (Term.weaken X term)
    ≃HEq≃
  Term.weaken (X.rename rawRenaming) (Term.rename termRenaming term)

Both sides factor into double-rename forms because `Term.weaken X term`
is `Term.rename (TermRenaming.weaken Γ X) term`.  By v1.37 each side
collapses to a single rename along a composed TermRenaming; the two
underlying renamings (`compose Renaming.weaken rawRenaming.lift` and
`compose rawRenaming Renaming.weaken`) are pointwise equal — both reduce
to `Fin.succ ∘ rawRenaming` modulo Fin proof-irrelevance.  The bridge is
`Term.rename_HEq_pointwise` (v1.36) over the trivial pointwise witness. -/
theorem Term.rename_weaken_commute_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceContext targetContext rawRenaming)
    (newType : Ty level sourceScope)
    {tyValue : Ty level sourceScope} (term : Term sourceContext tyValue) :
    HEq (Term.rename (TermRenaming.lift termRenaming newType)
          (Term.weaken newType term))
        (Term.weaken (newType.rename rawRenaming)
          (Term.rename termRenaming term)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.rename (TermRenaming.lift termRenaming newType)
      (Term.rename (TermRenaming.weaken sourceContext newType) term))
    (Term.rename (TermRenaming.weaken targetContext (newType.rename rawRenaming))
      (Term.rename termRenaming term))
  -- Collapse LHS via v1.37 to a single composed rename.
  apply HEq.trans
    (Term.rename_compose_HEq
      (TermRenaming.weaken sourceContext newType)
      (TermRenaming.lift termRenaming newType)
      term)
  -- Same for RHS, in symm orientation so it lands on the right of HEq.
  apply HEq.symm
  apply HEq.trans
    (Term.rename_compose_HEq
      termRenaming
      (TermRenaming.weaken targetContext (newType.rename rawRenaming))
      term)
  apply HEq.symm
  -- The two composed underlying renamings agree pointwise — `fun _ => rfl`.
  exact Term.rename_HEq_pointwise rfl
    (TermRenaming.compose
      (TermRenaming.weaken sourceContext newType)
      (TermRenaming.lift termRenaming newType))
    (TermRenaming.compose termRenaming
      (TermRenaming.weaken targetContext (newType.rename rawRenaming)))
    (fun _ => rfl)
    term



end LeanFX.Syntax
