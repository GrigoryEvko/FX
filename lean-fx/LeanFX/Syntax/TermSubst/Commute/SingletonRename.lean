import LeanFX.Syntax.TermSubst.Commute.Precompose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Singleton substitution and renaming.

This is the term-level companion to
`Subst.singleton_renameAfter_equiv_precompose`: substituting one
argument and then renaming the result agrees pointwise, up to HEq, with
renaming under the binder and substituting the renamed argument.  The
β-preservation proof for `Step.rename_compatible` uses this to compare
the renamed β-reduct with the β-reduct of the renamed redex. -/

/-- Term-level singleton substitution commutes with downstream renaming,
pointwise up to HEq. -/
theorem TermSubst.singleton_renameAfter_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {argumentType : Ty level sourceScope}
    (argumentTerm : Term sourceCtx argumentType) :
    ∀ (position : Fin (sourceScope + 1)),
      HEq
        (TermSubst.renameAfter (TermSubst.singleton argumentTerm) termRenaming position)
        (TermSubst.precompose (TermRenaming.lift termRenaming argumentType)
          (TermSubst.singleton (Term.rename termRenaming argumentTerm)) position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.rename_HEq_cast_input termRenaming
          (Ty.weaken_subst_singleton argumentType argumentType).symm
          argumentTerm)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact (eqRec_heq _ _).symm
  | ⟨index + 1, isWithinScope⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.rename_HEq_cast_input termRenaming
          (Ty.weaken_subst_singleton
            (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
            argumentType).symm
          (Term.var ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩))
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact (eqRec_heq _ _).symm

/-- Term-bearing analog: `TermSubst.termSingleton` commutes with
downstream renaming, pointwise up to HEq.  Same proof template as
`singleton_renameAfter_pointwise`, with `Ty.weaken_subst_singleton`
replaced by `Ty.weaken_subst_termSingleton` (which carries an extra
rawArg parameter, irrelevant after weakening). -/
theorem TermSubst.termSingleton_renameAfter_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {argumentType : Ty level sourceScope}
    (argumentTerm : Term sourceCtx argumentType) :
    ∀ (position : Fin (sourceScope + 1)),
      HEq
        (TermSubst.renameAfter
          (TermSubst.termSingleton argumentTerm) termRenaming position)
        (TermSubst.precompose (TermRenaming.lift termRenaming argumentType)
          (TermSubst.termSingleton
            (Term.rename termRenaming argumentTerm)) position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.rename_HEq_cast_input termRenaming
          (Ty.weaken_subst_termSingleton argumentType argumentType
            (Term.toRaw argumentTerm)).symm
          argumentTerm)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact (eqRec_heq _ _).symm
  | ⟨index + 1, isWithinScope⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.rename_HEq_cast_input termRenaming
          (Ty.weaken_subst_termSingleton
            (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
            argumentType (Term.toRaw argumentTerm)).symm
          (Term.var ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩))
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact (eqRec_heq _ _).symm

end LeanFX.Syntax
