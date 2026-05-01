import LeanFX.Syntax.TermSubst.Rename

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-level `renameAfter` and its lift commute.

`TermSubst.renameAfter termSubstitution termRenaming` composes a subst
with a downstream rename, producing a subst along
`Subst.renameAfter typeSubstitution rawRenaming`.  The
companion lemma `lift_renameAfter_pointwise` says lifting then
composing agrees with composing then lifting (pointwise HEq) —
the term-level analogue of `Subst.lift_renameAfter_commute`. -/

/-- Term-level `renameAfter`: subst termSubstitution then rename
termRenaming to a downstream context.  At each position, applies
termSubstitution then renames the result via termRenaming; the result
type is bridged via `Ty.subst_rename_commute`. -/
def TermSubst.renameAfter
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {middleContext : Ctx mode level middleScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope middleScope}
    {rawRenaming : Renaming middleScope targetScope}
    (termSubstitution :
      TermSubst sourceContext middleContext typeSubstitution)
    (termRenaming : TermRenaming middleContext targetContext rawRenaming) :
    TermSubst sourceContext targetContext
      (Subst.renameAfter typeSubstitution rawRenaming) := fun position =>
  Ty.subst_rename_commute (varType sourceContext position)
    typeSubstitution rawRenaming ▸
    Term.rename termRenaming (termSubstitution position)

/-- Lifting commutes with `renameAfter` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets, bridged by `heq_var_across_ctx_eq`
over `Ty.subst_rename_commute newType typeSubstitution rawRenaming`.
Position `predecessor + 1` reduces both sides to a `Term.weaken` of
`Term.rename termRenaming (termSubstitution predecessor)` with
propositionally-distinct `newType` and inner type — the v1.38
`rename_weaken_commute_HEq` collapses LHS to weaken-of-rename, then
`Term.weaken_HEq_congr` bridges the two `Term.weaken` shapes. -/
theorem TermSubst.lift_renameAfter_pointwise
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {middleContext : Ctx mode level middleScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope middleScope}
    {rawRenaming : Renaming middleScope targetScope}
    (termSubstitution :
      TermSubst sourceContext middleContext typeSubstitution)
    (termRenaming : TermRenaming middleContext targetContext rawRenaming)
    (newType : Ty level sourceScope) :
    ∀ (position : Fin (sourceScope + 1)),
      HEq
        (TermSubst.renameAfter (termSubstitution.lift newType)
          (termRenaming.lift (newType.subst typeSubstitution)) position)
        ((TermSubst.renameAfter termSubstitution termRenaming).lift
          newType position) := by
  -- Bridge the cons-extended target contexts at the type level.
  have substRenameEq :
      (newType.subst typeSubstitution).rename rawRenaming
        = newType.subst (Subst.renameAfter typeSubstitution rawRenaming) :=
    Ty.subst_rename_commute newType typeSubstitution rawRenaming
  have targetContextEq :
      targetContext.cons ((newType.subst typeSubstitution).rename rawRenaming)
        = targetContext.cons
            (newType.subst (Subst.renameAfter typeSubstitution rawRenaming)) :=
    congrArg targetContext.cons substRenameEq
  intro position
  match position with
  | ⟨0, _zeroBound⟩ =>
    -- LHS reduces to: outer_cast ▸ rename (termRenaming.lift
    --   (newType.subst typeSubstitution))
    --   (inner_cast.symm ▸ Term.var ⟨0, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (termRenaming.lift (newType.subst typeSubstitution))
        (Ty.subst_weaken_commute newType typeSubstitution).symm
        (Term.var (context := middleContext.cons (newType.subst typeSubstitution))
          ⟨0, Nat.zero_lt_succ _⟩))
    -- Now: rename (termRenaming.lift X) (Term.var ⟨0, _⟩)
    --    = ((termRenaming.lift X) ⟨0, _⟩) ▸ Term.var (rawRenaming.lift ⟨0, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq targetContextEq ⟨0, Nat.zero_lt_succ _⟩)
    -- RHS = (Ty.subst_weaken_commute newType
    --   (Subst.renameAfter typeSubstitution rawRenaming)).symm ▸ Term.var ⟨0, _⟩
    exact (eqRec_heq _ _).symm
  | ⟨predecessor + 1, succBound⟩ =>
    -- LHS = outer_cast ▸ rename (termRenaming.lift X)
    --   (inner_cast.symm ▸ Term.weaken X (termSubstitution k')).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (termRenaming.lift (newType.subst typeSubstitution))
        (Ty.subst_weaken_commute
          (varType sourceContext
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          typeSubstitution).symm
        (Term.weaken (newType.subst typeSubstitution)
          (termSubstitution
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)))
    -- Now: rename (termRenaming.lift X) (Term.weaken X (termSubstitution k'))
    --    ≃HEq≃ Term.weaken (X.rename rawRenaming)
    --             (Term.rename termRenaming (termSubstitution k'))   [by v1.38]
    apply HEq.trans
      (Term.rename_weaken_commute_HEq termRenaming
        (newType.subst typeSubstitution)
        (termSubstitution ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
    -- RHS at k+1 = outer_cast ▸ Term.weaken
    --   (newType.subst (renameAfter typeSubstitution rawRenaming))
    --   ((renameAfter termSubstitution termRenaming) ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Bridge via Term.weaken_HEq_congr.
    apply HEq.symm
    -- Use the cast-input helper to push the inner cast on RHS through
    -- Term.weaken — Term.weaken_HEq_congr handles both newType
    -- differences AND a per-side type-cast difference, so we just supply
    -- the HEq.
    exact Term.weaken_HEq_congr
      substRenameEq
      (Ty.subst_rename_commute
        (varType sourceContext
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
        typeSubstitution rawRenaming)
      (Term.rename termRenaming
        (termSubstitution ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
      (_)
      (eqRec_heq _ _).symm


end LeanFX.Syntax
