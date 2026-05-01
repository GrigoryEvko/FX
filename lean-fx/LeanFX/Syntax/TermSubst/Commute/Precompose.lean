import LeanFX.Syntax.TermSubst.Commute.RenameAfter

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-level `precompose` and its lift commute.

`TermSubst.precompose termRenaming termSubstitution'` composes a
rename with a downstream subst, producing a subst along
`Subst.precompose rawRenaming typeSubstitution'`.  Companion
lemma `lift_precompose_pointwise` is the structural mirror of
`lift_renameAfter_pointwise`. -/

/-- Term-level `precompose`: rename termRenaming to a Γ' source, then
subst termSubstitution'.  At each position i, looks up
termSubstitution' at the renamed position rawRenaming i; the result
type is bridged via the TermRenaming's witness lifted by `congrArg
(·.subst typeSubstitution')` and chained with
`Ty.rename_subst_commute`. -/
def TermSubst.precompose
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {middleContext : Ctx mode level middleScope}
    {targetContext : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope middleScope}
    {typeSubstitution' : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceContext middleContext rawRenaming)
    (termSubstitution' :
      TermSubst middleContext targetContext typeSubstitution') :
    TermSubst sourceContext targetContext
      (Subst.precompose rawRenaming typeSubstitution') := fun position =>
  let renamedTypeEq :
      (varType middleContext (rawRenaming position)).subst typeSubstitution'
        = ((varType sourceContext position).rename rawRenaming).subst
            typeSubstitution' :=
    congrArg (·.subst typeSubstitution') (termRenaming position)
  let commuteEq :
      ((varType sourceContext position).rename rawRenaming).subst
          typeSubstitution'
        = (varType sourceContext position).subst
            (Subst.precompose rawRenaming typeSubstitution') :=
    Ty.rename_subst_commute (varType sourceContext position)
      rawRenaming typeSubstitution'
  (renamedTypeEq.trans commuteEq) ▸ termSubstitution' (rawRenaming position)

/-- Lifting commutes with `precompose` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets bridged by `Ty.rename_subst_commute
newType rawRenaming typeSubstitution'`.  Position `predecessor + 1`
reduces both sides to `Term.weaken` forms that `Term.weaken_HEq_congr`
collapses. -/
theorem TermSubst.lift_precompose_pointwise
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {middleContext : Ctx mode level middleScope}
    {targetContext : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope middleScope}
    {typeSubstitution' : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceContext middleContext rawRenaming)
    (termSubstitution' :
      TermSubst middleContext targetContext typeSubstitution')
    (newType : Ty level sourceScope) :
    ∀ (position : Fin (sourceScope + 1)),
      HEq
        (TermSubst.precompose (termRenaming.lift newType)
          (termSubstitution'.lift (newType.rename rawRenaming)) position)
        ((TermSubst.precompose termRenaming termSubstitution').lift
          newType position) := by
  have renameSubstEq :
      (newType.rename rawRenaming).subst typeSubstitution'
        = newType.subst (Subst.precompose rawRenaming typeSubstitution') :=
    Ty.rename_subst_commute newType rawRenaming typeSubstitution'
  have targetContextEq :
      targetContext.cons ((newType.rename rawRenaming).subst typeSubstitution')
        = targetContext.cons
            (newType.subst (Subst.precompose rawRenaming typeSubstitution')) :=
    congrArg targetContext.cons renameSubstEq
  intro position
  match position with
  | ⟨0, _⟩ =>
    -- LHS: outer_witness_compose ▸ termSubstitution'.lift (newType.rename
    --   rawRenaming) ((lift termRenaming newType) ⟨0, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq targetContextEq ⟨0, Nat.zero_lt_succ _⟩)
    exact (eqRec_heq _ _).symm
  | ⟨predecessor + 1, succBound⟩ =>
    -- LHS: outer_witness_compose ▸ termSubstitution'.lift
    --        (newType.rename rawRenaming) (Fin.succ (rawRenaming ⟨k, _⟩))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.weaken ((newType.rename rawRenaming).subst
    --   typeSubstitution') (termSubstitution' (rawRenaming ⟨k, _⟩))
    -- RHS at k+1: outer ▸ Term.weaken
    --   (newType.subst (precompose rawRenaming typeSubstitution'))
    --   ((precompose termRenaming termSubstitution') ⟨k, _⟩)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.
    exact Term.weaken_HEq_congr
      renameSubstEq
      ((congrArg (·.subst typeSubstitution')
          (termRenaming ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)).trans
        (Ty.rename_subst_commute
          (varType sourceContext
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          rawRenaming typeSubstitution'))
      (termSubstitution' (rawRenaming
        ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
      (_)
      (eqRec_heq _ _).symm


end LeanFX.Syntax
