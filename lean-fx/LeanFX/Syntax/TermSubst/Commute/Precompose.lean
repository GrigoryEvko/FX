import LeanFX.Syntax.TermSubst.Commute.RenameAfter

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-level `precompose` and its lift commute.

`TermSubst.precompose ρt σt'` composes a rename with a downstream
subst, producing a subst along `Subst.precompose ρ σ'`.  Companion
lemma `lift_precompose_pointwise` is the structural mirror of
`lift_renameAfter_pointwise` (v1.39). -/

/-- Term-level `precompose`: rename ρt to a Γ' source, then subst σt'.
At each position i, looks up σt' at the renamed position ρ i; the
result type is bridged via the TermRenaming's witness lifted by
`congrArg (·.subst σ')` and chained with `Ty.rename_subst_commute`. -/
def TermSubst.precompose
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ') :
    TermSubst Γ Δ (Subst.precompose ρ σ') := fun i =>
  let h_witness : (varType Γ' (ρ i)).subst σ'
                    = ((varType Γ i).rename ρ).subst σ' :=
    congrArg (·.subst σ') (ρt i)
  let h_commute : ((varType Γ i).rename ρ).subst σ'
                    = (varType Γ i).subst (Subst.precompose ρ σ') :=
    Ty.rename_subst_commute (varType Γ i) ρ σ'
  (h_witness.trans h_commute) ▸ σt' (ρ i)

/-- Lifting commutes with `precompose` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets bridged by `Ty.rename_subst_commute
newType ρ σ'`.  Position `k + 1` reduces both sides to `Term.weaken`
forms that `Term.weaken_HEq_congr` collapses. -/
theorem TermSubst.lift_precompose_pointwise
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ')
    (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.precompose (ρt.lift newType)
          (σt'.lift (newType.rename ρ)) i)
        ((TermSubst.precompose ρt σt').lift newType i) := by
  have h_rename_subst :
      (newType.rename ρ).subst σ' = newType.subst (Subst.precompose ρ σ') :=
    Ty.rename_subst_commute newType ρ σ'
  have h_ctx :
      Δ.cons ((newType.rename ρ).subst σ')
        = Δ.cons (newType.subst (Subst.precompose ρ σ')) :=
    congrArg Δ.cons h_rename_subst
  intro i
  match i with
  | ⟨0, _⟩ =>
    -- LHS: outer_witness_compose ▸ σt'.lift (newType.rename ρ) ((lift ρt newType) ⟨0, _⟩)
    -- (lift ρt newType) ⟨0, _⟩ = ⟨0, _⟩ definitionally; σt'.lift's 0 arm
    -- emits inner_cast.symm ▸ Term.var ⟨0, _⟩.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq h_ctx ⟨0, Nat.zero_lt_succ _⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS: outer_witness_compose ▸ σt'.lift (newType.rename ρ) (Fin.succ (ρ ⟨k, _⟩))
    --    = outer_witness_compose ▸ (inner_subst_weaken.symm ▸
    --        Term.weaken ((newType.rename ρ).subst σ') (σt' (ρ ⟨k, _⟩)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.weaken ((newType.rename ρ).subst σ') (σt' (ρ ⟨k, _⟩))
    -- RHS at k+1: outer ▸ Term.weaken (newType.subst (precompose ρ σ'))
    --                       ((precompose ρt σt') ⟨k, _⟩)
    -- where (precompose ρt σt') ⟨k, _⟩
    --     = (h_w.trans h_c) ▸ σt' (ρ ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.  The h_T equation chains
    -- `congrArg (·.subst σ') (ρt k')` (varType bridge from Γ' to Γ-renamed)
    -- with `Ty.rename_subst_commute` (rename-subst commute), matching the
    -- chain inside `TermSubst.precompose`'s definition.
    exact Term.weaken_HEq_congr
      h_rename_subst
      ((congrArg (·.subst σ')
          (ρt ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).trans
        (Ty.rename_subst_commute
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) ρ σ'))
      (σt' (ρ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (_)
      (eqRec_heq _ _).symm


end LeanFX.Syntax
