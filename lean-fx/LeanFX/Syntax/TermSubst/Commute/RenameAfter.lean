import LeanFX.Syntax.TermSubst.Rename

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-level `renameAfter` and its lift commute.

`TermSubst.renameAfter σt ρt` composes a subst with a downstream
rename, producing a subst along `Subst.renameAfter σ ρ`.  The
companion lemma `lift_renameAfter_pointwise` says lifting then
composing agrees with composing then lifting (pointwise HEq) —
the term-level analogue of `Subst.lift_renameAfter_commute`. -/

/-- Term-level `renameAfter`: subst σt then rename ρt to a downstream
context.  At each position, applies σt then renames the result via
ρt; the result type is bridged via `Ty.subst_rename_commute`. -/
def TermSubst.renameAfter
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ) :
    TermSubst Γ Δ' (Subst.renameAfter σ ρ) := fun i =>
  Ty.subst_rename_commute (varType Γ i) σ ρ ▸ Term.rename ρt (σt i)

/-- Lifting commutes with `renameAfter` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets, bridged by `heq_var_across_ctx_eq`
over `Ty.subst_rename_commute newType σ ρ`.  Position `k + 1`
reduces both sides to a `Term.weaken` of `Term.rename ρt (σt k)`
with propositionally-distinct `newType` and inner type — the v1.38
`rename_weaken_commute_HEq` collapses LHS to weaken-of-rename, then
`Term.weaken_HEq_congr` bridges the two `Term.weaken` shapes. -/
theorem TermSubst.lift_renameAfter_pointwise
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ)
    (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.renameAfter (σt.lift newType)
          (ρt.lift (newType.subst σ)) i)
        ((TermSubst.renameAfter σt ρt).lift newType i) := by
  -- Bridge the cons-extended target contexts at the type level.
  have h_subst_rename :
      (newType.subst σ).rename ρ = newType.subst (Subst.renameAfter σ ρ) :=
    Ty.subst_rename_commute newType σ ρ
  have h_ctx :
      Δ'.cons ((newType.subst σ).rename ρ)
        = Δ'.cons (newType.subst (Subst.renameAfter σ ρ)) :=
    congrArg Δ'.cons h_subst_rename
  intro i
  match i with
  | ⟨0, h0⟩ =>
    -- LHS reduces to: outer_cast ▸ rename (ρt.lift (newType.subst σ))
    --                              (inner_cast.symm ▸ Term.var ⟨0, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (ρt.lift (newType.subst σ))
        (Ty.subst_weaken_commute newType σ).symm
        (Term.var (context := Δ.cons (newType.subst σ))
          ⟨0, Nat.zero_lt_succ _⟩))
    -- Now: rename (ρt.lift (newType.subst σ)) (Term.var ⟨0, _⟩)
    --    = ((ρt.lift (newType.subst σ)) ⟨0, _⟩) ▸ Term.var (ρ.lift ⟨0, _⟩)
    --    where ρ.lift ⟨0, _⟩ = ⟨0, _⟩ definitionally.
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.var ⟨0, _⟩ in Δ'.cons ((newType.subst σ).rename ρ)
    -- Naked RHS: Term.var ⟨0, _⟩ in Δ'.cons (newType.subst (Subst.renameAfter σ ρ))
    apply HEq.trans
      (heq_var_across_ctx_eq h_ctx ⟨0, Nat.zero_lt_succ _⟩)
    -- RHS = (Ty.subst_weaken_commute newType (Subst.renameAfter σ ρ)).symm
    --        ▸ Term.var ⟨0, _⟩
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = outer_cast ▸ rename (ρt.lift X)
    --                        (inner_cast.symm ▸ Term.weaken X (σt k'))
    -- where X = newType.subst σ, k' = ⟨k, Nat.lt_of_succ_lt_succ hk⟩.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (ρt.lift (newType.subst σ))
        (Ty.subst_weaken_commute
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ).symm
        (Term.weaken (newType.subst σ)
          (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))
    -- Now: rename (ρt.lift X) (Term.weaken X (σt k'))
    --    ≃HEq≃ Term.weaken (X.rename ρ) (Term.rename ρt (σt k'))    [by v1.38]
    apply HEq.trans
      (Term.rename_weaken_commute_HEq ρt (newType.subst σ)
        (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    -- Now LHS = Term.weaken ((newType.subst σ).rename ρ)
    --             (Term.rename ρt (σt ⟨k, _⟩))
    -- in target context Δ'.cons ((newType.subst σ).rename ρ).
    --
    -- RHS at k+1 = outer_cast ▸ Term.weaken (newType.subst (renameAfter σ ρ))
    --                              ((renameAfter σt ρt) ⟨k, _⟩)
    --             where (renameAfter σt ρt) ⟨k, _⟩
    --                   = inner_cast ▸ Term.rename ρt (σt ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Now: HEq RHS_naked LHS_naked, where
    --   RHS_naked = Term.weaken (newType.subst (renameAfter σ ρ))
    --                 (inner_cast ▸ Term.rename ρt (σt ⟨k, _⟩))
    --   LHS_naked = Term.weaken ((newType.subst σ).rename ρ)
    --                 (Term.rename ρt (σt ⟨k, _⟩))
    -- Bridge via Term.weaken_HEq_congr.
    apply HEq.symm
    -- Use the cast-input helper to push the inner cast on RHS through
    -- Term.weaken — but actually Term.weaken_HEq_congr handles both
    -- newType differences AND a per-side type-cast difference, so we
    -- just supply the HEq.
    exact Term.weaken_HEq_congr
      h_subst_rename
      (Ty.subst_rename_commute
        (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ ρ)
      (Term.rename ρt (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (_)
      (eqRec_heq _ _).symm


end LeanFX.Syntax
