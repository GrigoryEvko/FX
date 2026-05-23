import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose

/-! # LeanFX2.Term.PrecomposeLiftEntryHEq  (strength-T8 binder entry lemma)

The binder arms (`lam` / `lamPi` / `pathLam`) of `Term.rename_subst_commute`
push both operands under the bound variable and then must bridge

  `TermSubst.precomposeRenaming (termRenaming.lift _) (termSubst.lift _)`

against

  `(TermSubst.precomposeRenaming termRenaming termSubst).lift _`.

The two typed substitutions are over different-but-pointwise-equal underlying
`Subst`s (`Subst.precomposeRenaming rho.lift sigma.lift` vs
`(Subst.precomposeRenaming rho sigma).lift`) AND live in
propositionally-but-not-definitionally-equal target contexts (their cons-heads
differ by `Ty.rename_subst_commute rho sigma domainType`).  This file supplies
the per-position heterogeneous entry equality between them; the binder arm then
casts the second onto the first's target context (via
`Term.subst_targetCtx_cast_HEq`) and runs the cross-sigma
`Term.subst_pointwise_HEq` bridge on the body.

Pure HEq.trans chains over the two cast helpers — NO `funext`, NO `simp`,
no `unfold` in a case split: axiom-clean under the strict gate. -/

namespace LeanFX2

/-- Lifting a typed substitution commutes with precomposing it by a typed
renaming, at every position, up to heterogeneous equality.

This is the variable-entry core: `(termSubst.lift _) ∘ rho.lift` agrees with
`(precompose termRenaming termSubst).lift` on each de Bruijn position. -/
theorem TermSubst.lift_precompose_entry_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma)
    (domainType : Ty level sourceScope) :
    ∀ position,
      HEq
        ((termSubst.lift (domainType.rename rho)) (rho.lift position))
        (((TermSubst.precomposeRenaming termRenaming termSubst).lift
            domainType) position)
  | ⟨0, _⟩ =>
      -- Both sides are the cast fresh variable; peel the two `weaken_subst`
      -- casts and bridge the differing cons-head via `var_zero_cons_type_eq_heq`.
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.weaken_subst_commute sigma (domainType.rename rho)))
        (HEq.trans
          (Term.var_zero_cons_type_eq_heq
            (Ty.rename_subst_commute rho sigma domainType))
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute (Subst.precomposeRenaming rho sigma)
              domainType)).symm)
  | ⟨k + 1, h⟩ =>
      -- Both sides are the cast weakening of the underlying entry.  Peel the
      -- two `weaken_subst` casts, bridge the differing weaken-head type, then
      -- bridge `termSubst (rho k)` to the precomposed entry.
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.weaken_subst_commute sigma
            (varType middleCtx (rho ⟨k, Nat.lt_of_succ_lt_succ h⟩))))
        (HEq.trans
          (HEq.trans
            (Term.weaken_head_type_eq_heq
              (Ty.rename_subst_commute rho sigma domainType)
              (termSubst (rho ⟨k, Nat.lt_of_succ_lt_succ h⟩)))
            (Term.weaken_heq_of_eq
              (domainType.subst (Subst.precomposeRenaming rho sigma))
              (by
                show (varType middleCtx (rho ⟨k, Nat.lt_of_succ_lt_succ h⟩)).subst
                    sigma =
                  (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩).subst
                    (Subst.precomposeRenaming rho sigma)
                rw [termRenaming ⟨k, Nat.lt_of_succ_lt_succ h⟩]
                exact Ty.rename_subst_commute rho sigma
                  (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))
              rfl
              (HEq.symm
                (TermSubst.precomposeRenaming_position_HEq termRenaming
                  termSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩))))
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute (Subst.precomposeRenaming rho sigma)
              (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))).symm)

/-- Full binder entry equality consumed by the `lam` / `lamPi` / `pathLam`
arms of `Term.rename_subst_commute`: the lift of the precomposition equals the
precomposition of the lifts, heterogeneously, at every position. -/
theorem TermSubst.precomposeRenaming_lift_entry_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope middleScope}
    {sigma : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceCtx middleCtx rho)
    (termSubst : TermSubst middleCtx targetCtx sigma)
    (domainType : Ty level sourceScope)
    (position : Fin (sourceScope + 1)) :
    HEq
      ((TermSubst.precomposeRenaming (termRenaming.lift domainType)
          (termSubst.lift (domainType.rename rho))) position)
      (((TermSubst.precomposeRenaming termRenaming termSubst).lift
          domainType) position) :=
  HEq.trans
    (TermSubst.precomposeRenaming_position_HEq (termRenaming.lift domainType)
      (termSubst.lift (domainType.rename rho)) position)
    (TermSubst.lift_precompose_entry_HEq termRenaming termSubst domainType
      position)

end LeanFX2
