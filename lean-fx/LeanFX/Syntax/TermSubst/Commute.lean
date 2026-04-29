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

/-! ## `Term.subst_rename_commute_HEq`.

Term-level analogue of `Ty.subst_rename_commute`:

  Term.rename ρt (Term.subst σt t)
    ≃HEq≃
  Term.subst (TermSubst.renameAfter σt ρt) t

12-case structural induction on the term.  Closed-context cases
combine the constructor HEq congruence (v1.21) with
`Ty.subst_rename_commute` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) peel outer casts via `eqRec_heq` and push inner
casts through `Term.{rename,subst}_HEq_cast_input` (v1.26 / v1.37).
Binder cases (lam/lamPi) use the IH at lifted TermSubst/TermRenaming,
then bridge `renameAfter (lift σt dom) (lift ρt (dom.subst σ))`
against `lift (renameAfter σt ρt) dom` via `Term.subst_HEq_pointwise`
(v1.24) over `TermSubst.lift_renameAfter_pointwise` (v1.39). -/
theorem Term.subst_rename_commute_HEq
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename ρt (Term.subst σt t))
          (Term.subst (TermSubst.renameAfter σt ρt) t)
  | _, .var i => by
    -- LHS: Term.rename ρt (σt i)
    -- RHS: (renameAfter σt ρt) i = (Ty.subst_rename_commute _ σ ρ) ▸ Term.rename ρt (σt i)
    show HEq (Term.rename ρt (σt i))
             ((Ty.subst_rename_commute (varType Γ i) σ ρ) ▸
                Term.rename ρt (σt i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename ρt (Term.subst σt f))
                (Term.rename ρt (Term.subst σt a)))
      (Term.app (Term.subst (TermSubst.renameAfter σt ρt) f)
                (Term.subst (TermSubst.renameAfter σt ρt) a))
    exact Term.app_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      (Ty.subst_rename_commute cod σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt f)
      _ _ (Term.subst_rename_commute_HEq σt ρt a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename ρt (Term.subst σt p)))
      (Term.fst (Term.subst (TermSubst.renameAfter σt ρt) p))
    apply Term.fst_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
    exact Term.subst_rename_commute_HEq σt ρt p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename ρt (Term.subst σt s))
                     (Term.rename ρt (Term.subst σt t))
                     (Term.rename ρt (Term.subst σt e)))
      (Term.boolElim (Term.subst (TermSubst.renameAfter σt ρt) s)
                     (Term.subst (TermSubst.renameAfter σt ρt) t)
                     (Term.subst (TermSubst.renameAfter σt ρt) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt s))
      _ _ (Term.subst_rename_commute_HEq σt ρt t)
      _ _ (Term.subst_rename_commute_HEq σt ρt e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.rename ρt (cast_subst.symm ▸ Term.appPi (subst f) (subst a))
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute cod dom σ).symm
        (Term.appPi (Term.subst σt f) (Term.subst σt a)))
    -- After helper: rename ρt (Term.appPi ...)
    -- Strip outer cast from rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- RHS side: (renameAfter σt ρt) on Term.appPi emits cast.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      ((Ty.subst_rename_commute cod σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) cod))
      _ _ (Term.subst_rename_commute_HEq σt ρt f)
      _ _ (Term.subst_rename_commute_HEq σt ρt a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
    -- LHS secondVal: cast_outer_LHS ▸ rename ρt (cast_inner_LHS ▸ subst σt w)
    -- RHS secondVal: cast_compose ▸ subst (renameAfter σt ρt) w
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute second first σ)
        (Term.subst σt w))
    apply HEq.trans (Term.subst_rename_commute_HEq σt ρt w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute second first σ).symm
        (Term.snd (Term.subst σt p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
      _ _ (Term.subst_rename_commute_HEq σt ρt p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body lives at scope+1; double-traversed via lift σt then lift ρt.
    -- RHS body uses lift (renameAfter σt ρt) dom, pointwise HEq to
    -- renameAfter (lift σt dom) (lift ρt (dom.subst σ)) via v1.39.
    apply Term.lam_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      (Ty.subst_rename_commute cod σ ρ)
    -- Strip outer cast on LHS (rename's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift ρt (dom.subst σ)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift ρt (dom.subst σ))
        (Ty.subst_weaken_commute cod σ)
        (Term.subst (TermSubst.lift σt dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ))
        body)
    -- Now LHS_naked = Term.subst (renameAfter (lift σt dom)
    --                              (lift ρt (dom.subst σ))) body
    -- Bridge to RHS_naked = Term.subst (lift (renameAfter σt ρt) dom) body
    -- via subst_HEq_pointwise + v1.39.
    apply HEq.symm
    -- Strip outer cast on RHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Δ'.cons (Ty.subst_rename_commute dom σ ρ))
      (TermSubst.renameAfter
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ)))
      ((TermSubst.renameAfter σt ρt).lift dom)
      (Subst.lift_renameAfter_commute σ ρ)
      (TermSubst.lift_renameAfter_pointwise σt ρt dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      ((Ty.subst_rename_commute cod σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) cod))
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Δ'.cons (Ty.subst_rename_commute dom σ ρ))
      (TermSubst.renameAfter
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ)))
      ((TermSubst.renameAfter σt ρt).lift dom)
      (Subst.lift_renameAfter_commute σ ρ)
      (TermSubst.lift_renameAfter_pointwise σt ρt dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_rename_commute_HEq σt ρt pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename ρt (Term.subst σt scrutinee))
        (Term.rename ρt (Term.subst σt zeroBranch))
        (Term.rename ρt (Term.subst σt succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.renameAfter σt ρt) scrutinee)
        (Term.subst (TermSubst.renameAfter σt ρt) zeroBranch)
        (Term.subst (TermSubst.renameAfter σt ρt) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt scrutinee))
      _ _ (Term.subst_rename_commute_HEq σt ρt zeroBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt scrutinee))
      _ _ (Term.subst_rename_commute_HEq σt ρt zeroBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_rename_commute elem σ ρ)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt hd)
      _ _ (Term.subst_rename_commute_HEq σt ρt tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt nilBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_rename_commute elem σ ρ)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt noneBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt leftBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.subst_rename_commute carrier σ ρ)
      (RawTerm.rename_subst_commute rawTerm σ.forRaw ρ)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_rename_commute carrier σ ρ)
      (RawTerm.rename_subst_commute leftEnd σ.forRaw ρ)
      (RawTerm.rename_subst_commute rightEnd σ.forRaw ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt baseCase)
      _ _ (Term.subst_rename_commute_HEq σt ρt witness)

/-! ## `Term.rename_subst_commute_HEq`.

Term-level analogue of `Ty.rename_subst_commute`:

  Term.subst σt' (Term.rename ρt t)
    ≃HEq≃
  Term.subst (TermSubst.precompose ρt σt') t

Mirrors v1.40 (subst-rename commute) with rename and subst swapped.
12-case structural induction with constructor HEq congruences for
the closed-context cases, outer-cast strips + inner-cast pushes
for the cast-bearing cases, and `Term.subst_HEq_pointwise` over
`TermSubst.lift_precompose_pointwise` (v1.41) for the binder
cases. -/
theorem Term.rename_subst_commute_HEq
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ') :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst σt' (Term.rename ρt t))
          (Term.subst (TermSubst.precompose ρt σt') t)
  | _, .var i => by
    -- LHS: Term.subst σt' ((ρt i) ▸ Term.var (ρ i)).
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input σt' (ρt i)
        (Term.var (context := Γ') (ρ i)))
    -- LHS reduces to σt' (ρ i); RHS = (precompose ρt σt') i,
    -- which by precompose's definition is `chain ▸ σt' (ρ i)`.
    -- Stage the chained equation via `have` so Lean β-reduces the
    -- congrArg-on-lambda before checking the ▸ type alignment.
    have h_witness : (varType Γ' (ρ i)).subst σ'
                       = ((varType Γ i).rename ρ).subst σ' :=
      congrArg (fun T : Ty level scope_m => T.subst σ') (ρt i)
    have h_chain : (varType Γ' (ρ i)).subst σ'
                     = (varType Γ i).subst (Subst.precompose ρ σ') :=
      h_witness.trans
        (Ty.rename_subst_commute (varType Γ i) ρ σ')
    show HEq (σt' (ρ i)) (h_chain ▸ σt' (ρ i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst σt' (Term.rename ρt f))
                (Term.subst σt' (Term.rename ρt a)))
      (Term.app (Term.subst (TermSubst.precompose ρt σt') f)
                (Term.subst (TermSubst.precompose ρt σt') a))
    exact Term.app_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      (Ty.rename_subst_commute cod ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' f)
      _ _ (Term.rename_subst_commute_HEq ρt σt' a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst σt' (Term.rename ρt p)))
      (Term.fst (Term.subst (TermSubst.precompose ρt σt') p))
    apply Term.fst_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
    exact Term.rename_subst_commute_HEq ρt σt' p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst σt' (Term.rename ρt s))
                     (Term.subst σt' (Term.rename ρt t))
                     (Term.subst σt' (Term.rename ρt e)))
      (Term.boolElim (Term.subst (TermSubst.precompose ρt σt') s)
                     (Term.subst (TermSubst.precompose ρt σt') t)
                     (Term.subst (TermSubst.precompose ρt σt') e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' s))
      _ _ (Term.rename_subst_commute_HEq ρt σt' t)
      _ _ (Term.rename_subst_commute_HEq ρt σt' e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.subst σt' (cast_rename.symm ▸ Term.appPi (rename f) (rename a))
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute cod dom ρ).symm
        (Term.appPi (Term.rename ρt f) (Term.rename ρt a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      ((Ty.rename_subst_commute cod ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') cod))
      _ _ (Term.rename_subst_commute_HEq ρt σt' f)
      _ _ (Term.rename_subst_commute_HEq ρt σt' a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
    -- LHS secondVal: cast_outer_LHS ▸ subst σt' (cast_inner_LHS ▸ rename ρt w)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute second first ρ)
        (Term.rename ρt w))
    apply HEq.trans (Term.rename_subst_commute_HEq ρt σt' w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute second first ρ).symm
        (Term.snd (Term.rename ρt p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
      _ _ (Term.rename_subst_commute_HEq ρt σt' p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      (Ty.rename_subst_commute cod ρ σ')
    -- Strip outer cast on LHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through subst (lift σt' (dom.rename ρ)).
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift σt' (dom.rename ρ))
        (Ty.rename_weaken_commute cod ρ)
        (Term.rename (TermRenaming.lift ρt dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ))
        body)
    -- Bridge via subst_HEq_pointwise + v1.41.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Δ.cons (Ty.rename_subst_commute dom ρ σ'))
      (TermSubst.precompose
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ)))
      ((TermSubst.precompose ρt σt').lift dom)
      (Subst.lift_precompose_commute ρ σ')
      (TermSubst.lift_precompose_pointwise ρt σt' dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      ((Ty.rename_subst_commute cod ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') cod))
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Δ.cons (Ty.rename_subst_commute dom ρ σ'))
      (TermSubst.precompose
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ)))
      ((TermSubst.precompose ρt σt').lift dom)
      (Subst.lift_precompose_commute ρ σ')
      (TermSubst.lift_precompose_pointwise ρt σt' dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_subst_commute_HEq ρt σt' pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst σt' (Term.rename ρt scrutinee))
        (Term.subst σt' (Term.rename ρt zeroBranch))
        (Term.subst σt' (Term.rename ρt succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.precompose ρt σt') scrutinee)
        (Term.subst (TermSubst.precompose ρt σt') zeroBranch)
        (Term.subst (TermSubst.precompose ρt σt') succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' scrutinee))
      _ _ (Term.rename_subst_commute_HEq ρt σt' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' scrutinee))
      _ _ (Term.rename_subst_commute_HEq ρt σt' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_subst_commute elem ρ σ')
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' hd)
      _ _ (Term.rename_subst_commute_HEq ρt σt' tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' nilBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_subst_commute elem ρ σ')
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' noneBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' leftBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_subst_commute carrier ρ σ')
      (RawTerm.subst_rename_commute rawTerm ρ σ'.forRaw)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_subst_commute carrier ρ σ')
      (RawTerm.subst_rename_commute leftEnd ρ σ'.forRaw)
      (RawTerm.subst_rename_commute rightEnd ρ σ'.forRaw)
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' baseCase)
      _ _ (Term.rename_subst_commute_HEq ρt σt' witness)

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
