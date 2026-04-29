import LeanFX.Syntax.TermSubst.Commute

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `TermSubst.lift_compose_pointwise` (full theorem).

Lifting commutes with TermSubst composition pointwise (HEq).  Position 0
delegates to the existing `lift_compose_pointwise_zero` fragment.
Position `k + 1` is the substantive case:

  * LHS at `k+1`: `outer_subst_weaken_commute.symm ▸ Term.weaken
    (newType.subst (Subst.compose σ₁ σ₂)) (Ty.subst_compose ...
    ▸ Term.subst σt₂ (σt₁ k'))`.

  * RHS at `k+1`: `outer_subst_compose ▸ Term.subst (σt₂.lift
    (newType.subst σ₁)) ((Ty.subst_weaken_commute ...).symm ▸
    Term.weaken (newType.subst σ₁) (σt₁ k'))`.

The RHS inner reduces, via `Term.subst_HEq_cast_input` + v1.43
`Term.subst_weaken_commute_HEq`, to `Term.weaken ((newType.subst
σ₁).subst σ₂) (Term.subst σt₂ (σt₁ k'))`.  The two `Term.weaken`
forms differ only by `Ty.subst_compose newType σ₁ σ₂` on the
`newType` and the per-position analogue on the inner type;
`Term.weaken_HEq_congr` closes via `eqRec_heq`. -/
theorem TermSubst.lift_compose_pointwise
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty level scope₁) :
    ∀ (i : Fin (scope₁ + 1)),
      HEq
        (TermSubst.lift (TermSubst.compose σt₁ σt₂) newType i)
        (TermSubst.compose (σt₁.lift newType)
          (σt₂.lift (newType.subst σ₁)) i)
  | ⟨0, _⟩ =>
      TermSubst.lift_compose_pointwise_zero σt₁ σt₂ newType
  | ⟨k + 1, hk⟩ => by
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and strip outer cast on RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast on RHS through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (σt₂.lift (newType.subst σ₁))
        (Ty.subst_weaken_commute
          (varType Γ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₁).symm
        (Term.weaken (newType.subst σ₁)
          (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))
    -- After helper: Term.subst (σt₂.lift X) (Term.weaken X (σt₁ k')).
    -- Apply v1.43 to get Term.weaken (X.subst σ₂) (Term.subst σt₂ (σt₁ k')).
    apply HEq.trans
      (Term.subst_weaken_commute_HEq
        σt₂ (newType.subst σ₁)
        (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    -- Flip back to LHS-orientation.
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.
    exact Term.weaken_HEq_congr
      (Ty.subst_compose newType σ₁ σ₂).symm
      (Ty.subst_compose
        (varType Γ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₁ σ₂).symm
      _ _ (eqRec_heq _ _)

/-! ## `Term.subst_compose`.

The cap-stone of substitution functoriality at the term level:

  Term.subst σt₂ (Term.subst σt₁ t)
    ≃HEq≃
  Term.subst (TermSubst.compose σt₁ σt₂) t

Both sides have type `Term Γ₃ T'` for propositionally-equal `T'`s
(`((T.subst σ₁).subst σ₂)` vs `T.subst (Subst.compose σ₁ σ₂)`,
bridged by `Ty.subst_compose`).  HEq carries the difference.

12-case structural induction on the term.

  * Closed-context cases (var, unit/boolTrue/boolFalse, app, fst,
    boolElim) combine constructor HEq congruences with
    `Ty.subst_compose` at each Ty level index.
  * Cast-bearing cases (appPi/pair/snd) peel outer casts via
    `eqRec_heq` and push inner casts through
    `Term.subst_HEq_cast_input`.  The sigmaTy/piTy second-component
    bridge chains `Ty.subst_compose` at scope+1 with
    `Subst.lift_compose_equiv`.
  * Binder cases (lam, lamPi) recurse via the IH at lifted
    TermSubsts (`lift σt₁ dom` and `lift σt₂ (dom.subst σ₁)`),
    then bridge `compose (lift σt₁) (lift σt₂)` against
    `lift (compose σt₁ σt₂)` via `Term.subst_HEq_pointwise` (v1.24)
    over `TermSubst.lift_compose_pointwise` (v1.44).

Mirrors v1.40 / v1.42 with subst on both sides instead of mixed
subst+rename. -/
theorem Term.subst_compose_HEq
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂) :
    {T : Ty level scope₁} → (t : Term Γ₁ T) →
      HEq (Term.subst σt₂ (Term.subst σt₁ t))
          (Term.subst (TermSubst.compose σt₁ σt₂) t)
  | _, .var i => by
    -- LHS: Term.subst σt₂ (σt₁ i).
    -- RHS: (compose σt₁ σt₂) i = (Ty.subst_compose ...) ▸ Term.subst σt₂ (σt₁ i).
    show HEq (Term.subst σt₂ (σt₁ i))
      ((Ty.subst_compose (varType Γ₁ i) σ₁ σ₂)
        ▸ Term.subst σt₂ (σt₁ i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst σt₂ (Term.subst σt₁ f))
                (Term.subst σt₂ (Term.subst σt₁ a)))
      (Term.app (Term.subst (TermSubst.compose σt₁ σt₂) f)
                (Term.subst (TermSubst.compose σt₁ σt₂) a))
    exact Term.app_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      (Ty.subst_compose cod σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ f)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst σt₂ (Term.subst σt₁ p)))
      (Term.fst (Term.subst (TermSubst.compose σt₁ σt₂) p))
    apply Term.fst_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
    exact Term.subst_compose_HEq σt₁ σt₂ p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst σt₂ (Term.subst σt₁ s))
                     (Term.subst σt₂ (Term.subst σt₁ t))
                     (Term.subst σt₂ (Term.subst σt₁ e)))
      (Term.boolElim (Term.subst (TermSubst.compose σt₁ σt₂) s)
                     (Term.subst (TermSubst.compose σt₁ σt₂) t)
                     (Term.subst (TermSubst.compose σt₁ σt₂) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ s))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ t)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute cod dom σ₁).symm
        (Term.appPi (Term.subst σt₁ f) (Term.subst σt₁ a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      ((Ty.subst_compose cod σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) cod))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ f)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute second first σ₁)
        (Term.subst σt₁ w))
    apply HEq.trans (Term.subst_compose_HEq σt₁ σt₂ w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute second first σ₁).symm
        (Term.snd (Term.subst σt₁ p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      (Ty.subst_compose cod σ₁ σ₂)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift σt₂ (dom.subst σ₁))
        (Ty.subst_weaken_commute cod σ₁)
        (Term.subst (TermSubst.lift σt₁ dom) body))
    -- IH on body with the lifts.
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁))
        body)
    -- Bridge compose-of-lifts to lift-of-compose.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Γ₃.cons (Ty.subst_compose dom σ₁ σ₂))
      (TermSubst.compose
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁)))
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) dom)
      (Subst.lift_compose_equiv σ₁ σ₂)
      (fun i =>
        (TermSubst.lift_compose_pointwise σt₁ σt₂ dom i).symm)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      ((Ty.subst_compose cod σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) cod))
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Γ₃.cons (Ty.subst_compose dom σ₁ σ₂))
      (TermSubst.compose
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁)))
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) dom)
      (Subst.lift_compose_equiv σ₁ σ₂)
      (fun i =>
        (TermSubst.lift_compose_pointwise σt₁ σt₂ dom i).symm)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_compose_HEq σt₁ σt₂ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst σt₂ (Term.subst σt₁ scrutinee))
        (Term.subst σt₂ (Term.subst σt₁ zeroBranch))
        (Term.subst σt₂ (Term.subst σt₁ succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.compose σt₁ σt₂) scrutinee)
        (Term.subst (TermSubst.compose σt₁ σt₂) zeroBranch)
        (Term.subst (TermSubst.compose σt₁ σt₂) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ scrutinee))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ zeroBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ scrutinee))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ zeroBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_compose elem σ₁ σ₂)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ hd)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ nilBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_compose elem σ₁ σ₂)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ noneBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ leftBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.subst_compose carrier σ₁ σ₂)
      (RawTerm.subst_compose rawTerm σ₁.forRaw σ₂.forRaw)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_compose carrier σ₁ σ₂)
      (RawTerm.subst_compose leftEnd σ₁.forRaw σ₂.forRaw)
      (RawTerm.subst_compose rightEnd σ₁.forRaw σ₂.forRaw)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ baseCase)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ witness)

/-- The explicit-`▸` form of `Term.subst_compose`: `eq_of_heq` plus
the outer cast strip.  Mirrors the v1.25 derivation of `Term.subst_id`
from `Term.subst_id_HEq`. -/
theorem Term.subst_compose
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    {T : Ty level scope₁} (t : Term Γ₁ T) :
    Term.subst σt₂ (Term.subst σt₁ t)
      = (Ty.subst_compose T σ₁ σ₂).symm
          ▸ Term.subst (TermSubst.compose σt₁ σt₂) t :=
  eq_of_heq
    ((Term.subst_compose_HEq σt₁ σt₂ t).trans (eqRec_heq _ _).symm)


end LeanFX.Syntax
