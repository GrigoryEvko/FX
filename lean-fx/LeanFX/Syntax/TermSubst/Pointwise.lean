import LeanFX.Syntax.TermSubst.HEqCongr

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `TermSubst.lift_HEq_pointwise`.

Pointwise HEq for the lifts of two TermSubsts that are pointwise HEq
themselves (and whose underlying Substs are pointwise equal).  Used
by the binder cases of `Term.subst_HEq_pointwise` to extend the
hypothesis under each new binder. -/
theorem TermSubst.lift_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ₁ σ₂ : Subst level scope scope'}
    (σt₁ : TermSubst Γ Δ σ₁) (σt₂ : TermSubst Γ Δ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i))
    (newType : Ty level scope) :
    ∀ i, HEq (TermSubst.lift σt₁ newType i)
             (TermSubst.lift σt₂ newType i) := by
  -- Bridging fact: newType.subst σ₁ = newType.subst σ₂.
  have h_new : newType.subst σ₁ = newType.subst σ₂ :=
    Ty.subst_congr h_subst newType
  intro i
  match i with
  | ⟨0, _⟩ =>
    -- LHS = (Ty.subst_weaken_commute newType σ₁).symm ▸
    --        Term.var (context := Δ.cons (newType.subst σ₁)) ⟨0, _⟩
    -- RHS = (Ty.subst_weaken_commute newType σ₂).symm ▸
    --        Term.var (context := Δ.cons (newType.subst σ₂)) ⟨0, _⟩
    -- Strip outer casts on both sides via eqRec_heq, bridge naked
    -- Term.var values via heq_var_across_ctx_eq + congrArg-cons.
    -- Note: Term.var lives at scope' + 1, so the Fin uses
    -- Nat.zero_lt_succ scope' (NOT the Fin destructure's h0 which
    -- is at scope + 1).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq (congrArg (Δ.cons) h_new)
        ⟨0, Nat.zero_lt_succ scope'⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) σ₁).symm ▸
    --        Term.weaken (newType.subst σ₁) (σt₁ ⟨k, _⟩)
    -- RHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) σ₂).symm ▸
    --        Term.weaken (newType.subst σ₂) (σt₂ ⟨k, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.weaken (newType.subst σ₂)
        (σt₂ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    · exact Term.weaken_HEq_congr h_new
        (Ty.subst_congr h_subst
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
        (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (σt₂ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (h_pointwise ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
    · exact (eqRec_heq _ _).symm

/-! ## `Term.subst_HEq_pointwise`.

Substitution respects pointwise HEq of TermSubsts.  The `h_ctx :
Δ₁ = Δ₂` parameter accommodates binder-case recursive calls where
`TermSubst.lift σt_i dom` lands in `Δ.cons (dom.subst σ_i)` —
same scope, different concrete contexts. -/
theorem Term.subst_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ₁ Δ₂ : Ctx m level scope'}
    (h_ctx : Δ₁ = Δ₂)
    {σ₁ σ₂ : Subst level scope scope'}
    (σt₁ : TermSubst Γ Δ₁ σ₁) (σt₂ : TermSubst Γ Δ₂ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i)) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst σt₁ t) (Term.subst σt₂ t)
  | _, .var i => h_pointwise i
  | _, .unit => by term_context_refl
  | _, .app (domainType := T₁) (codomainType := T₂) f a => by
    cases h_ctx
    show HEq (Term.app (Term.subst σt₁ f) (Term.subst σt₁ a))
             (Term.app (Term.subst σt₂ f) (Term.subst σt₂ a))
    exact Term.app_HEq_congr
      (Ty.subst_congr h_subst T₁) (Ty.subst_congr h_subst T₂)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise f)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise a)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lam (codomainType := cod.subst σ₁)
        ((Ty.subst_weaken_commute cod σ₁) ▸
          (Term.subst (TermSubst.lift σt₁ dom) body)))
      (Term.lam (codomainType := cod.subst σ₂)
        ((Ty.subst_weaken_commute cod σ₂) ▸
          (Term.subst (TermSubst.lift σt₂ dom) body)))
    apply Term.lam_HEq_congr
      (Ty.subst_congr h_subst dom) (Ty.subst_congr h_subst cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Δ₁.cons (Ty.subst_congr h_subst dom))
        (TermSubst.lift σt₁ dom) (TermSubst.lift σt₂ dom)
        (Subst.lift_equiv h_subst)
        (TermSubst.lift_HEq_pointwise σt₁ σt₂ h_subst h_pointwise dom)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift σt₁ dom) body))
      (Term.lamPi (Term.subst (TermSubst.lift σt₂ dom) body))
    apply Term.lamPi_HEq_congr
      (Ty.subst_congr h_subst dom)
      (Ty.subst_congr (Subst.lift_equiv h_subst) cod)
    exact Term.subst_HEq_pointwise
      (congrArg Δ₁.cons (Ty.subst_congr h_subst dom))
      (TermSubst.lift σt₁ dom) (TermSubst.lift σt₂ dom)
      (Subst.lift_equiv h_subst)
      (TermSubst.lift_HEq_pointwise σt₁ σt₂ h_subst h_pointwise dom)
      body
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    cases h_ctx
    show HEq
      ((Ty.subst0_subst_commute cod dom σ₁).symm ▸
        Term.appPi (Term.subst σt₁ f) (Term.subst σt₁ a))
      ((Ty.subst0_subst_commute cod dom σ₂).symm ▸
        Term.appPi (Term.subst σt₂ f) (Term.subst σt₂ a))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.subst σt₂ f) (Term.subst σt₂ a))
    · exact Term.appPi_HEq_congr
        (Ty.subst_congr h_subst dom)
        (Ty.subst_congr (Subst.lift_equiv h_subst) cod)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise f)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise a)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := first) (secondType := second) v w => by
    cases h_ctx
    show HEq
      (Term.pair (Term.subst σt₁ v)
        ((Ty.subst0_subst_commute second first σ₁) ▸ (Term.subst σt₁ w)))
      (Term.pair (Term.subst σt₂ v)
        ((Ty.subst0_subst_commute second first σ₂) ▸ (Term.subst σt₂ w)))
    apply Term.pair_HEq_congr
      (Ty.subst_congr h_subst first)
      (Ty.subst_congr (Subst.lift_equiv h_subst) second)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise w)
    exact (eqRec_heq _ _).symm
  | _, .fst (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq (Term.fst (Term.subst σt₁ p)) (Term.fst (Term.subst σt₂ p))
    exact Term.fst_HEq_congr
      (Ty.subst_congr h_subst first)
      (Ty.subst_congr (Subst.lift_equiv h_subst) second)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise p)
  | _, .snd (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      ((Ty.subst0_subst_commute second first σ₁).symm ▸
        Term.snd (Term.subst σt₁ p))
      ((Ty.subst0_subst_commute second first σ₂).symm ▸
        Term.snd (Term.subst σt₂ p))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.subst σt₂ p))
    · exact Term.snd_HEq_congr
        (Ty.subst_congr h_subst first)
        (Ty.subst_congr (Subst.lift_equiv h_subst) second)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise p)
    · exact (eqRec_heq _ _).symm
  | _, .boolTrue => by term_context_refl
  | _, .boolFalse => by term_context_refl
  | _, .boolElim (resultType := result) s t e => by
    cases h_ctx
    show HEq
      (Term.boolElim (Term.subst σt₁ s) (Term.subst σt₁ t) (Term.subst σt₁ e))
      (Term.boolElim (Term.subst σt₂ s) (Term.subst σt₂ t) (Term.subst σt₂ e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise s))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise t)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise e)
  | _, .natZero => by term_context_refl
  | _, .natSucc pred => by
    cases h_ctx
    show HEq (Term.natSucc (Term.subst σt₁ pred))
             (Term.natSucc (Term.subst σt₂ pred))
    exact Term.natSucc_HEq_congr _ _
      (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    show HEq
      (Term.natElim (Term.subst σt₁ scrutinee)
                    (Term.subst σt₁ zeroBranch)
                    (Term.subst σt₁ succBranch))
      (Term.natElim (Term.subst σt₂ scrutinee)
                    (Term.subst σt₂ zeroBranch)
                    (Term.subst σt₂ succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    exact Term.natRec_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise succBranch)
  | _, .listNil (elementType := elem) => by
    cases h_ctx
    exact Term.listNil_HEq_congr (Ty.subst_congr h_subst elem)
  | _, .listCons (elementType := elem) hd tl => by
    cases h_ctx
    show HEq (Term.listCons (Term.subst σt₁ hd) (Term.subst σt₁ tl))
             (Term.listCons (Term.subst σt₂ hd) (Term.subst σt₂ tl))
    exact Term.listCons_HEq_congr
      (Ty.subst_congr h_subst elem)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise hd)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch => by
    cases h_ctx
    show HEq
      (Term.listElim (Term.subst σt₁ scrutinee)
                     (Term.subst σt₁ nilBranch)
                     (Term.subst σt₁ consBranch))
      (Term.listElim (Term.subst σt₂ scrutinee)
                     (Term.subst σt₂ nilBranch)
                     (Term.subst σt₂ consBranch))
    exact Term.listElim_HEq_congr
      (Ty.subst_congr h_subst elem)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise nilBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise consBranch)
  | _, .optionNone (elementType := elem) => by
    cases h_ctx
    exact Term.optionNone_HEq_congr (Ty.subst_congr h_subst elem)
  | _, .optionSome (elementType := elem) v => by
    cases h_ctx
    show HEq (Term.optionSome (Term.subst σt₁ v))
             (Term.optionSome (Term.subst σt₂ v))
    exact Term.optionSome_HEq_congr
      (Ty.subst_congr h_subst elem)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch => by
    cases h_ctx
    show HEq
      (Term.optionMatch (Term.subst σt₁ scrutinee)
                        (Term.subst σt₁ noneBranch)
                        (Term.subst σt₁ someBranch))
      (Term.optionMatch (Term.subst σt₂ scrutinee)
                        (Term.subst σt₂ noneBranch)
                        (Term.subst σt₂ someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.subst_congr h_subst elem)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise noneBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInl_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInr_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch => by
    cases h_ctx
    exact Term.eitherMatch_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise leftBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise rightBranch)
  | _, .refl (carrier := carrier) rawTerm => by
    cases h_ctx
    exact Term.refl_HEq_congr
      (Ty.subst_congr h_subst carrier)
      (RawTerm.subst_congr (Subst.equiv_forRaw h_subst) rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness => by
    cases h_ctx
    exact Term.idJ_HEq_congr
      (Ty.subst_congr h_subst carrier)
      (RawTerm.subst_congr (Subst.equiv_forRaw h_subst) leftEnd)
      (RawTerm.subst_congr (Subst.equiv_forRaw h_subst) rightEnd)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise baseCase)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise witness)

/-! ## `Term.subst_id_HEq`.

Full HEq form of subst-by-identity.  Structural induction; binder
cases use `Term.subst_HEq_pointwise` to bridge
`TermSubst.lift (TermSubst.identity Γ)` to
`TermSubst.identity (Γ.cons _)` via `lift_identity_pointwise`. -/
theorem Term.subst_id_HEq {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst (TermSubst.identity Γ) t) t
  | _, .var i => Term.subst_id_HEq_var i
  | _, .unit => Term.subst_id_HEq_unit
  | _, .app f a =>
    Term.subst_id_HEq_app f a
      (Term.subst_id_HEq f) (Term.subst_id_HEq a)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lam (codomainType := cod.subst Subst.identity)
        ((Ty.subst_weaken_commute cod Subst.identity) ▸
          (Term.subst (TermSubst.lift (TermSubst.identity Γ) dom) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr (Ty.subst_id dom) (Ty.subst_id cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Γ.cons (Ty.subst_id dom))
        (TermSubst.lift (TermSubst.identity Γ) dom)
        (TermSubst.identity (Γ.cons dom))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise Γ dom)
        body)
    exact Term.subst_id_HEq body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift (TermSubst.identity Γ) dom) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr (Ty.subst_id dom)
      ((Ty.subst_congr Subst.lift_identity_equiv cod).trans
       (Ty.subst_id cod))
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Γ.cons (Ty.subst_id dom))
        (TermSubst.lift (TermSubst.identity Γ) dom)
        (TermSubst.identity (Γ.cons dom))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise Γ dom)
        body)
    exact Term.subst_id_HEq body
  | _, .appPi f a =>
    Term.subst_id_HEq_appPi f a
      (Term.subst_id_HEq f) (Term.subst_id_HEq a)
  | _, .pair v w =>
    Term.subst_id_HEq_pair v w
      (Term.subst_id_HEq v) (Term.subst_id_HEq w)
  | _, .fst p =>
    Term.subst_id_HEq_fst p (Term.subst_id_HEq p)
  | _, .snd p =>
    Term.subst_id_HEq_snd p (Term.subst_id_HEq p)
  | _, .boolTrue => Term.subst_id_HEq_boolTrue
  | _, .boolFalse => Term.subst_id_HEq_boolFalse
  | _, .boolElim s t e =>
    Term.subst_id_HEq_boolElim s t e
      (Term.subst_id_HEq s) (Term.subst_id_HEq t) (Term.subst_id_HEq e)
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_id_HEq pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim (Term.subst (TermSubst.identity Γ) scrutinee)
                    (Term.subst (TermSubst.identity Γ) zeroBranch)
                    (Term.subst (TermSubst.identity Γ) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.subst_id result)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_id result)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_id elem)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_id elem)
      _ _ (Term.subst_id_HEq hd)
      _ _ (Term.subst_id_HEq tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_id elem) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq nilBranch)
      _ _ (Term.subst_id_HEq consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_id elem)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_id elem)
      _ _ (Term.subst_id_HEq v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_id elem) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq noneBranch)
      _ _ (Term.subst_id_HEq someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT)
      _ _ (Term.subst_id_HEq v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT)
      _ _ (Term.subst_id_HEq v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq leftBranch)
      _ _ (Term.subst_id_HEq rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr (Ty.subst_id carrier) (RawTerm.subst_id rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_id carrier) (RawTerm.subst_id leftEnd) (RawTerm.subst_id rightEnd)
      (Ty.subst_id result)
      _ _ (Term.subst_id_HEq baseCase)
      _ _ (Term.subst_id_HEq witness)

/-! ## `Term.subst_id` (explicit-`▸` form).

Corollary of `Term.subst_id_HEq` + `eqRec_heq`. -/
theorem Term.subst_id {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T : Ty level scope} (t : Term Γ T) :
    (Ty.subst_id T) ▸ Term.subst (TermSubst.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.subst_id_HEq t))

/-! ## Cast-through-Term.subst HEq helper.

Pushes a type-cast on the input out through `Term.subst` so the
substitution's structural recursion can fire on the bare
constructor.  Bridge for `lift_compose_pointwise_zero` and the
cast-bearing closed-context commute cases. -/
theorem Term.subst_HEq_cast_input
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ)
    {T₁ T₂ : Ty level scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.subst σt (h ▸ t)) (Term.subst σt t) := by
  cases h
  rfl

/-! ## `TermSubst.lift_compose_pointwise` at position 0.

Lifting a composed term-substitution under a binder agrees HEq with
composing the two lifts on the freshly-bound variable.  The position-
`k+1` case requires `Term.subst_weaken_commute_HEq` (binder cases
deferred) and is shipped as a separate companion. -/
theorem TermSubst.lift_compose_pointwise_zero
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty level scope₁) :
    HEq
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) newType
        ⟨0, Nat.zero_lt_succ _⟩)
      (TermSubst.compose (σt₁.lift newType)
                          (σt₂.lift (newType.subst σ₁))
        ⟨0, Nat.zero_lt_succ _⟩) := by
  -- LHS = (Ty.subst_weaken_commute newType (Subst.compose σ₁ σ₂)).symm ▸
  --        Term.var (context := Γ₃.cons (newType.subst (Subst.compose σ₁ σ₂))) ⟨0, _⟩
  --
  -- RHS = Ty.subst_compose newType.weaken σ₁.lift σ₂.lift ▸
  --        Term.subst (σt₂.lift (newType.subst σ₁))
  --          ((Ty.subst_weaken_commute newType σ₁).symm ▸
  --            Term.var (context := Γ₂.cons (newType.subst σ₁)) ⟨0, _⟩)
  --
  -- Strip outer cast on LHS via eqRec_heq.
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩) RHS
  --
  -- Flip and strip outer cast on RHS too.
  apply HEq.symm
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.subst (σt₂.lift _) (cast ▸ Term.var ⟨0, _⟩))
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Push the inner cast out through Term.subst via v1.26 helper.
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (σt₂.lift (newType.subst σ₁))
      (Ty.subst_weaken_commute newType σ₁).symm
      (Term.var (context := Γ₂.cons (newType.subst σ₁))
        ⟨0, Nat.zero_lt_succ _⟩))
  -- Goal: HEq (Term.subst (σt₂.lift _) (Term.var ⟨0, _⟩))
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Term.subst σt (Term.var i) ≡ σt i (Term.subst's var arm).
  show HEq ((σt₂.lift (newType.subst σ₁)) ⟨0, Nat.zero_lt_succ _⟩) _
  -- (σt₂.lift X) ⟨0, _⟩ = (Ty.subst_weaken_commute X σ₂).symm ▸ Term.var ⟨0, _⟩
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.var (context := Γ₃.cons ((newType.subst σ₁).subst σ₂)) ⟨0, _⟩)
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Bridge via Ty.subst_compose newType σ₁ σ₂ at the context level.
  exact heq_var_across_ctx_eq
    (congrArg Γ₃.cons (Ty.subst_compose newType σ₁ σ₂))
    ⟨0, Nat.zero_lt_succ _⟩


end LeanFX.Syntax
