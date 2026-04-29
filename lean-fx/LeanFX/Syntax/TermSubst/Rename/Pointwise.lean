import LeanFX.Syntax.TermSubst.Pointwise

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.rename_HEq_pointwise`.

Two TermRenamings whose underlying Renamings agree pointwise produce
HEq results when applied to the same term.  The rawRenaming-side analogue
of `Term.subst_HEq_pointwise`.  The `h_ctx : Δ₁ = Δ₂` parameter
accommodates the binder cases, where `TermRenaming.lift ρt_i dom`
lands in `Δ_i.cons (dom.rename ρ_i)` — different cons-extensions
across i = 1, 2. -/
theorem Term.rename_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ₁ Δ₂ : Ctx m level scope'}
    (h_ctx : Δ₁ = Δ₂)
    {ρ₁ ρ₂ : Renaming scope scope'}
    (ρt₁ : TermRenaming Γ Δ₁ ρ₁) (ρt₂ : TermRenaming Γ Δ₂ ρ₂)
    (h_ρ : Renaming.equiv ρ₁ ρ₂) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename ρt₁ t) (Term.rename ρt₂ t)
  | _, .var i => by
    cases h_ctx
    -- Term.rename ρt₁ (Term.var i) = (ρt₁ i) ▸ Term.var (ρ₁ i)
    -- Term.rename ρt₂ (Term.var i) = (ρt₂ i) ▸ Term.var (ρ₂ i)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Goal: HEq (Term.var (ρ₁ i)) (Term.var (ρ₂ i))
    -- Use h_ρ i to align the Fin positions.
    rw [h_ρ i]
  | _, .unit => by cases h_ctx; exact HEq.refl _
  | _, .app f a => by
    cases h_ctx
    show HEq
      (Term.app (Term.rename ρt₁ f) (Term.rename ρt₁ a))
      (Term.app (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    exact Term.app_HEq_congr
      (Ty.rename_congr h_ρ _)
      (Ty.rename_congr h_ρ _)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ f)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      (Term.fst (Term.rename ρt₁ p))
      (Term.fst (Term.rename ρt₂ p))
    apply Term.fst_HEq_congr
      (Ty.rename_congr h_ρ first)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
    exact Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ p
  | _, .boolTrue => by cases h_ctx; exact HEq.refl _
  | _, .boolFalse => by cases h_ctx; exact HEq.refl _
  | _, .boolElim (resultType := result) s t e => by
    cases h_ctx
    show HEq
      (Term.boolElim (Term.rename ρt₁ s)
                     (Term.rename ρt₁ t)
                     (Term.rename ρt₁ e))
      (Term.boolElim (Term.rename ρt₂ s)
                     (Term.rename ρt₂ t)
                     (Term.rename ρt₂ e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ s))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ t)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    cases h_ctx
    show HEq
      ((Ty.subst0_rename_commute cod dom ρ₁).symm ▸
        Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a))
      ((Ty.subst0_rename_commute cod dom ρ₂).symm ▸
        Term.appPi (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    · exact Term.appPi_HEq_congr
        (Ty.rename_congr h_ρ dom)
        (Ty.rename_congr (Renaming.lift_equiv h_ρ) cod)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ f)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ a)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := first) (secondType := second) v w => by
    cases h_ctx
    show HEq
      (Term.pair (Term.rename ρt₁ v)
        ((Ty.subst0_rename_commute second first ρ₁) ▸
          (Term.rename ρt₁ w)))
      (Term.pair (Term.rename ρt₂ v)
        ((Ty.subst0_rename_commute second first ρ₂) ▸
          (Term.rename ρt₂ w)))
    apply Term.pair_HEq_congr
      (Ty.rename_congr h_ρ first)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      ((Ty.subst0_rename_commute second first ρ₁).symm ▸
        Term.snd (Term.rename ρt₁ p))
      ((Ty.subst0_rename_commute second first ρ₂).symm ▸
        Term.snd (Term.rename ρt₂ p))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.rename ρt₂ p))
    · exact Term.snd_HEq_congr
        (Ty.rename_congr h_ρ first)
        (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ p)
    · exact (eqRec_heq _ _).symm
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lam (codomainType := cod.rename ρ₁)
        ((Ty.rename_weaken_commute cod ρ₁) ▸
          (Term.rename (TermRenaming.lift ρt₁ dom) body)))
      (Term.lam (codomainType := cod.rename ρ₂)
        ((Ty.rename_weaken_commute cod ρ₂) ▸
          (Term.rename (TermRenaming.lift ρt₂ dom) body)))
    apply Term.lam_HEq_congr
      (Ty.rename_congr h_ρ dom) (Ty.rename_congr h_ρ cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg (·.cons (dom.rename ρ₁)) (rfl : Δ₁ = Δ₁) |>.trans
          (congrArg Δ₁.cons (Ty.rename_congr h_ρ dom)))
        (TermRenaming.lift ρt₁ dom)
        (TermRenaming.lift ρt₂ dom)
        (Renaming.lift_equiv h_ρ)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lamPi (Term.rename (TermRenaming.lift ρt₁ dom) body))
      (Term.lamPi (Term.rename (TermRenaming.lift ρt₂ dom) body))
    apply Term.lamPi_HEq_congr
      (Ty.rename_congr h_ρ dom)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) cod)
    exact Term.rename_HEq_pointwise
      (congrArg Δ₁.cons (Ty.rename_congr h_ρ dom))
      (TermRenaming.lift ρt₁ dom)
      (TermRenaming.lift ρt₂ dom)
      (Renaming.lift_equiv h_ρ)
      body
  | _, .natZero => by cases h_ctx; exact HEq.refl _
  | _, .natSucc pred => by
    cases h_ctx
    show HEq (Term.natSucc (Term.rename ρt₁ pred))
             (Term.natSucc (Term.rename ρt₂ pred))
    exact Term.natSucc_HEq_congr _ _
      (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    show HEq
      (Term.natElim (Term.rename ρt₁ scrutinee)
                    (Term.rename ρt₁ zeroBranch)
                    (Term.rename ρt₁ succBranch))
      (Term.natElim (Term.rename ρt₂ scrutinee)
                    (Term.rename ρt₂ zeroBranch)
                    (Term.rename ρt₂ succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    exact Term.natRec_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ succBranch)
  | _, .listNil (elementType := elem) => by
    cases h_ctx
    exact Term.listNil_HEq_congr (Ty.rename_congr h_ρ elem)
  | _, .listCons (elementType := elem) hd tl => by
    cases h_ctx
    show HEq (Term.listCons (Term.rename ρt₁ hd) (Term.rename ρt₁ tl))
             (Term.listCons (Term.rename ρt₂ hd) (Term.rename ρt₂ tl))
    exact Term.listCons_HEq_congr
      (Ty.rename_congr h_ρ elem)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ hd)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch => by
    cases h_ctx
    show HEq
      (Term.listElim (Term.rename ρt₁ scrutinee)
                     (Term.rename ρt₁ nilBranch)
                     (Term.rename ρt₁ consBranch))
      (Term.listElim (Term.rename ρt₂ scrutinee)
                     (Term.rename ρt₂ nilBranch)
                     (Term.rename ρt₂ consBranch))
    exact Term.listElim_HEq_congr
      (Ty.rename_congr h_ρ elem) (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ nilBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ consBranch)
  | _, .optionNone (elementType := elem) => by
    cases h_ctx
    exact Term.optionNone_HEq_congr (Ty.rename_congr h_ρ elem)
  | _, .optionSome (elementType := elem) v => by
    cases h_ctx
    show HEq (Term.optionSome (Term.rename ρt₁ v))
             (Term.optionSome (Term.rename ρt₂ v))
    exact Term.optionSome_HEq_congr
      (Ty.rename_congr h_ρ elem)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch => by
    cases h_ctx
    show HEq
      (Term.optionMatch (Term.rename ρt₁ scrutinee)
                        (Term.rename ρt₁ noneBranch)
                        (Term.rename ρt₁ someBranch))
      (Term.optionMatch (Term.rename ρt₂ scrutinee)
                        (Term.rename ρt₂ noneBranch)
                        (Term.rename ρt₂ someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.rename_congr h_ρ elem) (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ noneBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInl_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInr_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch => by
    cases h_ctx
    exact Term.eitherMatch_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ leftBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ rightBranch)
  | _, .refl (carrier := carrier) rawTerm => by
    cases h_ctx
    exact Term.refl_HEq_congr
      (Ty.rename_congr h_ρ carrier)
      (RawTerm.rename_congr h_ρ rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness => by
    cases h_ctx
    exact Term.idJ_HEq_congr
      (Ty.rename_congr h_ρ carrier)
      (RawTerm.rename_congr h_ρ leftEnd)
      (RawTerm.rename_congr h_ρ rightEnd)
      (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ baseCase)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ witness)


end LeanFX.Syntax
