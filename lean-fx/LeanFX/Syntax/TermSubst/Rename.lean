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

/-! ## `Term.rename_id_HEq`.

Renaming-side identity, the companion to `Term.subst_id_HEq` (v1.25):

  HEq (Term.rename (TermRenaming.identity Γ) t) t

Mirrors `Term.subst_id_HEq`'s 12-case structural induction.  Simpler
than the subst version because `TermRenaming` is `Prop`-valued —
the binder cases bridge `TermRenaming.lift (identity Γ) dom` against
`TermRenaming.identity (Γ.cons dom)` directly via
`Term.rename_HEq_pointwise` over `Renaming.lift_identity_equiv`,
without needing a separate `lift_identity_pointwise` stepping stone
(those existed for subst because TermSubst is Type-valued and pointwise
HEq on the witness is non-trivial).

Closed-context cases use the constructor HEq congruences plus
`Ty.rename_identity` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) strip outer casts via `eqRec_heq`. -/
theorem Term.rename_id_HEq {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename (TermRenaming.identity Γ) t) t
  | _, .var i => by
    -- LHS: (TermRenaming.identity Γ i) ▸ Term.var (Renaming.identity i)
    --    = (Ty.rename_identity (varType Γ i)).symm ▸ Term.var i
    show HEq ((Ty.rename_identity (varType Γ i)).symm ▸ Term.var i) (Term.var i)
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename (TermRenaming.identity Γ) f)
                (Term.rename (TermRenaming.identity Γ) a))
      (Term.app f a)
    exact Term.app_HEq_congr
      (Ty.rename_identity dom) (Ty.rename_identity cod)
      _ _ (Term.rename_id_HEq f)
      _ _ (Term.rename_id_HEq a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename (TermRenaming.identity Γ) p))
      (Term.fst p)
    apply Term.fst_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
    exact Term.rename_id_HEq p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename (TermRenaming.identity Γ) s)
                     (Term.rename (TermRenaming.identity Γ) t)
                     (Term.rename (TermRenaming.identity Γ) e))
      (Term.boolElim s t e)
    exact Term.boolElim_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq s))
      _ _ (Term.rename_id_HEq t)
      _ _ (Term.rename_id_HEq e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: (Ty.subst0_rename_commute cod dom Renaming.identity).symm ▸
    --        Term.appPi (Term.rename (identity Γ) f)
    --                   (Term.rename (identity Γ) a)
    show HEq
      ((Ty.subst0_rename_commute cod dom Renaming.identity).symm ▸
        Term.appPi (Term.rename (TermRenaming.identity Γ) f)
                   (Term.rename (TermRenaming.identity Γ) a))
      (Term.appPi f a)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.appPi_HEq_congr
      (Ty.rename_identity dom)
      ((Ty.rename_congr Renaming.lift_identity_equiv cod).trans
        (Ty.rename_identity cod))
      _ _ (Term.rename_id_HEq f)
      _ _ (Term.rename_id_HEq a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    show HEq
      (Term.pair (Term.rename (TermRenaming.identity Γ) v)
        ((Ty.subst0_rename_commute second first Renaming.identity) ▸
          (Term.rename (TermRenaming.identity Γ) w)))
      (Term.pair v w)
    apply Term.pair_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
      _ _ (Term.rename_id_HEq v)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.rename_id_HEq w
  | _, .snd (firstType := first) (secondType := second) p => by
    show HEq
      ((Ty.subst0_rename_commute second first Renaming.identity).symm ▸
        Term.snd (Term.rename (TermRenaming.identity Γ) p))
      (Term.snd p)
    apply HEq.trans (eqRec_heq _ _)
    apply Term.snd_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
    exact Term.rename_id_HEq p
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lam (codomainType := cod.rename Renaming.identity)
        ((Ty.rename_weaken_commute cod Renaming.identity) ▸
          (Term.rename (TermRenaming.lift (TermRenaming.identity Γ) dom) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr
      (Ty.rename_identity dom) (Ty.rename_identity cod)
    -- Strip outer cast.
    apply HEq.trans (eqRec_heq _ _)
    -- Bridge `TermRenaming.lift (identity Γ) dom` to
    -- `TermRenaming.identity (Γ.cons dom)` via rename_HEq_pointwise
    -- + Renaming.lift_identity_equiv, then recurse.
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg Γ.cons (Ty.rename_identity dom))
        (TermRenaming.lift (TermRenaming.identity Γ) dom)
        (TermRenaming.identity (Γ.cons dom))
        Renaming.lift_identity_equiv
        body)
    exact Term.rename_id_HEq body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lamPi
        (Term.rename (TermRenaming.lift (TermRenaming.identity Γ) dom) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr
      (Ty.rename_identity dom)
      ((Ty.rename_congr Renaming.lift_identity_equiv cod).trans
        (Ty.rename_identity cod))
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg Γ.cons (Ty.rename_identity dom))
        (TermRenaming.lift (TermRenaming.identity Γ) dom)
        (TermRenaming.identity (Γ.cons dom))
        Renaming.lift_identity_equiv
        body)
    exact Term.rename_id_HEq body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_id_HEq pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename (TermRenaming.identity Γ) scrutinee)
        (Term.rename (TermRenaming.identity Γ) zeroBranch)
        (Term.rename (TermRenaming.identity Γ) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_identity elem)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_identity elem)
      _ _ (Term.rename_id_HEq hd)
      _ _ (Term.rename_id_HEq tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_identity elem) (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq nilBranch)
      _ _ (Term.rename_id_HEq consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_identity elem)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_identity elem)
      _ _ (Term.rename_id_HEq v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_identity elem) (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq noneBranch)
      _ _ (Term.rename_id_HEq someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      _ _ (Term.rename_id_HEq v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      _ _ (Term.rename_id_HEq v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq leftBranch)
      _ _ (Term.rename_id_HEq rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_identity carrier)
      (RawTerm.rename_identity (level := level) rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_identity carrier)
      (RawTerm.rename_identity (level := level) leftEnd)
      (RawTerm.rename_identity (level := level) rightEnd)
      (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq baseCase)
      _ _ (Term.rename_id_HEq witness)

/-- The explicit-`▸` form of `Term.rename_id`: `eq_of_heq` plus an
outer cast strip.  Mirrors v1.25's `Term.subst_id` derivation from
`Term.subst_id_HEq`. -/
theorem Term.rename_id {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T : Ty level scope} (t : Term Γ T) :
    (Ty.rename_identity T) ▸ Term.rename (TermRenaming.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.rename_id_HEq t))

/-! ## Term-rename composition. -/

/-- Composition of term-level renamings.  Position-equality witness
chains the two `TermRenaming`s through `Ty.rename_compose`. -/
theorem TermRenaming.compose
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    TermRenaming Γ₁ Γ₃ (Renaming.compose ρ₁ ρ₂) := fun i => by
  show varType Γ₃ (ρ₂ (ρ₁ i))
     = (varType Γ₁ i).rename (Renaming.compose ρ₁ ρ₂)
  rw [ρt₂ (ρ₁ i)]
  rw [ρt₁ i]
  exact Ty.rename_compose (varType Γ₁ i) ρ₁ ρ₂

/-- Push a propositional type-cast on the input of `Term.rename ρt`
out to an HEq.  Mirror of `Term.subst_HEq_cast_input` and
`Term.weaken_HEq_cast_input`. -/
theorem Term.rename_HEq_cast_input
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    {T₁ T₂ : Ty level scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.rename ρt (h ▸ t)) (Term.rename ρt t) := by
  cases h
  rfl

/-! ## `Term.rename_compose_HEq`.

Double-rename equals single-rename by composed rawRenaming, modulo HEq.
The two sides have types `Term Γ₃ ((T.rename ρ₁).rename ρ₂)` and
`Term Γ₃ (T.rename (Renaming.compose ρ₁ ρ₂))`; these agree
propositionally by `Ty.rename_compose`.  Pattern-matched structural
induction on the term.

Binder cases bridge `TermRenaming.lift (compose ρt₁ ρt₂) dom` against
`compose (lift ρt₁ dom) (lift ρt₂ (dom.rename ρ₁))` via
`Term.rename_HEq_pointwise` over `Renaming.lift_compose_equiv`. -/
theorem Term.rename_compose_HEq
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    {T : Ty level scope₁} → (t : Term Γ₁ T) →
      HEq (Term.rename ρt₂ (Term.rename ρt₁ t))
          (Term.rename (TermRenaming.compose ρt₁ ρt₂) t)
  | _, .var i => by
    -- LHS: Term.rename ρt₂ ((ρt₁ i) ▸ Term.var (ρ₁ i))
    -- Push the inner cast through Term.rename ρt₂.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂ (ρt₁ i) (Term.var (ρ₁ i)))
    -- Now: Term.rename ρt₂ (Term.var (ρ₁ i))
    --    = (ρt₂ (ρ₁ i)) ▸ Term.var (ρ₂ (ρ₁ i))
    -- RHS: ((compose ρt₁ ρt₂) i) ▸ Term.var ((Renaming.compose ρ₁ ρ₂) i)
    --    where (Renaming.compose ρ₁ ρ₂) i ≡ ρ₂ (ρ₁ i) definitionally.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename ρt₂ (Term.rename ρt₁ f))
                (Term.rename ρt₂ (Term.rename ρt₁ a)))
      (Term.app (Term.rename (TermRenaming.compose ρt₁ ρt₂) f)
                (Term.rename (TermRenaming.compose ρt₁ ρt₂) a))
    exact Term.app_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      (Ty.rename_compose cod ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ f)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename ρt₂ (Term.rename ρt₁ p)))
      (Term.fst (Term.rename (TermRenaming.compose ρt₁ ρt₂) p))
    apply Term.fst_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
    exact Term.rename_compose_HEq ρt₁ ρt₂ p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename ρt₂ (Term.rename ρt₁ s))
                     (Term.rename ρt₂ (Term.rename ρt₁ t))
                     (Term.rename ρt₂ (Term.rename ρt₁ e)))
      (Term.boolElim (Term.rename (TermRenaming.compose ρt₁ ρt₂) s)
                     (Term.rename (TermRenaming.compose ρt₁ ρt₂) t)
                     (Term.rename (TermRenaming.compose ρt₁ ρt₂) e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ s))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ t)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- Outer-cast peeling on each side, then constructor congruence.
    -- LHS: Term.rename ρt₂ ((cast₁).symm ▸ Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a))
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute cod dom ρ₁).symm
        (Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a)))
    -- Now: Term.rename ρt₂ (Term.appPi (...) (...))
    -- Strip outer cast from Term.rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and process RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      ((Ty.rename_compose cod ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) cod))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ f)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    -- Outer Term.pair has no cast; secondVal carries nested casts on both sides.
    apply Term.pair_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
    -- LHS secondVal: cast_outer ▸ Term.rename ρt₂ (cast_inner ▸ Term.rename ρt₁ w)
    -- RHS secondVal: cast_compose ▸ Term.rename (compose ρt₁ ρt₂) w
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.rename ρt₂.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute second first ρ₁)
        (Term.rename ρt₁ w))
    -- Use IH on w.
    apply HEq.trans (Term.rename_compose_HEq ρt₁ ρt₂ w)
    -- Strip outer cast on RHS.
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    -- Mirror of fst plus outer cast strips on each side.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute second first ρ₁).symm
        (Term.snd (Term.rename ρt₁ p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body: cast₂ ▸ rename (lift ρt₂ (dom.rename ρ₁)) (cast₁ ▸ rename (lift ρt₁ dom) body)
    -- RHS body: cast_compose ▸ rename (lift (compose ρt₁ ρt₂) dom) body
    apply Term.lam_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      (Ty.rename_compose cod ρ₁ ρ₂)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift ρt₂ (dom.rename ρ₁)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift ρt₂ (dom.rename ρ₁))
        (Ty.rename_weaken_commute cod ρ₁)
        (Term.rename (TermRenaming.lift ρt₁ dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)) body)
    -- Bridge compose-of-lifts to lift-of-compose via rename_HEq_pointwise.
    apply HEq.symm
    -- Strip outer cast on RHS (now in symm orientation, so it's the LHS goal).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.rename_HEq_pointwise
      (congrArg Γ₃.cons (Ty.rename_compose dom ρ₁ ρ₂))
      (TermRenaming.compose
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)))
      (TermRenaming.lift (TermRenaming.compose ρt₁ ρt₂) dom)
      (Renaming.lift_compose_equiv ρ₁ ρ₂)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    -- LHS body: rename (lift ρt₂ (dom.rename ρ₁)) (rename (lift ρt₁ dom) body)
    --          (no outer casts because Term.rename's lamPi clause has no cast)
    -- RHS body: rename (lift (compose ρt₁ ρt₂) dom) body
    apply Term.lamPi_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      ((Ty.rename_compose cod ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) cod))
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)) body)
    exact Term.rename_HEq_pointwise
      (congrArg Γ₃.cons (Ty.rename_compose dom ρ₁ ρ₂))
      (TermRenaming.compose
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)))
      (TermRenaming.lift (TermRenaming.compose ρt₁ ρt₂) dom)
      (Renaming.lift_compose_equiv ρ₁ ρ₂)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_compose_HEq ρt₁ ρt₂ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename ρt₂ (Term.rename ρt₁ scrutinee))
        (Term.rename ρt₂ (Term.rename ρt₁ zeroBranch))
        (Term.rename ρt₂ (Term.rename ρt₁ succBranch)))
      (Term.natElim
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) scrutinee)
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) zeroBranch)
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ zeroBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ zeroBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_compose elem ρ₁ ρ₂)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ hd)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ nilBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_compose elem ρ₁ ρ₂)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ noneBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ leftBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_compose carrier ρ₁ ρ₂)
      (RawTerm.rename_compose rawTerm ρ₁ ρ₂)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_compose carrier ρ₁ ρ₂)
      (RawTerm.rename_compose leftEnd ρ₁ ρ₂)
      (RawTerm.rename_compose rightEnd ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ baseCase)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ witness)

/-! ## `Term.rename_weaken_commute_HEq`.

Term-level analogue of `Ty.rename_weaken_commute`:

  Term.rename (lift ρt X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.rename ρ) (Term.rename ρt t)

Both sides factor into double-rename forms because `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`.  By v1.37 each side
collapses to a single rename along a composed TermRenaming; the two
underlying renamings (`compose Renaming.weaken ρ.lift` and `compose
ρ Renaming.weaken`) are pointwise equal — both reduce to `Fin.succ ∘ ρ`
modulo Fin proof-irrelevance.  The bridge is `Term.rename_HEq_pointwise`
(v1.36) over the trivial pointwise witness. -/
theorem Term.rename_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.rename (TermRenaming.lift ρt newType) (Term.weaken newType t))
        (Term.weaken (newType.rename ρ) (Term.rename ρt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.rename (TermRenaming.lift ρt newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.rename ρ))
      (Term.rename ρt t))
  -- Collapse LHS via v1.37 to a single composed rename.
  apply HEq.trans
    (Term.rename_compose_HEq
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType)
      t)
  -- Same for RHS, in symm orientation so it lands on the right of HEq.
  apply HEq.symm
  apply HEq.trans
    (Term.rename_compose_HEq
      ρt
      (TermRenaming.weaken Δ (newType.rename ρ))
      t)
  apply HEq.symm
  -- The two composed underlying renamings agree pointwise — `fun _ => rfl`.
  exact Term.rename_HEq_pointwise rfl
    (TermRenaming.compose
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType))
    (TermRenaming.compose ρt
      (TermRenaming.weaken Δ (newType.rename ρ)))
    (fun _ => rfl)
    t


end LeanFX.Syntax
