import LeanFX.Syntax.TermSubst.Commute.SubstRename

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

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


end LeanFX.Syntax
