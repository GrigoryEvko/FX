import LeanFX.Syntax.TermSubst.Commute.Precompose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

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


end LeanFX.Syntax
