import LeanFX.Syntax.TermSubst.Commute.Precompose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.subst_rename_commute_HEq`.

Term-level analogue of `Ty.subst_rename_commute`:

  Term.rename termRenaming (Term.subst termSubstitution t)
    ≃HEq≃
  Term.subst (TermSubst.renameAfter termSubstitution termRenaming) t

12-case structural induction on the term.  Closed-context cases
combine the constructor HEq congruence (v1.21) with
`Ty.subst_rename_commute` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) peel outer casts via `eqRec_heq` and push inner
casts through `Term.{rename,subst}_HEq_cast_input` (v1.26 / v1.37).
Binder cases (lam/lamPi) use the IH at lifted TermSubst/TermRenaming,
then bridge `renameAfter (lift termSubstitution dom) (lift termRenaming (dom.subst typeSubstitution))`
against `lift (renameAfter termSubstitution termRenaming) dom` via `Term.subst_HEq_pointwise`
(v1.24) over `TermSubst.lift_renameAfter_pointwise` (v1.39). -/
theorem Term.subst_rename_commute_HEq
    {mode : Mode} {level scope middleScope targetScope : Nat}
    {sourceContext : Ctx mode level scope}
    {middleContext : Ctx mode level middleScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level scope middleScope} {rawRenaming : Renaming middleScope targetScope}
    (termSubstitution : TermSubst sourceContext middleContext typeSubstitution) (termRenaming : TermRenaming middleContext targetContext rawRenaming) :
    {T : Ty level scope} → (t : Term sourceContext T) →
      HEq (Term.rename termRenaming (Term.subst termSubstitution t))
          (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) t)
  | _, .var i => by
    -- LHS: Term.rename termRenaming (termSubstitution i)
    -- RHS: (renameAfter termSubstitution termRenaming) i = (Ty.subst_rename_commute _ typeSubstitution rawRenaming) ▸ Term.rename termRenaming (termSubstitution i)
    show HEq (Term.rename termRenaming (termSubstitution i))
             ((Ty.subst_rename_commute (varType sourceContext i) typeSubstitution rawRenaming) ▸
                Term.rename termRenaming (termSubstitution i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename termRenaming (Term.subst termSubstitution f))
                (Term.rename termRenaming (Term.subst termSubstitution a)))
      (Term.app (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) f)
                (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) a))
    exact Term.app_HEq_congr
      (Ty.subst_rename_commute dom typeSubstitution rawRenaming)
      (Ty.subst_rename_commute cod typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming f)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename termRenaming (Term.subst termSubstitution p)))
      (Term.fst (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) p))
    apply Term.fst_HEq_congr
      (Ty.subst_rename_commute first typeSubstitution rawRenaming)
      ((Ty.subst_rename_commute second typeSubstitution.lift rawRenaming.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute typeSubstitution rawRenaming) second))
    exact Term.subst_rename_commute_HEq termSubstitution termRenaming p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename termRenaming (Term.subst termSubstitution s))
                     (Term.rename termRenaming (Term.subst termSubstitution t))
                     (Term.rename termRenaming (Term.subst termSubstitution e)))
      (Term.boolElim (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) s)
                     (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) t)
                     (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq termSubstitution termRenaming s))
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming t)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.rename termRenaming (cast_subst.symm ▸ Term.appPi (subst f) (subst a))
    apply HEq.trans
      (Term.rename_HEq_cast_input termRenaming
        (Ty.subst0_subst_commute cod dom typeSubstitution).symm
        (Term.appPi (Term.subst termSubstitution f) (Term.subst termSubstitution a)))
    -- After helper: rename termRenaming (Term.appPi ...)
    -- Strip outer cast from rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- RHS side: (renameAfter termSubstitution termRenaming) on Term.appPi emits cast.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.subst_rename_commute dom typeSubstitution rawRenaming)
      ((Ty.subst_rename_commute cod typeSubstitution.lift rawRenaming.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute typeSubstitution rawRenaming) cod))
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming f)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_rename_commute first typeSubstitution rawRenaming)
      ((Ty.subst_rename_commute second typeSubstitution.lift rawRenaming.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute typeSubstitution rawRenaming) second))
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming v)
    -- LHS secondVal: cast_outer_LHS ▸ rename termRenaming (cast_inner_LHS ▸ subst termSubstitution w)
    -- RHS secondVal: cast_compose ▸ subst (renameAfter termSubstitution termRenaming) w
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input termRenaming
        (Ty.subst0_subst_commute second first typeSubstitution)
        (Term.subst termSubstitution w))
    apply HEq.trans (Term.subst_rename_commute_HEq termSubstitution termRenaming w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.rename_HEq_cast_input termRenaming
        (Ty.subst0_subst_commute second first typeSubstitution).symm
        (Term.snd (Term.subst termSubstitution p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_rename_commute first typeSubstitution rawRenaming)
      ((Ty.subst_rename_commute second typeSubstitution.lift rawRenaming.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute typeSubstitution rawRenaming) second))
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body lives at scope+1; double-traversed via lift termSubstitution then lift termRenaming.
    -- RHS body uses lift (renameAfter termSubstitution termRenaming) dom, pointwise HEq to
    -- renameAfter (lift termSubstitution dom) (lift termRenaming (dom.subst typeSubstitution)) via v1.39.
    apply Term.lam_HEq_congr
      (Ty.subst_rename_commute dom typeSubstitution rawRenaming)
      (Ty.subst_rename_commute cod typeSubstitution rawRenaming)
    -- Strip outer cast on LHS (rename's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift termRenaming (dom.subst typeSubstitution)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift termRenaming (dom.subst typeSubstitution))
        (Ty.subst_weaken_commute cod typeSubstitution)
        (Term.subst (TermSubst.lift termSubstitution dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift termSubstitution dom)
        (TermRenaming.lift termRenaming (dom.subst typeSubstitution))
        body)
    -- Now LHS_naked = Term.subst (renameAfter (lift termSubstitution dom)
    --                              (lift termRenaming (dom.subst typeSubstitution))) body
    -- Bridge to RHS_naked = Term.subst (lift (renameAfter termSubstitution termRenaming) dom) body
    -- via subst_HEq_pointwise + v1.39.
    apply HEq.symm
    -- Strip outer cast on RHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg targetContext.cons (Ty.subst_rename_commute dom typeSubstitution rawRenaming))
      (TermSubst.renameAfter
        (TermSubst.lift termSubstitution dom)
        (TermRenaming.lift termRenaming (dom.subst typeSubstitution)))
      ((TermSubst.renameAfter termSubstitution termRenaming).lift dom)
      (Subst.lift_renameAfter_commute typeSubstitution rawRenaming)
      (TermSubst.lift_renameAfter_pointwise termSubstitution termRenaming dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_rename_commute dom typeSubstitution rawRenaming)
      ((Ty.subst_rename_commute cod typeSubstitution.lift rawRenaming.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute typeSubstitution rawRenaming) cod))
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift termSubstitution dom)
        (TermRenaming.lift termRenaming (dom.subst typeSubstitution))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg targetContext.cons (Ty.subst_rename_commute dom typeSubstitution rawRenaming))
      (TermSubst.renameAfter
        (TermSubst.lift termSubstitution dom)
        (TermRenaming.lift termRenaming (dom.subst typeSubstitution)))
      ((TermSubst.renameAfter termSubstitution termRenaming).lift dom)
      (Subst.lift_renameAfter_commute typeSubstitution rawRenaming)
      (TermSubst.lift_renameAfter_pointwise termSubstitution termRenaming dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename termRenaming (Term.subst termSubstitution scrutinee))
        (Term.rename termRenaming (Term.subst termSubstitution zeroBranch))
        (Term.rename termRenaming (Term.subst termSubstitution succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) scrutinee)
        (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) zeroBranch)
        (Term.subst (TermSubst.renameAfter termSubstitution termRenaming) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq termSubstitution termRenaming scrutinee))
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming zeroBranch)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq termSubstitution termRenaming scrutinee))
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming zeroBranch)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_rename_commute elem typeSubstitution rawRenaming)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_rename_commute elem typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming hd)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_rename_commute elem typeSubstitution rawRenaming)
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming scrutinee)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming nilBranch)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_rename_commute elem typeSubstitution rawRenaming)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_rename_commute elem typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_rename_commute elem typeSubstitution rawRenaming)
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming scrutinee)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming noneBranch)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_rename_commute lefT typeSubstitution rawRenaming)
      (Ty.subst_rename_commute righT typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_rename_commute lefT typeSubstitution rawRenaming)
      (Ty.subst_rename_commute righT typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_rename_commute lefT typeSubstitution rawRenaming)
      (Ty.subst_rename_commute righT typeSubstitution rawRenaming)
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming scrutinee)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming leftBranch)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.subst_rename_commute carrier typeSubstitution rawRenaming)
      (RawTerm.rename_subst_commute rawTerm typeSubstitution.forRaw rawRenaming)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_rename_commute carrier typeSubstitution rawRenaming)
      (RawTerm.rename_subst_commute leftEnd typeSubstitution.forRaw rawRenaming)
      (RawTerm.rename_subst_commute rightEnd typeSubstitution.forRaw rawRenaming)
      (Ty.subst_rename_commute result typeSubstitution rawRenaming)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming baseCase)
      _ _ (Term.subst_rename_commute_HEq termSubstitution termRenaming witness)


end LeanFX.Syntax
