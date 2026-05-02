import LeanFX.Syntax.TermSubst.Commute.SubstRename

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.rename_subst_commute_HEq`.

Term-level analogue of `Ty.rename_subst_commute`:

  Term.subst termSubstitution' (Term.rename termRenaming t)
    ≃HEq≃
  Term.subst (TermSubst.precompose termRenaming termSubstitution') t

Mirrors v1.40 (subst-rename commute) with rename and subst swapped.
12-case structural induction with constructor HEq congruences for
the closed-context cases, outer-cast strips + inner-cast pushes
for the cast-bearing cases, and `Term.subst_HEq_pointwise` over
`TermSubst.lift_precompose_pointwise` (v1.41) for the binder
cases. -/
theorem Term.rename_subst_commute_HEq
    {mode : Mode} {level scope middleScope targetScope : Nat}
    {sourceContext : Ctx mode level scope}
    {middleContext : Ctx mode level middleScope}
    {targetContext : Ctx mode level targetScope}
    {rawRenaming : Renaming scope middleScope} {typeSubstitution' : Subst level middleScope targetScope}
    (termRenaming : TermRenaming sourceContext middleContext rawRenaming) (termSubstitution' : TermSubst middleContext targetContext typeSubstitution') :
    {T : Ty level scope} → (t : Term sourceContext T) →
      HEq (Term.subst termSubstitution' (Term.rename termRenaming t))
          (Term.subst (TermSubst.precompose termRenaming termSubstitution') t)
  | _, .var i => by
    -- LHS: Term.subst termSubstitution' ((termRenaming i) ▸ Term.var (rawRenaming i)).
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input termSubstitution' (termRenaming i)
        (Term.var (context := middleContext) (rawRenaming i)))
    -- LHS reduces to termSubstitution' (rawRenaming i); RHS = (precompose termRenaming termSubstitution') i,
    -- which by precompose's definition is `chain ▸ termSubstitution' (rawRenaming i)`.
    -- Stage the chained equation via `have` so Lean β-reduces the
    -- congrArg-on-lambda before checking the ▸ type alignment.
    have h_witness : (varType middleContext (rawRenaming i)).subst typeSubstitution'
                       = ((varType sourceContext i).rename rawRenaming).subst typeSubstitution' :=
      congrArg (fun T : Ty level middleScope => T.subst typeSubstitution') (termRenaming i)
    have h_chain : (varType middleContext (rawRenaming i)).subst typeSubstitution'
                     = (varType sourceContext i).subst (Subst.precompose rawRenaming typeSubstitution') :=
      h_witness.trans
        (Ty.rename_subst_commute (varType sourceContext i) rawRenaming typeSubstitution')
    show HEq (termSubstitution' (rawRenaming i)) (h_chain ▸ termSubstitution' (rawRenaming i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst termSubstitution' (Term.rename termRenaming f))
                (Term.subst termSubstitution' (Term.rename termRenaming a)))
      (Term.app (Term.subst (TermSubst.precompose termRenaming termSubstitution') f)
                (Term.subst (TermSubst.precompose termRenaming termSubstitution') a))
    exact Term.app_HEq_congr
      (Ty.rename_subst_commute dom rawRenaming typeSubstitution')
      (Ty.rename_subst_commute cod rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' f)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst termSubstitution' (Term.rename termRenaming p)))
      (Term.fst (Term.subst (TermSubst.precompose termRenaming termSubstitution') p))
    apply Term.fst_HEq_congr
      (Ty.rename_subst_commute first rawRenaming typeSubstitution')
      ((Ty.rename_subst_commute second rawRenaming.lift typeSubstitution'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute rawRenaming typeSubstitution') second))
    exact Term.rename_subst_commute_HEq termRenaming termSubstitution' p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst termSubstitution' (Term.rename termRenaming s))
                     (Term.subst termSubstitution' (Term.rename termRenaming t))
                     (Term.subst termSubstitution' (Term.rename termRenaming e)))
      (Term.boolElim (Term.subst (TermSubst.precompose termRenaming termSubstitution') s)
                     (Term.subst (TermSubst.precompose termRenaming termSubstitution') t)
                     (Term.subst (TermSubst.precompose termRenaming termSubstitution') e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq termRenaming termSubstitution' s))
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' t)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' e)
  | _, .appPi (domainType := dom) (codomainType := cod) resultEq f a => by
    -- W9.B1.1 — equation-bearing appPi.  Cases on resultEq normalises shape.
    cases resultEq
    -- LHS: Term.subst termSubstitution' (rfl-cast.symm ▸ rename-cast.symm ▸ Term.appPi rfl (rename f) (rename a))
    apply HEq.trans
      (Term.subst_HEq_cast_input termSubstitution'
        (Ty.subst0_rename_commute cod dom rawRenaming).symm
        (Term.appPi rfl (Term.rename termRenaming f) (Term.rename termRenaming a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.rename_subst_commute dom rawRenaming typeSubstitution')
      ((Ty.rename_subst_commute cod rawRenaming.lift typeSubstitution'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute rawRenaming typeSubstitution') cod))
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' f)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.rename_subst_commute first rawRenaming typeSubstitution')
      ((Ty.rename_subst_commute second rawRenaming.lift typeSubstitution'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute rawRenaming typeSubstitution') second))
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' v)
    -- LHS secondVal: cast_outer_LHS ▸ subst termSubstitution' (cast_inner_LHS ▸ rename termRenaming w)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input termSubstitution'
        (Ty.subst0_rename_commute second first rawRenaming)
        (Term.rename termRenaming w))
    apply HEq.trans (Term.rename_subst_commute_HEq termRenaming termSubstitution' w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p resultEq => by
    -- W9.B1.2 — equation-bearing snd.  Mirror of appPi.
    cases resultEq
    apply HEq.trans
      (Term.subst_HEq_cast_input termSubstitution'
        (Ty.subst0_rename_commute second first rawRenaming).symm
        (Term.snd (Term.rename termRenaming p) rfl))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_subst_commute first rawRenaming typeSubstitution')
      ((Ty.rename_subst_commute second rawRenaming.lift typeSubstitution'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute rawRenaming typeSubstitution') second))
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.rename_subst_commute dom rawRenaming typeSubstitution')
      (Ty.rename_subst_commute cod rawRenaming typeSubstitution')
    -- Strip outer cast on LHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through subst (lift termSubstitution' (dom.rename rawRenaming)).
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift termSubstitution' (dom.rename rawRenaming))
        (Ty.rename_weaken_commute cod rawRenaming)
        (Term.rename (TermRenaming.lift termRenaming dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift termRenaming dom)
        (TermSubst.lift termSubstitution' (dom.rename rawRenaming))
        body)
    -- Bridge via subst_HEq_pointwise + v1.41.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg targetContext.cons (Ty.rename_subst_commute dom rawRenaming typeSubstitution'))
      (TermSubst.precompose
        (TermRenaming.lift termRenaming dom)
        (TermSubst.lift termSubstitution' (dom.rename rawRenaming)))
      ((TermSubst.precompose termRenaming termSubstitution').lift dom)
      (Subst.lift_precompose_commute rawRenaming typeSubstitution')
      (TermSubst.lift_precompose_pointwise termRenaming termSubstitution' dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.rename_subst_commute dom rawRenaming typeSubstitution')
      ((Ty.rename_subst_commute cod rawRenaming.lift typeSubstitution'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute rawRenaming typeSubstitution') cod))
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift termRenaming dom)
        (TermSubst.lift termSubstitution' (dom.rename rawRenaming))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg targetContext.cons (Ty.rename_subst_commute dom rawRenaming typeSubstitution'))
      (TermSubst.precompose
        (TermRenaming.lift termRenaming dom)
        (TermSubst.lift termSubstitution' (dom.rename rawRenaming)))
      ((TermSubst.precompose termRenaming termSubstitution').lift dom)
      (Subst.lift_precompose_commute rawRenaming typeSubstitution')
      (TermSubst.lift_precompose_pointwise termRenaming termSubstitution' dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst termSubstitution' (Term.rename termRenaming scrutinee))
        (Term.subst termSubstitution' (Term.rename termRenaming zeroBranch))
        (Term.subst termSubstitution' (Term.rename termRenaming succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.precompose termRenaming termSubstitution') scrutinee)
        (Term.subst (TermSubst.precompose termRenaming termSubstitution') zeroBranch)
        (Term.subst (TermSubst.precompose termRenaming termSubstitution') succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq termRenaming termSubstitution' scrutinee))
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq termRenaming termSubstitution' scrutinee))
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_subst_commute elem rawRenaming typeSubstitution')
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_subst_commute elem rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' hd)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_subst_commute elem rawRenaming typeSubstitution')
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' scrutinee)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' nilBranch)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_subst_commute elem rawRenaming typeSubstitution')
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_subst_commute elem rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_subst_commute elem rawRenaming typeSubstitution')
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' scrutinee)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' noneBranch)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_subst_commute lefT rawRenaming typeSubstitution')
      (Ty.rename_subst_commute righT rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_subst_commute lefT rawRenaming typeSubstitution')
      (Ty.rename_subst_commute righT rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_subst_commute lefT rawRenaming typeSubstitution')
      (Ty.rename_subst_commute righT rawRenaming typeSubstitution')
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' scrutinee)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' leftBranch)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_subst_commute carrier rawRenaming typeSubstitution')
      (RawTerm.subst_rename_commute rawTerm rawRenaming typeSubstitution'.forRaw)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := result)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_subst_commute carrier rawRenaming typeSubstitution')
      (RawTerm.subst_rename_commute leftEnd rawRenaming typeSubstitution'.forRaw)
      (RawTerm.subst_rename_commute rightEnd rawRenaming typeSubstitution'.forRaw)
      (Ty.rename_subst_commute result rawRenaming typeSubstitution')
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' baseCase)
      _ _ (Term.rename_subst_commute_HEq termRenaming termSubstitution' witness)


end LeanFX.Syntax
