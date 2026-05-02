import LeanFX.Syntax.TermSubst.Rename.Pointwise

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

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
theorem Term.rename_id_HEq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    {tyValue : Ty level scope} → (term : Term context tyValue) →
      HEq (Term.rename (TermRenaming.identity context) term) term
  | _, .var position => by
    -- LHS: (TermRenaming.identity Γ i) ▸ Term.var (Renaming.identity i)
    --    = (Ty.rename_identity (varType Γ i)).symm ▸ Term.var i
    show HEq ((Ty.rename_identity (varType context position)).symm ▸
                Term.var position)
             (Term.var position)
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := domainType) (codomainType := codomainType)
        functionTerm argumentTerm => by
    show HEq
      (Term.app (Term.rename (TermRenaming.identity context) functionTerm)
                (Term.rename (TermRenaming.identity context) argumentTerm))
      (Term.app functionTerm argumentTerm)
    exact Term.app_HEq_congr
      (Ty.rename_identity domainType) (Ty.rename_identity codomainType)
      _ _ (Term.rename_id_HEq functionTerm)
      _ _ (Term.rename_id_HEq argumentTerm)
  | _, .fst (firstType := firstType) (secondType := secondType) pairTerm => by
    show HEq
      (Term.fst (Term.rename (TermRenaming.identity context) pairTerm))
      (Term.fst pairTerm)
    apply Term.fst_HEq_congr
      (Ty.rename_identity firstType)
      ((Ty.rename_congr Renaming.lift_identity_equiv secondType).trans
        (Ty.rename_identity secondType))
    exact Term.rename_id_HEq pairTerm
  | _, .boolElim (resultType := resultType) scrutinee thenBranch elseBranch => by
    show HEq
      (Term.boolElim (Term.rename (TermRenaming.identity context) scrutinee)
                     (Term.rename (TermRenaming.identity context) thenBranch)
                     (Term.rename (TermRenaming.identity context) elseBranch))
      (Term.boolElim scrutinee thenBranch elseBranch)
    exact Term.boolElim_HEq_congr
      (Ty.rename_identity resultType)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq thenBranch)
      _ _ (Term.rename_id_HEq elseBranch)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        (argumentRaw := argumentRaw) resultEq functionTerm argumentTerm => by
    -- W9.B1.3a — Term.rename on termSingleton-flavored appPi yields a double cast.
    show HEq
      ((congrArg (Ty.rename · Renaming.identity) resultEq).symm ▸
        ((Ty.subst_termSingleton_rename_commute codomainType domainType
            argumentRaw Renaming.identity).symm ▸
          Term.appPi (argumentRaw := argumentRaw.rename Renaming.identity) rfl
            (Term.rename (TermRenaming.identity context) functionTerm)
            (Term.rename (TermRenaming.identity context) argumentTerm)))
      (Term.appPi resultEq functionTerm argumentTerm)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    cases resultEq
    exact Term.appPi_HEq_congr
      (Ty.rename_identity domainType)
      ((Ty.rename_congr Renaming.lift_identity_equiv codomainType).trans
        (Ty.rename_identity codomainType))
      (RawTerm.rename_identity (level := level) argumentRaw)
      _ _ (Term.rename_id_HEq functionTerm)
      _ _ (Term.rename_id_HEq argumentTerm)
  | _, .pair (firstType := firstType) (secondType := secondType)
        firstVal secondVal => by
    show HEq
      (Term.pair (Term.rename (TermRenaming.identity context) firstVal)
        ((Ty.subst0_rename_commute secondType firstType Renaming.identity) ▸
          (Term.rename (TermRenaming.identity context) secondVal)))
      (Term.pair firstVal secondVal)
    apply Term.pair_HEq_congr
      (Ty.rename_identity firstType)
      ((Ty.rename_congr Renaming.lift_identity_equiv secondType).trans
        (Ty.rename_identity secondType))
      _ _ (Term.rename_id_HEq firstVal)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.rename_id_HEq secondVal
  | _, .snd (firstType := firstType) (secondType := secondType)
        pairTerm resultEq => by
    -- W9.B1.2 — Term.rename on equation-bearing snd yields a double cast.
    show HEq
      ((congrArg (Ty.rename · Renaming.identity) resultEq).symm ▸
        ((Ty.subst0_rename_commute secondType firstType
            Renaming.identity).symm ▸
          Term.snd (Term.rename (TermRenaming.identity context) pairTerm) rfl))
      (Term.snd pairTerm resultEq)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    cases resultEq
    exact Term.snd_HEq_congr
      (Ty.rename_identity firstType)
      ((Ty.rename_congr Renaming.lift_identity_equiv secondType).trans
        (Ty.rename_identity secondType))
      _ _ (Term.rename_id_HEq pairTerm)
  | _, .lam (domainType := domainType) (codomainType := codomainType)
        lambdaBody => by
    show HEq
      (Term.lam (codomainType := codomainType.rename Renaming.identity)
        ((Ty.rename_weaken_commute codomainType Renaming.identity) ▸
          (Term.rename (TermRenaming.lift (TermRenaming.identity context) domainType)
            lambdaBody)))
      (Term.lam lambdaBody)
    apply Term.lam_HEq_congr
      (Ty.rename_identity domainType) (Ty.rename_identity codomainType)
    -- Strip outer cast.
    apply HEq.trans (eqRec_heq _ _)
    -- Bridge `TermRenaming.lift (identity Γ) dom` to
    -- `TermRenaming.identity (Γ.cons dom)` via rename_HEq_pointwise
    -- + Renaming.lift_identity_equiv, then recurse.
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg context.cons (Ty.rename_identity domainType))
        (TermRenaming.lift (TermRenaming.identity context) domainType)
        (TermRenaming.identity (context.cons domainType))
        Renaming.lift_identity_equiv
        lambdaBody)
    exact Term.rename_id_HEq lambdaBody
  | _, .lamPi (domainType := domainType) (codomainType := codomainType)
        lambdaBody => by
    show HEq
      (Term.lamPi
        (Term.rename (TermRenaming.lift (TermRenaming.identity context) domainType)
          lambdaBody))
      (Term.lamPi lambdaBody)
    apply Term.lamPi_HEq_congr
      (Ty.rename_identity domainType)
      ((Ty.rename_congr Renaming.lift_identity_equiv codomainType).trans
        (Ty.rename_identity codomainType))
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg context.cons (Ty.rename_identity domainType))
        (TermRenaming.lift (TermRenaming.identity context) domainType)
        (TermRenaming.identity (context.cons domainType))
        Renaming.lift_identity_equiv
        lambdaBody)
    exact Term.rename_id_HEq lambdaBody
  | _, .natZero => HEq.refl _
  | _, .natSucc predecessor =>
    Term.natSucc_HEq_congr _ _ (Term.rename_id_HEq predecessor)
  | _, .natElim (resultType := resultType) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename (TermRenaming.identity context) scrutinee)
        (Term.rename (TermRenaming.identity context) zeroBranch)
        (Term.rename (TermRenaming.identity context) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.rename_identity resultType)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .natRec (resultType := resultType) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_identity resultType)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .listNil (elementType := elementType) =>
    Term.listNil_HEq_congr (Ty.rename_identity elementType)
  | _, .listCons (elementType := elementType) head tail =>
    Term.listCons_HEq_congr
      (Ty.rename_identity elementType)
      _ _ (Term.rename_id_HEq head)
      _ _ (Term.rename_id_HEq tail)
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_identity elementType) (Ty.rename_identity resultType)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq nilBranch)
      _ _ (Term.rename_id_HEq consBranch)
  | _, .optionNone (elementType := elementType) =>
    Term.optionNone_HEq_congr (Ty.rename_identity elementType)
  | _, .optionSome (elementType := elementType) value =>
    Term.optionSome_HEq_congr
      (Ty.rename_identity elementType)
      _ _ (Term.rename_id_HEq value)
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_identity elementType) (Ty.rename_identity resultType)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq noneBranch)
      _ _ (Term.rename_id_HEq someBranch)
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInl_HEq_congr
      (Ty.rename_identity leftType) (Ty.rename_identity rightType)
      _ _ (Term.rename_id_HEq value)
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInr_HEq_congr
      (Ty.rename_identity leftType) (Ty.rename_identity rightType)
      _ _ (Term.rename_id_HEq value)
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
        (resultType := resultType)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_identity leftType) (Ty.rename_identity rightType)
      (Ty.rename_identity resultType)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq leftBranch)
      _ _ (Term.rename_id_HEq rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_identity carrier)
      (RawTerm.rename_identity (level := level) rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := resultType)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_identity carrier)
      (RawTerm.rename_identity (level := level) leftEnd)
      (RawTerm.rename_identity (level := level) rightEnd)
      (Ty.rename_identity resultType)
      _ _ (Term.rename_id_HEq baseCase)
      _ _ (Term.rename_id_HEq witness)

/-- The explicit-`▸` form of `Term.rename_id`: `eq_of_heq` plus an
outer cast strip.  Mirrors v1.25's `Term.subst_id` derivation from
`Term.subst_id_HEq`. -/
theorem Term.rename_id
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {tyValue : Ty level scope} (term : Term context tyValue) :
    (Ty.rename_identity tyValue) ▸
      Term.rename (TermRenaming.identity context) term = term :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.rename_id_HEq term))


end LeanFX.Syntax
