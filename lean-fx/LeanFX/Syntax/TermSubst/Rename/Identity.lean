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


end LeanFX.Syntax
