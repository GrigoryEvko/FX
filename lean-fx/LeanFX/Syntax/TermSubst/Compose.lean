import LeanFX.Syntax.TermSubst.Commute

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `TermSubst.lift_compose_pointwise` (full theorem).

Lifting commutes with TermSubst composition pointwise (HEq).
Position 0 delegates to the existing `lift_compose_pointwise_zero`
fragment.  Position `predecessor + 1` is the substantive case:

  * LHS at successor positions: `outer_subst_weaken_commute.symm ▸
    Term.weaken (newType.subst (Subst.compose firstTypeSubstitution
    secondTypeSubstitution)) (Ty.subst_compose ... ▸ Term.subst
    secondTermSubstitution (firstTermSubstitution predecessor))`.

  * RHS at successor positions: `outer_subst_compose ▸ Term.subst
    (secondTermSubstitution.lift (newType.subst firstTypeSubstitution))
    ((Ty.subst_weaken_commute ...).symm ▸ Term.weaken
    (newType.subst firstTypeSubstitution)
    (firstTermSubstitution predecessor))`.

The RHS inner reduces, via `Term.subst_HEq_cast_input` + v1.43
`Term.subst_weaken_commute_HEq`, to `Term.weaken ((newType.subst
firstTypeSubstitution).subst secondTypeSubstitution) (Term.subst
secondTermSubstitution (firstTermSubstitution predecessor))`.  The
two `Term.weaken` forms differ only by `Ty.subst_compose newType
firstTypeSubstitution secondTypeSubstitution` on the `newType` and
the per-position analogue on the inner type;
`Term.weaken_HEq_congr` closes via `eqRec_heq`. -/
theorem TermSubst.lift_compose_pointwise
    {mode : Mode} {level firstScope middleScope finalScope : Nat}
    {firstContext : Ctx mode level firstScope}
    {middleContext : Ctx mode level middleScope}
    {finalContext : Ctx mode level finalScope}
    {firstTypeSubstitution : Subst level firstScope middleScope}
    {secondTypeSubstitution : Subst level middleScope finalScope}
    (firstTermSubstitution :
      TermSubst firstContext middleContext firstTypeSubstitution)
    (secondTermSubstitution :
      TermSubst middleContext finalContext secondTypeSubstitution)
    (newType : Ty level firstScope) :
    ∀ (position : Fin (firstScope + 1)),
      HEq
        (TermSubst.lift
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          newType position)
        (TermSubst.compose (firstTermSubstitution.lift newType)
          (secondTermSubstitution.lift (newType.subst firstTypeSubstitution))
          position)
  | ⟨0, _⟩ =>
      TermSubst.lift_compose_pointwise_zero
        firstTermSubstitution secondTermSubstitution newType
  | ⟨predecessor + 1, succBound⟩ => by
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and strip outer cast on RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast on RHS through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (secondTermSubstitution.lift (newType.subst firstTypeSubstitution))
        (Ty.subst_weaken_commute
          (varType firstContext
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          firstTypeSubstitution).symm
        (Term.weaken (newType.subst firstTypeSubstitution)
          (firstTermSubstitution
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)))
    -- After helper: Term.subst (secondTermSubstitution.lift X)
    --   (Term.weaken X (firstTermSubstitution predecessor)).
    -- Apply v1.43 to get Term.weaken (X.subst secondTypeSubstitution)
    --   (Term.subst secondTermSubstitution
    --     (firstTermSubstitution predecessor)).
    apply HEq.trans
      (Term.subst_weaken_commute_HEq
        secondTermSubstitution (newType.subst firstTypeSubstitution)
        (firstTermSubstitution
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
    -- Flip back to LHS-orientation.
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.
    exact Term.weaken_HEq_congr
      (Ty.subst_compose newType firstTypeSubstitution secondTypeSubstitution).symm
      (Ty.subst_compose
        (varType firstContext
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
        firstTypeSubstitution secondTypeSubstitution).symm
      _ _ (eqRec_heq _ _)

/-! ## `Term.subst_compose`.

The cap-stone of substitution functoriality at the term level:

  Term.subst secondTermSubstitution (Term.subst firstTermSubstitution term)
    ≃HEq≃
  Term.subst (TermSubst.compose firstTermSubstitution secondTermSubstitution) term

Both sides have type `Term finalContext targetType` for
propositionally-equal `targetType`s (`((tyValue.subst
firstTypeSubstitution).subst secondTypeSubstitution)` vs
`tyValue.subst (Subst.compose firstTypeSubstitution
secondTypeSubstitution)`, bridged by `Ty.subst_compose`).  HEq
carries the difference.

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
    TermSubsts, then bridge `compose (lift firstTermSubstitution)
    (lift secondTermSubstitution)` against
    `lift (compose firstTermSubstitution secondTermSubstitution)`
    via `Term.subst_HEq_pointwise` (v1.24) over
    `TermSubst.lift_compose_pointwise` (v1.44).

Mirrors v1.40 / v1.42 with subst on both sides instead of mixed
subst+rename. -/
theorem Term.subst_compose_HEq
    {mode : Mode} {level firstScope middleScope finalScope : Nat}
    {firstContext : Ctx mode level firstScope}
    {middleContext : Ctx mode level middleScope}
    {finalContext : Ctx mode level finalScope}
    {firstTypeSubstitution : Subst level firstScope middleScope}
    {secondTypeSubstitution : Subst level middleScope finalScope}
    (firstTermSubstitution :
      TermSubst firstContext middleContext firstTypeSubstitution)
    (secondTermSubstitution :
      TermSubst middleContext finalContext secondTypeSubstitution) :
    {tyValue : Ty level firstScope} → (term : Term firstContext tyValue) →
      HEq
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution term))
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          term)
  | _, .var position => by
    show HEq
        (Term.subst secondTermSubstitution
          (firstTermSubstitution position))
        ((Ty.subst_compose
            (varType firstContext position)
            firstTypeSubstitution secondTypeSubstitution)
          ▸ Term.subst secondTermSubstitution
              (firstTermSubstitution position))
    exact (eqRec_heq _ _).symm
  | _, .unit       => HEq.refl _
  | _, .boolTrue   => HEq.refl _
  | _, .boolFalse  => HEq.refl _
  | _, .app (domainType := domainType) (codomainType := codomainType)
            functionTerm argumentTerm => by
    show HEq
      (Term.app (Term.subst secondTermSubstitution
                  (Term.subst firstTermSubstitution functionTerm))
                (Term.subst secondTermSubstitution
                  (Term.subst firstTermSubstitution argumentTerm)))
      (Term.app
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          functionTerm)
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          argumentTerm))
    exact Term.app_HEq_congr
      (Ty.subst_compose domainType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose codomainType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution functionTerm)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution argumentTerm)
  | _, .fst (firstType := firstType) (secondType := secondType)
            pairTerm => by
    show HEq
      (Term.fst (Term.subst secondTermSubstitution
                  (Term.subst firstTermSubstitution pairTerm)))
      (Term.fst (Term.subst
        (TermSubst.compose firstTermSubstitution secondTermSubstitution)
        pairTerm))
    apply Term.fst_HEq_congr
      (Ty.subst_compose firstType
        firstTypeSubstitution secondTypeSubstitution)
      ((Ty.subst_compose secondType
          firstTypeSubstitution.lift secondTypeSubstitution.lift).trans
        (Ty.subst_congr
          (Subst.lift_compose_equiv
            firstTypeSubstitution secondTypeSubstitution)
          secondType))
    exact Term.subst_compose_HEq
      firstTermSubstitution secondTermSubstitution pairTerm
  | _, .boolElim (resultType := resultType)
                  scrutinee thenBranch elseBranch => by
    show HEq
      (Term.boolElim
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution scrutinee))
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution thenBranch))
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution elseBranch)))
      (Term.boolElim
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          scrutinee)
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          thenBranch)
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          elseBranch))
    exact Term.boolElim_HEq_congr
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (eq_of_heq (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution scrutinee))
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution thenBranch)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution elseBranch)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
              resultEq functionTerm argumentTerm => by
    -- W9.B1.1 — equation-bearing appPi.  Cases on resultEq normalises shape.
    cases resultEq
    apply HEq.trans
      (Term.subst_HEq_cast_input secondTermSubstitution
        (Ty.subst0_subst_commute codomainType domainType
          firstTypeSubstitution).symm
        (Term.appPi rfl (Term.subst firstTermSubstitution functionTerm)
                        (Term.subst firstTermSubstitution argumentTerm)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.subst_compose domainType
        firstTypeSubstitution secondTypeSubstitution)
      ((Ty.subst_compose codomainType
          firstTypeSubstitution.lift secondTypeSubstitution.lift).trans
        (Ty.subst_congr
          (Subst.lift_compose_equiv
            firstTypeSubstitution secondTypeSubstitution)
          codomainType))
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution functionTerm)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution argumentTerm)
  | _, .pair (firstType := firstType) (secondType := secondType)
              firstVal secondVal => by
    apply Term.pair_HEq_congr
      (Ty.subst_compose firstType
        firstTypeSubstitution secondTypeSubstitution)
      ((Ty.subst_compose secondType
          firstTypeSubstitution.lift secondTypeSubstitution.lift).trans
        (Ty.subst_congr
          (Subst.lift_compose_equiv
            firstTypeSubstitution secondTypeSubstitution)
          secondType))
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution firstVal)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input secondTermSubstitution
        (Ty.subst0_subst_commute secondType firstType firstTypeSubstitution)
        (Term.subst firstTermSubstitution secondVal))
    apply HEq.trans
      (Term.subst_compose_HEq
        firstTermSubstitution secondTermSubstitution secondVal)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := firstType) (secondType := secondType)
            pairTerm resultEq => by
    -- W9.B1.2 — equation-bearing snd.  Mirror of appPi.
    cases resultEq
    apply HEq.trans
      (Term.subst_HEq_cast_input secondTermSubstitution
        (Ty.subst0_subst_commute secondType firstType
          firstTypeSubstitution).symm
        (Term.snd (Term.subst firstTermSubstitution pairTerm) rfl))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_compose firstType
        firstTypeSubstitution secondTypeSubstitution)
      ((Ty.subst_compose secondType
          firstTypeSubstitution.lift secondTypeSubstitution.lift).trans
        (Ty.subst_congr
          (Subst.lift_compose_equiv
            firstTypeSubstitution secondTypeSubstitution)
          secondType))
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution pairTerm)
  | _, .lam (domainType := domainType) (codomainType := codomainType)
            body => by
    apply Term.lam_HEq_congr
      (Ty.subst_compose domainType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose codomainType
        firstTypeSubstitution secondTypeSubstitution)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift secondTermSubstitution
          (domainType.subst firstTypeSubstitution))
        (Ty.subst_weaken_commute codomainType firstTypeSubstitution)
        (Term.subst (TermSubst.lift firstTermSubstitution domainType)
          body))
    -- IH on body with the lifts.
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift firstTermSubstitution domainType)
        (TermSubst.lift secondTermSubstitution
          (domainType.subst firstTypeSubstitution))
        body)
    -- Bridge compose-of-lifts to lift-of-compose.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg finalContext.cons
        (Ty.subst_compose domainType
          firstTypeSubstitution secondTypeSubstitution))
      (TermSubst.compose
        (TermSubst.lift firstTermSubstitution domainType)
        (TermSubst.lift secondTermSubstitution
          (domainType.subst firstTypeSubstitution)))
      (TermSubst.lift
        (TermSubst.compose firstTermSubstitution secondTermSubstitution)
        domainType)
      (Subst.lift_compose_equiv
        firstTypeSubstitution secondTypeSubstitution)
      (fun position =>
        (TermSubst.lift_compose_pointwise
          firstTermSubstitution secondTermSubstitution domainType
          position).symm)
      body
  | _, .lamPi (domainType := domainType) (codomainType := codomainType)
              body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_compose domainType
        firstTypeSubstitution secondTypeSubstitution)
      ((Ty.subst_compose codomainType
          firstTypeSubstitution.lift secondTypeSubstitution.lift).trans
        (Ty.subst_congr
          (Subst.lift_compose_equiv
            firstTypeSubstitution secondTypeSubstitution)
          codomainType))
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift firstTermSubstitution domainType)
        (TermSubst.lift secondTermSubstitution
          (domainType.subst firstTypeSubstitution))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg finalContext.cons
        (Ty.subst_compose domainType
          firstTypeSubstitution secondTypeSubstitution))
      (TermSubst.compose
        (TermSubst.lift firstTermSubstitution domainType)
        (TermSubst.lift secondTermSubstitution
          (domainType.subst firstTypeSubstitution)))
      (TermSubst.lift
        (TermSubst.compose firstTermSubstitution secondTermSubstitution)
        domainType)
      (Subst.lift_compose_equiv
        firstTypeSubstitution secondTypeSubstitution)
      (fun position =>
        (TermSubst.lift_compose_pointwise
          firstTermSubstitution secondTermSubstitution domainType
          position).symm)
      body
  | _, .natZero       => HEq.refl _
  | _, .natSucc predecessor =>
    Term.natSucc_HEq_congr _ _
      (Term.subst_compose_HEq
        firstTermSubstitution secondTermSubstitution predecessor)
  | _, .natElim (resultType := resultType)
                scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution scrutinee))
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution zeroBranch))
        (Term.subst secondTermSubstitution
          (Term.subst firstTermSubstitution succBranch)))
      (Term.natElim
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          scrutinee)
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          zeroBranch)
        (Term.subst
          (TermSubst.compose firstTermSubstitution secondTermSubstitution)
          succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (eq_of_heq (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution scrutinee))
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution zeroBranch)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution succBranch)
  | _, .natRec (resultType := resultType)
                scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (eq_of_heq (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution scrutinee))
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution zeroBranch)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution succBranch)
  | _, .listNil (elementType := elementType) =>
    Term.listNil_HEq_congr
      (Ty.subst_compose elementType
        firstTypeSubstitution secondTypeSubstitution)
  | _, .listCons (elementType := elementType) headValue tailValue =>
    Term.listCons_HEq_congr
      (Ty.subst_compose elementType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution headValue)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution tailValue)
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_compose elementType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution scrutinee)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution nilBranch)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution consBranch)
  | _, .optionNone (elementType := elementType) =>
    Term.optionNone_HEq_congr
      (Ty.subst_compose elementType
        firstTypeSubstitution secondTypeSubstitution)
  | _, .optionSome (elementType := elementType) value =>
    Term.optionSome_HEq_congr
      (Ty.subst_compose elementType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution value)
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_compose elementType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution scrutinee)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution noneBranch)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution someBranch)
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInl_HEq_congr
      (Ty.subst_compose leftType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose rightType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution value)
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInr_HEq_congr
      (Ty.subst_compose leftType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose rightType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution value)
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
                    (resultType := resultType)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_compose leftType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose rightType
        firstTypeSubstitution secondTypeSubstitution)
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution scrutinee)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution leftBranch)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.subst_compose carrier
        firstTypeSubstitution secondTypeSubstitution)
      (RawTerm.subst_compose rawTerm
        firstTypeSubstitution.forRaw secondTypeSubstitution.forRaw)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := resultType)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_compose carrier
        firstTypeSubstitution secondTypeSubstitution)
      (RawTerm.subst_compose leftEnd
        firstTypeSubstitution.forRaw secondTypeSubstitution.forRaw)
      (RawTerm.subst_compose rightEnd
        firstTypeSubstitution.forRaw secondTypeSubstitution.forRaw)
      (Ty.subst_compose resultType
        firstTypeSubstitution secondTypeSubstitution)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution baseCase)
      _ _ (Term.subst_compose_HEq
            firstTermSubstitution secondTermSubstitution witness)

/-- The explicit-`▸` form of `Term.subst_compose`: `eq_of_heq` plus
the outer cast strip.  Mirrors the v1.25 derivation of `Term.subst_id`
from `Term.subst_id_HEq`. -/
theorem Term.subst_compose
    {mode : Mode} {level firstScope middleScope finalScope : Nat}
    {firstContext : Ctx mode level firstScope}
    {middleContext : Ctx mode level middleScope}
    {finalContext : Ctx mode level finalScope}
    {firstTypeSubstitution : Subst level firstScope middleScope}
    {secondTypeSubstitution : Subst level middleScope finalScope}
    (firstTermSubstitution :
      TermSubst firstContext middleContext firstTypeSubstitution)
    (secondTermSubstitution :
      TermSubst middleContext finalContext secondTypeSubstitution)
    {tyValue : Ty level firstScope} (term : Term firstContext tyValue) :
    Term.subst secondTermSubstitution (Term.subst firstTermSubstitution term)
      = (Ty.subst_compose tyValue
            firstTypeSubstitution secondTypeSubstitution).symm
          ▸ Term.subst
              (TermSubst.compose firstTermSubstitution secondTermSubstitution)
              term :=
  eq_of_heq
    ((Term.subst_compose_HEq
        firstTermSubstitution secondTermSubstitution term).trans
      (eqRec_heq _ _).symm)


end LeanFX.Syntax
