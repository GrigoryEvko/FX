import LeanFX.Syntax.TermSubst.Pointwise

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.rename_HEq_pointwise`.

Two TermRenamings whose underlying Renamings agree pointwise produce
HEq results when applied to the same term.  The rawRenaming-side analogue
of `Term.subst_HEq_pointwise`.  The `targetContextEq : firstTargetContext
= secondTargetContext` parameter accommodates the binder cases, where
`TermRenaming.lift termRenaming_i domainType` lands in
`targetContext_i.cons (domainType.rename rawRenaming_i)` — different
cons-extensions across i = 1, 2. -/
theorem Term.rename_HEq_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {firstTargetContext secondTargetContext : Ctx mode level targetScope}
    (targetContextEq : firstTargetContext = secondTargetContext)
    {firstRawRenaming secondRawRenaming : Renaming sourceScope targetScope}
    (firstTermRenaming :
      TermRenaming sourceContext firstTargetContext firstRawRenaming)
    (secondTermRenaming :
      TermRenaming sourceContext secondTargetContext secondRawRenaming)
    (rawRenamingsAgreePointwise :
      Renaming.equiv firstRawRenaming secondRawRenaming) :
    {tyValue : Ty level sourceScope} → (term : Term sourceContext tyValue) →
      HEq (Term.rename firstTermRenaming term)
          (Term.rename secondTermRenaming term)
  | _, .var position => by
    cases targetContextEq
    -- Term.rename firstTermRenaming (Term.var i) =
    --   (firstTermRenaming i) ▸ Term.var (firstRawRenaming i)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Goal: HEq (Term.var (firstRawRenaming i)) (Term.var (secondRawRenaming i))
    -- Use rawRenamingsAgreePointwise i to align the Fin positions.
    rw [rawRenamingsAgreePointwise position]
  | _, .unit => by term_context_refl
  | _, .app functionTerm argumentTerm => by
    cases targetContextEq
    show HEq
      (Term.app (Term.rename firstTermRenaming functionTerm)
                (Term.rename firstTermRenaming argumentTerm))
      (Term.app (Term.rename secondTermRenaming functionTerm)
                (Term.rename secondTermRenaming argumentTerm))
    exact Term.app_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise _)
      (Ty.rename_congr rawRenamingsAgreePointwise _)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise functionTerm)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise argumentTerm)
  | _, .fst (firstType := firstType) (secondType := secondType) pairTerm => by
    cases targetContextEq
    show HEq
      (Term.fst (Term.rename firstTermRenaming pairTerm))
      (Term.fst (Term.rename secondTermRenaming pairTerm))
    apply Term.fst_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise firstType)
      (Ty.rename_congr (Renaming.lift_equiv rawRenamingsAgreePointwise) secondType)
    exact Term.rename_HEq_pointwise rfl firstTermRenaming
      secondTermRenaming rawRenamingsAgreePointwise pairTerm
  | _, .boolTrue => by term_context_refl
  | _, .boolFalse => by term_context_refl
  | _, .boolElim (resultType := resultType) scrutinee thenBranch elseBranch => by
    cases targetContextEq
    show HEq
      (Term.boolElim (Term.rename firstTermRenaming scrutinee)
                     (Term.rename firstTermRenaming thenBranch)
                     (Term.rename firstTermRenaming elseBranch))
      (Term.boolElim (Term.rename secondTermRenaming scrutinee)
                     (Term.rename secondTermRenaming thenBranch)
                     (Term.rename secondTermRenaming elseBranch))
    exact Term.boolElim_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise thenBranch)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise elseBranch)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        functionTerm argumentTerm => by
    cases targetContextEq
    show HEq
      ((Ty.subst0_rename_commute codomainType domainType firstRawRenaming).symm ▸
        Term.appPi (Term.rename firstTermRenaming functionTerm)
                   (Term.rename firstTermRenaming argumentTerm))
      ((Ty.subst0_rename_commute codomainType domainType secondRawRenaming).symm ▸
        Term.appPi (Term.rename secondTermRenaming functionTerm)
                   (Term.rename secondTermRenaming argumentTerm))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.rename secondTermRenaming functionTerm)
                 (Term.rename secondTermRenaming argumentTerm))
    · exact Term.appPi_HEq_congr
        (Ty.rename_congr rawRenamingsAgreePointwise domainType)
        (Ty.rename_congr (Renaming.lift_equiv rawRenamingsAgreePointwise) codomainType)
        _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
              secondTermRenaming rawRenamingsAgreePointwise functionTerm)
        _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
              secondTermRenaming rawRenamingsAgreePointwise argumentTerm)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := firstType) (secondType := secondType) firstVal secondVal => by
    cases targetContextEq
    show HEq
      (Term.pair (Term.rename firstTermRenaming firstVal)
        ((Ty.subst0_rename_commute secondType firstType firstRawRenaming) ▸
          (Term.rename firstTermRenaming secondVal)))
      (Term.pair (Term.rename secondTermRenaming firstVal)
        ((Ty.subst0_rename_commute secondType firstType secondRawRenaming) ▸
          (Term.rename secondTermRenaming secondVal)))
    apply Term.pair_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise firstType)
      (Ty.rename_congr (Renaming.lift_equiv rawRenamingsAgreePointwise) secondType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise firstVal)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise rfl firstTermRenaming
        secondTermRenaming rawRenamingsAgreePointwise secondVal)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := firstType) (secondType := secondType) pairTerm => by
    cases targetContextEq
    show HEq
      ((Ty.subst0_rename_commute secondType firstType firstRawRenaming).symm ▸
        Term.snd (Term.rename firstTermRenaming pairTerm))
      ((Ty.subst0_rename_commute secondType firstType secondRawRenaming).symm ▸
        Term.snd (Term.rename secondTermRenaming pairTerm))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.rename secondTermRenaming pairTerm))
    · exact Term.snd_HEq_congr
        (Ty.rename_congr rawRenamingsAgreePointwise firstType)
        (Ty.rename_congr (Renaming.lift_equiv rawRenamingsAgreePointwise) secondType)
        _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
              secondTermRenaming rawRenamingsAgreePointwise pairTerm)
    · exact (eqRec_heq _ _).symm
  | _, .lam (domainType := domainType) (codomainType := codomainType) lambdaBody => by
    cases targetContextEq
    show HEq
      (Term.lam (codomainType := codomainType.rename firstRawRenaming)
        ((Ty.rename_weaken_commute codomainType firstRawRenaming) ▸
          (Term.rename (TermRenaming.lift firstTermRenaming domainType) lambdaBody)))
      (Term.lam (codomainType := codomainType.rename secondRawRenaming)
        ((Ty.rename_weaken_commute codomainType secondRawRenaming) ▸
          (Term.rename (TermRenaming.lift secondTermRenaming domainType) lambdaBody)))
    apply Term.lam_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise domainType)
      (Ty.rename_congr rawRenamingsAgreePointwise codomainType)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg (·.cons (domainType.rename firstRawRenaming))
            (rfl : firstTargetContext = firstTargetContext) |>.trans
          (congrArg firstTargetContext.cons
            (Ty.rename_congr rawRenamingsAgreePointwise domainType)))
        (TermRenaming.lift firstTermRenaming domainType)
        (TermRenaming.lift secondTermRenaming domainType)
        (Renaming.lift_equiv rawRenamingsAgreePointwise)
        lambdaBody)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := domainType) (codomainType := codomainType) lambdaBody => by
    cases targetContextEq
    show HEq
      (Term.lamPi (Term.rename
        (TermRenaming.lift firstTermRenaming domainType) lambdaBody))
      (Term.lamPi (Term.rename
        (TermRenaming.lift secondTermRenaming domainType) lambdaBody))
    apply Term.lamPi_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise domainType)
      (Ty.rename_congr (Renaming.lift_equiv rawRenamingsAgreePointwise) codomainType)
    exact Term.rename_HEq_pointwise
      (congrArg firstTargetContext.cons
        (Ty.rename_congr rawRenamingsAgreePointwise domainType))
      (TermRenaming.lift firstTermRenaming domainType)
      (TermRenaming.lift secondTermRenaming domainType)
      (Renaming.lift_equiv rawRenamingsAgreePointwise)
      lambdaBody
  | _, .natZero => by term_context_refl
  | _, .natSucc predecessor => by
    cases targetContextEq
    show HEq (Term.natSucc (Term.rename firstTermRenaming predecessor))
             (Term.natSucc (Term.rename secondTermRenaming predecessor))
    exact Term.natSucc_HEq_congr _ _
      (Term.rename_HEq_pointwise rfl firstTermRenaming
        secondTermRenaming rawRenamingsAgreePointwise predecessor)
  | _, .natElim (resultType := resultType) scrutinee zeroBranch succBranch => by
    cases targetContextEq
    show HEq
      (Term.natElim (Term.rename firstTermRenaming scrutinee)
                    (Term.rename firstTermRenaming zeroBranch)
                    (Term.rename firstTermRenaming succBranch))
      (Term.natElim (Term.rename secondTermRenaming scrutinee)
                    (Term.rename secondTermRenaming zeroBranch)
                    (Term.rename secondTermRenaming succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise succBranch)
  | _, .natRec (resultType := resultType) scrutinee zeroBranch succBranch => by
    cases targetContextEq
    exact Term.natRec_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise succBranch)
  | _, .listNil (elementType := elementType) => by
    cases targetContextEq
    exact Term.listNil_HEq_congr (Ty.rename_congr rawRenamingsAgreePointwise elementType)
  | _, .listCons (elementType := elementType) head tail => by
    cases targetContextEq
    show HEq
      (Term.listCons (Term.rename firstTermRenaming head)
                     (Term.rename firstTermRenaming tail))
      (Term.listCons (Term.rename secondTermRenaming head)
                     (Term.rename secondTermRenaming tail))
    exact Term.listCons_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise elementType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise head)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise tail)
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch => by
    cases targetContextEq
    show HEq
      (Term.listElim (Term.rename firstTermRenaming scrutinee)
                     (Term.rename firstTermRenaming nilBranch)
                     (Term.rename firstTermRenaming consBranch))
      (Term.listElim (Term.rename secondTermRenaming scrutinee)
                     (Term.rename secondTermRenaming nilBranch)
                     (Term.rename secondTermRenaming consBranch))
    exact Term.listElim_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise elementType)
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise nilBranch)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise consBranch)
  | _, .optionNone (elementType := elementType) => by
    cases targetContextEq
    exact Term.optionNone_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise elementType)
  | _, .optionSome (elementType := elementType) value => by
    cases targetContextEq
    show HEq (Term.optionSome (Term.rename firstTermRenaming value))
             (Term.optionSome (Term.rename secondTermRenaming value))
    exact Term.optionSome_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise elementType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise value)
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch => by
    cases targetContextEq
    show HEq
      (Term.optionMatch (Term.rename firstTermRenaming scrutinee)
                        (Term.rename firstTermRenaming noneBranch)
                        (Term.rename firstTermRenaming someBranch))
      (Term.optionMatch (Term.rename secondTermRenaming scrutinee)
                        (Term.rename secondTermRenaming noneBranch)
                        (Term.rename secondTermRenaming someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise elementType)
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise noneBranch)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise someBranch)
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value => by
    cases targetContextEq
    exact Term.eitherInl_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise leftType)
      (Ty.rename_congr rawRenamingsAgreePointwise rightType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise value)
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value => by
    cases targetContextEq
    exact Term.eitherInr_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise leftType)
      (Ty.rename_congr rawRenamingsAgreePointwise rightType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise value)
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
        (resultType := resultType)
        scrutinee leftBranch rightBranch => by
    cases targetContextEq
    exact Term.eitherMatch_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise leftType)
      (Ty.rename_congr rawRenamingsAgreePointwise rightType)
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise leftBranch)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise rightBranch)
  | _, .refl (carrier := carrier) rawTerm => by
    cases targetContextEq
    exact Term.refl_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise carrier)
      (RawTerm.rename_congr rawRenamingsAgreePointwise rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := resultType)
            baseCase witness => by
    cases targetContextEq
    exact Term.idJ_HEq_congr
      (Ty.rename_congr rawRenamingsAgreePointwise carrier)
      (RawTerm.rename_congr rawRenamingsAgreePointwise leftEnd)
      (RawTerm.rename_congr rawRenamingsAgreePointwise rightEnd)
      (Ty.rename_congr rawRenamingsAgreePointwise resultType)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise baseCase)
      _ _ (Term.rename_HEq_pointwise rfl firstTermRenaming
            secondTermRenaming rawRenamingsAgreePointwise witness)


end LeanFX.Syntax
