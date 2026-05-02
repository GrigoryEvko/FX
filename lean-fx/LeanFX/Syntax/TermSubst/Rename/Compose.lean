import LeanFX.Syntax.TermSubst.Rename.Identity

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-rename composition. -/

/-- Composition of term-level renamings.  Position-equality witness
chains the two `TermRenaming`s through `Ty.rename_compose`. -/
theorem TermRenaming.compose
    {mode : Mode} {level firstScope middleScope finalScope : Nat}
    {firstContext : Ctx mode level firstScope}
    {middleContext : Ctx mode level middleScope}
    {finalContext : Ctx mode level finalScope}
    {firstRawRenaming : Renaming firstScope middleScope}
    {secondRawRenaming : Renaming middleScope finalScope}
    (firstTermRenaming :
      TermRenaming firstContext middleContext firstRawRenaming)
    (secondTermRenaming :
      TermRenaming middleContext finalContext secondRawRenaming) :
    TermRenaming firstContext finalContext
      (Renaming.compose firstRawRenaming secondRawRenaming) := fun position => by
  show varType finalContext (secondRawRenaming (firstRawRenaming position))
     = (varType firstContext position).rename
         (Renaming.compose firstRawRenaming secondRawRenaming)
  rw [secondTermRenaming (firstRawRenaming position)]
  rw [firstTermRenaming position]
  exact Ty.rename_compose (varType firstContext position)
    firstRawRenaming secondRawRenaming

/-- Push a propositional type-cast on the input of `Term.rename termRenaming`
out to an HEq.  Mirror of `Term.subst_HEq_cast_input` and
`Term.weaken_HEq_cast_input`. -/
theorem Term.rename_HEq_cast_input
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceContext targetContext rawRenaming)
    {sourceTy targetTy : Ty level sourceScope} (typeEq : sourceTy = targetTy)
    (term : Term sourceContext sourceTy) :
    HEq (Term.rename termRenaming (typeEq ▸ term))
        (Term.rename termRenaming term) := by
  cases typeEq
  rfl

/-! ## `Term.rename_compose_HEq`.

Double-rename equals single-rename by composed rawRenaming, modulo HEq.
The two sides have types `Term Γ₃ ((T.rename ρ₁).rename ρ₂)` and
`Term Γ₃ (T.rename (Renaming.compose ρ₁ ρ₂))`; these agree
propositionally by `Ty.rename_compose`.  Pattern-matched structural
induction on the term.

Binder cases bridge `TermRenaming.lift (compose firstTermRenaming
secondTermRenaming) dom` against `compose (lift firstTermRenaming dom)
(lift secondTermRenaming (dom.rename firstRawRenaming))` via
`Term.rename_HEq_pointwise` over `Renaming.lift_compose_equiv`. -/
theorem Term.rename_compose_HEq
    {mode : Mode} {level firstScope middleScope finalScope : Nat}
    {firstContext : Ctx mode level firstScope}
    {middleContext : Ctx mode level middleScope}
    {finalContext : Ctx mode level finalScope}
    {firstRawRenaming : Renaming firstScope middleScope}
    {secondRawRenaming : Renaming middleScope finalScope}
    (firstTermRenaming :
      TermRenaming firstContext middleContext firstRawRenaming)
    (secondTermRenaming :
      TermRenaming middleContext finalContext secondRawRenaming) :
    {tyValue : Ty level firstScope} → (term : Term firstContext tyValue) →
      HEq (Term.rename secondTermRenaming (Term.rename firstTermRenaming term))
          (Term.rename
            (TermRenaming.compose firstTermRenaming secondTermRenaming) term)
  | _, .var position => by
    -- LHS: Term.rename secondTermRenaming
    --        ((firstTermRenaming i) ▸ Term.var (firstRawRenaming i))
    -- Push the inner cast through Term.rename secondTermRenaming.
    apply HEq.trans
      (Term.rename_HEq_cast_input secondTermRenaming
        (firstTermRenaming position) (Term.var (firstRawRenaming position)))
    -- Now: Term.rename secondTermRenaming (Term.var (firstRawRenaming i))
    --    = (secondTermRenaming (firstRawRenaming i))
    --        ▸ Term.var (secondRawRenaming (firstRawRenaming i))
    -- RHS: ((compose firstTermRenaming secondTermRenaming) i)
    --        ▸ Term.var ((Renaming.compose firstRawRenaming secondRawRenaming) i)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := domainType) (codomainType := codomainType)
        functionTerm argumentTerm => by
    show HEq
      (Term.app (Term.rename secondTermRenaming
                  (Term.rename firstTermRenaming functionTerm))
                (Term.rename secondTermRenaming
                  (Term.rename firstTermRenaming argumentTerm)))
      (Term.app (Term.rename
                  (TermRenaming.compose firstTermRenaming secondTermRenaming)
                  functionTerm)
                (Term.rename
                  (TermRenaming.compose firstTermRenaming secondTermRenaming)
                  argumentTerm))
    exact Term.app_HEq_congr
      (Ty.rename_compose domainType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose codomainType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming functionTerm)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming argumentTerm)
  | _, .fst (firstType := firstType) (secondType := secondType) pairTerm => by
    show HEq
      (Term.fst (Term.rename secondTermRenaming
                  (Term.rename firstTermRenaming pairTerm)))
      (Term.fst (Term.rename
                  (TermRenaming.compose firstTermRenaming secondTermRenaming)
                  pairTerm))
    apply Term.fst_HEq_congr
      (Ty.rename_compose firstType firstRawRenaming secondRawRenaming)
      ((Ty.rename_compose secondType firstRawRenaming.lift
          secondRawRenaming.lift).trans
        (Ty.rename_congr
          (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
          secondType))
    exact Term.rename_compose_HEq firstTermRenaming secondTermRenaming pairTerm
  | _, .boolElim (resultType := resultType) scrutinee thenBranch elseBranch => by
    show HEq
      (Term.boolElim (Term.rename secondTermRenaming
                       (Term.rename firstTermRenaming scrutinee))
                     (Term.rename secondTermRenaming
                       (Term.rename firstTermRenaming thenBranch))
                     (Term.rename secondTermRenaming
                       (Term.rename firstTermRenaming elseBranch)))
      (Term.boolElim (Term.rename
                       (TermRenaming.compose firstTermRenaming secondTermRenaming)
                       scrutinee)
                     (Term.rename
                       (TermRenaming.compose firstTermRenaming secondTermRenaming)
                       thenBranch)
                     (Term.rename
                       (TermRenaming.compose firstTermRenaming secondTermRenaming)
                       elseBranch))
    exact Term.boolElim_HEq_congr
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (eq_of_heq
        (Term.rename_compose_HEq firstTermRenaming secondTermRenaming scrutinee))
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming thenBranch)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming elseBranch)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        resultEq functionTerm argumentTerm => by
    -- W9.B1.1 — equation-bearing appPi.  Because resultEq is propositional,
    -- cases on resultEq once normalises resultType := codomain.subst0 domain
    -- on both sides.  The remaining casts are subst0_rename_commute on each
    -- rename layer.  Use rename_HEq_cast_input + cong with rfl-resultEq
    -- both cancel via eqRec_heq.
    cases resultEq
    -- Total casts: LHS has rename second (rename first (rfl-cast ▸ subst0-cast ▸ appPi)).
    -- Inner rfl-cast vanishes; then rename second processes (subst0-cast ▸ appPi).
    -- Use Term.rename_HEq_cast_input on the outer.
    apply HEq.trans
      (Term.rename_HEq_cast_input secondTermRenaming
        (Ty.subst0_rename_commute codomainType domainType firstRawRenaming).symm
        (Term.appPi rfl (Term.rename firstTermRenaming functionTerm)
                        (Term.rename firstTermRenaming argumentTerm)))
    -- LHS now: rename second (appPi rfl ...) which unfolds to:
    --   (rfl-cast ▸ subst0-cast ▸ appPi rfl rename rename)
    -- The rfl-cast is congrArg of rfl, which is rfl on the function level,
    -- so its `▸` is actually the identity. Thus only ONE actual cast remains.
    apply HEq.trans (eqRec_heq _ _)
    -- LHS now: appPi rfl (rename second (rename first f)) (rename second (rename first a))
    -- RHS: rename compose (appPi rfl f a) = rfl-cast ▸ subst0-cast ▸ appPi rfl (rename compose f) (rename compose a)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.rename_compose domainType firstRawRenaming secondRawRenaming)
      ((Ty.rename_compose codomainType firstRawRenaming.lift
          secondRawRenaming.lift).trans
        (Ty.rename_congr
          (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
          codomainType))
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming functionTerm)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming argumentTerm)
  | _, .pair (firstType := firstType) (secondType := secondType)
        firstVal secondVal => by
    -- Outer Term.pair has no cast; secondVal carries nested casts on both sides.
    apply Term.pair_HEq_congr
      (Ty.rename_compose firstType firstRawRenaming secondRawRenaming)
      ((Ty.rename_compose secondType firstRawRenaming.lift
          secondRawRenaming.lift).trans
        (Ty.rename_congr
          (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
          secondType))
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming firstVal)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.rename secondTermRenaming.
    apply HEq.trans
      (Term.rename_HEq_cast_input secondTermRenaming
        (Ty.subst0_rename_commute secondType firstType firstRawRenaming)
        (Term.rename firstTermRenaming secondVal))
    -- Use IH on secondVal.
    apply HEq.trans
      (Term.rename_compose_HEq firstTermRenaming secondTermRenaming secondVal)
    -- Strip outer cast on RHS.
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := firstType) (secondType := secondType) pairTerm => by
    -- Mirror of fst plus outer cast strips on each side.
    apply HEq.trans
      (Term.rename_HEq_cast_input secondTermRenaming
        (Ty.subst0_rename_commute secondType firstType firstRawRenaming).symm
        (Term.snd (Term.rename firstTermRenaming pairTerm)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_compose firstType firstRawRenaming secondRawRenaming)
      ((Ty.rename_compose secondType firstRawRenaming.lift
          secondRawRenaming.lift).trans
        (Ty.rename_congr
          (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
          secondType))
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming pairTerm)
  | _, .lam (domainType := domainType) (codomainType := codomainType)
        lambdaBody => by
    apply Term.lam_HEq_congr
      (Ty.rename_compose domainType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose codomainType firstRawRenaming secondRawRenaming)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift secondTermRenaming
    --                                     (domainType.rename firstRawRenaming)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift secondTermRenaming
          (domainType.rename firstRawRenaming))
        (Ty.rename_weaken_commute codomainType firstRawRenaming)
        (Term.rename (TermRenaming.lift firstTermRenaming domainType) lambdaBody))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift firstTermRenaming domainType)
        (TermRenaming.lift secondTermRenaming (domainType.rename firstRawRenaming))
        lambdaBody)
    -- Bridge compose-of-lifts to lift-of-compose via rename_HEq_pointwise.
    apply HEq.symm
    -- Strip outer cast on RHS (now in symm orientation).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.rename_HEq_pointwise
      (congrArg finalContext.cons
        (Ty.rename_compose domainType firstRawRenaming secondRawRenaming))
      (TermRenaming.compose
        (TermRenaming.lift firstTermRenaming domainType)
        (TermRenaming.lift secondTermRenaming (domainType.rename firstRawRenaming)))
      (TermRenaming.lift
        (TermRenaming.compose firstTermRenaming secondTermRenaming) domainType)
      (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
      lambdaBody
  | _, .lamPi (domainType := domainType) (codomainType := codomainType)
        lambdaBody => by
    apply Term.lamPi_HEq_congr
      (Ty.rename_compose domainType firstRawRenaming secondRawRenaming)
      ((Ty.rename_compose codomainType firstRawRenaming.lift
          secondRawRenaming.lift).trans
        (Ty.rename_congr
          (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
          codomainType))
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift firstTermRenaming domainType)
        (TermRenaming.lift secondTermRenaming (domainType.rename firstRawRenaming))
        lambdaBody)
    exact Term.rename_HEq_pointwise
      (congrArg finalContext.cons
        (Ty.rename_compose domainType firstRawRenaming secondRawRenaming))
      (TermRenaming.compose
        (TermRenaming.lift firstTermRenaming domainType)
        (TermRenaming.lift secondTermRenaming (domainType.rename firstRawRenaming)))
      (TermRenaming.lift
        (TermRenaming.compose firstTermRenaming secondTermRenaming) domainType)
      (Renaming.lift_compose_equiv firstRawRenaming secondRawRenaming)
      lambdaBody
  | _, .natZero => HEq.refl _
  | _, .natSucc predecessor =>
    Term.natSucc_HEq_congr _ _
      (Term.rename_compose_HEq firstTermRenaming secondTermRenaming predecessor)
  | _, .natElim (resultType := resultType) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename secondTermRenaming (Term.rename firstTermRenaming scrutinee))
        (Term.rename secondTermRenaming (Term.rename firstTermRenaming zeroBranch))
        (Term.rename secondTermRenaming (Term.rename firstTermRenaming succBranch)))
      (Term.natElim
        (Term.rename
          (TermRenaming.compose firstTermRenaming secondTermRenaming) scrutinee)
        (Term.rename
          (TermRenaming.compose firstTermRenaming secondTermRenaming) zeroBranch)
        (Term.rename
          (TermRenaming.compose firstTermRenaming secondTermRenaming) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (eq_of_heq
        (Term.rename_compose_HEq firstTermRenaming secondTermRenaming scrutinee))
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming zeroBranch)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming succBranch)
  | _, .natRec (resultType := resultType) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (eq_of_heq
        (Term.rename_compose_HEq firstTermRenaming secondTermRenaming scrutinee))
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming zeroBranch)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming succBranch)
  | _, .listNil (elementType := elementType) =>
    Term.listNil_HEq_congr
      (Ty.rename_compose elementType firstRawRenaming secondRawRenaming)
  | _, .listCons (elementType := elementType) head tail =>
    Term.listCons_HEq_congr
      (Ty.rename_compose elementType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming head)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming tail)
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_compose elementType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming scrutinee)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming nilBranch)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming consBranch)
  | _, .optionNone (elementType := elementType) =>
    Term.optionNone_HEq_congr
      (Ty.rename_compose elementType firstRawRenaming secondRawRenaming)
  | _, .optionSome (elementType := elementType) value =>
    Term.optionSome_HEq_congr
      (Ty.rename_compose elementType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming value)
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_compose elementType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming scrutinee)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming noneBranch)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming someBranch)
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInl_HEq_congr
      (Ty.rename_compose leftType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose rightType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming value)
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInr_HEq_congr
      (Ty.rename_compose leftType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose rightType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming value)
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
        (resultType := resultType)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_compose leftType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose rightType firstRawRenaming secondRawRenaming)
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming scrutinee)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming leftBranch)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr
      (Ty.rename_compose carrier firstRawRenaming secondRawRenaming)
      (RawTerm.rename_compose rawTerm firstRawRenaming secondRawRenaming)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := resultType)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.rename_compose carrier firstRawRenaming secondRawRenaming)
      (RawTerm.rename_compose leftEnd firstRawRenaming secondRawRenaming)
      (RawTerm.rename_compose rightEnd firstRawRenaming secondRawRenaming)
      (Ty.rename_compose resultType firstRawRenaming secondRawRenaming)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming baseCase)
      _ _ (Term.rename_compose_HEq firstTermRenaming secondTermRenaming witness)


end LeanFX.Syntax
