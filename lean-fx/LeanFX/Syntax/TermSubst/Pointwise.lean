import LeanFX.Syntax.TermSubst.HEqCongr

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `TermSubst.lift_HEq_pointwise`.

Pointwise HEq for the lifts of two TermSubsts that are pointwise HEq
themselves (and whose underlying Substs are pointwise equal).  Used
by the binder cases of `Term.subst_HEq_pointwise` to extend the
hypothesis under each new binder. -/
theorem TermSubst.lift_HEq_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {firstTypeSubstitution secondTypeSubstitution :
      Subst level sourceScope targetScope}
    (firstTermSubstitution :
      TermSubst sourceContext targetContext firstTypeSubstitution)
    (secondTermSubstitution :
      TermSubst sourceContext targetContext secondTypeSubstitution)
    (substitutionsAgreePointwise :
      Subst.equiv firstTypeSubstitution secondTypeSubstitution)
    (termSubstitutionsAgreePointwise :
      ∀ position, HEq (firstTermSubstitution position)
                      (secondTermSubstitution position))
    (newType : Ty level sourceScope) :
    ∀ position,
      HEq (TermSubst.lift firstTermSubstitution newType position)
          (TermSubst.lift secondTermSubstitution newType position) := by
  -- Bridging fact: newType.subst firstTypeSubstitution =
  --                  newType.subst secondTypeSubstitution.
  have newTypeSubstEq :
      newType.subst firstTypeSubstitution
        = newType.subst secondTypeSubstitution :=
    Ty.subst_congr substitutionsAgreePointwise newType
  intro position
  match position with
  | ⟨0, _⟩ =>
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq (congrArg (targetContext.cons) newTypeSubstEq)
        ⟨0, Nat.zero_lt_succ targetScope⟩)
    exact (eqRec_heq _ _).symm
  | ⟨predecessor + 1, succBound⟩ =>
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.weaken (newType.subst secondTypeSubstitution)
        (secondTermSubstitution
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
    · exact Term.weaken_HEq_congr newTypeSubstEq
        (Ty.subst_congr substitutionsAgreePointwise
          (varType sourceContext
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
        (firstTermSubstitution
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
        (secondTermSubstitution
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
        (termSubstitutionsAgreePointwise
          ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
    · exact (eqRec_heq _ _).symm

/-! ## `Term.subst_HEq_pointwise`.

Substitution respects pointwise HEq of TermSubsts.  The
`targetContextEq : firstTargetContext = secondTargetContext`
parameter accommodates binder-case recursive calls where
`TermSubst.lift termSubstitution_i domainType` lands in
`targetContext.cons (domainType.subst typeSubstitution_i)` —
same scope, different concrete contexts. -/
theorem Term.subst_HEq_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {firstTargetContext secondTargetContext : Ctx mode level targetScope}
    (targetContextEq : firstTargetContext = secondTargetContext)
    {firstTypeSubstitution secondTypeSubstitution :
      Subst level sourceScope targetScope}
    (firstTermSubstitution :
      TermSubst sourceContext firstTargetContext firstTypeSubstitution)
    (secondTermSubstitution :
      TermSubst sourceContext secondTargetContext secondTypeSubstitution)
    (substitutionsAgreePointwise :
      Subst.equiv firstTypeSubstitution secondTypeSubstitution)
    (termSubstitutionsAgreePointwise :
      ∀ position, HEq (firstTermSubstitution position)
                      (secondTermSubstitution position)) :
    {tyValue : Ty level sourceScope} → (term : Term sourceContext tyValue) →
      HEq (Term.subst firstTermSubstitution term)
          (Term.subst secondTermSubstitution term)
  | _, .var position => termSubstitutionsAgreePointwise position
  | _, .unit => by term_context_refl
  | _, .app (domainType := domainType) (codomainType := codomainType)
            functionTerm argumentTerm => by
    cases targetContextEq
    show HEq (Term.app (Term.subst firstTermSubstitution functionTerm)
                       (Term.subst firstTermSubstitution argumentTerm))
             (Term.app (Term.subst secondTermSubstitution functionTerm)
                       (Term.subst secondTermSubstitution argumentTerm))
    exact Term.app_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise domainType)
      (Ty.subst_congr substitutionsAgreePointwise codomainType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise functionTerm)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise argumentTerm)
  | _, .lam (domainType := domainType) (codomainType := codomainType) body => by
    cases targetContextEq
    show HEq
      (Term.lam (codomainType := codomainType.subst firstTypeSubstitution)
        ((Ty.subst_weaken_commute codomainType firstTypeSubstitution) ▸
          (Term.subst (TermSubst.lift firstTermSubstitution domainType) body)))
      (Term.lam (codomainType := codomainType.subst secondTypeSubstitution)
        ((Ty.subst_weaken_commute codomainType secondTypeSubstitution) ▸
          (Term.subst (TermSubst.lift secondTermSubstitution domainType) body)))
    apply Term.lam_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise domainType)
      (Ty.subst_congr substitutionsAgreePointwise codomainType)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg firstTargetContext.cons
          (Ty.subst_congr substitutionsAgreePointwise domainType))
        (TermSubst.lift firstTermSubstitution domainType)
        (TermSubst.lift secondTermSubstitution domainType)
        (Subst.lift_equiv substitutionsAgreePointwise)
        (TermSubst.lift_HEq_pointwise
          firstTermSubstitution secondTermSubstitution
          substitutionsAgreePointwise
          termSubstitutionsAgreePointwise domainType)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := domainType) (codomainType := codomainType) body => by
    cases targetContextEq
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift firstTermSubstitution domainType) body))
      (Term.lamPi (Term.subst (TermSubst.lift secondTermSubstitution domainType) body))
    apply Term.lamPi_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise domainType)
      (Ty.subst_congr (Subst.lift_equiv substitutionsAgreePointwise)
        codomainType)
    exact Term.subst_HEq_pointwise
      (congrArg firstTargetContext.cons
        (Ty.subst_congr substitutionsAgreePointwise domainType))
      (TermSubst.lift firstTermSubstitution domainType)
      (TermSubst.lift secondTermSubstitution domainType)
      (Subst.lift_equiv substitutionsAgreePointwise)
      (TermSubst.lift_HEq_pointwise
        firstTermSubstitution secondTermSubstitution
        substitutionsAgreePointwise
        termSubstitutionsAgreePointwise domainType)
      body
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
              resultEq functionTerm argumentTerm => by
    cases targetContextEq
    -- Term.subst on Term.appPi produces a double-cast term:
    -- (congrArg (Ty.subst · σ) resultEq).symm ▸ (subst0_subst_commute ▸ Term.appPi rfl _ _).
    -- Strip both casts via eqRec_heq, then HEq congr the inner appPi.
    show HEq
      ((congrArg (Ty.subst · firstTypeSubstitution) resultEq).symm ▸
        ((Ty.subst0_subst_commute codomainType domainType firstTypeSubstitution).symm ▸
          Term.appPi rfl (Term.subst firstTermSubstitution functionTerm)
                         (Term.subst firstTermSubstitution argumentTerm)))
      ((congrArg (Ty.subst · secondTypeSubstitution) resultEq).symm ▸
        ((Ty.subst0_subst_commute codomainType domainType secondTypeSubstitution).symm ▸
          Term.appPi rfl (Term.subst secondTermSubstitution functionTerm)
                         (Term.subst secondTermSubstitution argumentTerm)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (context := firstTargetContext) rfl
        (Term.subst secondTermSubstitution functionTerm)
        (Term.subst secondTermSubstitution argumentTerm))
    · exact Term.appPi_HEq_congr
        (Ty.subst_congr substitutionsAgreePointwise domainType)
        (Ty.subst_congr (Subst.lift_equiv substitutionsAgreePointwise)
          codomainType)
        _ _ (Term.subst_HEq_pointwise rfl
              firstTermSubstitution secondTermSubstitution
              substitutionsAgreePointwise
              termSubstitutionsAgreePointwise functionTerm)
        _ _ (Term.subst_HEq_pointwise rfl
              firstTermSubstitution secondTermSubstitution
              substitutionsAgreePointwise
              termSubstitutionsAgreePointwise argumentTerm)
    · apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      exact (eqRec_heq _ _)
  | _, .pair (firstType := firstType) (secondType := secondType)
              firstVal secondVal => by
    cases targetContextEq
    show HEq
      (Term.pair (Term.subst firstTermSubstitution firstVal)
        ((Ty.subst0_subst_commute secondType firstType firstTypeSubstitution) ▸
          (Term.subst firstTermSubstitution secondVal)))
      (Term.pair (Term.subst secondTermSubstitution firstVal)
        ((Ty.subst0_subst_commute secondType firstType secondTypeSubstitution) ▸
          (Term.subst secondTermSubstitution secondVal)))
    apply Term.pair_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise firstType)
      (Ty.subst_congr (Subst.lift_equiv substitutionsAgreePointwise) secondType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise firstVal)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise rfl
        firstTermSubstitution secondTermSubstitution
        substitutionsAgreePointwise
        termSubstitutionsAgreePointwise secondVal)
    exact (eqRec_heq _ _).symm
  | _, .fst (firstType := firstType) (secondType := secondType) pairTerm => by
    cases targetContextEq
    show HEq (Term.fst (Term.subst firstTermSubstitution pairTerm))
             (Term.fst (Term.subst secondTermSubstitution pairTerm))
    exact Term.fst_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise firstType)
      (Ty.subst_congr (Subst.lift_equiv substitutionsAgreePointwise) secondType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise pairTerm)
  | _, .snd (firstType := firstType) (secondType := secondType) pairTerm => by
    cases targetContextEq
    show HEq
      ((Ty.subst0_subst_commute secondType firstType firstTypeSubstitution).symm ▸
        Term.snd (Term.subst firstTermSubstitution pairTerm))
      ((Ty.subst0_subst_commute secondType firstType secondTypeSubstitution).symm ▸
        Term.snd (Term.subst secondTermSubstitution pairTerm))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.subst secondTermSubstitution pairTerm))
    · exact Term.snd_HEq_congr
        (Ty.subst_congr substitutionsAgreePointwise firstType)
        (Ty.subst_congr (Subst.lift_equiv substitutionsAgreePointwise) secondType)
        _ _ (Term.subst_HEq_pointwise rfl
              firstTermSubstitution secondTermSubstitution
              substitutionsAgreePointwise
              termSubstitutionsAgreePointwise pairTerm)
    · exact (eqRec_heq _ _).symm
  | _, .boolTrue => by term_context_refl
  | _, .boolFalse => by term_context_refl
  | _, .boolElim (resultType := resultType) scrutinee thenBranch elseBranch => by
    cases targetContextEq
    show HEq
      (Term.boolElim (Term.subst firstTermSubstitution scrutinee)
                     (Term.subst firstTermSubstitution thenBranch)
                     (Term.subst firstTermSubstitution elseBranch))
      (Term.boolElim (Term.subst secondTermSubstitution scrutinee)
                     (Term.subst secondTermSubstitution thenBranch)
                     (Term.subst secondTermSubstitution elseBranch))
    exact Term.boolElim_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl
              firstTermSubstitution secondTermSubstitution
              substitutionsAgreePointwise
              termSubstitutionsAgreePointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise thenBranch)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise elseBranch)
  | _, .natZero => by term_context_refl
  | _, .natSucc predecessor => by
    cases targetContextEq
    show HEq (Term.natSucc (Term.subst firstTermSubstitution predecessor))
             (Term.natSucc (Term.subst secondTermSubstitution predecessor))
    exact Term.natSucc_HEq_congr _ _
      (Term.subst_HEq_pointwise rfl
        firstTermSubstitution secondTermSubstitution
        substitutionsAgreePointwise
        termSubstitutionsAgreePointwise predecessor)
  | _, .natElim (resultType := resultType) scrutinee zeroBranch succBranch => by
    cases targetContextEq
    show HEq
      (Term.natElim (Term.subst firstTermSubstitution scrutinee)
                    (Term.subst firstTermSubstitution zeroBranch)
                    (Term.subst firstTermSubstitution succBranch))
      (Term.natElim (Term.subst secondTermSubstitution scrutinee)
                    (Term.subst secondTermSubstitution zeroBranch)
                    (Term.subst secondTermSubstitution succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl
              firstTermSubstitution secondTermSubstitution
              substitutionsAgreePointwise
              termSubstitutionsAgreePointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise succBranch)
  | _, .natRec (resultType := resultType) scrutinee zeroBranch succBranch => by
    cases targetContextEq
    exact Term.natRec_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl
              firstTermSubstitution secondTermSubstitution
              substitutionsAgreePointwise
              termSubstitutionsAgreePointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise succBranch)
  | _, .listNil (elementType := elementType) => by
    cases targetContextEq
    exact Term.listNil_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise elementType)
  | _, .listCons (elementType := elementType) headValue tailValue => by
    cases targetContextEq
    show HEq (Term.listCons (Term.subst firstTermSubstitution headValue)
                            (Term.subst firstTermSubstitution tailValue))
             (Term.listCons (Term.subst secondTermSubstitution headValue)
                            (Term.subst secondTermSubstitution tailValue))
    exact Term.listCons_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise elementType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise headValue)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise tailValue)
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch => by
    cases targetContextEq
    show HEq
      (Term.listElim (Term.subst firstTermSubstitution scrutinee)
                     (Term.subst firstTermSubstitution nilBranch)
                     (Term.subst firstTermSubstitution consBranch))
      (Term.listElim (Term.subst secondTermSubstitution scrutinee)
                     (Term.subst secondTermSubstitution nilBranch)
                     (Term.subst secondTermSubstitution consBranch))
    exact Term.listElim_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise elementType)
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise nilBranch)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise consBranch)
  | _, .optionNone (elementType := elementType) => by
    cases targetContextEq
    exact Term.optionNone_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise elementType)
  | _, .optionSome (elementType := elementType) value => by
    cases targetContextEq
    show HEq (Term.optionSome (Term.subst firstTermSubstitution value))
             (Term.optionSome (Term.subst secondTermSubstitution value))
    exact Term.optionSome_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise elementType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise value)
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch => by
    cases targetContextEq
    show HEq
      (Term.optionMatch (Term.subst firstTermSubstitution scrutinee)
                        (Term.subst firstTermSubstitution noneBranch)
                        (Term.subst firstTermSubstitution someBranch))
      (Term.optionMatch (Term.subst secondTermSubstitution scrutinee)
                        (Term.subst secondTermSubstitution noneBranch)
                        (Term.subst secondTermSubstitution someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise elementType)
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise noneBranch)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise someBranch)
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value => by
    cases targetContextEq
    exact Term.eitherInl_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise leftType)
      (Ty.subst_congr substitutionsAgreePointwise rightType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise value)
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value => by
    cases targetContextEq
    exact Term.eitherInr_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise leftType)
      (Ty.subst_congr substitutionsAgreePointwise rightType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise value)
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
                    (resultType := resultType)
        scrutinee leftBranch rightBranch => by
    cases targetContextEq
    exact Term.eitherMatch_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise leftType)
      (Ty.subst_congr substitutionsAgreePointwise rightType)
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise leftBranch)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise rightBranch)
  | _, .refl (carrier := carrier) rawTerm => by
    cases targetContextEq
    exact Term.refl_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise carrier)
      (RawTerm.subst_congr (Subst.equiv_forRaw substitutionsAgreePointwise)
        rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := resultType)
            baseCase witness => by
    cases targetContextEq
    exact Term.idJ_HEq_congr
      (Ty.subst_congr substitutionsAgreePointwise carrier)
      (RawTerm.subst_congr (Subst.equiv_forRaw substitutionsAgreePointwise)
        leftEnd)
      (RawTerm.subst_congr (Subst.equiv_forRaw substitutionsAgreePointwise)
        rightEnd)
      (Ty.subst_congr substitutionsAgreePointwise resultType)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise baseCase)
      _ _ (Term.subst_HEq_pointwise rfl
            firstTermSubstitution secondTermSubstitution
            substitutionsAgreePointwise
            termSubstitutionsAgreePointwise witness)

/-! ## `Term.subst_id_HEq`.

Full HEq form of subst-by-identity.  Structural induction; binder
cases use `Term.subst_HEq_pointwise` to bridge
`TermSubst.lift (TermSubst.identity sourceContext)` to
`TermSubst.identity (sourceContext.cons _)` via
`lift_identity_pointwise`. -/
theorem Term.subst_id_HEq
    {mode : Mode} {level scope : Nat} {sourceContext : Ctx mode level scope} :
    {tyValue : Ty level scope} → (term : Term sourceContext tyValue) →
      HEq (Term.subst (TermSubst.identity sourceContext) term) term
  | _, .var position => Term.subst_id_HEq_var position
  | _, .unit => Term.subst_id_HEq_unit
  | _, .app functionTerm argumentTerm =>
    Term.subst_id_HEq_app functionTerm argumentTerm
      (Term.subst_id_HEq functionTerm) (Term.subst_id_HEq argumentTerm)
  | _, .lam (domainType := domainType) (codomainType := codomainType) body => by
    show HEq
      (Term.lam (codomainType := codomainType.subst Subst.identity)
        ((Ty.subst_weaken_commute codomainType Subst.identity) ▸
          (Term.subst (TermSubst.lift
              (TermSubst.identity sourceContext) domainType) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr (Ty.subst_id domainType) (Ty.subst_id codomainType)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg sourceContext.cons (Ty.subst_id domainType))
        (TermSubst.lift (TermSubst.identity sourceContext) domainType)
        (TermSubst.identity (sourceContext.cons domainType))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise sourceContext domainType)
        body)
    exact Term.subst_id_HEq body
  | _, .lamPi (domainType := domainType) (codomainType := codomainType) body => by
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift
        (TermSubst.identity sourceContext) domainType) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr (Ty.subst_id domainType)
      ((Ty.subst_congr Subst.lift_identity_equiv codomainType).trans
       (Ty.subst_id codomainType))
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg sourceContext.cons (Ty.subst_id domainType))
        (TermSubst.lift (TermSubst.identity sourceContext) domainType)
        (TermSubst.identity (sourceContext.cons domainType))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise sourceContext domainType)
        body)
    exact Term.subst_id_HEq body
  | _, .appPi resultEq functionTerm argumentTerm =>
    Term.subst_id_HEq_appPi resultEq functionTerm argumentTerm
      (Term.subst_id_HEq functionTerm) (Term.subst_id_HEq argumentTerm)
  | _, .pair firstVal secondVal =>
    Term.subst_id_HEq_pair firstVal secondVal
      (Term.subst_id_HEq firstVal) (Term.subst_id_HEq secondVal)
  | _, .fst pairTerm =>
    Term.subst_id_HEq_fst pairTerm (Term.subst_id_HEq pairTerm)
  | _, .snd pairTerm =>
    Term.subst_id_HEq_snd pairTerm (Term.subst_id_HEq pairTerm)
  | _, .boolTrue => Term.subst_id_HEq_boolTrue
  | _, .boolFalse => Term.subst_id_HEq_boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
    Term.subst_id_HEq_boolElim scrutinee thenBranch elseBranch
      (Term.subst_id_HEq scrutinee)
      (Term.subst_id_HEq thenBranch)
      (Term.subst_id_HEq elseBranch)
  | _, .natZero => HEq.refl _
  | _, .natSucc predecessor =>
    Term.natSucc_HEq_congr _ _ (Term.subst_id_HEq predecessor)
  | _, .natElim (resultType := resultType) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst (TermSubst.identity sourceContext) scrutinee)
        (Term.subst (TermSubst.identity sourceContext) zeroBranch)
        (Term.subst (TermSubst.identity sourceContext) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.subst_id resultType)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .natRec (resultType := resultType) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_id resultType)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .listNil (elementType := elementType) =>
    Term.listNil_HEq_congr (Ty.subst_id elementType)
  | _, .listCons (elementType := elementType) headValue tailValue =>
    Term.listCons_HEq_congr
      (Ty.subst_id elementType)
      _ _ (Term.subst_id_HEq headValue)
      _ _ (Term.subst_id_HEq tailValue)
  | _, .listElim (elementType := elementType) (resultType := resultType)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_id elementType) (Ty.subst_id resultType)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq nilBranch)
      _ _ (Term.subst_id_HEq consBranch)
  | _, .optionNone (elementType := elementType) =>
    Term.optionNone_HEq_congr (Ty.subst_id elementType)
  | _, .optionSome (elementType := elementType) value =>
    Term.optionSome_HEq_congr
      (Ty.subst_id elementType)
      _ _ (Term.subst_id_HEq value)
  | _, .optionMatch (elementType := elementType) (resultType := resultType)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_id elementType) (Ty.subst_id resultType)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq noneBranch)
      _ _ (Term.subst_id_HEq someBranch)
  | _, .eitherInl (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInl_HEq_congr
      (Ty.subst_id leftType) (Ty.subst_id rightType)
      _ _ (Term.subst_id_HEq value)
  | _, .eitherInr (leftType := leftType) (rightType := rightType) value =>
    Term.eitherInr_HEq_congr
      (Ty.subst_id leftType) (Ty.subst_id rightType)
      _ _ (Term.subst_id_HEq value)
  | _, .eitherMatch (leftType := leftType) (rightType := rightType)
                    (resultType := resultType)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_id leftType) (Ty.subst_id rightType) (Ty.subst_id resultType)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq leftBranch)
      _ _ (Term.subst_id_HEq rightBranch)
  | _, .refl (carrier := carrier) rawTerm =>
    Term.refl_HEq_congr (Ty.subst_id carrier) (RawTerm.subst_id rawTerm)
  | _, .idJ (carrier := carrier) (leftEnd := leftEnd) (rightEnd := rightEnd)
            (resultType := resultType)
            baseCase witness =>
    Term.idJ_HEq_congr
      (Ty.subst_id carrier) (RawTerm.subst_id leftEnd) (RawTerm.subst_id rightEnd)
      (Ty.subst_id resultType)
      _ _ (Term.subst_id_HEq baseCase)
      _ _ (Term.subst_id_HEq witness)

/-! ## `Term.subst_id` (explicit-`▸` form).

Corollary of `Term.subst_id_HEq` + `eqRec_heq`. -/
theorem Term.subst_id {mode : Mode} {level scope : Nat}
    {sourceContext : Ctx mode level scope}
    {tyValue : Ty level scope} (term : Term sourceContext tyValue) :
    (Ty.subst_id tyValue) ▸ Term.subst (TermSubst.identity sourceContext) term
      = term :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.subst_id_HEq term))

/-! ## Cast-through-Term.subst HEq helper.

Pushes a type-cast on the input out through `Term.subst` so the
substitution's structural recursion can fire on the bare
constructor.  Bridge for `lift_compose_pointwise_zero` and the
cast-bearing closed-context commute cases. -/
theorem Term.subst_HEq_cast_input
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceContext targetContext typeSubstitution)
    {sourceTy targetTy : Ty level sourceScope}
    (typeEq : sourceTy = targetTy)
    (term : Term sourceContext sourceTy) :
    HEq (Term.subst termSubstitution (typeEq ▸ term))
        (Term.subst termSubstitution term) := by
  cases typeEq
  rfl

/-- Push a type-cast on a one-hole-substitution body out through
`Term.subst0`. -/
theorem Term.subst0_HEq_cast_input
    {mode : Mode} {level scope : Nat} {sourceContext : Ctx mode level scope}
    {argumentType : Ty level scope}
    {sourceBodyType targetBodyType : Ty level (scope + 1)}
    (bodyTypeEquality : sourceBodyType = targetBodyType)
    (bodyTerm : Term (sourceContext.cons argumentType) sourceBodyType)
    (argumentTerm : Term sourceContext argumentType) :
    HEq (Term.subst0 (bodyTypeEquality ▸ bodyTerm) argumentTerm)
      (Term.subst0 bodyTerm argumentTerm) := by
  show HEq
    (Term.subst (TermSubst.singleton argumentTerm)
      (bodyTypeEquality ▸ bodyTerm))
    (Term.subst (TermSubst.singleton argumentTerm) bodyTerm)
  exact Term.subst_HEq_cast_input
    (TermSubst.singleton argumentTerm) bodyTypeEquality bodyTerm

/-- Push a type-cast on a one-hole-substitution body out through
`Term.subst0_term` (Wave 9 / Phase C — termSingleton-flavor). -/
theorem Term.subst0_term_HEq_cast_input
    {mode : Mode} {level scope : Nat} {sourceContext : Ctx mode level scope}
    {argumentType : Ty level scope}
    {sourceBodyType targetBodyType : Ty level (scope + 1)}
    (bodyTypeEquality : sourceBodyType = targetBodyType)
    (bodyTerm : Term (sourceContext.cons argumentType) sourceBodyType)
    (argumentTerm : Term sourceContext argumentType) :
    HEq (Term.subst0_term (bodyTypeEquality ▸ bodyTerm) argumentTerm)
      (Term.subst0_term bodyTerm argumentTerm) := by
  show HEq
    (Term.subst (TermSubst.termSingleton argumentTerm)
      (bodyTypeEquality ▸ bodyTerm))
    (Term.subst (TermSubst.termSingleton argumentTerm) bodyTerm)
  exact Term.subst_HEq_cast_input
    (TermSubst.termSingleton argumentTerm) bodyTypeEquality bodyTerm

/-! ## `TermSubst.lift_compose_pointwise` at position 0.

Lifting a composed term-substitution under a binder agrees HEq with
composing the two lifts on the freshly-bound variable.  The position-
`predecessor + 1` case requires `Term.subst_weaken_commute_HEq`
(binder cases deferred) and is shipped as a separate companion. -/
theorem TermSubst.lift_compose_pointwise_zero
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
    HEq
      (TermSubst.lift
        (TermSubst.compose firstTermSubstitution secondTermSubstitution)
        newType ⟨0, Nat.zero_lt_succ _⟩)
      (TermSubst.compose
        (firstTermSubstitution.lift newType)
        (secondTermSubstitution.lift (newType.subst firstTypeSubstitution))
        ⟨0, Nat.zero_lt_succ _⟩) := by
  apply HEq.trans (eqRec_heq _ _)
  apply HEq.symm
  apply HEq.trans (eqRec_heq _ _)
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (secondTermSubstitution.lift (newType.subst firstTypeSubstitution))
      (Ty.subst_weaken_commute newType firstTypeSubstitution).symm
      (Term.var (context := middleContext.cons (newType.subst firstTypeSubstitution))
        ⟨0, Nat.zero_lt_succ _⟩))
  show HEq ((secondTermSubstitution.lift (newType.subst firstTypeSubstitution))
              ⟨0, Nat.zero_lt_succ _⟩) _
  apply HEq.trans (eqRec_heq _ _)
  exact heq_var_across_ctx_eq
    (congrArg finalContext.cons
      (Ty.subst_compose newType firstTypeSubstitution secondTypeSubstitution))
    ⟨0, Nat.zero_lt_succ _⟩


end LeanFX.Syntax
