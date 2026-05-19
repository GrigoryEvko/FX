import LeanFX2.Term.Pointwise.IdentitySubst.IdentityRecursive

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityEliminators

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## Non-dependent eliminator cases -/

/-- Application case for ordinary identity substitution. -/
theorem Term.subst_identity_app_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst (TermSubst.identity context) functionTerm)
        functionTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.app functionTerm argumentTerm))
      (Term.app functionTerm argumentTerm) := by
  simp only [Term.subst]
  exact Term.app_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (RawTerm.subst_identity functionRaw)
    (RawTerm.subst_identity argumentRaw)
    functionHEq argumentHEq

/-- Dependent function application case for ordinary identity substitution. -/
theorem Term.subst_identity_appPi_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst (TermSubst.identity context) functionTerm)
        functionTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.appPi functionTerm argumentTerm))
      (Term.appPi functionTerm argumentTerm) := by
  simp only [Term.subst]
  have codomainIdentity :
      codomainType.subst (@Subst.identity level scope).lift = codomainType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      codomainType]
    exact Ty.subst_identity codomainType
  have appPiWithoutCastHEq :
      HEq
        (Term.appPi
          (Term.subst (TermSubst.identity context) functionTerm)
          (Term.subst (TermSubst.identity context) argumentTerm))
        (Term.appPi functionTerm argumentTerm) :=
    Term.appPi_HEq_congr
      (Ty.subst_identity domainType)
      codomainIdentity
      (RawTerm.subst_identity functionRaw)
      (RawTerm.subst_identity argumentRaw)
      functionHEq argumentHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute codomainType domainType argumentRaw
          Subst.identity).symm ▸
          Term.appPi
            (Term.subst (TermSubst.identity context) functionTerm)
            (Term.subst (TermSubst.identity context) argumentTerm))
        (Term.appPi
          (Term.subst (TermSubst.identity context) functionTerm)
          (Term.subst (TermSubst.identity context) argumentTerm)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute codomainType domainType argumentRaw
        Subst.identity).symm
      (Term.appPi
        (Term.subst (TermSubst.identity context) functionTerm)
        (Term.subst (TermSubst.identity context) argumentTerm))
  exact HEq.trans resultCastHEq appPiWithoutCastHEq

/-- Sigma pair introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_pair_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw)
    (firstHEq :
      HEq (Term.subst (TermSubst.identity context) firstValue) firstValue)
    (secondHEq :
      HEq (Term.subst (TermSubst.identity context) secondValue)
        secondValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.pair (secondType := secondType) firstValue secondValue))
      (Term.pair (secondType := secondType) firstValue secondValue) := by
  simp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst (@Subst.identity level scope).lift = secondType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      secondType]
    exact Ty.subst_identity secondType
  have secondCastHEq :
      HEq
        ((Ty.subst0_subst_commute secondType firstType firstRaw
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) secondValue)
        secondValue :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute secondType firstType firstRaw
          Subst.identity)
        (Term.subst (TermSubst.identity context) secondValue))
      secondHEq
  exact Term.pair_HEq_congr
    (Ty.subst_identity firstType)
    secondTypeIdentity
    (RawTerm.subst_identity firstRaw)
    (RawTerm.subst_identity secondRaw)
    firstHEq secondCastHEq

/-- Sigma first projection case for ordinary identity substitution. -/
theorem Term.subst_identity_fst_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq (Term.subst (TermSubst.identity context) pairTerm) pairTerm) :
    HEq
      (Term.subst (TermSubst.identity context) (Term.fst pairTerm))
      (Term.fst pairTerm) := by
  simp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst (@Subst.identity level scope).lift = secondType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      secondType]
    exact Ty.subst_identity secondType
  exact Term.fst_HEq_congr
    (Ty.subst_identity firstType)
    secondTypeIdentity
    (RawTerm.subst_identity pairRaw)
    pairHEq

/-- Sigma second projection case for ordinary identity substitution. -/
theorem Term.subst_identity_snd_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq (Term.subst (TermSubst.identity context) pairTerm) pairTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.snd (secondType := secondType) pairTerm))
      (Term.snd (secondType := secondType) pairTerm) := by
  simp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst (@Subst.identity level scope).lift = secondType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      secondType]
    exact Ty.subst_identity secondType
  have sndWithoutCastHEq :
      HEq
        (Term.snd
          (Term.subst (TermSubst.identity context) pairTerm))
        (Term.snd (secondType := secondType) pairTerm) :=
    Term.snd_HEq_congr
      (Ty.subst_identity firstType)
      secondTypeIdentity
      (RawTerm.subst_identity pairRaw)
      pairHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute secondType firstType
          (RawTerm.fst pairRaw) Subst.identity).symm ▸
          Term.snd (Term.subst (TermSubst.identity context) pairTerm))
        (Term.snd (Term.subst (TermSubst.identity context) pairTerm)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute secondType firstType
        (RawTerm.fst pairRaw) Subst.identity).symm
      (Term.snd (Term.subst (TermSubst.identity context) pairTerm))
  exact HEq.trans resultCastHEq sndWithoutCastHEq

/-- Dependent boolean eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_boolElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee) scrutinee)
    (thenHEq :
      HEq (Term.subst (TermSubst.identity context) thenBranch) thenBranch)
    (elseHEq :
      HEq (Term.subst (TermSubst.identity context) elseBranch) elseBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolElim scrutinee thenBranch elseBranch))
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  simp only [Term.subst]
  have motiveIdentity :
      motiveType.subst (@Subst.identity level scope).lift = motiveType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      motiveType]
    exact Ty.subst_identity motiveType
  have thenCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) thenBranch)
        thenBranch :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          Subst.identity)
        (Term.subst (TermSubst.identity context) thenBranch))
      thenHEq
  have elseCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) elseBranch)
        elseBranch :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          Subst.identity)
        (Term.subst (TermSubst.identity context) elseBranch))
      elseHEq
  have boolElimWithoutCastHEq :
      HEq
        (Term.boolElim
          (motiveType := motiveType.subst (@Subst.identity level scope).lift)
          (Term.subst (TermSubst.identity context) scrutinee)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) thenBranch)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) elseBranch))
        (Term.boolElim scrutinee thenBranch elseBranch) :=
    Term.boolElim_HEq_congr
      motiveIdentity
      (RawTerm.subst_identity scrutineeRaw)
      (RawTerm.subst_identity thenRaw)
      (RawTerm.subst_identity elseRaw)
      scrutineeHEq thenCastHEq elseCastHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
          Subst.identity).symm ▸
          Term.boolElim
            (motiveType := motiveType.subst
              (@Subst.identity level scope).lift)
            (Term.subst (TermSubst.identity context) scrutinee)
            ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
              Subst.identity) ▸
              Term.subst (TermSubst.identity context) thenBranch)
            ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
              Subst.identity) ▸
              Term.subst (TermSubst.identity context) elseBranch))
        (Term.boolElim
          (motiveType := motiveType.subst (@Subst.identity level scope).lift)
          (Term.subst (TermSubst.identity context) scrutinee)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) thenBranch)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            Subst.identity) ▸
            Term.subst (TermSubst.identity context) elseBranch)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
        Subst.identity).symm
      (Term.boolElim
        (motiveType := motiveType.subst (@Subst.identity level scope).lift)
        (Term.subst (TermSubst.identity context) scrutinee)
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) thenBranch)
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          Subst.identity) ▸
          Term.subst (TermSubst.identity context) elseBranch))
  exact HEq.trans resultCastHEq boolElimWithoutCastHEq

/-- Natural eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_natElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (zeroHEq :
      HEq (Term.subst (TermSubst.identity context) zeroBranch)
        zeroBranch)
    (succHEq :
      HEq (Term.subst (TermSubst.identity context) succBranch)
        succBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natElim scrutinee zeroBranch succBranch))
      (Term.natElim scrutinee zeroBranch succBranch) := by
  simp only [Term.subst]
  exact Term.natElim_HEq_congr
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity zeroRaw)
    (RawTerm.subst_identity succRaw)
    scrutineeHEq zeroHEq succHEq

/-- Primitive natural recursor case for ordinary identity substitution. -/
theorem Term.subst_identity_natRec_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (zeroHEq :
      HEq (Term.subst (TermSubst.identity context) zeroBranch)
        zeroBranch)
    (succHEq :
      HEq (Term.subst (TermSubst.identity context) succBranch)
        succBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natRec scrutinee zeroBranch succBranch))
      (Term.natRec scrutinee zeroBranch succBranch) := by
  simp only [Term.subst]
  exact Term.natRec_HEq_congr
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity zeroRaw)
    (RawTerm.subst_identity succRaw)
    scrutineeHEq zeroHEq succHEq

/-- List eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_listElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context
      (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
      consRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (nilHEq :
      HEq (Term.subst (TermSubst.identity context) nilBranch)
        nilBranch)
    (consHEq :
      HEq (Term.subst (TermSubst.identity context) consBranch)
        consBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listElim scrutinee nilBranch consBranch))
      (Term.listElim scrutinee nilBranch consBranch) := by
  simp only [Term.subst]
  exact Term.listElim_HEq_congr
    (Ty.subst_identity elementType)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity nilRaw)
    (RawTerm.subst_identity consRaw)
    scrutineeHEq nilHEq consHEq

/-- Option match case for ordinary identity substitution. -/
theorem Term.subst_identity_optionMatch_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (noneHEq :
      HEq (Term.subst (TermSubst.identity context) noneBranch)
        noneBranch)
    (someHEq :
      HEq (Term.subst (TermSubst.identity context) someBranch)
        someBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionMatch scrutinee noneBranch someBranch))
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  simp only [Term.subst]
  exact Term.optionMatch_HEq_congr
    (Ty.subst_identity elementType)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity noneRaw)
    (RawTerm.subst_identity someRaw)
    scrutineeHEq noneHEq someHEq

/-- Either match case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherMatch_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee)
        scrutinee)
    (leftHEq :
      HEq (Term.subst (TermSubst.identity context) leftBranch)
        leftBranch)
    (rightHEq :
      HEq (Term.subst (TermSubst.identity context) rightBranch)
        rightBranch) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherMatch scrutinee leftBranch rightBranch))
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  simp only [Term.subst]
  exact Term.eitherMatch_HEq_congr
    (Ty.subst_identity leftType)
    (Ty.subst_identity rightType)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity scrutineeRaw)
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)
    scrutineeHEq leftHEq rightHEq

end LeanFX2
