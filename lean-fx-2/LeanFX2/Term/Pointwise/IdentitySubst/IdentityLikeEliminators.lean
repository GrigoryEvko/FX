import LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeIntro
import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeEliminators

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

theorem Term.subst_identityLike_app_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst termSubst functionTerm) functionTerm)
    (argumentHEq :
      HEq (Term.subst termSubst argumentTerm) argumentTerm) :
    HEq
      (Term.subst termSubst (Term.app functionTerm argumentTerm))
      (Term.app functionTerm argumentTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.app_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq domainType)
    (substitutionIsIdentityLike.tySubst_eq codomainType)
    (substitutionIsIdentityLike.rawSubst_eq functionRaw)
    (substitutionIsIdentityLike.rawSubst_eq argumentRaw)
    functionHEq argumentHEq

/-- Dependent function application case for an identity-like substitution. -/
theorem Term.subst_identityLike_appPi_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionHEq :
      HEq (Term.subst termSubst functionTerm) functionTerm)
    (argumentHEq :
      HEq (Term.subst termSubst argumentTerm) argumentTerm) :
    HEq
      (Term.subst termSubst (Term.appPi functionTerm argumentTerm))
      (Term.appPi functionTerm argumentTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  have codomainIdentity :
      codomainType.subst sigma.lift = codomainType :=
    (substitutionIsIdentityLike.lift domainType).tySubst_eq codomainType
  have appPiWithoutCastHEq :
      HEq
        (Term.appPi
          (Term.subst termSubst functionTerm)
          (Term.subst termSubst argumentTerm))
        (Term.appPi functionTerm argumentTerm) :=
    Term.appPi_HEq_congr
      (substitutionIsIdentityLike.tySubst_eq domainType)
      codomainIdentity
      (substitutionIsIdentityLike.rawSubst_eq functionRaw)
      (substitutionIsIdentityLike.rawSubst_eq argumentRaw)
      functionHEq argumentHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute codomainType domainType argumentRaw
          sigma).symm ▸
          Term.appPi
            (Term.subst termSubst functionTerm)
            (Term.subst termSubst argumentTerm))
        (Term.appPi
          (Term.subst termSubst functionTerm)
          (Term.subst termSubst argumentTerm)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute codomainType domainType argumentRaw
        sigma).symm
      (Term.appPi
        (Term.subst termSubst functionTerm)
        (Term.subst termSubst argumentTerm))
  exact HEq.trans resultCastHEq appPiWithoutCastHEq

/-- Sigma pair introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_pair_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term sourceCtx firstType firstRaw)
    (secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw)
    (firstHEq :
      HEq (Term.subst termSubst firstValue) firstValue)
    (secondHEq :
      HEq (Term.subst termSubst secondValue) secondValue) :
    HEq
      (Term.subst termSubst
        (Term.pair (secondType := secondType) firstValue secondValue))
      (Term.pair (secondType := secondType) firstValue secondValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst sigma.lift = secondType :=
    (substitutionIsIdentityLike.lift firstType).tySubst_eq secondType
  have secondCastHEq :
      HEq
        ((Ty.subst0_subst_commute secondType firstType firstRaw sigma) ▸
          Term.subst termSubst secondValue)
        secondValue :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute secondType firstType firstRaw sigma)
        (Term.subst termSubst secondValue))
      secondHEq
  exact Term.pair_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq firstType)
    secondTypeIdentity
    (substitutionIsIdentityLike.rawSubst_eq firstRaw)
    (substitutionIsIdentityLike.rawSubst_eq secondRaw)
    firstHEq secondCastHEq

/-- Sigma first projection case for an identity-like substitution. -/
theorem Term.subst_identityLike_fst_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq (Term.subst termSubst pairTerm) pairTerm) :
    HEq
      (Term.subst termSubst (Term.fst pairTerm))
      (Term.fst pairTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst sigma.lift = secondType :=
    (substitutionIsIdentityLike.lift firstType).tySubst_eq secondType
  exact Term.fst_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq firstType)
    secondTypeIdentity
    (substitutionIsIdentityLike.rawSubst_eq pairRaw)
    pairHEq

/-- Sigma second projection case for an identity-like substitution. -/
theorem Term.subst_identityLike_snd_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq (Term.subst termSubst pairTerm) pairTerm) :
    HEq
      (Term.subst termSubst
        (Term.snd (secondType := secondType) pairTerm))
      (Term.snd (secondType := secondType) pairTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  have secondTypeIdentity :
      secondType.subst sigma.lift = secondType :=
    (substitutionIsIdentityLike.lift firstType).tySubst_eq secondType
  have sndWithoutCastHEq :
      HEq
        (Term.snd (Term.subst termSubst pairTerm))
        (Term.snd (secondType := secondType) pairTerm) :=
    Term.snd_HEq_congr
      (substitutionIsIdentityLike.tySubst_eq firstType)
      secondTypeIdentity
      (substitutionIsIdentityLike.rawSubst_eq pairRaw)
      pairHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute secondType firstType
          (RawTerm.fst pairRaw) sigma).symm ▸
          Term.snd (Term.subst termSubst pairTerm))
        (Term.snd (Term.subst termSubst pairTerm)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute secondType firstType
        (RawTerm.fst pairRaw) sigma).symm
      (Term.snd (Term.subst termSubst pairTerm))
  exact HEq.trans resultCastHEq sndWithoutCastHEq

/-- Dependent boolean eliminator case for an identity-like substitution. -/
theorem Term.subst_identityLike_boolElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term sourceCtx Ty.bool scrutineeRaw)
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeHEq :
      HEq (Term.subst termSubst scrutinee) scrutinee)
    (thenHEq :
      HEq (Term.subst termSubst thenBranch) thenBranch)
    (elseHEq :
      HEq (Term.subst termSubst elseBranch) elseBranch) :
    HEq
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch))
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  have motiveIdentity :
      motiveType.subst sigma.lift = motiveType :=
    (substitutionIsIdentityLike.lift Ty.bool).tySubst_eq motiveType
  have thenCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          sigma) ▸
          Term.subst termSubst thenBranch)
        thenBranch :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          sigma)
        (Term.subst termSubst thenBranch))
      thenHEq
  have elseCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          sigma) ▸
          Term.subst termSubst elseBranch)
        elseBranch :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          sigma)
        (Term.subst termSubst elseBranch))
      elseHEq
  have boolElimWithoutCastHEq :
      HEq
        (Term.boolElim
          (motiveType := motiveType.subst sigma.lift)
          (Term.subst termSubst scrutinee)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            sigma) ▸
            Term.subst termSubst thenBranch)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            sigma) ▸
            Term.subst termSubst elseBranch))
        (Term.boolElim scrutinee thenBranch elseBranch) :=
    Term.boolElim_HEq_congr
      motiveIdentity
      (substitutionIsIdentityLike.rawSubst_eq scrutineeRaw)
      (substitutionIsIdentityLike.rawSubst_eq thenRaw)
      (substitutionIsIdentityLike.rawSubst_eq elseRaw)
      scrutineeHEq thenCastHEq elseCastHEq
  have resultCastHEq :
      HEq
        ((Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw
          sigma).symm ▸
          Term.boolElim
            (motiveType := motiveType.subst sigma.lift)
            (Term.subst termSubst scrutinee)
            ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
              sigma) ▸
              Term.subst termSubst thenBranch)
            ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
              sigma) ▸
              Term.subst termSubst elseBranch))
        (Term.boolElim
          (motiveType := motiveType.subst sigma.lift)
          (Term.subst termSubst scrutinee)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
            sigma) ▸
            Term.subst termSubst thenBranch)
          ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
            sigma) ▸
            Term.subst termSubst elseBranch)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute motiveType Ty.bool scrutineeRaw sigma).symm
      (Term.boolElim
        (motiveType := motiveType.subst sigma.lift)
        (Term.subst termSubst scrutinee)
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolTrue
          sigma) ▸
          Term.subst termSubst thenBranch)
        ((Ty.subst0_subst_commute motiveType Ty.bool RawTerm.boolFalse
          sigma) ▸
          Term.subst termSubst elseBranch))
  exact HEq.trans resultCastHEq boolElimWithoutCastHEq

/-- Natural eliminator case for an identity-like substitution. -/
theorem Term.subst_identityLike_natElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeHEq :
      HEq (Term.subst termSubst scrutinee) scrutinee)
    (zeroHEq :
      HEq (Term.subst termSubst zeroBranch) zeroBranch)
    (succHEq :
      HEq (Term.subst termSubst succBranch) succBranch) :
    HEq
      (Term.subst termSubst
        (Term.natElim scrutinee zeroBranch succBranch))
      (Term.natElim scrutinee zeroBranch succBranch) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.natElim_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq scrutineeRaw)
    (substitutionIsIdentityLike.rawSubst_eq zeroRaw)
    (substitutionIsIdentityLike.rawSubst_eq succRaw)
    scrutineeHEq zeroHEq succHEq

/-- Primitive natural recursor case for an identity-like substitution. -/
theorem Term.subst_identityLike_natRec_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeHEq :
      HEq (Term.subst termSubst scrutinee) scrutinee)
    (zeroHEq :
      HEq (Term.subst termSubst zeroBranch) zeroBranch)
    (succHEq :
      HEq (Term.subst termSubst succBranch) succBranch) :
    HEq
      (Term.subst termSubst
        (Term.natRec scrutinee zeroBranch succBranch))
      (Term.natRec scrutinee zeroBranch succBranch) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.natRec_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq scrutineeRaw)
    (substitutionIsIdentityLike.rawSubst_eq zeroRaw)
    (substitutionIsIdentityLike.rawSubst_eq succRaw)
    scrutineeHEq zeroHEq succHEq

/-- List eliminator case for an identity-like substitution. -/
theorem Term.subst_identityLike_listElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term sourceCtx motiveType nilRaw)
    (consBranch : Term sourceCtx
      (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
      consRaw)
    (scrutineeHEq :
      HEq (Term.subst termSubst scrutinee) scrutinee)
    (nilHEq :
      HEq (Term.subst termSubst nilBranch) nilBranch)
    (consHEq :
      HEq (Term.subst termSubst consBranch) consBranch) :
    HEq
      (Term.subst termSubst
        (Term.listElim scrutinee nilBranch consBranch))
      (Term.listElim scrutinee nilBranch consBranch) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.listElim_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq scrutineeRaw)
    (substitutionIsIdentityLike.rawSubst_eq nilRaw)
    (substitutionIsIdentityLike.rawSubst_eq consRaw)
    scrutineeHEq nilHEq consHEq

/-- Option match case for an identity-like substitution. -/
theorem Term.subst_identityLike_optionMatch_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term sourceCtx motiveType noneRaw)
    (someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutineeHEq :
      HEq (Term.subst termSubst scrutinee) scrutinee)
    (noneHEq :
      HEq (Term.subst termSubst noneBranch) noneBranch)
    (someHEq :
      HEq (Term.subst termSubst someBranch) someBranch) :
    HEq
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch))
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.optionMatch_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq scrutineeRaw)
    (substitutionIsIdentityLike.rawSubst_eq noneRaw)
    (substitutionIsIdentityLike.rawSubst_eq someRaw)
    scrutineeHEq noneHEq someHEq

/-- Either match case for an identity-like substitution. -/
theorem Term.subst_identityLike_eitherMatch_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeHEq :
      HEq (Term.subst termSubst scrutinee) scrutinee)
    (leftHEq :
      HEq (Term.subst termSubst leftBranch) leftBranch)
    (rightHEq :
      HEq (Term.subst termSubst rightBranch) rightBranch) :
    HEq
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch))
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.eitherMatch_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq leftType)
    (substitutionIsIdentityLike.tySubst_eq rightType)
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq scrutineeRaw)
    (substitutionIsIdentityLike.rawSubst_eq leftRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightRaw)
    scrutineeHEq leftHEq rightHEq

/-- Identity reflexivity case for an identity-like substitution. -/
theorem Term.subst_identityLike_refl_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.refl (context := sourceCtx) carrier rawWitness))
      (Term.refl (context := sourceCtx) carrier rawWitness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.refl_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq rawWitness)

/-- Identity eliminator case for an identity-like substitution. -/
theorem Term.subst_identityLike_idJ_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness : Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst termSubst baseCase) baseCase)
    (witnessHEq :
      HEq (Term.subst termSubst witness) witness) :
    HEq
      (Term.subst termSubst (Term.idJ baseCase witness))
      (Term.idJ baseCase witness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.idJ_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq leftEndpoint)
    (substitutionIsIdentityLike.rawSubst_eq rightEndpoint)
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq baseRaw)
    (substitutionIsIdentityLike.rawSubst_eq witnessRaw)
    baseCaseHEq witnessHEq

/-- Observational equality reflexivity case for an identity-like substitution. -/
theorem Term.subst_identityLike_oeqRefl_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.oeqRefl (context := sourceCtx) carrier rawWitness))
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.oeqRefl_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq rawWitness)

/-- Observational equality eliminator case for an identity-like substitution. -/
theorem Term.subst_identityLike_oeqJ_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness : Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst termSubst baseCase) baseCase)
    (witnessHEq :
      HEq (Term.subst termSubst witness) witness) :
    HEq
      (Term.subst termSubst (Term.oeqJ baseCase witness))
      (Term.oeqJ baseCase witness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.oeqJ_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq leftEndpoint)
    (substitutionIsIdentityLike.rawSubst_eq rightEndpoint)
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq baseRaw)
    (substitutionIsIdentityLike.rawSubst_eq witnessRaw)
    baseCaseHEq witnessHEq

/-- Strict identity reflexivity case for an identity-like substitution. -/
theorem Term.subst_identityLike_idStrictRefl_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
          rawWitness))
      (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
        rawWitness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.idStrictRefl_HEq_congr
    modeIsStrict
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq rawWitness)

/-- Strict identity eliminator case for an identity-like substitution. -/
theorem Term.subst_identityLike_idStrictRec_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness : Term sourceCtx
      (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst termSubst baseCase) baseCase)
    (witnessHEq :
      HEq (Term.subst termSubst witness) witness) :
    HEq
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseCase witness))
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  dsimp only [Term.subst]
  exact Term.idStrictRec_HEq_congr
    modeIsStrict
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq leftEndpoint)
    (substitutionIsIdentityLike.rawSubst_eq rightEndpoint)
    (substitutionIsIdentityLike.tySubst_eq motiveType)
    (substitutionIsIdentityLike.rawSubst_eq baseRaw)
    (substitutionIsIdentityLike.rawSubst_eq witnessRaw)
    baseCaseHEq witnessHEq

end LeanFX2
