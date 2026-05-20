import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.LiftCompose

/-! # LeanFX2.Term.Pointwise.EliminatorArms

weaken-subst-singleton arms for the eliminator family: boolElim, natElim,
natRec, listElim, optionMatch, eitherMatch.  Each carries a motive that
travels under a fresh binder, so these are the dependent-pattern-match
heart of the cascade.

## Root status

Kernel — eliminator arms of the Pointwise weaken-then-singleton cascade. -/

namespace LeanFX2

/-- Boolean elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_boolElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (thenHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType thenBranch))
        thenBranch)
    (elseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType elseBranch))
        elseBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.boolElim scrutinee thenBranch elseBranch)))
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  simp only [Term.weaken, Term.rename]
  have scrutineeWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            scrutinee))
        scrutinee := by
    simpa only [Term.weaken] using scrutineeHEq
  have thenWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            thenBranch))
        thenBranch := by
    simpa only [Term.weaken] using thenHEq
  have elseWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            elseBranch))
        elseBranch := by
    simpa only [Term.weaken] using elseHEq
  have innerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute motiveType Ty.bool
            scrutineeRaw RawRenaming.weaken).symm ▸
            Term.boolElim
              (motiveType := motiveType.rename RawRenaming.weaken.lift)
              (Term.rename (TermRenaming.weakenStep context newType)
                scrutinee)
              ((Ty.subst0_rename_commute motiveType Ty.bool
                RawTerm.boolTrue RawRenaming.weaken) ▸
                Term.rename (TermRenaming.weakenStep context newType)
                  thenBranch)
              ((Ty.subst0_rename_commute motiveType Ty.bool
                RawTerm.boolFalse RawRenaming.weaken) ▸
                Term.rename (TermRenaming.weakenStep context newType)
                  elseBranch)))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.boolElim
            (motiveType := motiveType.rename RawRenaming.weaken.lift)
            (Term.rename (TermRenaming.weakenStep context newType)
              scrutinee)
            ((Ty.subst0_rename_commute motiveType Ty.bool
              RawTerm.boolTrue RawRenaming.weaken) ▸
              Term.rename (TermRenaming.weakenStep context newType)
                thenBranch)
            ((Ty.subst0_rename_commute motiveType Ty.bool
              RawTerm.boolFalse RawRenaming.weaken) ▸
              Term.rename (TermRenaming.weakenStep context newType)
                elseBranch))) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      (Ty.subst0_rename_commute motiveType Ty.bool
        scrutineeRaw RawRenaming.weaken).symm
      (Term.boolElim
        (motiveType := motiveType.rename RawRenaming.weaken.lift)
        (Term.rename (TermRenaming.weakenStep context newType)
          scrutinee)
        ((Ty.subst0_rename_commute motiveType Ty.bool
          RawTerm.boolTrue RawRenaming.weaken) ▸
          Term.rename (TermRenaming.weakenStep context newType)
            thenBranch)
        ((Ty.subst0_rename_commute motiveType Ty.bool
          RawTerm.boolFalse RawRenaming.weaken) ▸
          Term.rename (TermRenaming.weakenStep context newType)
            elseBranch))
  have thenInnerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolTrue RawRenaming.weaken) ▸
            Term.rename (TermRenaming.weakenStep context newType)
              thenBranch))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            thenBranch)) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      (Ty.subst0_rename_commute motiveType Ty.bool
        RawTerm.boolTrue RawRenaming.weaken)
      (Term.rename (TermRenaming.weakenStep context newType)
        thenBranch)
  have elseInnerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolFalse RawRenaming.weaken) ▸
            Term.rename (TermRenaming.weakenStep context newType)
              elseBranch))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            elseBranch)) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      (Ty.subst0_rename_commute motiveType Ty.bool
        RawTerm.boolFalse RawRenaming.weaken)
      (Term.rename (TermRenaming.weakenStep context newType)
        elseBranch)
  let substitutedMotive :=
    (motiveType.rename RawRenaming.weaken.lift).subst
      (Subst.singleton newType singletonRaw).lift
  let substitutedScrutinee :=
    Term.subst (TermSubst.singleton singletonTerm)
      (Term.rename (TermRenaming.weakenStep context newType)
        scrutinee)
  let substitutedThen :=
    Term.subst (TermSubst.singleton singletonTerm)
      (Term.rename (TermRenaming.weakenStep context newType)
        thenBranch)
  let substitutedElse :=
    Term.subst (TermSubst.singleton singletonTerm)
      (Term.rename (TermRenaming.weakenStep context newType)
        elseBranch)
  let substitutedThenWithInnerCast :=
    Term.subst (TermSubst.singleton singletonTerm)
      ((Ty.subst0_rename_commute motiveType Ty.bool
        RawTerm.boolTrue RawRenaming.weaken) ▸
        Term.rename (TermRenaming.weakenStep context newType)
          thenBranch)
  let substitutedElseWithInnerCast :=
    Term.subst (TermSubst.singleton singletonTerm)
      ((Ty.subst0_rename_commute motiveType Ty.bool
        RawTerm.boolFalse RawRenaming.weaken) ▸
        Term.rename (TermRenaming.weakenStep context newType)
          elseBranch)
  let thenOuterEq :=
    Ty.subst0_subst_commute
      (motiveType.rename RawRenaming.weaken.lift)
      Ty.bool RawTerm.boolTrue
      (Subst.singleton newType singletonRaw)
  let elseOuterEq :=
    Ty.subst0_subst_commute
      (motiveType.rename RawRenaming.weaken.lift)
      Ty.bool RawTerm.boolFalse
      (Subst.singleton newType singletonRaw)
  have thenOuterInnerHEq :
      HEq (thenOuterEq ▸ substitutedThenWithInnerCast)
        substitutedThenWithInnerCast :=
    Term.type_eq_cast_heq thenOuterEq substitutedThenWithInnerCast
  have elseOuterInnerHEq :
      HEq (elseOuterEq ▸ substitutedElseWithInnerCast)
        substitutedElseWithInnerCast :=
    Term.type_eq_cast_heq elseOuterEq substitutedElseWithInnerCast
  have thenFullBranchHEq :
      HEq (thenOuterEq ▸ substitutedThenWithInnerCast) thenBranch :=
    HEq.trans thenOuterInnerHEq
      (HEq.trans thenInnerCastHEq thenWithoutCastsHEq)
  have elseFullBranchHEq :
      HEq (elseOuterEq ▸ substitutedElseWithInnerCast) elseBranch :=
    HEq.trans elseOuterInnerHEq
      (HEq.trans elseInnerCastHEq elseWithoutCastsHEq)
  have boolElimWithoutOuterCastHEq :
      HEq
        (Term.boolElim (motiveType := substitutedMotive)
          substitutedScrutinee
          (thenOuterEq ▸ substitutedThenWithInnerCast)
          (elseOuterEq ▸ substitutedElseWithInnerCast))
        (Term.boolElim scrutinee thenBranch elseBranch) :=
    Term.boolElim_HEq_congr
      (Ty.weaken_lift_subst_singleton_lift motiveType newType singletonRaw)
      (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
      (RawTerm.weaken_subst_singleton thenRaw singletonRaw)
      (RawTerm.weaken_subst_singleton elseRaw singletonRaw)
      scrutineeWithoutCastsHEq
      thenFullBranchHEq
      elseFullBranchHEq
  have outerCastHEq :
      HEq
        ((Ty.subst0_subst_commute
            (motiveType.rename RawRenaming.weaken.lift)
            Ty.bool
            (scrutineeRaw.rename RawRenaming.weaken)
            (Subst.singleton newType singletonRaw)).symm ▸
          Term.boolElim (motiveType := substitutedMotive)
            substitutedScrutinee
            (thenOuterEq ▸ substitutedThenWithInnerCast)
            (elseOuterEq ▸ substitutedElseWithInnerCast))
        (Term.boolElim (motiveType := substitutedMotive)
          substitutedScrutinee
          (thenOuterEq ▸ substitutedThenWithInnerCast)
          (elseOuterEq ▸ substitutedElseWithInnerCast)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute
        (motiveType.rename RawRenaming.weaken.lift)
        Ty.bool
        (scrutineeRaw.rename RawRenaming.weaken)
        (Subst.singleton newType singletonRaw)).symm
      (Term.boolElim (motiveType := substitutedMotive)
        substitutedScrutinee
        (thenOuterEq ▸ substitutedThenWithInnerCast)
        (elseOuterEq ▸ substitutedElseWithInnerCast))
  exact HEq.trans innerCastHEq
    (HEq.trans outerCastHEq boolElimWithoutOuterCastHEq)

/-- Natural elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (zeroHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType zeroBranch))
        zeroBranch)
    (succHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType succBranch))
        succBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.natElim scrutinee zeroBranch succBranch)))
      (Term.natElim scrutinee zeroBranch succBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.natElim_HEq_congr
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton zeroRaw singletonRaw)
    (RawTerm.weaken_subst_singleton succRaw singletonRaw)
    scrutineeHEq zeroHEq succHEq

/-- Natural recursion preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natRec_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (zeroHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType zeroBranch))
        zeroBranch)
    (succHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType succBranch))
        succBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.natRec scrutinee zeroBranch succBranch)))
      (Term.natRec scrutinee zeroBranch succBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.natRec_HEq_congr
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton zeroRaw singletonRaw)
    (RawTerm.weaken_subst_singleton succRaw singletonRaw)
    scrutineeHEq zeroHEq succHEq

/-- List elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (nilHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType nilBranch))
        nilBranch)
    (consHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType consBranch))
        consBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.listElim scrutinee nilBranch consBranch)))
      (Term.listElim scrutinee nilBranch consBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.listElim_HEq_congr
    (Ty.weaken_subst_singleton elementType newType singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton nilRaw singletonRaw)
    (RawTerm.weaken_subst_singleton consRaw singletonRaw)
    scrutineeHEq nilHEq consHEq

/-- Option matching preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionMatch_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (noneHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType noneBranch))
        noneBranch)
    (someHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType someBranch))
        someBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.optionMatch scrutinee noneBranch someBranch)))
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.optionMatch_HEq_congr
    (Ty.weaken_subst_singleton elementType newType singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton noneRaw singletonRaw)
    (RawTerm.weaken_subst_singleton someRaw singletonRaw)
    scrutineeHEq noneHEq someHEq

/-- Either matching preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherMatch_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType scrutinee))
        scrutinee)
    (leftHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType leftBranch))
        leftBranch)
    (rightHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType rightBranch))
        rightBranch) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.eitherMatch scrutinee leftBranch rightBranch)))
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherMatch_HEq_congr
    (Ty.weaken_subst_singleton leftType newType singletonRaw)
    (Ty.weaken_subst_singleton rightType newType singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton scrutineeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton leftRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightRaw singletonRaw)
    scrutineeHEq leftHEq rightHEq


end LeanFX2
