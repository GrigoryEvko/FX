import LeanFX2.Reducibility.FundamentalAliases

/-! # LeanFX2.Reducibility.FundamentalCubical.IdentitySubstEliminators

Identity-substitution SN endpoints for the ι-eliminator family:
`boolElim`, `natElim`, `natRec`, `listElim`, `optionMatch`,
`eitherMatch`.  Each projects SN of a reducible scrutinee + arms
through the identity substitution.

## Root status

Layer 3 metatheory leaf.  Fourth slice of `FundamentalCubical`. -/

namespace LeanFX2


/-- **K12.27 identity-substitution boolean eliminator SN endpoint**.

Boolean elimination is SN-output at the current motive boundary.  This
identity wrapper exposes the exact M04 consequence from reducibility of
the scrutinee and both branches. -/
theorem Reducible.fundamental_identity_boolElim_at_bool_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.bool : Ty level scope).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (thenIdentityReducible :
      Reducible
        ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst
          Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) thenBranch))
    (elseIdentityReducible :
      Reducible
        ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst
          Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) elseBranch)) :
    Term.isStronglyNormalizing
      (Term.boolElim scrutinee thenBranch elseBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.boolElim scrutinee thenBranch elseBranch)
    (Reducible.fundamental_boolElim_at_bool
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible thenIdentityReducible
      elseIdentityReducible)

/-- **K12.27 identity-substitution natural eliminator SN endpoint**.

The current natural eliminator fundamental is SN-output and keeps the
successor-application closure explicit.  This identity wrapper only erases
the identity substitution from that exact endpoint; it does not claim a
full motive-type reducibility closure. -/
theorem Reducible.fundamental_identity_natElim_at_nat_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.nat : Ty level scope).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (zeroIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) zeroBranch))
    (succIdentityReducible :
      Reducible ((Ty.arrow Ty.nat motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) succBranch))
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succRaw predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.natElim scrutinee zeroBranch succBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.natElim scrutinee zeroBranch succBranch)
    (Reducible.fundamental_natElim_at_nat
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible zeroIdentityReducible
      succIdentityReducible
      (by
        intro predecessorRaw predecessorIsSN
        rw [RawTerm.subst_identity succRaw]
        exact succAppIsSN predecessorIsSN))

/-- **K12.27 identity-substitution natural recursor SN endpoint**.

As with `fundamental_identity_natElim_at_nat_sn`, the recursive
contractum closure is an explicit M04 obligation.  The theorem is an
identity-route bridge, not a full recursive-motive reducibility theorem. -/
theorem Reducible.fundamental_identity_natRec_at_nat_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.nat : Ty level scope).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (zeroIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) zeroBranch))
    (succIdentityReducible :
      Reducible
        ((Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)).subst
          Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) succBranch))
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.natRec scrutinee zeroBranch succBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.natRec scrutinee zeroBranch succBranch)
    (Reducible.fundamental_natRec_at_nat
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible zeroIdentityReducible
      succIdentityReducible
      (by
        intro predecessorRaw zeroTargetRaw succTargetRaw
          predecessorIsSN zeroTargetIsSN succTargetIsSN
        exact contractumIsSN predecessorIsSN zeroTargetIsSN
          succTargetIsSN))

/-- **K12.27 identity-substitution list eliminator SN endpoint**.

The current list eliminator endpoint keeps the cons-application closure
explicit because the list candidate tracks the tail at SN only.  This
identity wrapper preserves that exact obligation. -/
theorem Reducible.fundamental_identity_listElim_at_listType_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.listType elementType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (nilIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) nilBranch))
    (consIdentityReducible :
      Reducible
        ((Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)).subst
            Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) consBranch))
    (consAppIsSN :
      ∀ {headRaw tailRaw : RawTerm scope}
        (headTerm :
          Term sourceCtx (elementType.subst Subst.identity) headRaw)
        (tailTerm :
          Term sourceCtx ((Ty.listType elementType).subst Subst.identity)
            tailRaw),
        Reducible (elementType.subst Subst.identity) headTerm →
        Term.isStronglyNormalizing tailTerm →
        Term.isStronglyNormalizing
          (Term.app
            (Term.app
              (Term.subst (TermSubst.identity sourceCtx) consBranch)
              headTerm)
            tailTerm)) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.listElim scrutinee nilBranch consBranch)
    (Reducible.fundamental_listElim_at_listType
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible nilIdentityReducible
      consIdentityReducible
      (by
        intro headRaw tailRaw headTerm tailTerm headReducible tailIsSN
        exact consAppIsSN headTerm tailTerm headReducible tailIsSN))

/-- **K12.27 identity-substitution option match SN endpoint**. -/
theorem Reducible.fundamental_identity_optionMatch_at_optionType_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.optionType elementType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (noneIdentityReducible :
      Reducible (motiveType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) noneBranch))
    (someIdentityReducible :
      Reducible ((Ty.arrow elementType motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) someBranch)) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.optionMatch scrutinee noneBranch someBranch)
    (Reducible.fundamental_optionMatch_at_optionType
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible noneIdentityReducible
      someIdentityReducible)

/-- **K12.27 identity-substitution either match SN endpoint**. -/
theorem Reducible.fundamental_identity_eitherMatch_at_eitherType_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIdentityReducible :
      Reducible ((Ty.eitherType leftType rightType).subst
        Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) scrutinee))
    (leftIdentityReducible :
      Reducible ((Ty.arrow leftType motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) leftBranch))
    (rightIdentityReducible :
      Reducible ((Ty.arrow rightType motiveType).subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) rightBranch)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) :=
  Term.strong_normalization_of_identity_subst
    (Term.eitherMatch scrutinee leftBranch rightBranch)
    (Reducible.fundamental_eitherMatch_at_eitherType
      (termSubst := TermSubst.identity sourceCtx)
      scrutineeIdentityReducible leftIdentityReducible
      rightIdentityReducible)

end LeanFX2
