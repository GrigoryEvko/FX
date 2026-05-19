import LeanFX2.Term.Pointwise.IdentitySubst.IdentityVariableAndBinders

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityRecursive

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## Recursive value cases -/

/-- Natural successor case for ordinary identity substitution. -/
theorem Term.subst_identity_natSucc_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (predecessorHEq :
      HEq (Term.subst (TermSubst.identity context) predecessor)
        predecessor) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natSucc predecessor))
      (Term.natSucc predecessor) := by
  simp only [Term.subst]
  exact Term.natSucc_HEq_congr
    (RawTerm.subst_identity predecessorRaw) predecessorHEq

/-- List cons case for ordinary identity substitution. -/
theorem Term.subst_identity_listCons_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headHEq :
      HEq (Term.subst (TermSubst.identity context) headTerm)
        headTerm)
    (tailHEq :
      HEq (Term.subst (TermSubst.identity context) tailTerm)
        tailTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listCons headTerm tailTerm))
      (Term.listCons headTerm tailTerm) := by
  simp only [Term.subst]
  exact Term.listCons_HEq_congr
    (Ty.subst_identity elementType)
    (RawTerm.subst_identity headRaw)
    (RawTerm.subst_identity tailRaw)
    headHEq tailHEq

/-- Option some case for ordinary identity substitution. -/
theorem Term.subst_identity_optionSome_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (valueHEq :
      HEq (Term.subst (TermSubst.identity context) valueTerm)
        valueTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionSome valueTerm))
      (Term.optionSome valueTerm) := by
  simp only [Term.subst]
  exact Term.optionSome_HEq_congr
    (Ty.subst_identity elementType)
    (RawTerm.subst_identity valueRaw)
    valueHEq

/-- Either-left injection case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherInl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (valueHEq :
      HEq (Term.subst (TermSubst.identity context) valueTerm)
        valueTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherInl (rightType := rightType) valueTerm))
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  simp only [Term.subst]
  exact Term.eitherInl_HEq_congr
    (Ty.subst_identity leftType)
    (Ty.subst_identity rightType)
    (RawTerm.subst_identity valueRaw)
    valueHEq

/-- Either-right injection case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherInr_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (valueHEq :
      HEq (Term.subst (TermSubst.identity context) valueTerm)
        valueTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherInr (leftType := leftType) valueTerm))
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  simp only [Term.subst]
  exact Term.eitherInr_HEq_congr
    (Ty.subst_identity leftType)
    (Ty.subst_identity rightType)
    (RawTerm.subst_identity valueRaw)
    valueHEq

/-- Interval negation case for ordinary identity substitution. -/
theorem Term.subst_identity_intervalOpp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerValue)
        innerValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.intervalOpp innerValue))
      (Term.intervalOpp innerValue) := by
  simp only [Term.subst]
  exact Term.intervalOpp_HEq_congr
    (RawTerm.subst_identity innerRaw) innerHEq

/-- Interval meet case for ordinary identity substitution. -/
theorem Term.subst_identity_intervalMeet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst (TermSubst.identity context) leftValue)
        leftValue)
    (rightHEq :
      HEq (Term.subst (TermSubst.identity context) rightValue)
        rightValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.intervalMeet leftValue rightValue))
      (Term.intervalMeet leftValue rightValue) := by
  simp only [Term.subst]
  exact Term.intervalMeet_HEq_congr
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)
    leftHEq rightHEq

/-- Interval join case for ordinary identity substitution. -/
theorem Term.subst_identity_intervalJoin_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst (TermSubst.identity context) leftValue)
        leftValue)
    (rightHEq :
      HEq (Term.subst (TermSubst.identity context) rightValue)
        rightValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.intervalJoin leftValue rightValue))
      (Term.intervalJoin leftValue rightValue) := by
  simp only [Term.subst]
  exact Term.intervalJoin_HEq_congr
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)
    leftHEq rightHEq

/-- Modal introduction wrapper case for ordinary identity substitution. -/
theorem Term.subst_identity_modIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerTerm)
        innerTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.modIntro innerTerm))
      (Term.modIntro innerTerm) := by
  simp only [Term.subst]
  exact Term.modIntro_HEq_congr
    (Ty.subst_identity innerType)
    (RawTerm.subst_identity innerRaw)
    innerHEq

/-- Modal elimination wrapper case for ordinary identity substitution. -/
theorem Term.subst_identity_modElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerTerm)
        innerTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.modElim innerTerm))
      (Term.modElim innerTerm) := by
  simp only [Term.subst]
  exact Term.modElim_HEq_congr
    (Ty.subst_identity innerType)
    (RawTerm.subst_identity innerRaw)
    innerHEq

/-- Modal subsumption wrapper case for ordinary identity substitution. -/
theorem Term.subst_identity_subsume_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq (Term.subst (TermSubst.identity context) innerTerm)
        innerTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.subsume innerTerm))
      (Term.subsume innerTerm) := by
  simp only [Term.subst]
  exact Term.subsume_HEq_congr
    (Ty.subst_identity innerType)
    (RawTerm.subst_identity innerRaw)
    innerHEq

end LeanFX2
