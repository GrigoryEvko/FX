import LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.Base

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeIntro

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## Identity-like substitution at the term surface -/

/-- Variable case for an identity-like substitution. -/
theorem Term.subst_identityLike_var_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (position : Fin scope) :
    HEq
      (Term.subst termSubst
        (Term.var (context := sourceCtx) position))
      (Term.var (context := sourceCtx) position) := by
  simp only [Term.subst]
  exact HEq.trans
    (substitutionIsIdentityLike.entryHEq position)
    (Term.type_eq_symm_cast_heq
      (context := sourceCtx)
      (typeEq := Ty.subst_identity (varType sourceCtx position))
      (targetTerm := Term.var (context := sourceCtx) position))

/-- Unit case for an identity-like substitution. -/
theorem Term.subst_identityLike_unit_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.unit (context := sourceCtx)))
      (Term.unit (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Boolean true case for an identity-like substitution. -/
theorem Term.subst_identityLike_boolTrue_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.boolTrue (context := sourceCtx)))
      (Term.boolTrue (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Boolean false case for an identity-like substitution. -/
theorem Term.subst_identityLike_boolFalse_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.boolFalse (context := sourceCtx)))
      (Term.boolFalse (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Natural zero case for an identity-like substitution. -/
theorem Term.subst_identityLike_natZero_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.natZero (context := sourceCtx)))
      (Term.natZero (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Left interval endpoint case for an identity-like substitution. -/
theorem Term.subst_identityLike_interval0_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.interval0 (context := sourceCtx)))
      (Term.interval0 (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Right interval endpoint case for an identity-like substitution. -/
theorem Term.subst_identityLike_interval1_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst) :
    HEq
      (Term.subst termSubst
        (Term.interval1 (context := sourceCtx)))
      (Term.interval1 (context := sourceCtx)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Empty list case for an identity-like substitution. -/
theorem Term.subst_identityLike_listNil_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope} :
    HEq
      (Term.subst termSubst
        (Term.listNil (context := sourceCtx) (elementType := elementType)))
      (Term.listNil (context := sourceCtx) (elementType := elementType)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.listNil_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)

/-- Empty option case for an identity-like substitution. -/
theorem Term.subst_identityLike_optionNone_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope} :
    HEq
      (Term.subst termSubst
        (Term.optionNone (context := sourceCtx) (elementType := elementType)))
      (Term.optionNone (context := sourceCtx) (elementType := elementType)) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.optionNone_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)

/-- Natural successor case for an identity-like substitution. -/
theorem Term.subst_identityLike_natSucc_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {predecessorRaw : RawTerm scope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorHEq :
      HEq (Term.subst termSubst predecessor) predecessor) :
    HEq
      (Term.subst termSubst (Term.natSucc predecessor))
      (Term.natSucc predecessor) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.natSucc_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq predecessorRaw)
    predecessorHEq

/-- List cons case for an identity-like substitution. -/
theorem Term.subst_identityLike_listCons_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headHEq :
      HEq (Term.subst termSubst headTerm) headTerm)
    (tailHEq :
      HEq (Term.subst termSubst tailTerm) tailTerm) :
    HEq
      (Term.subst termSubst (Term.listCons headTerm tailTerm))
      (Term.listCons headTerm tailTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.listCons_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)
    (substitutionIsIdentityLike.rawSubst_eq headRaw)
    (substitutionIsIdentityLike.rawSubst_eq tailRaw)
    headHEq tailHEq

/-- Option some case for an identity-like substitution. -/
theorem Term.subst_identityLike_optionSome_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueHEq :
      HEq (Term.subst termSubst valueTerm) valueTerm) :
    HEq
      (Term.subst termSubst (Term.optionSome valueTerm))
      (Term.optionSome valueTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.optionSome_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq elementType)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    valueHEq

/-- Either-left injection case for an identity-like substitution. -/
theorem Term.subst_identityLike_eitherInl_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueHEq :
      HEq (Term.subst termSubst valueTerm) valueTerm) :
    HEq
      (Term.subst termSubst
        (Term.eitherInl (rightType := rightType) valueTerm))
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.eitherInl_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq leftType)
    (substitutionIsIdentityLike.tySubst_eq rightType)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    valueHEq

/-- Either-right injection case for an identity-like substitution. -/
theorem Term.subst_identityLike_eitherInr_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueHEq :
      HEq (Term.subst termSubst valueTerm) valueTerm) :
    HEq
      (Term.subst termSubst
        (Term.eitherInr (leftType := leftType) valueTerm))
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.eitherInr_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq leftType)
    (substitutionIsIdentityLike.tySubst_eq rightType)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    valueHEq

/-- Interval negation case for an identity-like substitution. -/
theorem Term.subst_identityLike_intervalOpp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerRaw : RawTerm scope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerValue) innerValue) :
    HEq
      (Term.subst termSubst (Term.intervalOpp innerValue))
      (Term.intervalOpp innerValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.intervalOpp_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Interval meet case for an identity-like substitution. -/
theorem Term.subst_identityLike_intervalMeet_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst termSubst leftValue) leftValue)
    (rightHEq :
      HEq (Term.subst termSubst rightValue) rightValue) :
    HEq
      (Term.subst termSubst (Term.intervalMeet leftValue rightValue))
      (Term.intervalMeet leftValue rightValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.intervalMeet_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq leftRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightRaw)
    leftHEq rightHEq

/-- Interval join case for an identity-like substitution. -/
theorem Term.subst_identityLike_intervalJoin_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftHEq :
      HEq (Term.subst termSubst leftValue) leftValue)
    (rightHEq :
      HEq (Term.subst termSubst rightValue) rightValue) :
    HEq
      (Term.subst termSubst (Term.intervalJoin leftValue rightValue))
      (Term.intervalJoin leftValue rightValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.intervalJoin_HEq_congr
    (substitutionIsIdentityLike.rawSubst_eq leftRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightRaw)
    leftHEq rightHEq

/-- Modal introduction wrapper case for an identity-like substitution. -/
theorem Term.subst_identityLike_modIntro_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerTerm) innerTerm) :
    HEq
      (Term.subst termSubst (Term.modIntro innerTerm))
      (Term.modIntro innerTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.modIntro_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq innerType)
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Modal elimination wrapper case for an identity-like substitution. -/
theorem Term.subst_identityLike_modElim_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerTerm) innerTerm) :
    HEq
      (Term.subst termSubst (Term.modElim innerTerm))
      (Term.modElim innerTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.modElim_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq innerType)
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

/-- Modal subsumption wrapper case for an identity-like substitution. -/
theorem Term.subst_identityLike_subsume_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerHEq :
      HEq (Term.subst termSubst innerTerm) innerTerm) :
    HEq
      (Term.subst termSubst (Term.subsume innerTerm))
      (Term.subsume innerTerm) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.subsume_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq innerType)
    (substitutionIsIdentityLike.rawSubst_eq innerRaw)
    innerHEq

end LeanFX2
