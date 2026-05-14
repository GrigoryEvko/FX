import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

/-! # LeanFX2.Term.Pointwise.IdentitySubst

Typed identity-substitution erasure helpers for the M04 lambda route.

These lemmas are kept out of `PointwiseAndCompositionInfrastructure`
so the identity-erasure cascade can evolve without forcing every edit
through the large composition-infrastructure module. -/

namespace LeanFX2

/-! ## Lifted identity entries -/

/-- Fresh entry of lifted identity substitution. -/
theorem TermSubst.identity_lift_zero_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    HEq
      ((TermSubst.identity context).lift newType
        ⟨0, Nat.zero_lt_succ scope⟩)
      (TermSubst.identity (context.cons newType)
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  change HEq
    ((Ty.weaken_subst_commute (@Subst.identity level scope) newType).symm ▸
      (show
        Term
          (context.cons (newType.subst (@Subst.identity level scope)))
          ((newType.subst (@Subst.identity level scope)).weaken)
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) from
        Term.var
          (context := context.cons
            (newType.subst (@Subst.identity level scope)))
          ⟨0, Nat.zero_lt_succ scope⟩))
    ((Ty.subst_identity (newType.weaken)).symm ▸
      (show
        Term (context.cons newType) newType.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) from
        Term.var
          (context := context.cons newType)
          ⟨0, Nat.zero_lt_succ scope⟩))
  exact HEq.trans
    (Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (@Subst.identity level scope) newType))
    (HEq.trans
      (Term.var_zero_cons_type_eq_heq
        (Ty.subst_identity newType))
      (HEq.symm
        (Term.type_eq_symm_cast_heq
          (context := context.cons newType)
          (typeEq := Ty.subst_identity (newType.weaken))
          (targetTerm := Term.var
            (context := context.cons newType)
            ⟨0, Nat.zero_lt_succ scope⟩))))

/-- Old-variable entry of lifted identity substitution. -/
theorem TermSubst.identity_lift_succ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin scope) :
    HEq
      ((TermSubst.identity context).lift newType (Fin.succ position))
      (TermSubst.identity (context.cons newType) (Fin.succ position)) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  simp only [TermSubst.lift, TermSubst.identity]
  exact HEq.trans
    (Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (@Subst.identity level scope)
        (varType context ⟨positionIndex, positionIsWithinScope⟩)))
    (HEq.trans
      (Term.weaken_head_type_eq_heq
        (Ty.subst_identity newType)
        ((Ty.subst_identity
          (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm ▸
          Term.var ⟨positionIndex, positionIsWithinScope⟩))
      (HEq.trans
        (Term.rename_type_eq_cast_heq
          (TermRenaming.weakenStep context newType)
          (Ty.subst_identity
            (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm
          (Term.var ⟨positionIndex, positionIsWithinScope⟩))
        (HEq.trans
          (Term.type_eq_cast_heq
            (context := context.cons newType)
            (typeEq := congrArg
              (fun someType => Ty.rename someType RawRenaming.weaken)
              (Ty.subst_identity
                (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm)
            (sourceTerm :=
              Term.rename (TermRenaming.weakenStep context newType)
                (Term.var ⟨positionIndex, positionIsWithinScope⟩)))
          (HEq.trans
            (Term.rename_var_HEq
              (TermRenaming.weakenStep context newType)
              ⟨positionIndex, positionIsWithinScope⟩)
            (HEq.symm
              (Term.type_eq_symm_cast_heq
                (context := context.cons newType)
                (typeEq := Ty.subst_identity
                  (varType (context.cons newType)
                    (Fin.succ ⟨positionIndex, positionIsWithinScope⟩)))
                (targetTerm := Term.var
                  (context := context.cons newType)
                  (Fin.succ
                    ⟨positionIndex, positionIsWithinScope⟩))))))))

/-- Lifting identity substitution is pointwise heterogeneously equal
to identity on the extended context. -/
theorem TermSubst.identity_lift_position_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin (scope + 1)) :
    HEq
      ((TermSubst.identity context).lift newType position)
      (TermSubst.identity (context.cons newType) position) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  cases positionIndex with
  | zero =>
      exact TermSubst.identity_lift_zero_HEq
        (context := context) newType
  | succ previousIndex =>
      exact TermSubst.identity_lift_succ_HEq
        (context := context) newType
        ⟨previousIndex,
          Nat.lt_of_succ_lt_succ positionIsWithinScope⟩

/-! ## Lifted identity at the term surface -/

/-- Variable surface case for ordinary identity substitution. -/
theorem Term.subst_identity_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (position : Fin scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.var (context := context) position))
      (Term.var (context := context) position) := by
  simp only [Term.subst, TermSubst.identity]
  exact Term.type_eq_symm_cast_heq
    (context := context)
    (typeEq := Ty.subst_identity (varType context position))
    (targetTerm := Term.var (context := context) position)

/-- Variable surface case for lifted identity substitution. -/
theorem Term.subst_identity_lift_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin (scope + 1)) :
    HEq
      (Term.subst ((TermSubst.identity context).lift newType)
        (Term.var (context := context.cons newType) position))
      (Term.var (context := context.cons newType) position) := by
  simp only [Term.subst]
  exact HEq.trans
    (TermSubst.identity_lift_position_HEq
      (context := context) newType position)
    (Term.type_eq_symm_cast_heq
      (context := context.cons newType)
      (typeEq := Ty.subst_identity
        (varType (context.cons newType) position))
      (targetTerm := Term.var
        (context := context.cons newType) position))

/-! ## Nullary value cases -/

/-- Unit value case for ordinary identity substitution. -/
theorem Term.subst_identity_unit_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.unit (context := context)))
      (Term.unit (context := context)) := by
  rfl

/-- Boolean true case for ordinary identity substitution. -/
theorem Term.subst_identity_boolTrue_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolTrue (context := context)))
      (Term.boolTrue (context := context)) := by
  rfl

/-- Boolean false case for ordinary identity substitution. -/
theorem Term.subst_identity_boolFalse_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolFalse (context := context)))
      (Term.boolFalse (context := context)) := by
  rfl

/-- Natural zero case for ordinary identity substitution. -/
theorem Term.subst_identity_natZero_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natZero (context := context)))
      (Term.natZero (context := context)) := by
  rfl

/-- Left interval endpoint case for ordinary identity substitution. -/
theorem Term.subst_identity_interval0_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.interval0 (context := context)))
      (Term.interval0 (context := context)) := by
  rfl

/-- Right interval endpoint case for ordinary identity substitution. -/
theorem Term.subst_identity_interval1_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.interval1 (context := context)))
      (Term.interval1 (context := context)) := by
  rfl

/-- Empty list case for ordinary identity substitution. -/
theorem Term.subst_identity_listNil_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listNil (context := context) (elementType := elementType)))
      (Term.listNil (context := context) (elementType := elementType)) := by
  simp only [Term.subst]
  exact Term.listNil_HEq_congr (Ty.subst_identity elementType)

/-- Empty option case for ordinary identity substitution. -/
theorem Term.subst_identity_optionNone_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionNone (context := context) (elementType := elementType)))
      (Term.optionNone (context := context) (elementType := elementType)) := by
  simp only [Term.subst]
  exact Term.optionNone_HEq_congr (Ty.subst_identity elementType)

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

/-! ## Equality-family cases -/

/-- Identity reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_refl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.refl (context := context) carrier rawWitness))
      (Term.refl (context := context) carrier rawWitness) := by
  simp only [Term.subst]
  exact Term.refl_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity rawWitness)

/-- Identity eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_idJ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst (TermSubst.identity context) baseCase)
        baseCase)
    (witnessHEq :
      HEq (Term.subst (TermSubst.identity context) witness)
        witness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idJ baseCase witness))
      (Term.idJ baseCase witness) := by
  simp only [Term.subst]
  exact Term.idJ_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity witnessRaw)
    baseCaseHEq witnessHEq

/-- Observational equality reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_oeqRefl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.oeqRefl (context := context) carrier rawWitness))
      (Term.oeqRefl (context := context) carrier rawWitness) := by
  simp only [Term.subst]
  exact Term.oeqRefl_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity rawWitness)

/-- Observational equality eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_oeqJ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst (TermSubst.identity context) baseCase)
        baseCase)
    (witnessHEq :
      HEq (Term.subst (TermSubst.identity context) witness)
        witness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.oeqJ baseCase witness))
      (Term.oeqJ baseCase witness) := by
  simp only [Term.subst]
  exact Term.oeqJ_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity witnessRaw)
    baseCaseHEq witnessHEq

/-- Strict identity reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_idStrictRefl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idStrictRefl (context := context) modeIsStrict carrier
          rawWitness))
      (Term.idStrictRefl (context := context) modeIsStrict carrier
        rawWitness) := by
  simp only [Term.subst]
  exact Term.idStrictRefl_HEq_congr
    modeIsStrict
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity rawWitness)

/-- Strict identity eliminator case for ordinary identity substitution. -/
theorem Term.subst_identity_idStrictRec_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context
      (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseCaseHEq :
      HEq (Term.subst (TermSubst.identity context) baseCase)
        baseCase)
    (witnessHEq :
      HEq (Term.subst (TermSubst.identity context) witness)
        witness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idStrictRec modeIsStrict baseCase witness))
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  simp only [Term.subst]
  exact Term.idStrictRec_HEq_congr
    modeIsStrict
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (Ty.subst_identity motiveType)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity witnessRaw)
    baseCaseHEq witnessHEq

end LeanFX2
