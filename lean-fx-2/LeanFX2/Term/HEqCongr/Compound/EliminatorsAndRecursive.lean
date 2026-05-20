import LeanFX2.Term

/-! # Term/HEqCongr/Compound/EliminatorsAndRecursive

HEq congruence lemmas for recursive data constructors and eliminators. -/

namespace LeanFX2

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType1 motiveType2 : Ty level (scope + 1)}
    {scrutineeRaw1 scrutineeRaw2 thenRaw1 thenRaw2 elseRaw1 elseRaw2 : RawTerm scope}
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (thenRawEq : thenRaw1 = thenRaw2)
    (elseRawEq : elseRaw1 = elseRaw2)
    {scrutinee1 : Term context Ty.bool scrutineeRaw1}
    {scrutinee2 : Term context Ty.bool scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {thenBranch1 :
      Term context (motiveType1.subst0 Ty.bool RawTerm.boolTrue) thenRaw1}
    {thenBranch2 :
      Term context (motiveType2.subst0 Ty.bool RawTerm.boolTrue) thenRaw2}
    (thenHEq : HEq thenBranch1 thenBranch2)
    {elseBranch1 :
      Term context (motiveType1.subst0 Ty.bool RawTerm.boolFalse) elseRaw1}
    {elseBranch2 :
      Term context (motiveType2.subst0 Ty.bool RawTerm.boolFalse) elseRaw2}
    (elseHEq : HEq elseBranch1 elseBranch2) :
    HEq (Term.boolElim scrutinee1 thenBranch1 elseBranch1)
        (Term.boolElim scrutinee2 thenBranch2 elseBranch2) := by
  subst motiveEq
  subst scrutineeRawEq
  subst thenRawEq
  subst elseRawEq
  cases scrutineeHEq
  cases thenHEq
  cases elseHEq
  rfl

/-- HEq congruence for `Term.natSucc`. -/
theorem Term.natSucc_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {predecessorRaw1 predecessorRaw2 : RawTerm scope}
    (rawEq : predecessorRaw1 = predecessorRaw2)
    {predecessor1 : Term context Ty.nat predecessorRaw1}
    {predecessor2 : Term context Ty.nat predecessorRaw2}
    (predecessorHEq : HEq predecessor1 predecessor2) :
    HEq (Term.natSucc predecessor1) (Term.natSucc predecessor2) := by
  subst rawEq
  cases predecessorHEq
  rfl

/-- HEq congruence for `Term.natElim`. -/
theorem Term.natElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 zeroRaw1 zeroRaw2 succRaw1 succRaw2 : RawTerm scope}
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (zeroRawEq : zeroRaw1 = zeroRaw2)
    (succRawEq : succRaw1 = succRaw2)
    {scrutinee1 : Term context Ty.nat scrutineeRaw1}
    {scrutinee2 : Term context Ty.nat scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {zeroBranch1 : Term context motiveType1 zeroRaw1}
    {zeroBranch2 : Term context motiveType2 zeroRaw2}
    (zeroHEq : HEq zeroBranch1 zeroBranch2)
    {succBranch1 : Term context (Ty.arrow Ty.nat motiveType1) succRaw1}
    {succBranch2 : Term context (Ty.arrow Ty.nat motiveType2) succRaw2}
    (succHEq : HEq succBranch1 succBranch2) :
    HEq (Term.natElim scrutinee1 zeroBranch1 succBranch1)
        (Term.natElim scrutinee2 zeroBranch2 succBranch2) := by
  subst motiveEq
  subst scrutineeRawEq
  subst zeroRawEq
  subst succRawEq
  cases scrutineeHEq
  cases zeroHEq
  cases succHEq
  rfl

/-- HEq congruence for `Term.natRec`. -/
theorem Term.natRec_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 zeroRaw1 zeroRaw2 succRaw1 succRaw2 : RawTerm scope}
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (zeroRawEq : zeroRaw1 = zeroRaw2)
    (succRawEq : succRaw1 = succRaw2)
    {scrutinee1 : Term context Ty.nat scrutineeRaw1}
    {scrutinee2 : Term context Ty.nat scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {zeroBranch1 : Term context motiveType1 zeroRaw1}
    {zeroBranch2 : Term context motiveType2 zeroRaw2}
    (zeroHEq : HEq zeroBranch1 zeroBranch2)
    {succBranch1 : Term context (Ty.arrow Ty.nat (Ty.arrow motiveType1 motiveType1)) succRaw1}
    {succBranch2 : Term context (Ty.arrow Ty.nat (Ty.arrow motiveType2 motiveType2)) succRaw2}
    (succHEq : HEq succBranch1 succBranch2) :
    HEq (Term.natRec scrutinee1 zeroBranch1 succBranch1)
        (Term.natRec scrutinee2 zeroBranch2 succBranch2) := by
  subst motiveEq
  subst scrutineeRawEq
  subst zeroRawEq
  subst succRawEq
  cases scrutineeHEq
  cases zeroHEq
  cases succHEq
  rfl

/-- HEq congruence for `Term.listCons`. -/
theorem Term.listCons_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    {headRaw1 headRaw2 tailRaw1 tailRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (headRawEq : headRaw1 = headRaw2)
    (tailRawEq : tailRaw1 = tailRaw2)
    {head1 : Term context elementType1 headRaw1}
    {head2 : Term context elementType2 headRaw2}
    (headHEq : HEq head1 head2)
    {tail1 : Term context (Ty.listType elementType1) tailRaw1}
    {tail2 : Term context (Ty.listType elementType2) tailRaw2}
    (tailHEq : HEq tail1 tail2) :
    HEq (Term.listCons head1 tail1) (Term.listCons head2 tail2) := by
  subst elementEq
  subst headRawEq
  subst tailRawEq
  cases headHEq
  cases tailHEq
  rfl

/-- HEq congruence for `Term.listElim`. -/
theorem Term.listElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 nilRaw1 nilRaw2 consRaw1 consRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (nilRawEq : nilRaw1 = nilRaw2)
    (consRawEq : consRaw1 = consRaw2)
    {scrutinee1 : Term context (Ty.listType elementType1) scrutineeRaw1}
    {scrutinee2 : Term context (Ty.listType elementType2) scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {nilBranch1 : Term context motiveType1 nilRaw1}
    {nilBranch2 : Term context motiveType2 nilRaw2}
    (nilHEq : HEq nilBranch1 nilBranch2)
    {consBranch1 : Term context (Ty.arrow elementType1 (Ty.arrow (Ty.listType elementType1) motiveType1)) consRaw1}
    {consBranch2 : Term context (Ty.arrow elementType2 (Ty.arrow (Ty.listType elementType2) motiveType2)) consRaw2}
    (consHEq : HEq consBranch1 consBranch2) :
    HEq (Term.listElim scrutinee1 nilBranch1 consBranch1)
        (Term.listElim scrutinee2 nilBranch2 consBranch2) := by
  subst elementEq
  subst motiveEq
  subst scrutineeRawEq
  subst nilRawEq
  subst consRawEq
  cases scrutineeHEq
  cases nilHEq
  cases consHEq
  rfl

/-- HEq congruence for `Term.optionSome`. -/
theorem Term.optionSome_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    {valueRaw1 valueRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (valueRawEq : valueRaw1 = valueRaw2)
    {value1 : Term context elementType1 valueRaw1}
    {value2 : Term context elementType2 valueRaw2}
    (valueHEq : HEq value1 value2) :
    HEq (Term.optionSome value1) (Term.optionSome value2) := by
  subst elementEq
  subst valueRawEq
  cases valueHEq
  rfl

/-- HEq congruence for `Term.optionMatch`. -/
theorem Term.optionMatch_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 noneRaw1 noneRaw2 someRaw1 someRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (noneRawEq : noneRaw1 = noneRaw2)
    (someRawEq : someRaw1 = someRaw2)
    {scrutinee1 : Term context (Ty.optionType elementType1) scrutineeRaw1}
    {scrutinee2 : Term context (Ty.optionType elementType2) scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {noneBranch1 : Term context motiveType1 noneRaw1}
    {noneBranch2 : Term context motiveType2 noneRaw2}
    (noneHEq : HEq noneBranch1 noneBranch2)
    {someBranch1 : Term context (Ty.arrow elementType1 motiveType1) someRaw1}
    {someBranch2 : Term context (Ty.arrow elementType2 motiveType2) someRaw2}
    (someHEq : HEq someBranch1 someBranch2) :
    HEq (Term.optionMatch scrutinee1 noneBranch1 someBranch1)
        (Term.optionMatch scrutinee2 noneBranch2 someBranch2) := by
  subst elementEq
  subst motiveEq
  subst scrutineeRawEq
  subst noneRawEq
  subst someRawEq
  cases scrutineeHEq
  cases noneHEq
  cases someHEq
  rfl

/-- HEq congruence for `Term.eitherInl`. -/
theorem Term.eitherInl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType1 leftType2 rightType1 rightType2 : Ty level scope}
    {valueRaw1 valueRaw2 : RawTerm scope}
    (leftEq : leftType1 = leftType2)
    (rightEq : rightType1 = rightType2)
    (valueRawEq : valueRaw1 = valueRaw2)
    {value1 : Term context leftType1 valueRaw1}
    {value2 : Term context leftType2 valueRaw2}
    (valueHEq : HEq value1 value2) :
    HEq (Term.eitherInl (rightType := rightType1) value1)
        (Term.eitherInl (rightType := rightType2) value2) := by
  subst leftEq
  subst rightEq
  subst valueRawEq
  cases valueHEq
  rfl

/-- HEq congruence for `Term.eitherInr`. -/
theorem Term.eitherInr_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType1 leftType2 rightType1 rightType2 : Ty level scope}
    {valueRaw1 valueRaw2 : RawTerm scope}
    (leftEq : leftType1 = leftType2)
    (rightEq : rightType1 = rightType2)
    (valueRawEq : valueRaw1 = valueRaw2)
    {value1 : Term context rightType1 valueRaw1}
    {value2 : Term context rightType2 valueRaw2}
    (valueHEq : HEq value1 value2) :
    HEq (Term.eitherInr (leftType := leftType1) value1)
        (Term.eitherInr (leftType := leftType2) value2) := by
  subst leftEq
  subst rightEq
  subst valueRawEq
  cases valueHEq
  rfl

/-- HEq congruence for `Term.eitherMatch`. -/
theorem Term.eitherMatch_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType1 leftType2 rightType1 rightType2 motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftEq : leftType1 = leftType2)
    (rightEq : rightType1 = rightType2)
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {scrutinee1 : Term context (Ty.eitherType leftType1 rightType1) scrutineeRaw1}
    {scrutinee2 : Term context (Ty.eitherType leftType2 rightType2) scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {leftBranch1 : Term context (Ty.arrow leftType1 motiveType1) leftRaw1}
    {leftBranch2 : Term context (Ty.arrow leftType2 motiveType2) leftRaw2}
    (leftBranchHEq : HEq leftBranch1 leftBranch2)
    {rightBranch1 : Term context (Ty.arrow rightType1 motiveType1) rightRaw1}
    {rightBranch2 : Term context (Ty.arrow rightType2 motiveType2) rightRaw2}
    (rightBranchHEq : HEq rightBranch1 rightBranch2) :
    HEq (Term.eitherMatch scrutinee1 leftBranch1 rightBranch1)
        (Term.eitherMatch scrutinee2 leftBranch2 rightBranch2) := by
  subst leftEq
  subst rightEq
  subst motiveEq
  subst scrutineeRawEq
  subst leftRawEq
  subst rightRawEq
  cases scrutineeHEq
  cases leftBranchHEq
  cases rightBranchHEq
  rfl

end LeanFX2
