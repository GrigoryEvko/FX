import LeanFX2.Term

/-! # Term/HEqCongr/Atomic/Base

Base and interval atomic HEq congruences. -/

namespace LeanFX2

/-- HEq congruence for variables at equal positions. -/
theorem Term.var_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {position1 position2 : Fin scope}
    (positionEq : position1 = position2) :
    HEq (Term.var (context := context) position1)
      (Term.var (context := context) position2) := by
  subst positionEq
  rfl

/-- HEq congruence for `Term.unit`. -/
theorem Term.unit_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.unit (context := context)) (Term.unit (context := context)) := by
  rfl

/-- HEq congruence for `Term.boolTrue`. -/
theorem Term.boolTrue_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.boolTrue (context := context))
      (Term.boolTrue (context := context)) := by
  rfl

/-- HEq congruence for `Term.boolFalse`. -/
theorem Term.boolFalse_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.boolFalse (context := context))
      (Term.boolFalse (context := context)) := by
  rfl

/-- HEq congruence for `Term.natZero`. -/
theorem Term.natZero_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.natZero (context := context))
      (Term.natZero (context := context)) := by
  rfl

/-- HEq congruence for `Term.listNil`. -/
theorem Term.listNil_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    (elementTypeEq : elementType1 = elementType2) :
    HEq (Term.listNil (context := context) (elementType := elementType1))
      (Term.listNil (context := context) (elementType := elementType2)) := by
  subst elementTypeEq
  rfl

/-- HEq congruence for `Term.optionNone`. -/
theorem Term.optionNone_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    (elementTypeEq : elementType1 = elementType2) :
    HEq (Term.optionNone (context := context) (elementType := elementType1))
      (Term.optionNone (context := context) (elementType := elementType2)) := by
  subst elementTypeEq
  rfl

/-- HEq congruence for `Term.interval0`. -/
theorem Term.interval0_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.interval0 (context := context))
      (Term.interval0 (context := context)) := by
  rfl

/-- HEq congruence for `Term.interval1`. -/
theorem Term.interval1_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.interval1 (context := context))
      (Term.interval1 (context := context)) := by
  rfl

/-- HEq congruence for interval negation. -/
theorem Term.intervalOpp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerRawEq : innerRaw1 = innerRaw2)
    {innerValue1 : Term context Ty.interval innerRaw1}
    {innerValue2 : Term context Ty.interval innerRaw2}
    (innerValueHEq : HEq innerValue1 innerValue2) :
    HEq (Term.intervalOpp innerValue1) (Term.intervalOpp innerValue2) := by
  subst innerRawEq
  cases innerValueHEq
  rfl

/-- HEq congruence for interval meet. -/
theorem Term.intervalMeet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {leftValue1 : Term context Ty.interval leftRaw1}
    {leftValue2 : Term context Ty.interval leftRaw2}
    (leftValueHEq : HEq leftValue1 leftValue2)
    {rightValue1 : Term context Ty.interval rightRaw1}
    {rightValue2 : Term context Ty.interval rightRaw2}
    (rightValueHEq : HEq rightValue1 rightValue2) :
    HEq (Term.intervalMeet leftValue1 rightValue1)
      (Term.intervalMeet leftValue2 rightValue2) := by
  subst leftRawEq
  subst rightRawEq
  cases leftValueHEq
  cases rightValueHEq
  rfl

/-- HEq congruence for interval join. -/
theorem Term.intervalJoin_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {leftValue1 : Term context Ty.interval leftRaw1}
    {leftValue2 : Term context Ty.interval leftRaw2}
    (leftValueHEq : HEq leftValue1 leftValue2)
    {rightValue1 : Term context Ty.interval rightRaw1}
    {rightValue2 : Term context Ty.interval rightRaw2}
    (rightValueHEq : HEq rightValue1 rightValue2) :
    HEq (Term.intervalJoin leftValue1 rightValue1)
      (Term.intervalJoin leftValue2 rightValue2) := by
  subst leftRawEq
  subst rightRawEq
  cases leftValueHEq
  cases rightValueHEq
  rfl

end LeanFX2
