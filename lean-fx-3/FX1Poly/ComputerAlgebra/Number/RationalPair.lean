import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntExactDivision
import FX1Poly.ComputerAlgebra.Number.NatGreatestCommonDivisor

/-! # RationalPair — the ℚ carrier (NUM-Q-1)

The ℚ rung of the zero-axiom number tower: a rational is a pair
`numerator / (denominatorPredecessor + 1)`.  The SUCCESSOR SHAPE makes denominator
positivity STRUCTURAL — no subtype, no invariant to thread, no proof field to
transport.  Sameness is the cross-multiplication setoid `a/b ~ c/d ⟺ a·d = c·b`,
decidable because it IS an `Int` equality.

Transitivity is the one contentful law: scale the target equation by the middle
denominator, walk a right-commutation chain through both hypotheses, and cancel —
the cancellation is exactly `intMulRightCancel` at the middle denominator, whose
positivity the successor shape hands over for free.  This is the same
scale-chain-cancel shape as `denotesSameAsTrans` on the float carrier, with the
radix-power plumbing gone. -/

namespace FX1Poly.ComputerAlgebra

/-- A rational number as a pair: `numerator / (denominatorPredecessor + 1)`. -/
structure RationalPair where
  numerator : Int
  denominatorPredecessor : Nat

namespace RationalPair

/-- The denominator, read back as an `Int` — always a successor, hence positive. -/
def denominatorInt (value : RationalPair) : Int :=
  Int.ofNat (value.denominatorPredecessor + 1)

/-- Structural denominator positivity — the successor shape pays out. -/
theorem denominatorIntIsPositive (value : RationalPair) :
    (0 : Int) < denominatorInt value :=
  intOfNatLeOfNat (Nat.le.intro (Nat.add_comm 1 value.denominatorPredecessor))

/-- **Value equality by cross-multiplication** — `a/b` and `c/d` denote the same
rational exactly when `a * d = c * b`. -/
def DenotesSameAs (leftValue rightValue : RationalPair) : Prop :=
  leftValue.numerator * denominatorInt rightValue =
    rightValue.numerator * denominatorInt leftValue

/-- The setoid is decidable — it IS an `Int` equality (`Int.decEq` is clean). -/
def decideDenotesSameAs (leftValue rightValue : RationalPair) :
    Decidable (DenotesSameAs leftValue rightValue) :=
  Int.decEq (leftValue.numerator * denominatorInt rightValue)
    (rightValue.numerator * denominatorInt leftValue)

/-- Reflexivity — both cross-products are the same term. -/
theorem denotesSameAsRefl (value : RationalPair) : DenotesSameAs value value := rfl

/-- Symmetry — cross-multiplication is symmetric by construction. -/
theorem denotesSameAsSymm {leftValue rightValue : RationalPair}
    (areSame : DenotesSameAs leftValue rightValue) :
    DenotesSameAs rightValue leftValue := areSame.symm

/-- **Transitivity** — scale by the middle denominator, chain five
right-commutation steps through both hypotheses, cancel the positive middle
denominator. -/
theorem denotesSameAsTrans {firstValue middleValue lastValue : RationalPair}
    (firstAgrees : DenotesSameAs firstValue middleValue)
    (secondAgrees : DenotesSameAs middleValue lastValue) :
    DenotesSameAs firstValue lastValue :=
  intMulRightCancel (denominatorIntIsPositive middleValue)
    ((intMulRightComm firstValue.numerator (denominatorInt lastValue)
        (denominatorInt middleValue)).trans
      ((congrArg (· * denominatorInt lastValue) firstAgrees).trans
        ((intMulRightComm middleValue.numerator (denominatorInt firstValue)
            (denominatorInt lastValue)).trans
          ((congrArg (· * denominatorInt firstValue) secondAgrees).trans
            (intMulRightComm lastValue.numerator (denominatorInt middleValue)
              (denominatorInt firstValue))))))

/-! ## Exact field operations (NUM-Q-2)

Addition and multiplication both land on the PRODUCT denominator.  Built
predecessor-shaped — `(leftPredecessor + 1) * rightPredecessor + leftPredecessor` —
its successor is DEFINITIONALLY `(leftPredecessor + 1) * (rightPredecessor + 1)`
(`Nat.mul` recurses on its second argument, `Nat.add` on its second), so the
"result denominator = product of denominators" equations are `rfl`.  Every
congruence is then one `intRightDistrib` dispatch over per-term
`intMulSwapMiddle` chains threading the cross-multiplication hypothesis. -/

/-- Exact addition: `a/b + c/d = (a*d + c*b) / (b*d)`. -/
def addExact (leftValue rightValue : RationalPair) : RationalPair :=
  { numerator := leftValue.numerator * denominatorInt rightValue +
      rightValue.numerator * denominatorInt leftValue
    denominatorPredecessor :=
      (leftValue.denominatorPredecessor + 1) * rightValue.denominatorPredecessor +
        leftValue.denominatorPredecessor }

/-- The addition numerator, definitional. -/
theorem addExactNumerator (leftValue rightValue : RationalPair) :
    (addExact leftValue rightValue).numerator =
      leftValue.numerator * denominatorInt rightValue +
        rightValue.numerator * denominatorInt leftValue := rfl

/-- The addition denominator IS the product of the denominators — definitional,
by the predecessor-shaped construction. -/
theorem addExactDenominatorInt (leftValue rightValue : RationalPair) :
    denominatorInt (addExact leftValue rightValue) =
      denominatorInt leftValue * denominatorInt rightValue := rfl

/-- Exact multiplication: `(a/b) * (c/d) = (a*c) / (b*d)`. -/
def mulExact (leftValue rightValue : RationalPair) : RationalPair :=
  { numerator := leftValue.numerator * rightValue.numerator
    denominatorPredecessor :=
      (leftValue.denominatorPredecessor + 1) * rightValue.denominatorPredecessor +
        leftValue.denominatorPredecessor }

/-- The multiplication numerator, definitional. -/
theorem mulExactNumerator (leftValue rightValue : RationalPair) :
    (mulExact leftValue rightValue).numerator =
      leftValue.numerator * rightValue.numerator := rfl

/-- The multiplication denominator IS the product of the denominators —
definitional. -/
theorem mulExactDenominatorInt (leftValue rightValue : RationalPair) :
    denominatorInt (mulExact leftValue rightValue) =
      denominatorInt leftValue * denominatorInt rightValue := rfl

/-- Exact negation: flip the numerator, keep the denominator. -/
def negExact (value : RationalPair) : RationalPair :=
  { numerator := -value.numerator
    denominatorPredecessor := value.denominatorPredecessor }

/-- **Addition respects the setoid on the left**: distribute, fix each summand by
one `intMulSwapMiddle` chain (the hypothesis enters the first term; the second term
is EXACTLY one middle swap), and fold back. -/
theorem addExactCongrLeft {leftValue newLeftValue : RationalPair}
    (rightValue : RationalPair)
    (leftAgrees : DenotesSameAs leftValue newLeftValue) :
    DenotesSameAs (addExact leftValue rightValue)
      (addExact newLeftValue rightValue) :=
  have firstTermAgrees :
      leftValue.numerator * denominatorInt rightValue *
        (denominatorInt newLeftValue * denominatorInt rightValue) =
      newLeftValue.numerator * denominatorInt rightValue *
        (denominatorInt leftValue * denominatorInt rightValue) :=
    (intMulSwapMiddle leftValue.numerator (denominatorInt rightValue)
        (denominatorInt newLeftValue) (denominatorInt rightValue)).trans
      ((congrArg (· * (denominatorInt rightValue * denominatorInt rightValue))
          leftAgrees).trans
        (intMulSwapMiddle newLeftValue.numerator (denominatorInt leftValue)
          (denominatorInt rightValue) (denominatorInt rightValue)))
  have secondTermAgrees :
      rightValue.numerator * denominatorInt leftValue *
        (denominatorInt newLeftValue * denominatorInt rightValue) =
      rightValue.numerator * denominatorInt newLeftValue *
        (denominatorInt leftValue * denominatorInt rightValue) :=
    intMulSwapMiddle rightValue.numerator (denominatorInt leftValue)
      (denominatorInt newLeftValue) (denominatorInt rightValue)
  (intRightDistrib (leftValue.numerator * denominatorInt rightValue)
      (rightValue.numerator * denominatorInt leftValue)
      (denominatorInt newLeftValue * denominatorInt rightValue)).trans
    ((congrArg
        (· + rightValue.numerator * denominatorInt leftValue *
          (denominatorInt newLeftValue * denominatorInt rightValue))
        firstTermAgrees).trans
      ((congrArg
          (newLeftValue.numerator * denominatorInt rightValue *
            (denominatorInt leftValue * denominatorInt rightValue) + ·)
          secondTermAgrees).trans
        (intRightDistrib (newLeftValue.numerator * denominatorInt rightValue)
          (rightValue.numerator * denominatorInt newLeftValue)
          (denominatorInt leftValue * denominatorInt rightValue)).symm))

/-- **Addition respects the setoid on the right** — the mirror dispatch; the
right-denominator swaps route through one extra commutation per term. -/
theorem addExactCongrRight (leftValue : RationalPair)
    {rightValue newRightValue : RationalPair}
    (rightAgrees : DenotesSameAs rightValue newRightValue) :
    DenotesSameAs (addExact leftValue rightValue)
      (addExact leftValue newRightValue) :=
  have firstTermAgrees :
      leftValue.numerator * denominatorInt rightValue *
        (denominatorInt leftValue * denominatorInt newRightValue) =
      leftValue.numerator * denominatorInt newRightValue *
        (denominatorInt leftValue * denominatorInt rightValue) :=
    (intMulSwapMiddle leftValue.numerator (denominatorInt rightValue)
        (denominatorInt leftValue) (denominatorInt newRightValue)).trans
      ((congrArg (leftValue.numerator * denominatorInt leftValue * ·)
          (intMulComm (denominatorInt rightValue)
            (denominatorInt newRightValue))).trans
        (intMulSwapMiddle leftValue.numerator (denominatorInt newRightValue)
          (denominatorInt leftValue) (denominatorInt rightValue)).symm)
  have secondTermAgrees :
      rightValue.numerator * denominatorInt leftValue *
        (denominatorInt leftValue * denominatorInt newRightValue) =
      newRightValue.numerator * denominatorInt leftValue *
        (denominatorInt leftValue * denominatorInt rightValue) :=
    (congrArg (rightValue.numerator * denominatorInt leftValue * ·)
        (intMulComm (denominatorInt leftValue)
          (denominatorInt newRightValue))).trans
      ((intMulSwapMiddle rightValue.numerator (denominatorInt leftValue)
          (denominatorInt newRightValue) (denominatorInt leftValue)).trans
        ((congrArg (· * (denominatorInt leftValue * denominatorInt leftValue))
            rightAgrees).trans
          ((intMulSwapMiddle newRightValue.numerator (denominatorInt leftValue)
              (denominatorInt rightValue) (denominatorInt leftValue)).symm.trans
            (congrArg (newRightValue.numerator * denominatorInt leftValue * ·)
              (intMulComm (denominatorInt rightValue)
                (denominatorInt leftValue))))))
  (intRightDistrib (leftValue.numerator * denominatorInt rightValue)
      (rightValue.numerator * denominatorInt leftValue)
      (denominatorInt leftValue * denominatorInt newRightValue)).trans
    ((congrArg
        (· + rightValue.numerator * denominatorInt leftValue *
          (denominatorInt leftValue * denominatorInt newRightValue))
        firstTermAgrees).trans
      ((congrArg
          (leftValue.numerator * denominatorInt newRightValue *
            (denominatorInt leftValue * denominatorInt rightValue) + ·)
          secondTermAgrees).trans
        (intRightDistrib (leftValue.numerator * denominatorInt newRightValue)
          (newRightValue.numerator * denominatorInt leftValue)
          (denominatorInt leftValue * denominatorInt rightValue)).symm))

/-- **Addition is a setoid congruence** — chain the two one-sided congruences. -/
theorem addExactRespectsDenotesSameAs
    {leftValue newLeftValue rightValue newRightValue : RationalPair}
    (leftAgrees : DenotesSameAs leftValue newLeftValue)
    (rightAgrees : DenotesSameAs rightValue newRightValue) :
    DenotesSameAs (addExact leftValue rightValue)
      (addExact newLeftValue newRightValue) :=
  denotesSameAsTrans (addExactCongrLeft rightValue leftAgrees)
    (addExactCongrRight newLeftValue rightAgrees)

/-- **Multiplication respects the setoid on the left** — one swap in, hypothesis,
one swap out. -/
theorem mulExactCongrLeft {leftValue newLeftValue : RationalPair}
    (rightValue : RationalPair)
    (leftAgrees : DenotesSameAs leftValue newLeftValue) :
    DenotesSameAs (mulExact leftValue rightValue)
      (mulExact newLeftValue rightValue) :=
  (intMulSwapMiddle leftValue.numerator rightValue.numerator
      (denominatorInt newLeftValue) (denominatorInt rightValue)).trans
    ((congrArg (· * (rightValue.numerator * denominatorInt rightValue))
        leftAgrees).trans
      (intMulSwapMiddle newLeftValue.numerator rightValue.numerator
        (denominatorInt leftValue) (denominatorInt rightValue)).symm)

/-- **Multiplication respects the setoid on the right** — the mirror. -/
theorem mulExactCongrRight (leftValue : RationalPair)
    {rightValue newRightValue : RationalPair}
    (rightAgrees : DenotesSameAs rightValue newRightValue) :
    DenotesSameAs (mulExact leftValue rightValue)
      (mulExact leftValue newRightValue) :=
  (intMulSwapMiddle leftValue.numerator rightValue.numerator
      (denominatorInt leftValue) (denominatorInt newRightValue)).trans
    ((congrArg (leftValue.numerator * denominatorInt leftValue * ·)
        rightAgrees).trans
      (intMulSwapMiddle leftValue.numerator newRightValue.numerator
        (denominatorInt leftValue) (denominatorInt rightValue)).symm)

/-- **Multiplication is a setoid congruence** — chain the two one-sided
congruences. -/
theorem mulExactRespectsDenotesSameAs
    {leftValue newLeftValue rightValue newRightValue : RationalPair}
    (leftAgrees : DenotesSameAs leftValue newLeftValue)
    (rightAgrees : DenotesSameAs rightValue newRightValue) :
    DenotesSameAs (mulExact leftValue rightValue)
      (mulExact newLeftValue newRightValue) :=
  denotesSameAsTrans (mulExactCongrLeft rightValue leftAgrees)
    (mulExactCongrRight newLeftValue rightAgrees)

/-- **Negation is a setoid congruence** — pull the sign out of both
cross-products around the hypothesis. -/
theorem negExactRespectsDenotesSameAs {leftValue rightValue : RationalPair}
    (areSame : DenotesSameAs leftValue rightValue) :
    DenotesSameAs (negExact leftValue) (negExact rightValue) :=
  (intNegMul leftValue.numerator (denominatorInt rightValue)).trans
    ((congrArg Int.neg areSame).trans
      (intNegMul rightValue.numerator (denominatorInt leftValue)).symm)

/-! ## The cross-multiplication order (NUM-Q-3)

`a/b <= c/d ⟺ a·d <= c·b` — valid because both denominators are structurally
positive.  Same shape as the float carrier's cross-aligned order: decidable,
reflexive, total; antisymmetry lands ON THE SETOID (mutual bounds force
cross-equality); transitivity is scale-chain-cancel at the middle denominator;
trichotomy splits the total order through the strict-or-equal gap. -/

/-- **The cross-multiplication order**: `a/b <= c/d ⟺ a·d <= c·b`. -/
def LessEqualAs (leftValue rightValue : RationalPair) : Prop :=
  leftValue.numerator * denominatorInt rightValue ≤
    rightValue.numerator * denominatorInt leftValue

/-- The order is decidable — it IS an `Int` bound (`Int.decLe` is clean). -/
def decideLessEqualAs (leftValue rightValue : RationalPair) :
    Decidable (LessEqualAs leftValue rightValue) :=
  Int.decLe (leftValue.numerator * denominatorInt rightValue)
    (rightValue.numerator * denominatorInt leftValue)

/-- **The strict cross-multiplication order.** -/
def LessThanAs (leftValue rightValue : RationalPair) : Prop :=
  leftValue.numerator * denominatorInt rightValue <
    rightValue.numerator * denominatorInt leftValue

/-- The strict order is decidable (`Int.decLt` is clean). -/
def decideLessThanAs (leftValue rightValue : RationalPair) :
    Decidable (LessThanAs leftValue rightValue) :=
  Int.decLt (leftValue.numerator * denominatorInt rightValue)
    (rightValue.numerator * denominatorInt leftValue)

/-- Strict implies weak — `Int.lt` IS the unit-shifted `Int.le`. -/
theorem lessEqualAsOfLessThan {leftValue rightValue : RationalPair}
    (isLessThan : LessThanAs leftValue rightValue) :
    LessEqualAs leftValue rightValue :=
  intLessEqualOfLessThan isLessThan

/-- Reflexivity — both cross-products are the same term. -/
theorem lessEqualAsRefl (value : RationalPair) : LessEqualAs value value :=
  intLessEqualRefl (value.numerator * denominatorInt value)

/-- Totality — inherited from the `Int` order. -/
theorem lessEqualAsTotal (leftValue rightValue : RationalPair) :
    LessEqualAs leftValue rightValue ∨ LessEqualAs rightValue leftValue :=
  intLessEqualTotal (leftValue.numerator * denominatorInt rightValue)
    (rightValue.numerator * denominatorInt leftValue)

/-- A setoid-equal pair is ordered — rewrite one endpoint of reflexivity. -/
theorem lessEqualAsOfDenotesSame {leftValue rightValue : RationalPair}
    (areSame : DenotesSameAs leftValue rightValue) :
    LessEqualAs leftValue rightValue :=
  intLessEqualOfEqLeft areSame
    (intLessEqualRefl (rightValue.numerator * denominatorInt leftValue))

/-- **Antisymmetry lands on the setoid**: mutual bounds force cross-equality. -/
theorem denotesSameAsOfLessEqualBoth {leftValue rightValue : RationalPair}
    (isForward : LessEqualAs leftValue rightValue)
    (isBackward : LessEqualAs rightValue leftValue) :
    DenotesSameAs leftValue rightValue :=
  intLessEqualAntisymm isForward isBackward

/-- **Transitivity** — scale each bound by the missing denominator, meet at the
middle by one right-commutation each, cancel the positive middle denominator. -/
theorem lessEqualAsTrans {firstValue middleValue lastValue : RationalPair}
    (isFirstBelowMiddle : LessEqualAs firstValue middleValue)
    (isMiddleBelowLast : LessEqualAs middleValue lastValue) :
    LessEqualAs firstValue lastValue :=
  intLeOfMulLeMulRightOfPos (denominatorIntIsPositive middleValue)
    (intLessEqualOfEqLeft
      (intMulRightComm firstValue.numerator (denominatorInt lastValue)
        (denominatorInt middleValue))
      (intLessEqualTrans
        (intMulLeMulRightOfNonNeg isFirstBelowMiddle
          (intLessEqualOfLessThan (denominatorIntIsPositive lastValue)))
        (intLessEqualOfEqLeft
          (intMulRightComm middleValue.numerator (denominatorInt firstValue)
            (denominatorInt lastValue))
          (intLessEqualOfEqRight
            (intMulLeMulRightOfNonNeg isMiddleBelowLast
              (intLessEqualOfLessThan (denominatorIntIsPositive firstValue)))
            (intMulRightComm lastValue.numerator (denominatorInt middleValue)
              (denominatorInt firstValue))))))

/-- The order respects the setoid on the left. -/
theorem lessEqualAsCongrLeft {leftValue newLeftValue rightValue : RationalPair}
    (areSame : DenotesSameAs leftValue newLeftValue)
    (isLessEqual : LessEqualAs leftValue rightValue) :
    LessEqualAs newLeftValue rightValue :=
  lessEqualAsTrans (lessEqualAsOfDenotesSame (denotesSameAsSymm areSame))
    isLessEqual

/-- The order respects the setoid on the right. -/
theorem lessEqualAsCongrRight {leftValue rightValue newRightValue : RationalPair}
    (areSame : DenotesSameAs rightValue newRightValue)
    (isLessEqual : LessEqualAs leftValue rightValue) :
    LessEqualAs leftValue newRightValue :=
  lessEqualAsTrans isLessEqual (lessEqualAsOfDenotesSame areSame)

/-- **Trichotomy**: strictly below, setoid-equal, or strictly above — the total
order split through the strict-or-equal gap. -/
theorem lessThanAsTrichotomy (leftValue rightValue : RationalPair) :
    LessThanAs leftValue rightValue ∨ DenotesSameAs leftValue rightValue ∨
      LessThanAs rightValue leftValue :=
  match lessEqualAsTotal leftValue rightValue with
  | .inl isForward =>
      match intLtOrEqOfLe isForward with
      | .inl isStrict => .inl isStrict
      | .inr areEqual => .inr (.inl areEqual)
  | .inr isBackward =>
      match intLtOrEqOfLe isBackward with
      | .inl isStrict => .inr (.inr isStrict)
      | .inr areEqual => .inr (.inl areEqual.symm)

/-! ## Ordered-field compatibility (NUM-Q-3b)

Addition is monotone in each argument (mirror the congruence dispatch with
`≤`-plumbing at the hypothesis term, scaled by the shared denominator square),
and multiplication of nonnegatives is nonnegative (nonnegativity READS on the
numerator because the denominator is structurally positive). -/

/-- The rational zero: `0/1`. -/
def zeroRational : RationalPair :=
  { numerator := 0, denominatorPredecessor := 0 }

/-- Nonnegativity: zero sits below the value in the cross-multiplication
order. -/
def IsNonNegative (value : RationalPair) : Prop :=
  LessEqualAs zeroRational value

/-- Nonnegativity reads on the numerator — the denominator is positive, so the
sign of `a/b` IS the sign of `a`. -/
theorem numeratorNonNegativeOfIsNonNegative {value : RationalPair}
    (isNonNegative : IsNonNegative value) : (0 : Int) ≤ value.numerator :=
  intLessEqualOfEqLeft (intZeroMul (denominatorInt value)).symm
    (intLessEqualOfEqRight isNonNegative (intMulOne value.numerator))

/-- The converse numerator-sign reading. -/
theorem isNonNegativeOfNumeratorNonNegative {value : RationalPair}
    (isNumeratorNonNegative : (0 : Int) ≤ value.numerator) :
    IsNonNegative value :=
  intLessEqualOfEqLeft (intZeroMul (denominatorInt value))
    (intLessEqualOfEqRight isNumeratorNonNegative
      (intMulOne value.numerator).symm)

/-- **Addition is monotone on the left** — mirror `addExactCongrLeft`: the
hypothesis term is scaled by the shared right-denominator square, the second
term rides along as an equality. -/
theorem addExactMonotoneLeft {lowValue highValue : RationalPair}
    (rightValue : RationalPair)
    (isLessEqual : LessEqualAs lowValue highValue) :
    LessEqualAs (addExact lowValue rightValue) (addExact highValue rightValue) :=
  have firstTermBound :
      lowValue.numerator * denominatorInt rightValue *
        (denominatorInt highValue * denominatorInt rightValue) ≤
      highValue.numerator * denominatorInt rightValue *
        (denominatorInt lowValue * denominatorInt rightValue) :=
    intLessEqualOfEqLeft
      (intMulSwapMiddle lowValue.numerator (denominatorInt rightValue)
        (denominatorInt highValue) (denominatorInt rightValue))
      (intLessEqualOfEqRight
        (intMulLeMulRightOfNonNeg isLessEqual
          (intMulNonNeg
            (intLessEqualOfLessThan (denominatorIntIsPositive rightValue))
            (intLessEqualOfLessThan (denominatorIntIsPositive rightValue))))
        (intMulSwapMiddle highValue.numerator (denominatorInt lowValue)
          (denominatorInt rightValue) (denominatorInt rightValue)))
  have secondTermAgrees :
      rightValue.numerator * denominatorInt lowValue *
        (denominatorInt highValue * denominatorInt rightValue) =
      rightValue.numerator * denominatorInt highValue *
        (denominatorInt lowValue * denominatorInt rightValue) :=
    intMulSwapMiddle rightValue.numerator (denominatorInt lowValue)
      (denominatorInt highValue) (denominatorInt rightValue)
  intLessEqualOfEqLeft
    (intRightDistrib (lowValue.numerator * denominatorInt rightValue)
      (rightValue.numerator * denominatorInt lowValue)
      (denominatorInt highValue * denominatorInt rightValue))
    (intLessEqualOfEqRight
      (intAddLeAddRight firstTermBound
        (rightValue.numerator * denominatorInt lowValue *
          (denominatorInt highValue * denominatorInt rightValue)))
      ((congrArg
          (highValue.numerator * denominatorInt rightValue *
            (denominatorInt lowValue * denominatorInt rightValue) + ·)
          secondTermAgrees).trans
        (intRightDistrib (highValue.numerator * denominatorInt rightValue)
          (rightValue.numerator * denominatorInt highValue)
          (denominatorInt lowValue * denominatorInt rightValue)).symm))

/-- **Addition is monotone on the right** — the mirror dispatch; the shared
left-denominator swaps route through one extra commutation per term. -/
theorem addExactMonotoneRight (leftValue : RationalPair)
    {lowValue highValue : RationalPair}
    (isLessEqual : LessEqualAs lowValue highValue) :
    LessEqualAs (addExact leftValue lowValue) (addExact leftValue highValue) :=
  have firstTermAgrees :
      leftValue.numerator * denominatorInt lowValue *
        (denominatorInt leftValue * denominatorInt highValue) =
      leftValue.numerator * denominatorInt highValue *
        (denominatorInt leftValue * denominatorInt lowValue) :=
    (intMulSwapMiddle leftValue.numerator (denominatorInt lowValue)
        (denominatorInt leftValue) (denominatorInt highValue)).trans
      ((congrArg (leftValue.numerator * denominatorInt leftValue * ·)
          (intMulComm (denominatorInt lowValue) (denominatorInt highValue))).trans
        (intMulSwapMiddle leftValue.numerator (denominatorInt highValue)
          (denominatorInt leftValue) (denominatorInt lowValue)).symm)
  have secondTermBound :
      lowValue.numerator * denominatorInt leftValue *
        (denominatorInt leftValue * denominatorInt highValue) ≤
      highValue.numerator * denominatorInt leftValue *
        (denominatorInt leftValue * denominatorInt lowValue) :=
    intLessEqualOfEqLeft
      ((congrArg (lowValue.numerator * denominatorInt leftValue * ·)
          (intMulComm (denominatorInt leftValue) (denominatorInt highValue))).trans
        (intMulSwapMiddle lowValue.numerator (denominatorInt leftValue)
          (denominatorInt highValue) (denominatorInt leftValue)))
      (intLessEqualOfEqRight
        (intMulLeMulRightOfNonNeg isLessEqual
          (intMulNonNeg
            (intLessEqualOfLessThan (denominatorIntIsPositive leftValue))
            (intLessEqualOfLessThan (denominatorIntIsPositive leftValue))))
        ((intMulSwapMiddle highValue.numerator (denominatorInt leftValue)
            (denominatorInt lowValue) (denominatorInt leftValue)).symm.trans
          (congrArg (highValue.numerator * denominatorInt leftValue * ·)
            (intMulComm (denominatorInt lowValue) (denominatorInt leftValue)))))
  intLessEqualOfEqLeft
    (intRightDistrib (leftValue.numerator * denominatorInt lowValue)
      (lowValue.numerator * denominatorInt leftValue)
      (denominatorInt leftValue * denominatorInt highValue))
    (intLessEqualOfEqRight
      (intAddLeAddLeft secondTermBound
        (leftValue.numerator * denominatorInt lowValue *
          (denominatorInt leftValue * denominatorInt highValue)))
      ((congrArg
          (· + highValue.numerator * denominatorInt leftValue *
            (denominatorInt leftValue * denominatorInt lowValue))
          firstTermAgrees).trans
        (intRightDistrib (leftValue.numerator * denominatorInt highValue)
          (highValue.numerator * denominatorInt leftValue)
          (denominatorInt leftValue * denominatorInt lowValue)).symm))

/-- **Addition is monotone** — chain the two one-sided monotonicities through
the mixed midpoint. -/
theorem addExactMonotone {lowLeft highLeft lowRight highRight : RationalPair}
    (isLeftLessEqual : LessEqualAs lowLeft highLeft)
    (isRightLessEqual : LessEqualAs lowRight highRight) :
    LessEqualAs (addExact lowLeft lowRight) (addExact highLeft highRight) :=
  lessEqualAsTrans (addExactMonotoneLeft lowRight isLeftLessEqual)
    (addExactMonotoneRight highLeft isRightLessEqual)

/-- **Multiplication of nonnegatives is nonnegative** — read both signs off
the numerators, multiply at the `Int` layer, read back. -/
theorem mulExactIsNonNegative {leftValue rightValue : RationalPair}
    (isLeftNonNegative : IsNonNegative leftValue)
    (isRightNonNegative : IsNonNegative rightValue) :
    IsNonNegative (mulExact leftValue rightValue) :=
  isNonNegativeOfNumeratorNonNegative
    (intMulNonNeg (numeratorNonNegativeOfIsNonNegative isLeftNonNegative)
      (numeratorNonNegativeOfIsNonNegative isRightNonNegative))

/-! ## The canonical normal form (NUM-Q-4c)

Divide numerator and denominator by their gcd.  The magnitude quotient and
the counting divider are EXACT here because the gcd divides both sides
(`natDividesRemainderIsZero`); the normalized denominator stays structurally
positive because the exact quotient of a successor is positive. -/

/-- The gcd divides the numerator's magnitude, so the magnitude remainder
vanishes — the bridge from the divides certificate to `intMagnitudeQuotient`
exactness. -/
theorem magnitudeRemainderVanishesOfDividesNatAbs {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ {value : Int}, NatDivides divisor value.natAbs →
      intMagnitudeRemainder divisor value = 0
  | .ofNat _, divides => natDividesRemainderIsZero isDivisorPositive divides
  | .negSucc _, divides => natDividesRemainderIsZero isDivisorPositive divides

/-- **Normalization**: divide out `gcd(|numerator|, denominator)`.  Proof-free
and computable — the numerator goes through the sign-splitting magnitude
quotient, the denominator through the counting divider with the result stored
back in predecessor form. -/
def normalize (value : RationalPair) : RationalPair :=
  { numerator :=
      intMagnitudeQuotient
        (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1))
        value.numerator
    denominatorPredecessor :=
      Nat.pred
        (natDivModCounting (value.denominatorPredecessor + 1)
          (natGcd value.numerator.natAbs
            (value.denominatorPredecessor + 1))).fst }

/-- **Normalization stays in the class**: `normalize value ~ value`.  Both
sides factor through the gcd — substitute the two exact factorizations into
the cross-multiplication and re-associate. -/
theorem normalizeDenotesSame (value : RationalPair) :
    DenotesSameAs (normalize value) value :=
  have gcdIsPositive :
      0 < natGcd value.numerator.natAbs (value.denominatorPredecessor + 1) :=
    natDivisorOfSuccIsPositive
      (natGcdDividesRight value.numerator.natAbs
        (value.denominatorPredecessor + 1))
  have numeratorFactors :
      value.numerator =
        intMagnitudeQuotient
            (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1))
            value.numerator *
          Int.ofNat
            (natGcd value.numerator.natAbs
              (value.denominatorPredecessor + 1)) :=
    intMagnitudeDivisionExact
      (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1))
      value.numerator
      (magnitudeRemainderVanishesOfDividesNatAbs gcdIsPositive
        (natGcdDividesLeft value.numerator.natAbs
          (value.denominatorPredecessor + 1)))
  have denominatorFactors :
      value.denominatorPredecessor + 1 =
        natGcd value.numerator.natAbs (value.denominatorPredecessor + 1) *
          (natDivModCounting (value.denominatorPredecessor + 1)
            (natGcd value.numerator.natAbs
              (value.denominatorPredecessor + 1))).fst :=
    natExactQuotientReconstructs gcdIsPositive
      (natGcdDividesRight value.numerator.natAbs
        (value.denominatorPredecessor + 1))
  have quotientIsPositive :
      0 < (natDivModCounting (value.denominatorPredecessor + 1)
            (natGcd value.numerator.natAbs
              (value.denominatorPredecessor + 1))).fst :=
    natExactQuotientIsPositive gcdIsPositive
      (natGcdDividesRight value.numerator.natAbs
        (value.denominatorPredecessor + 1))
  (congrArg
      (intMagnitudeQuotient
          (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1))
          value.numerator * ·)
      (congrArg Int.ofNat denominatorFactors)).trans
    ((intMulAssoc
        (intMagnitudeQuotient
          (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1))
          value.numerator)
        (Int.ofNat
          (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1)))
        (Int.ofNat
          (natDivModCounting (value.denominatorPredecessor + 1)
            (natGcd value.numerator.natAbs
              (value.denominatorPredecessor + 1))).fst)).symm.trans
      ((congrArg
          (· *
            Int.ofNat
              (natDivModCounting (value.denominatorPredecessor + 1)
                (natGcd value.numerator.natAbs
                  (value.denominatorPredecessor + 1))).fst)
          numeratorFactors.symm).trans
        (congrArg (fun denominatorMagnitude =>
            value.numerator * Int.ofNat denominatorMagnitude)
          (natSuccPredOfPositive quotientIsPositive)).symm))

/-- **The normal form is reduced**: the normalized numerator's magnitude and
the normalized denominator are coprime.  Rewrite both components onto the
counting quotients (`intMagnitudeQuotientNatAbs` for the magnitude, the
predecessor re-fold for the denominator) and land on the generic
divide-out-the-gcd coprimality. -/
theorem normalizeIsCoprime (value : RationalPair) :
    NatCoprime (normalize value).numerator.natAbs
      ((normalize value).denominatorPredecessor + 1) :=
  have gcdIsPositive :
      0 < natGcd value.numerator.natAbs (value.denominatorPredecessor + 1) :=
    natDivisorOfSuccIsPositive
      (natGcdDividesRight value.numerator.natAbs
        (value.denominatorPredecessor + 1))
  have quotientIsPositive :
      0 < (natDivModCounting (value.denominatorPredecessor + 1)
            (natGcd value.numerator.natAbs
              (value.denominatorPredecessor + 1))).fst :=
    natExactQuotientIsPositive gcdIsPositive
      (natGcdDividesRight value.numerator.natAbs
        (value.denominatorPredecessor + 1))
  (congrArg (natGcd · ((normalize value).denominatorPredecessor + 1))
      (intMagnitudeQuotientNatAbs
        (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1))
        value.numerator)).trans
    ((congrArg
        (natGcd
          (natDivModCounting value.numerator.natAbs
            (natGcd value.numerator.natAbs
              (value.denominatorPredecessor + 1))).fst)
        (natSuccPredOfPositive quotientIsPositive)).trans
      (natGcdOfExactQuotientsIsOne gcdIsPositive))

/-! ## Uniqueness of the normal form (NUM-Q-4c-4)

Reduced pairs that denote the same rational are EQUAL — the ℚ carrier's
canonical-representative theorem.  Reading the cross-multiplication equation at
`natAbs` (multiplicative over the positive denominators) makes each denominator
divide the opposite side's product; Euclid's lemma strips the coprime numerator
magnitude, so the denominators mutually divide and are equal by antisymmetry;
the numerators then agree by cancelling the shared positive denominator at the
`Int` level.  Consequently `DenotesSameAs` is CHARACTERIZED by equality of
normal forms — the decidable setoid computes through `normalize`. -/

/-- A pair is **reduced** when its numerator magnitude and denominator are
coprime — the shape `normalize` produces (`normalizeIsCoprime`). -/
def IsReduced (value : RationalPair) : Prop :=
  NatCoprime value.numerator.natAbs (value.denominatorPredecessor + 1)

/-- Reducedness is decidable — the gcd computes and coprimality IS a `Nat`
equality. -/
def decideIsReduced (value : RationalPair) : Decidable (IsReduced value) :=
  Nat.decEq
    (natGcd value.numerator.natAbs (value.denominatorPredecessor + 1)) 1

/-- **Uniqueness of reduced representatives**: reduced pairs denoting the same
rational are equal.  The denominators mutually divide through Euclid's lemma on
the `natAbs` cross-multiplication reading, antisymmetry pins them equal, and
the numerators follow by cancelling the shared positive denominator. -/
theorem eqOfReducedOfDenotesSame {leftValue rightValue : RationalPair}
    (isLeftReduced : IsReduced leftValue)
    (isRightReduced : IsReduced rightValue)
    (denotesSame : DenotesSameAs leftValue rightValue) :
    leftValue = rightValue :=
  have crossNatAbsEqual :
      leftValue.numerator.natAbs * (rightValue.denominatorPredecessor + 1) =
        rightValue.numerator.natAbs * (leftValue.denominatorPredecessor + 1) :=
    ((intNatAbsMulOfNatSucc leftValue.numerator
          rightValue.denominatorPredecessor).symm.trans
        (congrArg Int.natAbs denotesSame)).trans
      (intNatAbsMulOfNatSucc rightValue.numerator
        leftValue.denominatorPredecessor)
  have leftDenominatorDividesRight :
      NatDivides (leftValue.denominatorPredecessor + 1)
        (rightValue.denominatorPredecessor + 1) :=
    natDividesOfCoprimeOfDividesMul
      ((natGcdComm (leftValue.denominatorPredecessor + 1)
          leftValue.numerator.natAbs).trans isLeftReduced)
      (natDividesOfEq
        (crossNatAbsEqual.trans
          (Nat.mul_comm rightValue.numerator.natAbs
            (leftValue.denominatorPredecessor + 1)))
        ⟨rightValue.numerator.natAbs, rfl⟩)
  have rightDenominatorDividesLeft :
      NatDivides (rightValue.denominatorPredecessor + 1)
        (leftValue.denominatorPredecessor + 1) :=
    natDividesOfCoprimeOfDividesMul
      ((natGcdComm (rightValue.denominatorPredecessor + 1)
          rightValue.numerator.natAbs).trans isRightReduced)
      (natDividesOfEq
        (crossNatAbsEqual.symm.trans
          (Nat.mul_comm leftValue.numerator.natAbs
            (rightValue.denominatorPredecessor + 1)))
        ⟨leftValue.numerator.natAbs, rfl⟩)
  have predecessorsEqual :
      leftValue.denominatorPredecessor = rightValue.denominatorPredecessor :=
    Nat.succ.inj
      (natDividesAntisymm leftDenominatorDividesRight
        rightDenominatorDividesLeft)
  have numeratorsEqual : leftValue.numerator = rightValue.numerator :=
    intMulRightCancel (denominatorIntIsPositive rightValue)
      (denotesSame.trans
        (congrArg
          (fun predecessor =>
            rightValue.numerator * Int.ofNat (predecessor + 1))
          predecessorsEqual))
  (congrArg
      (fun numerator =>
        RationalPair.mk numerator leftValue.denominatorPredecessor)
      numeratorsEqual).trans
    (congrArg (RationalPair.mk rightValue.numerator) predecessorsEqual)

/-- Setoid-equal values have EQUAL normal forms — both normal forms are reduced
and denote the same value through `normalize l ~ l ~ r ~ normalize r`, so
uniqueness pins them. -/
theorem normalizeEqOfDenotesSameAs {leftValue rightValue : RationalPair}
    (denotesSame : DenotesSameAs leftValue rightValue) :
    normalize leftValue = normalize rightValue :=
  eqOfReducedOfDenotesSame (normalizeIsCoprime leftValue)
    (normalizeIsCoprime rightValue)
    (denotesSameAsTrans (normalizeDenotesSame leftValue)
      (denotesSameAsTrans denotesSame
        (denotesSameAsSymm (normalizeDenotesSame rightValue))))

/-- Equal normal forms denote the same value — chain both `normalizeDenotesSame`
certificates through the transported reflexivity at the shared normal form. -/
theorem denotesSameAsOfNormalizeEq {leftValue rightValue : RationalPair}
    (normalsEqual : normalize leftValue = normalize rightValue) :
    DenotesSameAs leftValue rightValue :=
  have normalsDenoteSame :
      DenotesSameAs (normalize leftValue) (normalize rightValue) :=
    Eq.rec
      (motive := fun target _ => DenotesSameAs (normalize leftValue) target)
      (denotesSameAsRefl (normalize leftValue)) normalsEqual
  denotesSameAsTrans (denotesSameAsSymm (normalizeDenotesSame leftValue))
    (denotesSameAsTrans normalsDenoteSame
      (normalizeDenotesSame rightValue))

/-- **The characterization**: the decidable cross-multiplication setoid IS
equality of normal forms — `normalize` is a computable canonical-representative
function for ℚ. -/
theorem denotesSameAsIffNormalizeEq (leftValue rightValue : RationalPair) :
    DenotesSameAs leftValue rightValue ↔
      normalize leftValue = normalize rightValue :=
  ⟨normalizeEqOfDenotesSameAs, denotesSameAsOfNormalizeEq⟩

/-- Normalizing a reduced pair returns it unchanged — uniqueness against the
normal form's own coprimality and denotation certificates. -/
theorem normalizeOfReducedIsSelf {value : RationalPair}
    (isReduced : IsReduced value) : normalize value = value :=
  eqOfReducedOfDenotesSame (normalizeIsCoprime value) isReduced
    (normalizeDenotesSame value)

/-- `normalize` is idempotent — the normal form is already reduced. -/
theorem normalizeIsIdempotent (value : RationalPair) :
    normalize (normalize value) = normalize value :=
  normalizeOfReducedIsSelf (normalizeIsCoprime value)

/-! ## The setoid ring laws (NUM-Q-6)

The commutative-group and commutative-monoid skeleton of the ℚ field, up to
`DenotesSameAs`.  The definitional denominator equations
(`addExactDenominatorInt`/`mulExactDenominatorInt` are `rfl`) mean every law
is plain `Int` algebra on the numerators against `intMulComm`/`intMulAssoc`
on the denominator products — no `Nat`/`ofNat` juggling anywhere. -/

/-- The rational one — `1 / 1`. -/
def oneRational : RationalPair :=
  { numerator := 1, denominatorPredecessor := 0 }

/-- **Addition is commutative** up to the setoid — flip the numerator sum and
the denominator product. -/
theorem addExactComm (leftValue rightValue : RationalPair) :
    DenotesSameAs (addExact leftValue rightValue)
      (addExact rightValue leftValue) :=
  (congrArg (· * denominatorInt (addExact rightValue leftValue))
      (intAddComm (leftValue.numerator * denominatorInt rightValue)
        (rightValue.numerator * denominatorInt leftValue))).trans
    (congrArg
      ((rightValue.numerator * denominatorInt leftValue +
          leftValue.numerator * denominatorInt rightValue) * ·)
      (intMulComm (denominatorInt rightValue) (denominatorInt leftValue)))

/-- **Zero is a right identity** up to the setoid — the scaled-zero summand
vanishes and both unit denominators collapse. -/
theorem addExactZeroRight (value : RationalPair) :
    DenotesSameAs (addExact value zeroRational) value :=
  have numeratorCollapses :
      (addExact value zeroRational).numerator = value.numerator :=
    (congrArg (value.numerator * denominatorInt zeroRational + ·)
        (intZeroMul (denominatorInt value))).trans
      ((intAddZero (value.numerator * denominatorInt zeroRational)).trans
        (intMulOne value.numerator))
  (congrArg (· * denominatorInt value) numeratorCollapses).trans
    (congrArg (value.numerator * ·) (intMulOne (denominatorInt value)).symm)

/-- **Zero is a left identity** up to the setoid — commute and reuse. -/
theorem addExactZeroLeft (value : RationalPair) :
    DenotesSameAs (addExact zeroRational value) value :=
  denotesSameAsTrans (addExactComm zeroRational value)
    (addExactZeroRight value)

/-- **Negation is a right inverse** up to the setoid — the numerator folds to
`(n + -n) * d` and annihilates. -/
theorem addExactNegRight (value : RationalPair) :
    DenotesSameAs (addExact value (negExact value)) zeroRational :=
  have numeratorVanishes :
      (addExact value (negExact value)).numerator = 0 :=
    ((intRightDistrib value.numerator (-value.numerator)
          (denominatorInt value)).symm.trans
        (congrArg (· * denominatorInt value)
          (intAddRightNeg value.numerator))).trans
      (intZeroMul (denominatorInt value))
  (congrArg (· * denominatorInt zeroRational) numeratorVanishes).trans
    ((intZeroMul (denominatorInt zeroRational)).trans
      (intZeroMul
        (denominatorInt (addExact value (negExact value)))).symm)

/-- **Addition is associative** up to the setoid.  The two numerators are
EQUAL as integers — distribute both nested sums, fix the middle term with one
right-commutation and the last with one association-then-right-commutation,
regroup — and the denominators differ by one association, so cross-
multiplication needs no scaling at all. -/
theorem addExactAssoc (firstValue middleValue lastValue : RationalPair) :
    DenotesSameAs (addExact (addExact firstValue middleValue) lastValue)
      (addExact firstValue (addExact middleValue lastValue)) :=
  have leftInnerExpanded :
      (firstValue.numerator * denominatorInt middleValue +
            middleValue.numerator * denominatorInt firstValue) *
          denominatorInt lastValue =
        firstValue.numerator *
            (denominatorInt middleValue * denominatorInt lastValue) +
          middleValue.numerator * denominatorInt lastValue *
            denominatorInt firstValue :=
    (intRightDistrib (firstValue.numerator * denominatorInt middleValue)
        (middleValue.numerator * denominatorInt firstValue)
        (denominatorInt lastValue)).trans
      ((congrArg
          (· + middleValue.numerator * denominatorInt firstValue *
            denominatorInt lastValue)
          (intMulAssoc firstValue.numerator (denominatorInt middleValue)
            (denominatorInt lastValue))).trans
        (congrArg
          (firstValue.numerator *
              (denominatorInt middleValue * denominatorInt lastValue) + ·)
          (intMulRightComm middleValue.numerator (denominatorInt firstValue)
            (denominatorInt lastValue))))
  have lastTermRewritten :
      lastValue.numerator *
          (denominatorInt firstValue * denominatorInt middleValue) =
        lastValue.numerator * denominatorInt middleValue *
          denominatorInt firstValue :=
    (intMulAssoc lastValue.numerator (denominatorInt firstValue)
        (denominatorInt middleValue)).symm.trans
      (intMulRightComm lastValue.numerator (denominatorInt firstValue)
        (denominatorInt middleValue))
  have numeratorsAgree :
      (addExact (addExact firstValue middleValue) lastValue).numerator =
        (addExact firstValue (addExact middleValue lastValue)).numerator :=
    ((congrArg
          (· + lastValue.numerator *
            (denominatorInt firstValue * denominatorInt middleValue))
          leftInnerExpanded).trans
        (congrArg
          (firstValue.numerator *
              (denominatorInt middleValue * denominatorInt lastValue) +
            middleValue.numerator * denominatorInt lastValue *
              denominatorInt firstValue + ·)
          lastTermRewritten)).trans
      ((intAddAssoc
          (firstValue.numerator *
            (denominatorInt middleValue * denominatorInt lastValue))
          (middleValue.numerator * denominatorInt lastValue *
            denominatorInt firstValue)
          (lastValue.numerator * denominatorInt middleValue *
            denominatorInt firstValue)).trans
        (congrArg
          (firstValue.numerator *
              (denominatorInt middleValue * denominatorInt lastValue) + ·)
          (intRightDistrib
            (middleValue.numerator * denominatorInt lastValue)
            (lastValue.numerator * denominatorInt middleValue)
            (denominatorInt firstValue)).symm))
  (congrArg
      (· * denominatorInt
        (addExact firstValue (addExact middleValue lastValue)))
      numeratorsAgree).trans
    (congrArg
      ((addExact firstValue (addExact middleValue lastValue)).numerator * ·)
      (intMulAssoc (denominatorInt firstValue) (denominatorInt middleValue)
        (denominatorInt lastValue)).symm)

/-- **Multiplication is commutative** up to the setoid — flip both products. -/
theorem mulExactComm (leftValue rightValue : RationalPair) :
    DenotesSameAs (mulExact leftValue rightValue)
      (mulExact rightValue leftValue) :=
  (congrArg (· * denominatorInt (mulExact rightValue leftValue))
      (intMulComm leftValue.numerator rightValue.numerator)).trans
    (congrArg ((rightValue.numerator * leftValue.numerator) * ·)
      (intMulComm (denominatorInt rightValue) (denominatorInt leftValue)))

/-- **One is a right identity** up to the setoid — both unit factors collapse. -/
theorem mulExactOneRight (value : RationalPair) :
    DenotesSameAs (mulExact value oneRational) value :=
  (congrArg (· * denominatorInt value) (intMulOne value.numerator)).trans
    (congrArg (value.numerator * ·) (intMulOne (denominatorInt value)).symm)

/-- **One is a left identity** up to the setoid — commute and reuse. -/
theorem mulExactOneLeft (value : RationalPair) :
    DenotesSameAs (mulExact oneRational value) value :=
  denotesSameAsTrans (mulExactComm oneRational value)
    (mulExactOneRight value)

/-- **Multiplication is associative** up to the setoid — one association on
each side of the cross-multiplication. -/
theorem mulExactAssoc (firstValue middleValue lastValue : RationalPair) :
    DenotesSameAs (mulExact (mulExact firstValue middleValue) lastValue)
      (mulExact firstValue (mulExact middleValue lastValue)) :=
  (congrArg
      (· * denominatorInt
        (mulExact firstValue (mulExact middleValue lastValue)))
      (intMulAssoc firstValue.numerator middleValue.numerator
        lastValue.numerator)).trans
    (congrArg
      ((firstValue.numerator *
          (middleValue.numerator * lastValue.numerator)) * ·)
      (intMulAssoc (denominatorInt firstValue) (denominatorInt middleValue)
        (denominatorInt lastValue)).symm)

end RationalPair

end FX1Poly.ComputerAlgebra
