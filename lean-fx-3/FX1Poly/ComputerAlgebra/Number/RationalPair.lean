import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntNegation

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

end RationalPair

end FX1Poly.ComputerAlgebra
