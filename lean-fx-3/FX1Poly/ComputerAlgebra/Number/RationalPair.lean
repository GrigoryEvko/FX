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

end RationalPair

end FX1Poly.ComputerAlgebra
