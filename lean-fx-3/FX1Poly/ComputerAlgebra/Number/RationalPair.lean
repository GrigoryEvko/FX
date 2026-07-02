import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

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

end RationalPair

end FX1Poly.ComputerAlgebra
