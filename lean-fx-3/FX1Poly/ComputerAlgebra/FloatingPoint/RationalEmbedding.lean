import FX1Poly.ComputerAlgebra.FloatingPoint.RadixScaledInteger
import FX1Poly.ComputerAlgebra.Number.RationalPair

/-! # FX1Poly/ComputerAlgebra/FloatingPoint/RationalEmbedding — ℤ[1/β] ↪ ℚ
    (NUM-Q-5)

Every radix-scaled integer IS a rational: `mantissa * radix ^ exponent` reads as
the pair `(mantissa * radix ^ exponent.toNat) / radix ^ (-exponent).toNat` — the
SAME min-free clamping that powers cross-alignment splits the exponent's sign
into numerator pumping versus denominator pumping, with no case split.  The
theorem is that this reading is a SETOID EMBEDDING: two radix-scaled integers
denote the same value exactly when their rational readings do.  Every float
rounding-error certificate therefore re-reads EXACTLY in ℚ — where Flocq
evaluates float semantics into classical ℝ, the zero-axiom tower never leaves
exact arithmetic.

Both directions are one scale-and-cancel: pump the hypothesis by the clamps it
is missing, land both sides on one total exponent via `intSplitClampsBalance`,
and cancel the shared power at the positive radix.

## Zero-axiom

Structure projections + `congrArg`/`Eq.trans` chains over the shipped power and
clamp kits.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/FloatingPoint/RationalEmbedding.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-- The rational reading of `mantissa * radix ^ exponent`: a nonnegative
exponent pumps the numerator, a negative exponent pumps the denominator — the
min-free clamps mean exactly one side pumps (and neither at exponent zero).
The denominator is stored predecessor-shaped, exactly like `normalize`. -/
def rationalOfRadixScaled (radix : Int) (value : RadixScaledInteger) :
    RationalPair :=
  { numerator := value.mantissa * intPower radix value.exponent.toNat
    denominatorPredecessor :=
      Nat.pred (intPower radix (-value.exponent).toNat).toNat }

/-- The embedded denominator reads back as the clamped power — the predecessor
re-fold at the power's positivity, then the `toNat` roundtrip. -/
theorem rationalOfRadixScaledDenominatorInt {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger) :
    RationalPair.denominatorInt (rationalOfRadixScaled radix value) =
      intPower radix (-value.exponent).toNat :=
  (congrArg Int.ofNat
      (natSuccPredOfPositive
        (intToNatPosOfPos
          (intPowerPos isRadixPositive (-value.exponent).toNat)))).trans
    (intOfNatToNatOfNonNeg
      (intLessEqualOfLessThan
        (intPowerPos isRadixPositive (-value.exponent).toNat)))

/-- **Setoid preservation, forward**: cross-aligned agreement transfers to the
rational cross-multiplication.  Scale the hypothesis by the right value's split
clamps, land both totals on the balanced exponent via `intSplitClampsBalance`,
cancel the shared gap clamp, and fold onto the embedded components. -/
theorem rationalOfRadixScaledRespectsDenotesSame {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger}
    (denotesSame : RadixScaledInteger.DenotesSameAs radix leftValue rightValue) :
    RationalPair.DenotesSameAs (rationalOfRadixScaled radix leftValue)
      (rationalOfRadixScaled radix rightValue) :=
  have scaledEquation :
      leftValue.mantissa *
            intPower radix (leftValue.exponent - rightValue.exponent).toNat *
          intPower radix
            (rightValue.exponent.toNat + (-leftValue.exponent).toNat) =
        rightValue.mantissa *
            intPower radix (rightValue.exponent - leftValue.exponent).toNat *
          intPower radix
            (rightValue.exponent.toNat + (-leftValue.exponent).toNat) :=
    congrArg
      (· * intPower radix
        (rightValue.exponent.toNat + (-leftValue.exponent).toNat))
      denotesSame
  have foldedEquation :
      leftValue.mantissa *
          intPower radix
            ((leftValue.exponent - rightValue.exponent).toNat +
              (rightValue.exponent.toNat + (-leftValue.exponent).toNat)) =
        rightValue.mantissa *
          intPower radix
            ((rightValue.exponent - leftValue.exponent).toNat +
              (rightValue.exponent.toNat + (-leftValue.exponent).toNat)) :=
    ((intMulPowerFold radix leftValue.mantissa
          (leftValue.exponent - rightValue.exponent).toNat
          (rightValue.exponent.toNat + (-leftValue.exponent).toNat)).symm.trans
        scaledEquation).trans
      (intMulPowerFold radix rightValue.mantissa
        (rightValue.exponent - leftValue.exponent).toNat
        (rightValue.exponent.toNat + (-leftValue.exponent).toNat))
  have canonicalEquation :
      leftValue.mantissa *
          intPower radix
            (leftValue.exponent.toNat + (-rightValue.exponent).toNat +
              (rightValue.exponent - leftValue.exponent).toNat) =
        rightValue.mantissa *
          intPower radix
            (rightValue.exponent.toNat + (-leftValue.exponent).toNat +
              (rightValue.exponent - leftValue.exponent).toNat) :=
    ((congrArg
          (fun totalExponent =>
            leftValue.mantissa * intPower radix totalExponent)
          (intSplitClampsBalance leftValue.exponent
            rightValue.exponent)).symm.trans
        foldedEquation).trans
      (congrArg
        (fun totalExponent =>
          rightValue.mantissa * intPower radix totalExponent)
        (Nat.add_comm (rightValue.exponent - leftValue.exponent).toNat
          (rightValue.exponent.toNat + (-leftValue.exponent).toNat)))
  have strippedEquation :
      leftValue.mantissa *
          intPower radix
            (leftValue.exponent.toNat + (-rightValue.exponent).toNat) =
        rightValue.mantissa *
          intPower radix
            (rightValue.exponent.toNat + (-leftValue.exponent).toNat) :=
    intMulPowerRightCancel isRadixPositive
      (rightValue.exponent - leftValue.exponent).toNat
      ((intMulPowerFold radix leftValue.mantissa
          (leftValue.exponent.toNat + (-rightValue.exponent).toNat)
          (rightValue.exponent - leftValue.exponent).toNat).trans
        (canonicalEquation.trans
          (intMulPowerFold radix rightValue.mantissa
            (rightValue.exponent.toNat + (-leftValue.exponent).toNat)
            (rightValue.exponent - leftValue.exponent).toNat).symm))
  (congrArg ((rationalOfRadixScaled radix leftValue).numerator * ·)
      (rationalOfRadixScaledDenominatorInt isRadixPositive rightValue)).trans
    ((intMulPowerFold radix leftValue.mantissa leftValue.exponent.toNat
        (-rightValue.exponent).toNat).trans
      (strippedEquation.trans
        ((intMulPowerFold radix rightValue.mantissa rightValue.exponent.toNat
            (-leftValue.exponent).toNat).symm.trans
          (congrArg ((rationalOfRadixScaled radix rightValue).numerator * ·)
            (rationalOfRadixScaledDenominatorInt isRadixPositive
              leftValue)).symm)))

/-- **Setoid reflection, backward**: rational cross-multiplication agreement
reflects to cross-alignment.  Unfold onto the split clamps, scale by the gap
clamp, land on the same balanced total, and cancel the split clamps. -/
theorem denotesSameOfRationalOfRadixScaled {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger}
    (rationalsDenoteSame :
      RationalPair.DenotesSameAs (rationalOfRadixScaled radix leftValue)
        (rationalOfRadixScaled radix rightValue)) :
    RadixScaledInteger.DenotesSameAs radix leftValue rightValue :=
  have strippedEquation :
      leftValue.mantissa *
          intPower radix
            (leftValue.exponent.toNat + (-rightValue.exponent).toNat) =
        rightValue.mantissa *
          intPower radix
            (rightValue.exponent.toNat + (-leftValue.exponent).toNat) :=
    ((intMulPowerFold radix leftValue.mantissa leftValue.exponent.toNat
          (-rightValue.exponent).toNat).symm.trans
        ((congrArg ((rationalOfRadixScaled radix leftValue).numerator * ·)
            (rationalOfRadixScaledDenominatorInt isRadixPositive
              rightValue)).symm.trans
          (rationalsDenoteSame.trans
            (congrArg ((rationalOfRadixScaled radix rightValue).numerator * ·)
              (rationalOfRadixScaledDenominatorInt isRadixPositive
                leftValue))))).trans
      (intMulPowerFold radix rightValue.mantissa rightValue.exponent.toNat
        (-leftValue.exponent).toNat)
  have scaledEquation :
      leftValue.mantissa *
            intPower radix
              (leftValue.exponent.toNat + (-rightValue.exponent).toNat) *
          intPower radix (rightValue.exponent - leftValue.exponent).toNat =
        rightValue.mantissa *
            intPower radix
              (rightValue.exponent.toNat + (-leftValue.exponent).toNat) *
          intPower radix (rightValue.exponent - leftValue.exponent).toNat :=
    congrArg
      (· * intPower radix (rightValue.exponent - leftValue.exponent).toNat)
      strippedEquation
  have balancedEquation :
      leftValue.mantissa *
          intPower radix
            ((leftValue.exponent - rightValue.exponent).toNat +
              (rightValue.exponent.toNat + (-leftValue.exponent).toNat)) =
        rightValue.mantissa *
          intPower radix
            ((rightValue.exponent - leftValue.exponent).toNat +
              (rightValue.exponent.toNat + (-leftValue.exponent).toNat)) :=
    ((congrArg
          (fun totalExponent =>
            leftValue.mantissa * intPower radix totalExponent)
          (intSplitClampsBalance leftValue.exponent rightValue.exponent)).trans
        ((intMulPowerFold radix leftValue.mantissa
            (leftValue.exponent.toNat + (-rightValue.exponent).toNat)
            (rightValue.exponent - leftValue.exponent).toNat).symm.trans
          (scaledEquation.trans
            (intMulPowerFold radix rightValue.mantissa
              (rightValue.exponent.toNat + (-leftValue.exponent).toNat)
              (rightValue.exponent - leftValue.exponent).toNat)))).trans
      (congrArg
        (fun totalExponent =>
          rightValue.mantissa * intPower radix totalExponent)
        (Nat.add_comm
          (rightValue.exponent.toNat + (-leftValue.exponent).toNat)
          (rightValue.exponent - leftValue.exponent).toNat))
  intMulPowerRightCancel isRadixPositive
    (rightValue.exponent.toNat + (-leftValue.exponent).toNat)
    ((intMulPowerFold radix leftValue.mantissa
        (leftValue.exponent - rightValue.exponent).toNat
        (rightValue.exponent.toNat + (-leftValue.exponent).toNat)).trans
      (balancedEquation.trans
        (intMulPowerFold radix rightValue.mantissa
          (rightValue.exponent - leftValue.exponent).toNat
          (rightValue.exponent.toNat + (-leftValue.exponent).toNat)).symm))

/-- **ℤ[1/β] ↪ ℚ is a setoid embedding** — radix-scaled integers denote the
same value exactly when their rational readings do; float rounding-error
certificates re-read EXACTLY in ℚ. -/
theorem rationalOfRadixScaledDenotesSameAsIff {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    (leftValue rightValue : RadixScaledInteger) :
    RadixScaledInteger.DenotesSameAs radix leftValue rightValue ↔
      RationalPair.DenotesSameAs (rationalOfRadixScaled radix leftValue)
        (rationalOfRadixScaled radix rightValue) :=
  ⟨rationalOfRadixScaledRespectsDenotesSame isRadixPositive,
    denotesSameOfRationalOfRadixScaled isRadixPositive⟩

end FX1Poly.ComputerAlgebra
