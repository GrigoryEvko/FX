import FX1Poly.ComputerAlgebra.FloatingPoint.RationalEmbedding
import FX1Poly.ComputerAlgebra.Number.RegularRealDistance
import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # FX1Poly/ComputerAlgebra/FloatingPoint/RealEmbedding — ℤ[1/β] ↪ ℝ, the float bridge

Every radix-scaled integer is a real: the rational reading followed by the
constant embedding.  The composite is faithful — it respects and reflects the
radix-scaled setoid — and monotone.

The re-read principle closes the bridge: a ℚ-level distance certificate between
constant reals is a real-level distance certificate, since the constant
approximants never move and the setoid modulus adds only slack.  Every
rounding-error bound, already exact in ℚ, therefore reads as a statement about
real numbers: unlike Flocq, which evaluates float semantics into classical ℝ,
this development reaches ℝ without leaving exact arithmetic. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- The ℤ[1/β] ↪ ℝ embedding: the rational reading, held constant. -/
def realOfRadixScaled (radix : Int) (value : RadixScaledInteger) :
    RegularReal :=
  constantReal (rationalOfRadixScaled radix value)

/-- The real embedding respects the radix-scaled setoid — through the
rational reading and the constant embedding in turn. -/
theorem realOfRadixScaledRespectsDenotesSame {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger}
    (denotesSame :
      RadixScaledInteger.DenotesSameAs radix leftValue rightValue) :
    DenotesSameReal (realOfRadixScaled radix leftValue)
      (realOfRadixScaled radix rightValue) :=
  constantRealRespectsDenotesSame
    (rationalOfRadixScaledRespectsDenotesSame isRadixPositive denotesSame)

/-- The real embedding reflects the setoid — both stages are
faithful, so setoid-equal embedded reals force cross-aligned
agreement of the radix-scaled integers. -/
theorem denotesSameOfRealOfRadixScaled {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger}
    (realsDenoteSame : DenotesSameReal (realOfRadixScaled radix leftValue)
      (realOfRadixScaled radix rightValue)) :
    RadixScaledInteger.DenotesSameAs radix leftValue rightValue :=
  denotesSameOfRationalOfRadixScaled isRadixPositive
    (denotesSameAsOfConstantRealDenotesSame realsDenoteSame)

/-- The re-read principle: a ℚ-level distance bound between two rationals is a
real-level distance bound between their constant embeddings, since the constant
approximants never move and the setoid modulus adds only slack. -/
theorem isWithinRealBoundConstantOfIsWithinBound
    {leftValue rightValue bound : RationalPair}
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinRealBound (constantReal leftValue) (constantReal rightValue)
      bound :=
  fun index =>
    isWithinBoundOfBoundLessEqual
      (lessEqualAsCongrLeft (addExactZeroRight bound)
        (addExactMonotoneRight bound
          (ratioOfNatSuccIsNonNegative 2 index)))
      isWithin

/-- The constant embedding is monotone: a ℚ-level order between two
rationals is a real-level order between their constant embeddings.
Per index the difference approximant is exactly the rational
difference; the shifted vanishing bound sits below the left value,
the left value sits below the recovered difference-plus-left, and
one shared-addend cancellation lands the order. -/
theorem lessEqualRealConstantOfLessEqualAs
    {leftValue rightValue : RationalPair}
    (isBelow : LessEqualAs leftValue rightValue) :
    LessEqualReal (constantReal leftValue) (constantReal rightValue) :=
  fun index =>
    have isNegativeOneBelowZero : Int.negSucc 0 ≤ (0 : Int) :=
      intLessEqualIntro (Int.negSucc 0) 1
    have isVanishingBoundBelowZero :
        LessEqualAs (negExact (reciprocalOfSucc index)) zeroRational :=
      intLessEqualOfEqRight isNegativeOneBelowZero
        ((intZeroMul
          (denominatorInt (negExact (reciprocalOfSucc index)))).symm)
    have shiftedVanishingIsBelowLeft :
        LessEqualAs
          (addExact (negExact (reciprocalOfSucc index)) leftValue)
          leftValue :=
      lessEqualAsCongrRight (addExactZeroLeft leftValue)
        (addExactMonotone isVanishingBoundBelowZero
          (lessEqualAsRefl leftValue))
    have leftIsBelowShiftedDifference :
        LessEqualAs leftValue
          (addExact (subExact rightValue leftValue) leftValue) :=
      lessEqualAsCongrRight
        (denotesSameAsSymm
          (denotesSameAsTrans
            (addExactComm (subExact rightValue leftValue) leftValue)
            (addExactSubExactCancelDenotesSame leftValue rightValue)))
        isBelow
    lessEqualAsAddRightCancel
      (lessEqualAsTrans shiftedVanishingIsBelowLeft
        leftIsBelowShiftedDifference)

/-- The real embedding is monotone on radix-scaled integers — the
rational reading respects the order, and the constant embedding
carries it to the reals. -/
theorem realOfRadixScaledRespectsLessEqual {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger}
    (isBelow : RadixScaledInteger.LessEqualAs radix leftValue rightValue) :
    LessEqualReal (realOfRadixScaled radix leftValue)
      (realOfRadixScaled radix rightValue) :=
  lessEqualRealConstantOfLessEqualAs
    (rationalOfRadixScaledRespectsLessEqual isRadixPositive isBelow)

end FX1Poly.ComputerAlgebra
