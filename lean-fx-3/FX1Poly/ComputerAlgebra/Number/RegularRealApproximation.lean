import FX1Poly.ComputerAlgebra.Number.RegularRealCompleteness

/-! # RegularReal approximation — rationals are dense in ℝ

Every real sits within `1/(n+1)` of the constant real of its own `n`-th
approximant — Bishop's rational approximation, exactly tight, straight
from regularity: pointwise the claim IS the value's regularity, with
the `1/(m+1)` leg widened into the `2/(m+1)` setoid modulus by one
numerator-monotone step.

Packaging the approximants as a regular Cauchy sequence and invoking
limit uniqueness then exercises the completeness arc end-to-end: every
real is setoid-equal to the diagonal limit of its own rational
approximants.

The ARCHIMEDEAN property rides the same substrate: every real sits
below the constant real of its canonical bound (a whole rational).
Per index, the difference approximant is `K − x`, nonnegative because
every approximant sits within the canonical magnitude bound; one
shared-addend cancellation turns the pointwise domination into the
vanishing-lower-bound order. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- **Rational approximation** — the constant real of the `n`-th
approximant sits within `1/(n+1)` of the value itself.  Pointwise this
is the value's own regularity, with the `1/(m+1)` leg widened into the
`2/(m+1)` setoid modulus. -/
theorem constantApproximantIsWithinReciprocal (value : RegularReal)
    (approximationIndex : Nat) :
    IsWithinRealBound
      (constantReal (value.approximation approximationIndex)) value
      (reciprocalOfSucc approximationIndex) :=
  fun index =>
    isWithinBoundOfBoundLessEqual
      (addExactMonotone
        (lessEqualAsRefl (reciprocalOfSucc approximationIndex))
        (ratioOfNatSuccMonotoneNumerator (Nat.le_succ 1) index))
      (value.isRegular approximationIndex index)

/-- **The rational approximation sequence** — the value's approximants,
each embedded as a constant real.  The Cauchy certificate is the
value's regularity widened by the nonnegative setoid modulus. -/
def rationalApproximationSequence (value : RegularReal) :
    RegularRealSequence :=
  { values := fun position => constantReal (value.approximation position)
    isCauchy := fun firstPosition secondPosition index =>
      isWithinBoundOfBoundLessEqual
        (lessEqualAsCongrLeft
          (addExactZeroRight
            (addExact (reciprocalOfSucc firstPosition)
              (reciprocalOfSucc secondPosition)))
          (addExactMonotoneRight
            (addExact (reciprocalOfSucc firstPosition)
              (reciprocalOfSucc secondPosition))
            (ratioOfNatSuccIsNonNegative 2 index)))
        (value.isRegular firstPosition secondPosition) }

/-- **Every real is the limit of its rational approximants** — the
completeness arc round-trips: the diagonal limit of the approximation
sequence is setoid-equal to the value itself, by limit uniqueness. -/
theorem limitOfRationalApproximantsDenotesSelf (value : RegularReal) :
    DenotesSameReal (limitReal (rationalApproximationSequence value))
      value :=
  limitRealIsTheUniqueLimit (rationalApproximationSequence value)
    (fun position => constantApproximantIsWithinReciprocal value position)

/-- **The Archimedean property** — every real sits below the constant
real of its canonical bound, a whole rational.  Per index, the
difference approximant is exactly `K − x` at the doubled sample; the
shifted vanishing bound sits below the sample (the negated reciprocal
is below zero), the sample sits below `(K − x) + x` (the magnitude
bound through the recovery identity), and one shared-addend
cancellation lands the order. -/
theorem realIsBelowItsCanonicalBound (value : RegularReal) :
    LessEqualReal value (constantReal (canonicalBound value)) :=
  fun index =>
    have isNegativeOneBelowZero : Int.negSucc 0 ≤ (0 : Int) :=
      intLessEqualIntro (Int.negSucc 0) 1
    have isVanishingBoundBelowZero :
        LessEqualAs (negExact (reciprocalOfSucc index)) zeroRational :=
      intLessEqualOfEqRight isNegativeOneBelowZero
        ((intZeroMul
          (denominatorInt (negExact (reciprocalOfSucc index)))).symm)
    have shiftedVanishingIsBelowSample :
        LessEqualAs
          (addExact (negExact (reciprocalOfSucc index))
            (value.approximation (2 * index + 1)))
          (value.approximation (2 * index + 1)) :=
      lessEqualAsCongrRight
        (addExactZeroLeft (value.approximation (2 * index + 1)))
        (addExactMonotone isVanishingBoundBelowZero
          (lessEqualAsRefl (value.approximation (2 * index + 1))))
    have sampleIsBelowShiftedDifference :
        LessEqualAs (value.approximation (2 * index + 1))
          (addExact
            (subExact (canonicalBound value)
              (value.approximation (2 * index + 1)))
            (value.approximation (2 * index + 1))) :=
      lessEqualAsCongrRight
        (denotesSameAsSymm
          (denotesSameAsTrans
            (addExactComm
              (subExact (canonicalBound value)
                (value.approximation (2 * index + 1)))
              (value.approximation (2 * index + 1)))
            (addExactSubExactCancelDenotesSame
              (value.approximation (2 * index + 1))
              (canonicalBound value))))
        (approximationIsWithinCanonicalBound value (2 * index + 1)).left
    lessEqualAsAddRightCancel
      (lessEqualAsTrans shiftedVanishingIsBelowSample
        sampleIsBelowShiftedDifference)

end FX1Poly.ComputerAlgebra
