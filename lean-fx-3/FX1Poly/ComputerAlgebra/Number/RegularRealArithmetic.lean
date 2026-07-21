import FX1Poly.ComputerAlgebra.Number.RegularReal

/-! # RegularReal arithmetic — addition and negation

The additive ℝ operations.  Negation is pointwise — the two-sided distance is
symmetric under negating both arguments, so regularity transfers verbatim.
Addition uses Bishop's INDEX DOUBLING: `(x + y) n := x (2n+1) + y (2n+1)`,
and the doubled-index moduli recombine EXACTLY — `1/(2n+2) + 1/(2n+2)`
denotes `1/(n+1)` on the nose (a setoid identity, not an estimate), so the
regularity certificate needs no inequality reasoning beyond the parallel
combination law.  The same doubling makes the congruence bounds collapse:
`2/(2n+2) + 2/(2n+2)` denotes `2/(n+1)`.

The ℚ-side shims: negation distributes over the two-sided bound (swap the
differences through double negation), parallel addition of two bounds
(`|(a+b) − (c+d)| ≤ |a−c| + |b−d|` via the MEDIAL regrouping), and the two
doubled-modulus collapse identities — both closed by ONE Int lemma each
(`intOneMul` / `intMulAssoc`) because the doubled denominators are
definitionally even. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- Double negation denotes the value back — the numerator round-trips. -/
theorem negExactNegExactDenotesSame (value : RationalPair) :
    DenotesSameAs (negExact (negExact value)) value :=
  congrArg (· * denominatorInt value) (intNegNeg value.numerator)

/-- Negation distributes over addition up to the setoid — the shared
denominator product rides a numerator identity. -/
theorem negExactAddExactDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs (negExact (addExact leftValue rightValue))
      (addExact (negExact leftValue) (negExact rightValue)) :=
  congrArg (· * denominatorInt (addExact leftValue rightValue))
    ((intNegAdd (leftValue.numerator * denominatorInt rightValue)
        (rightValue.numerator * denominatorInt leftValue)).trans
      ((congrArg (· + -(rightValue.numerator * denominatorInt leftValue))
          (intNegMul leftValue.numerator (denominatorInt rightValue)).symm).trans
        (congrArg (-leftValue.numerator * denominatorInt rightValue + ·)
          (intNegMul rightValue.numerator (denominatorInt leftValue)).symm)))

/-- **The medial regrouping**: `(p + q) + (r + s)` denotes `(p + r) + (q + s)`
— associate down, rotate the middle pair, associate back up. -/
theorem addExactMedialDenotesSame
    (firstValue secondValue thirdValue fourthValue : RationalPair) :
    DenotesSameAs
      (addExact (addExact firstValue secondValue)
        (addExact thirdValue fourthValue))
      (addExact (addExact firstValue thirdValue)
        (addExact secondValue fourthValue)) :=
  denotesSameAsTrans
    (addExactAssoc firstValue secondValue (addExact thirdValue fourthValue))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs (denotesSameAsRefl firstValue)
        (denotesSameAsTrans
          (denotesSameAsSymm (addExactAssoc secondValue thirdValue fourthValue))
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs (addExactComm secondValue thirdValue)
              (denotesSameAsRefl fourthValue))
            (addExactAssoc thirdValue secondValue fourthValue))))
      (denotesSameAsSymm
        (addExactAssoc firstValue thirdValue
          (addExact secondValue fourthValue))))

/-- The swapped difference denotes the difference of the negations —
commute, then un-double-negate the right leg. -/
theorem subExactSwapNegDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs (subExact rightValue leftValue)
      (subExact (negExact leftValue) (negExact rightValue)) :=
  denotesSameAsTrans (addExactComm rightValue (negExact leftValue))
    (addExactRespectsDenotesSameAs (denotesSameAsRefl (negExact leftValue))
      (denotesSameAsSymm (negExactNegExactDenotesSame rightValue)))

/-- Negating both values preserves the two-sided bound — the differences
swap sides. -/
theorem negExactRespectsIsWithinBound {leftValue rightValue bound : RationalPair}
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinBound (negExact leftValue) (negExact rightValue) bound :=
  ⟨lessEqualAsCongrLeft (subExactSwapNegDenotesSame leftValue rightValue)
      isWithin.right,
    lessEqualAsCongrLeft (subExactSwapNegDenotesSame rightValue leftValue)
      isWithin.left⟩

/-- The sum of two differences denotes the difference of the sums — medial
regrouping followed by folding the negation over the right sum. -/
theorem subExactAddDenotesSame
    (firstValue secondValue thirdValue fourthValue : RationalPair) :
    DenotesSameAs
      (addExact (subExact firstValue thirdValue)
        (subExact secondValue fourthValue))
      (subExact (addExact firstValue secondValue)
        (addExact thirdValue fourthValue)) :=
  denotesSameAsTrans
    (addExactMedialDenotesSame firstValue (negExact thirdValue) secondValue
      (negExact fourthValue))
    (addExactRespectsDenotesSameAs
      (denotesSameAsRefl (addExact firstValue secondValue))
      (denotesSameAsSymm (negExactAddExactDenotesSame thirdValue fourthValue)))

/-- **Parallel addition of bounds**: adding within two bounds stays within
the bound sum — the abs-free `|(a+b) − (c+d)| ≤ |a−c| + |b−d|`. -/
theorem addExactRespectsIsWithinBound
    {firstLow firstHigh secondLow secondHigh firstBound secondBound :
      RationalPair}
    (isFirstWithin : IsWithinBound firstLow firstHigh firstBound)
    (isSecondWithin : IsWithinBound secondLow secondHigh secondBound) :
    IsWithinBound (addExact firstLow secondLow)
      (addExact firstHigh secondHigh) (addExact firstBound secondBound) :=
  ⟨lessEqualAsCongrLeft
      (subExactAddDenotesSame firstLow secondLow firstHigh secondHigh)
      (addExactMonotone isFirstWithin.left isSecondWithin.left),
    lessEqualAsCongrLeft
      (subExactAddDenotesSame firstHigh secondHigh firstLow secondLow)
      (addExactMonotone isFirstWithin.right isSecondWithin.right)⟩

/-- The doubled-index modulus recombines exactly:
`1/(2n+2) + 1/(2n+2)` denotes `1/(n+1)` — the doubled denominator is
definitionally even, so one unit-factor strip closes the cross-product. -/
theorem reciprocalDoubleSumDenotesSame (index : Nat) :
    DenotesSameAs
      (addExact (reciprocalOfSucc (2 * index + 1))
        (reciprocalOfSucc (2 * index + 1)))
      (reciprocalOfSucc index) :=
  denotesSameAsTrans
    (ratioOfNatSuccSumDenotesSame 1 1 (2 * index + 1))
    (show DenotesSameAs (ratioOfNatSucc 2 (2 * index + 1))
        (reciprocalOfSucc index) from
      (intOneMul (Int.ofNat (2 * index + 1 + 1))).symm)

/-- The doubled-index congruence bound recombines exactly:
`2/(2n+2) + 2/(2n+2)` denotes `2/(n+1)` — `4 = 2·2` definitionally, so one
associativity closes the cross-product. -/
theorem ratioTwoDoubleSumDenotesSame (index : Nat) :
    DenotesSameAs
      (addExact (ratioOfNatSucc 2 (2 * index + 1))
        (ratioOfNatSucc 2 (2 * index + 1)))
      (ratioOfNatSucc 2 index) :=
  denotesSameAsTrans
    (ratioOfNatSuccSumDenotesSame 2 2 (2 * index + 1))
    (show DenotesSameAs (ratioOfNatSucc 4 (2 * index + 1))
        (ratioOfNatSucc 2 index) from
      intMulAssoc (Int.ofNat 2) (Int.ofNat 2) (Int.ofNat (index + 1)))

end RationalPair

open RationalPair

/-- **Negation on reals** — pointwise; the two-sided distance is symmetric
under negating both arguments. -/
def negReal (value : RegularReal) : RegularReal :=
  { approximation := fun index => negExact (value.approximation index)
    isRegular := fun firstIndex secondIndex =>
      negExactRespectsIsWithinBound (value.isRegular firstIndex secondIndex) }

/-- Negation respects the real setoid — pointwise. -/
theorem negRealRespectsDenotesSame {leftValue rightValue : RegularReal}
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal (negReal leftValue) (negReal rightValue) :=
  fun sharedIndex => negExactRespectsIsWithinBound (areSame sharedIndex)

/-- **Addition on reals** — Bishop's index doubling: sample both summands at
`2n+1`, where the doubled moduli recombine EXACTLY to the required
regularity. -/
def addReal (leftValue rightValue : RegularReal) : RegularReal :=
  { approximation := fun index =>
      addExact (leftValue.approximation (2 * index + 1))
        (rightValue.approximation (2 * index + 1))
    isRegular := fun firstIndex secondIndex =>
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (addExactMedialDenotesSame
            (reciprocalOfSucc (2 * firstIndex + 1))
            (reciprocalOfSucc (2 * secondIndex + 1))
            (reciprocalOfSucc (2 * firstIndex + 1))
            (reciprocalOfSucc (2 * secondIndex + 1)))
          (addExactRespectsDenotesSameAs
            (reciprocalDoubleSumDenotesSame firstIndex)
            (reciprocalDoubleSumDenotesSame secondIndex)))
        (addExactRespectsIsWithinBound
          (leftValue.isRegular (2 * firstIndex + 1) (2 * secondIndex + 1))
          (rightValue.isRegular (2 * firstIndex + 1) (2 * secondIndex + 1))) }

/-- Addition respects the real setoid in both arguments — the doubled
congruence bounds recombine exactly. -/
theorem addRealRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue) :
    DenotesSameReal (addReal leftValue rightValue)
      (addReal newLeftValue newRightValue) :=
  fun sharedIndex =>
    isWithinBoundCongrBound (ratioTwoDoubleSumDenotesSame sharedIndex)
      (addExactRespectsIsWithinBound
        (leftAgrees (2 * sharedIndex + 1))
        (rightAgrees (2 * sharedIndex + 1)))

end FX1Poly.ComputerAlgebra
