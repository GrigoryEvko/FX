import FX1Poly.ComputerAlgebra.Number.RegularRealArithmetic

/-! # RegularReal multiplication substrate (NUM-R-3a)

The kit `mulReal` will consume, in two layers.

**ℚ layer — the magnitude predicate and the product-difference bound.**
`IsMagnitudeWithin value bound` is the abs-free `|value| ≤ bound`: the
conjunction `value ≤ bound ∧ -value ≤ bound`, mirroring `IsWithinBound`'s
two-sided discipline (NUM-R-0).  Its keystone is the product bound

    |a| ≤ K  →  |c| ≤ E  →  0 ≤ E  →  |a·c| ≤ K·E

which cross-multiplies to ONE `Int` fact (`intMulLeMulOfMagnitudeLe`, proved
by a sign split — no halving, no ring identity) plus two `intMulSwapMiddle`
regroupings.  Combined with distributivity-over-subtraction it yields the
bound-respecting law `|a·b − a·d| ≤ K·|b − d|` — the abs-free
product-difference inequality that makes `(xy)ₙ` regular.

**ℝ layer — the canonical bound.**  Every approximant of a regular real sits
within `natAbs (numerator x₀) + 2`: regularity against index `0` bounds the
drift by `1/(n+1) + 1/1 ≤ 2`, and `x₀` itself sits within its numerator's
magnitude because the denominator is at least one.  The bound is a
`ratioOfNatSucc`, so its nonnegativity is free. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- Negation passes through the product's LEFT factor — the denominators are
the SAME expression, so the setoid identity is one numerator `congrArg`. -/
theorem mulExactNegLeftDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs (mulExact (negExact leftValue) rightValue)
      (negExact (mulExact leftValue rightValue)) :=
  congrArg (· * denominatorInt (mulExact leftValue rightValue))
    (intNegMul leftValue.numerator rightValue.numerator)

/-- Negation passes through the product's RIGHT factor. -/
theorem mulExactNegRightDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs (mulExact leftValue (negExact rightValue))
      (negExact (mulExact leftValue rightValue)) :=
  congrArg (· * denominatorInt (mulExact leftValue rightValue))
    (intMulNeg leftValue.numerator rightValue.numerator)

/-- Negating a difference swaps its sides — negation distributes over the
sum, the double negation collapses, and the summands commute. -/
theorem negExactSubExactDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs (negExact (subExact leftValue rightValue))
      (subExact rightValue leftValue) :=
  denotesSameAsTrans (negExactAddExactDenotesSame leftValue (negExact rightValue))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs (denotesSameAsRefl (negExact leftValue))
        (negExactNegExactDenotesSame rightValue))
      (addExactComm (negExact leftValue) rightValue))

/-- Multiplication distributes over subtraction — left distributivity with
the negation folded through the right factor. -/
theorem mulExactSubExactDenotesSame
    (multiplier leftValue rightValue : RationalPair) :
    DenotesSameAs (mulExact multiplier (subExact leftValue rightValue))
      (subExact (mulExact multiplier leftValue)
        (mulExact multiplier rightValue)) :=
  denotesSameAsTrans
    (mulExactLeftDistrib multiplier leftValue (negExact rightValue))
    (addExactRespectsDenotesSameAs
      (denotesSameAsRefl (mulExact multiplier leftValue))
      (mulExactNegRightDenotesSame multiplier rightValue))

/-- Adding a difference back onto its base recovers the value:
`base + (value − base)` denotes `value` — commute, associate, cancel. -/
theorem addExactSubExactCancelDenotesSame (base value : RationalPair) :
    DenotesSameAs (addExact base (subExact value base)) value :=
  denotesSameAsTrans (addExactComm base (subExact value base))
    (denotesSameAsTrans
      (addExactAssoc value (negExact base) base)
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs (denotesSameAsRefl value)
          (denotesSameAsTrans (addExactComm (negExact base) base)
            (addExactNegRight base)))
        (addExactZeroRight value)))

/-- The mirrored recovery: `(−base) + (base − value)` denotes `−value` —
associate the other way, cancel, absorb the zero on the left. -/
theorem addExactNegSubExactCollapsesDenotesSame (base value : RationalPair) :
    DenotesSameAs (addExact (negExact base) (subExact base value))
      (negExact value) :=
  denotesSameAsTrans
    (denotesSameAsSymm (addExactAssoc (negExact base) base (negExact value)))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (denotesSameAsTrans (addExactComm (negExact base) base)
          (addExactNegRight base))
        (denotesSameAsRefl (negExact value)))
      (addExactZeroLeft (negExact value)))

/-- **The magnitude bound**: both the value and its negation sit below the
bound — the abs-free `|value| ≤ bound`, the one-value sibling of
`IsWithinBound`. -/
def IsMagnitudeWithin (value bound : RationalPair) : Prop :=
  LessEqualAs value bound ∧ LessEqualAs (negExact value) bound

/-- The magnitude bound is decidable — a conjunction of decidable orders. -/
def decideIsMagnitudeWithin (value bound : RationalPair) :
    Decidable (IsMagnitudeWithin value bound) :=
  @instDecidableAnd _ _ (decideLessEqualAs value bound)
    (decideLessEqualAs (negExact value) bound)

/-- A magnitude bound may be relaxed upward. -/
theorem isMagnitudeWithinOfBoundLessEqual {value lowBound highBound : RationalPair}
    (isBoundBelow : LessEqualAs lowBound highBound)
    (isWithin : IsMagnitudeWithin value lowBound) :
    IsMagnitudeWithin value highBound :=
  ⟨lessEqualAsTrans isWithin.left isBoundBelow,
    lessEqualAsTrans isWithin.right isBoundBelow⟩

/-- The magnitude bound respects the setoid in the value. -/
theorem isMagnitudeWithinCongrValue {value newValue bound : RationalPair}
    (areSame : DenotesSameAs value newValue)
    (isWithin : IsMagnitudeWithin value bound) :
    IsMagnitudeWithin newValue bound :=
  ⟨lessEqualAsCongrLeft areSame isWithin.left,
    lessEqualAsCongrLeft (negExactRespectsDenotesSameAs areSame) isWithin.right⟩

/-- The magnitude bound respects the setoid in the bound. -/
theorem isMagnitudeWithinCongrBound {value bound newBound : RationalPair}
    (boundsAgree : DenotesSameAs bound newBound)
    (isWithin : IsMagnitudeWithin value bound) :
    IsMagnitudeWithin value newBound :=
  ⟨lessEqualAsCongrRight boundsAgree isWithin.left,
    lessEqualAsCongrRight boundsAgree isWithin.right⟩

/-- Negation preserves the magnitude bound — swap the conjuncts through the
double negation. -/
theorem isMagnitudeWithinNegExact {value bound : RationalPair}
    (isWithin : IsMagnitudeWithin value bound) :
    IsMagnitudeWithin (negExact value) bound :=
  ⟨isWithin.right,
    lessEqualAsCongrLeft (denotesSameAsSymm (negExactNegExactDenotesSame value))
      isWithin.left⟩

/-- A two-sided distance bound IS a magnitude bound on the difference. -/
theorem isMagnitudeWithinSubExactOfIsWithinBound
    {leftValue rightValue bound : RationalPair}
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsMagnitudeWithin (subExact leftValue rightValue) bound :=
  ⟨isWithin.left,
    lessEqualAsCongrLeft
      (denotesSameAsSymm (negExactSubExactDenotesSame leftValue rightValue))
      isWithin.right⟩

/-- A magnitude bound on the difference IS a two-sided distance bound. -/
theorem isWithinBoundOfIsMagnitudeWithinSubExact
    {leftValue rightValue bound : RationalPair}
    (isWithin : IsMagnitudeWithin (subExact leftValue rightValue) bound) :
    IsWithinBound leftValue rightValue bound :=
  ⟨isWithin.left,
    lessEqualAsCongrLeft (negExactSubExactDenotesSame leftValue rightValue)
      isWithin.right⟩

/-- **The magnitude triangle**: a value within `diffBound` of a base whose
magnitude sits within `baseBound` has magnitude within their sum — the
recovery identities feed `addExactMonotone` on each side. -/
theorem isMagnitudeWithinTriangle
    {leftValue rightValue baseBound diffBound : RationalPair}
    (isWithin : IsWithinBound leftValue rightValue diffBound)
    (rightMagnitude : IsMagnitudeWithin rightValue baseBound) :
    IsMagnitudeWithin leftValue (addExact baseBound diffBound) :=
  ⟨lessEqualAsCongrLeft (addExactSubExactCancelDenotesSame rightValue leftValue)
      (addExactMonotone rightMagnitude.left isWithin.left),
    lessEqualAsCongrLeft
      (addExactNegSubExactCollapsesDenotesSame rightValue leftValue)
      (addExactMonotone rightMagnitude.right isWithin.right)⟩

/-- **The product bound, one-sided**: bounded magnitudes multiply below the
product of the bounds.  Cross-multiplication turns the goal into the `Int`
two-sided product bound; two middle swaps regroup the four factors. -/
theorem mulExactLessEqualOfMagnitudesWithin
    {multiplier multiplierBound value valueBound : RationalPair}
    (multiplierWithin : IsMagnitudeWithin multiplier multiplierBound)
    (valueWithin : IsMagnitudeWithin value valueBound)
    (isValueBoundNonNegative : IsNonNegative valueBound) :
    LessEqualAs (mulExact multiplier value)
      (mulExact multiplierBound valueBound) :=
  have negMultiplierBelow :
      -(multiplier.numerator * denominatorInt multiplierBound) ≤
        multiplierBound.numerator * denominatorInt multiplier :=
    intLessEqualOfEqLeft
      (intNegMul multiplier.numerator (denominatorInt multiplierBound)).symm
      multiplierWithin.right
  have negValueBelow :
      -(value.numerator * denominatorInt valueBound) ≤
        valueBound.numerator * denominatorInt value :=
    intLessEqualOfEqLeft
      (intNegMul value.numerator (denominatorInt valueBound)).symm
      valueWithin.right
  have crossBoundNonNegative :
      (0 : Int) ≤ valueBound.numerator * denominatorInt value :=
    intMulNonNeg (numeratorNonNegativeOfIsNonNegative isValueBoundNonNegative)
      (intLessEqualOfLessThan (denominatorIntIsPositive value))
  have coreBound :
      multiplier.numerator * denominatorInt multiplierBound *
          (value.numerator * denominatorInt valueBound) ≤
        multiplierBound.numerator * denominatorInt multiplier *
          (valueBound.numerator * denominatorInt value) :=
    intMulLeMulOfMagnitudeLe multiplierWithin.left negMultiplierBelow
      valueWithin.left negValueBelow crossBoundNonNegative
  intLessEqualOfEqLeft
    (intMulSwapMiddle multiplier.numerator value.numerator
      (denominatorInt multiplierBound) (denominatorInt valueBound))
    (intLessEqualOfEqRight coreBound
      (intMulSwapMiddle multiplierBound.numerator (denominatorInt multiplier)
        valueBound.numerator (denominatorInt value)))

/-- **The product bound, two-sided**: `|a| ≤ K → |c| ≤ E → |a·c| ≤ K·E`.
The mirrored conjunct re-runs the one-sided bound at the negated multiplier
and folds the negation back through the product's left factor. -/
theorem isMagnitudeWithinMulExact
    {multiplier multiplierBound value valueBound : RationalPair}
    (multiplierWithin : IsMagnitudeWithin multiplier multiplierBound)
    (valueWithin : IsMagnitudeWithin value valueBound)
    (isValueBoundNonNegative : IsNonNegative valueBound) :
    IsMagnitudeWithin (mulExact multiplier value)
      (mulExact multiplierBound valueBound) :=
  ⟨mulExactLessEqualOfMagnitudesWithin multiplierWithin valueWithin
      isValueBoundNonNegative,
    lessEqualAsCongrLeft (mulExactNegLeftDenotesSame multiplier value)
      (mulExactLessEqualOfMagnitudesWithin
        (isMagnitudeWithinNegExact multiplierWithin) valueWithin
        isValueBoundNonNegative)⟩

/-- **The product-difference bound, multiplier on the left**: the abs-free
`|a·b − a·d| ≤ K·ε` from `|a| ≤ K` and `|b − d| ≤ ε` — distributivity turns
the product difference into a product OF the difference, and the two-sided
product bound closes it. -/
theorem mulExactRespectsIsWithinBoundLeft
    {multiplier multiplierBound leftValue rightValue diffBound : RationalPair}
    (multiplierWithin : IsMagnitudeWithin multiplier multiplierBound)
    (isWithin : IsWithinBound leftValue rightValue diffBound)
    (isDiffBoundNonNegative : IsNonNegative diffBound) :
    IsWithinBound (mulExact multiplier leftValue)
      (mulExact multiplier rightValue)
      (mulExact multiplierBound diffBound) :=
  isWithinBoundOfIsMagnitudeWithinSubExact
    (isMagnitudeWithinCongrValue
      (mulExactSubExactDenotesSame multiplier leftValue rightValue)
      (isMagnitudeWithinMulExact multiplierWithin
        (isMagnitudeWithinSubExactOfIsWithinBound isWithin)
        isDiffBoundNonNegative))

/-- The product-difference bound, multiplier on the right — commute both
products onto the left-handed law. -/
theorem mulExactRespectsIsWithinBoundRight
    {multiplier multiplierBound leftValue rightValue diffBound : RationalPair}
    (multiplierWithin : IsMagnitudeWithin multiplier multiplierBound)
    (isWithin : IsWithinBound leftValue rightValue diffBound)
    (isDiffBoundNonNegative : IsNonNegative diffBound) :
    IsWithinBound (mulExact leftValue multiplier)
      (mulExact rightValue multiplier)
      (mulExact multiplierBound diffBound) :=
  isWithinBoundCongrRight (mulExactComm multiplier rightValue)
    (isWithinBoundCongrLeft (mulExactComm multiplier leftValue)
      (mulExactRespectsIsWithinBoundLeft multiplierWithin isWithin
        isDiffBoundNonNegative))

end RationalPair

open RationalPair

/-- The canonical bound's numerator: `natAbs (numerator x₀) + 2` — the
zeroth approximant's magnitude plus the worst regularity drift. -/
def canonicalBoundNumerator (value : RegularReal) : Nat :=
  (value.approximation 0).numerator.natAbs + 2

/-- **The canonical bound** of a regular real, as a whole ratio — every
approximant's magnitude sits within it. -/
def canonicalBound (value : RegularReal) : RationalPair :=
  ratioOfNatSucc (canonicalBoundNumerator value) 0

/-- The canonical bound is nonnegative — its numerator IS an `ofNat`. -/
theorem canonicalBoundIsNonNegative (value : RegularReal) :
    IsNonNegative (canonicalBound value) :=
  ratioOfNatSuccIsNonNegative (canonicalBoundNumerator value) 0

/-- **Every approximant sits within the canonical bound**: regularity against
index `0` bounds the drift by `1/(index+1) + 1/1 ≤ 2/1`, the zeroth
approximant sits within its numerator's magnitude (the denominator is at
least one), and the magnitude triangle adds the two. -/
theorem approximationIsWithinCanonicalBound (value : RegularReal) (index : Nat) :
    IsMagnitudeWithin (value.approximation index) (canonicalBound value) :=
  have reciprocalIsBelowOne :
      LessEqualAs (reciprocalOfSucc index) (reciprocalOfSucc 0) :=
    intOfNatLeOfNat (Nat.le.intro (Nat.add_comm 1 (1 * index)))
  have boundCollapses :
      LessEqualAs (addExact (reciprocalOfSucc index) (reciprocalOfSucc 0))
        (ratioOfNatSucc 2 0) :=
    lessEqualAsCongrRight (ratioOfNatSuccSumDenotesSame 1 1 0)
      (addExactMonotone reciprocalIsBelowOne
        (lessEqualAsRefl (reciprocalOfSucc 0)))
  have regularityRelaxed :
      IsWithinBound (value.approximation index) (value.approximation 0)
        (ratioOfNatSucc 2 0) :=
    isWithinBoundOfBoundLessEqual boundCollapses (value.isRegular index 0)
  have oneIsBelowBaseDenominator :
      (1 : Int) ≤ denominatorInt (value.approximation 0) :=
    denominatorIntIsPositive (value.approximation 0)
  have boundBySignedNumerator :
      ∀ signedNumerator : Int,
        signedNumerator ≤ Int.ofNat (value.approximation 0).numerator.natAbs →
        signedNumerator * Int.ofNat 1 ≤
          Int.ofNat (value.approximation 0).numerator.natAbs *
            denominatorInt (value.approximation 0) :=
    fun signedNumerator isBelowAbs =>
      intLessEqualTrans
        (intLessEqualOfEqLeft (intMulOne signedNumerator) isBelowAbs)
        (intLessEqualOfEqLeft
          (intMulOne
            (Int.ofNat (value.approximation 0).numerator.natAbs)).symm
          (intMulLeMulLeftOfNonNeg oneIsBelowBaseDenominator
            (intZeroLeOfNat (value.approximation 0).numerator.natAbs)))
  have baseMagnitude :
      IsMagnitudeWithin (value.approximation 0)
        (ratioOfNatSucc (value.approximation 0).numerator.natAbs 0) :=
    ⟨boundBySignedNumerator (value.approximation 0).numerator
        (intSelfLessEqualOfNatNatAbs (value.approximation 0).numerator),
      boundBySignedNumerator (-(value.approximation 0).numerator)
        (intNegSelfLessEqualOfNatNatAbs (value.approximation 0).numerator)⟩
  isMagnitudeWithinCongrBound
    (ratioOfNatSuccSumDenotesSame (value.approximation 0).numerator.natAbs 2 0)
    (isMagnitudeWithinTriangle regularityRelaxed baseMagnitude)

end FX1Poly.ComputerAlgebra
