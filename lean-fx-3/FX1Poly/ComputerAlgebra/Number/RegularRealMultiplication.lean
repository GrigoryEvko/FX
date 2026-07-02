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

/-! ## The scaled sampling index and its exact collapse (NUM-R-3b)

`mulReal` samples both factors at a bound-scaled index.  The index is
predecessor-shaped so that `scaled + 1` is DEFINITIONALLY
`2·(bound)·(index+1)` — then the bound's numerator cancels against the
scaled denominator as a SETOID IDENTITY (the R-2 exactness pattern), the
medial regrouping pairs the doubled halves, and the R-2 half-reciprocal
recombination finishes: the product's regularity certificate needs no
inequality reasoning beyond the two product-difference legs. -/

namespace RationalPair

/-- The bound-scaled sampling index: `boundScaledIndex bp n + 1` is
DEFINITIONALLY `2·(bp+1)·(n+1)` — the predecessor-shaped spelling that
makes the scale collapse a numerator cancellation. -/
def boundScaledIndex (boundPredecessor index : Nat) : Nat :=
  2 * (boundPredecessor + 1) * index + (2 * boundPredecessor + 1)

/-- Same-denominator ratios order by their numerators. -/
theorem ratioOfNatSuccMonotoneNumerator {lowNumerator highNumerator : Nat}
    (isBelow : lowNumerator ≤ highNumerator) (denominatorPredecessor : Nat) :
    LessEqualAs (ratioOfNatSucc lowNumerator denominatorPredecessor)
      (ratioOfNatSucc highNumerator denominatorPredecessor) :=
  intMulLeMulRightOfNonNeg (intOfNatLeOfNat isBelow)
    (intZeroLeOfNat (denominatorPredecessor + 1))

/-- **The exact scale collapse**: the bound-scaled reciprocal at the scaled
index IS the half-reciprocal — `(bp+1)/1 · 1/(scaled+1)` denotes
`1/(2(index+1))` because `scaled + 1` is definitionally
`2·(bp+1)·(index+1)`, so the bound's numerator cancels against the scaled
denominator.  A setoid identity, not an estimate. -/
theorem mulRatioReciprocalScaledCollapses (boundPredecessor index : Nat) :
    DenotesSameAs
      (mulExact (ratioOfNatSucc (boundPredecessor + 1) 0)
        (reciprocalOfSucc (boundScaledIndex boundPredecessor index)))
      (reciprocalOfSucc (2 * index + 1)) :=
  have stripLeftUnit :
      (boundPredecessor + 1) * 1 * (2 * index + 1 + 1) =
        (boundPredecessor + 1) * (2 * index + 1 + 1) :=
    congrArg (· * (2 * index + 1 + 1)) (Nat.zero_add (boundPredecessor + 1))
  have regroupsToScale :
      (boundPredecessor + 1) * (2 * index + 1 + 1) =
        2 * (boundPredecessor + 1) * (index + 1) :=
    (natMulAssoc (boundPredecessor + 1) 2 (index + 1)).symm.trans
      (congrArg (· * (index + 1)) (Nat.mul_comm (boundPredecessor + 1) 2))
  have oneMulCollapses : ∀ factor : Nat, 1 * factor = factor :=
    fun factor => (Nat.mul_comm 1 factor).trans (Nat.zero_add factor)
  congrArg Int.ofNat
    (stripLeftUnit.trans
      (regroupsToScale.trans
        ((oneMulCollapses
            (1 * (2 * (boundPredecessor + 1) * (index + 1)))).trans
          (oneMulCollapses
            (2 * (boundPredecessor + 1) * (index + 1)))).symm))

/-- **The doubled product bound collapses exactly**: with `M` the regularity
modulus at the scaled index pair, `K·M + K·M` denotes
`1/(first+1) + 1/(second+1)` — distribute `K` over `M`, collapse each
scaled reciprocal to its half-reciprocal, regroup medially, and recombine
the doubled halves (the R-2 identities). -/
theorem doubledProductBoundCollapses
    (boundPredecessor firstIndex secondIndex : Nat) :
    DenotesSameAs
      (addExact
        (mulExact (ratioOfNatSucc (boundPredecessor + 1) 0)
          (addExact
            (reciprocalOfSucc (boundScaledIndex boundPredecessor firstIndex))
            (reciprocalOfSucc (boundScaledIndex boundPredecessor secondIndex))))
        (mulExact (ratioOfNatSucc (boundPredecessor + 1) 0)
          (addExact
            (reciprocalOfSucc (boundScaledIndex boundPredecessor firstIndex))
            (reciprocalOfSucc (boundScaledIndex boundPredecessor secondIndex)))))
      (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex)) :=
  have halfCollapses :
      DenotesSameAs
        (mulExact (ratioOfNatSucc (boundPredecessor + 1) 0)
          (addExact
            (reciprocalOfSucc (boundScaledIndex boundPredecessor firstIndex))
            (reciprocalOfSucc (boundScaledIndex boundPredecessor secondIndex))))
        (addExact (reciprocalOfSucc (2 * firstIndex + 1))
          (reciprocalOfSucc (2 * secondIndex + 1))) :=
    denotesSameAsTrans
      (mulExactLeftDistrib (ratioOfNatSucc (boundPredecessor + 1) 0)
        (reciprocalOfSucc (boundScaledIndex boundPredecessor firstIndex))
        (reciprocalOfSucc (boundScaledIndex boundPredecessor secondIndex)))
      (addExactRespectsDenotesSameAs
        (mulRatioReciprocalScaledCollapses boundPredecessor firstIndex)
        (mulRatioReciprocalScaledCollapses boundPredecessor secondIndex))
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs halfCollapses halfCollapses)
    (denotesSameAsTrans
      (addExactMedialDenotesSame
        (reciprocalOfSucc (2 * firstIndex + 1))
        (reciprocalOfSucc (2 * secondIndex + 1))
        (reciprocalOfSucc (2 * firstIndex + 1))
        (reciprocalOfSucc (2 * secondIndex + 1)))
      (addExactRespectsDenotesSameAs
        (reciprocalDoubleSumDenotesSame firstIndex)
        (reciprocalDoubleSumDenotesSame secondIndex)))

end RationalPair

/-- The shared magnitude bound's numerator PREDECESSOR — the sum of the two
canonical-bound numerators, so the shared bound's numerator is a literal
successor and dominates each canonical bound by construction. -/
def sharedBoundNumeratorPredecessor (leftValue rightValue : RegularReal) : Nat :=
  canonicalBoundNumerator leftValue + canonicalBoundNumerator rightValue

/-- The shared magnitude bound for a product — covers every approximant of
BOTH factors. -/
def sharedBound (leftValue rightValue : RegularReal) : RationalPair :=
  ratioOfNatSucc (sharedBoundNumeratorPredecessor leftValue rightValue + 1) 0

/-- The product's sampling index — the shared bound's scale. -/
def productSamplingIndex (leftValue rightValue : RegularReal)
    (index : Nat) : Nat :=
  boundScaledIndex (sharedBoundNumeratorPredecessor leftValue rightValue) index

/-- The left factor's approximants sit within the shared bound. -/
theorem leftApproximationIsWithinSharedBound
    (leftValue rightValue : RegularReal) (index : Nat) :
    IsMagnitudeWithin (leftValue.approximation index)
      (sharedBound leftValue rightValue) :=
  isMagnitudeWithinOfBoundLessEqual
    (ratioOfNatSuccMonotoneNumerator
      (Nat.le.intro (k := canonicalBoundNumerator rightValue + 1) rfl) 0)
    (approximationIsWithinCanonicalBound leftValue index)

/-- The right factor's approximants sit within the shared bound. -/
theorem rightApproximationIsWithinSharedBound
    (leftValue rightValue : RegularReal) (index : Nat) :
    IsMagnitudeWithin (rightValue.approximation index)
      (sharedBound leftValue rightValue) :=
  isMagnitudeWithinOfBoundLessEqual
    (ratioOfNatSuccMonotoneNumerator
      (Nat.le.intro (k := canonicalBoundNumerator leftValue + 1)
        (congrArg Nat.succ
          (Nat.add_comm (canonicalBoundNumerator rightValue)
            (canonicalBoundNumerator leftValue))))
      0)
    (approximationIsWithinCanonicalBound rightValue index)

/-- **Multiplication on reals** — sample both factors at the bound-scaled
index.  Regularity splits through the mixed middle product `x(s i)·y(s j)`:
each leg is one product-difference law at the shared bound, and the doubled
bound collapses EXACTLY to the required modulus. -/
def mulReal (leftValue rightValue : RegularReal) : RegularReal :=
  { approximation := fun index =>
      mulExact
        (leftValue.approximation
          (productSamplingIndex leftValue rightValue index))
        (rightValue.approximation
          (productSamplingIndex leftValue rightValue index))
    isRegular := fun firstIndex secondIndex =>
      have modulusIsNonNegative :
          IsNonNegative
            (addExact
              (reciprocalOfSucc
                (productSamplingIndex leftValue rightValue firstIndex))
              (reciprocalOfSucc
                (productSamplingIndex leftValue rightValue secondIndex))) :=
        addExactIsNonNegative
          (ratioOfNatSuccIsNonNegative 1
            (productSamplingIndex leftValue rightValue firstIndex))
          (ratioOfNatSuccIsNonNegative 1
            (productSamplingIndex leftValue rightValue secondIndex))
      isWithinBoundCongrBound
        (doubledProductBoundCollapses
          (sharedBoundNumeratorPredecessor leftValue rightValue)
          firstIndex secondIndex)
        (isWithinBoundTriangle
          (mulExactRespectsIsWithinBoundLeft
            (leftApproximationIsWithinSharedBound leftValue rightValue
              (productSamplingIndex leftValue rightValue firstIndex))
            (rightValue.isRegular
              (productSamplingIndex leftValue rightValue firstIndex)
              (productSamplingIndex leftValue rightValue secondIndex))
            modulusIsNonNegative)
          (mulExactRespectsIsWithinBoundRight
            (rightApproximationIsWithinSharedBound leftValue rightValue
              (productSamplingIndex leftValue rightValue secondIndex))
            (leftValue.isRegular
              (productSamplingIndex leftValue rightValue firstIndex)
              (productSamplingIndex leftValue rightValue secondIndex))
            modulusIsNonNegative)) }

/-! ## The multiplication congruence (NUM-R-3b-ii)

Two products of setoid-equal factors sample at DIFFERENT scaled indices, so
the congruence cannot be pointwise.  It goes through SLACK CLOSURE: chain
both products to the slack index by their own regularity, compare there via
the product-difference laws at the grand bound covering the old left factor
and the new right factor, relax the mismatched-sampling differences to
`4/(m+1)` by reciprocal antitonicity, and reshape the accumulated bound onto
`2/(n+1) + slack` with setoid identities. -/

namespace RationalPair

/-- Every index sits below its bound-scaled image — the additive witness is
read off after one `succ_mul` refold. -/
theorem natSelfLeBoundScaledIndex (boundPredecessor index : Nat) :
    index ≤ boundScaledIndex boundPredecessor index :=
  Nat.le.intro
    ((Nat.add_assoc index ((2 * boundPredecessor + 1) * index)
        (2 * boundPredecessor + 1)).symm.trans
      (congrArg (· + (2 * boundPredecessor + 1))
        ((Nat.add_comm index ((2 * boundPredecessor + 1) * index)).trans
          (Nat.succ_mul (2 * boundPredecessor + 1) index).symm)))

/-- Ratios shrink as their denominator index grows. -/
theorem ratioOfNatSuccAntitoneDenominator (numeratorNat : Nat)
    {lowIndex highIndex : Nat} (isBelow : lowIndex ≤ highIndex) :
    LessEqualAs (ratioOfNatSucc numeratorNat highIndex)
      (ratioOfNatSucc numeratorNat lowIndex) :=
  intMulLeMulLeftOfNonNeg
    (intOfNatLeOfNat (natSuccLeSuccOfLe isBelow))
    (intZeroLeOfNat numeratorNat)

/-- A whole ratio times a ratio multiplies the numerators — the denominator
picks up only a unit factor. -/
theorem mulExactRatioRatioDenotesSame
    (leftNumerator rightNumerator denominatorPredecessor : Nat) :
    DenotesSameAs
      (mulExact (ratioOfNatSucc leftNumerator 0)
        (ratioOfNatSucc rightNumerator denominatorPredecessor))
      (ratioOfNatSucc (leftNumerator * rightNumerator)
        denominatorPredecessor) :=
  congrArg Int.ofNat
    (congrArg
      (fun scaledDenominator =>
        leftNumerator * rightNumerator * (scaledDenominator + 1))
      ((Nat.mul_comm 1 denominatorPredecessor).trans
        (Nat.zero_add denominatorPredecessor)).symm)

/-- **The chained slack bound reshapes**: the bound accumulated by the
regularity-middle-regularity chain regroups so the outer pieces pair up and
the slack pieces gather with the middle — associate, rotate, cross-pair. -/
theorem chainedSlackBoundReshapesDenotesSame
    (outerPiece slackPiece middlePiece : RationalPair) :
    DenotesSameAs
      (addExact
        (addExact (addExact outerPiece slackPiece) middlePiece)
        (addExact slackPiece outerPiece))
      (addExact (addExact outerPiece outerPiece)
        (addExact (addExact slackPiece slackPiece) middlePiece)) :=
  denotesSameAsTrans
    (addExactAssoc (addExact outerPiece slackPiece) middlePiece
      (addExact slackPiece outerPiece))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (denotesSameAsRefl (addExact outerPiece slackPiece))
        (addExactComm middlePiece (addExact slackPiece outerPiece)))
      (denotesSameAsTrans
        (denotesSameAsSymm
          (addExactAssoc (addExact outerPiece slackPiece)
            (addExact slackPiece outerPiece) middlePiece))
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (addExactCrossPairsDenotesSame outerPiece slackPiece)
            (denotesSameAsRefl middlePiece))
          (addExactAssoc (addExact outerPiece outerPiece)
            (addExact slackPiece slackPiece) middlePiece))))

end RationalPair

/-- **Multiplication respects the real setoid** in both arguments.  Per
index, slack closure: both products chain to the slack index by their own
regularity; there the factors are compared through the mixed middle
`x(old)·y'(new)` — each factor difference bridges its sampling mismatch by
regularity and lands on the setoid hypothesis, relaxed to `4/(m+1)` — and
the accumulated bound reshapes onto `2/(n+1)` plus vanishing slack. -/
theorem mulRealRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue) :
    DenotesSameReal (mulReal leftValue rightValue)
      (mulReal newLeftValue newRightValue) :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      let oldSampling := productSamplingIndex leftValue rightValue slackIndex
      let newSampling :=
        productSamplingIndex newLeftValue newRightValue slackIndex
      have relaxedDiffBound :
          LessEqualAs
            (addExact
              (addExact (reciprocalOfSucc oldSampling)
                (reciprocalOfSucc newSampling))
              (ratioOfNatSucc 2 newSampling))
            (ratioOfNatSucc 4 slackIndex) :=
        lessEqualAsCongrRight
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs
              (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
              (denotesSameAsRefl (ratioOfNatSucc 2 slackIndex)))
            (ratioOfNatSuccSumDenotesSame 2 2 slackIndex))
          (addExactMonotone
            (addExactMonotone
              (ratioOfNatSuccAntitoneDenominator 1
                (natSelfLeBoundScaledIndex
                  (sharedBoundNumeratorPredecessor leftValue rightValue)
                  slackIndex))
              (ratioOfNatSuccAntitoneDenominator 1
                (natSelfLeBoundScaledIndex
                  (sharedBoundNumeratorPredecessor newLeftValue newRightValue)
                  slackIndex)))
            (ratioOfNatSuccAntitoneDenominator 2
              (natSelfLeBoundScaledIndex
                (sharedBoundNumeratorPredecessor newLeftValue newRightValue)
                slackIndex)))
      have rightFactorsDiffer :
          IsWithinBound (rightValue.approximation oldSampling)
            (newRightValue.approximation newSampling)
            (ratioOfNatSucc 4 slackIndex) :=
        isWithinBoundOfBoundLessEqual relaxedDiffBound
          (isWithinBoundTriangle
            (rightValue.isRegular oldSampling newSampling)
            (rightAgrees newSampling))
      have leftFactorsDiffer :
          IsWithinBound (leftValue.approximation oldSampling)
            (newLeftValue.approximation newSampling)
            (ratioOfNatSucc 4 slackIndex) :=
        isWithinBoundOfBoundLessEqual relaxedDiffBound
          (isWithinBoundTriangle
            (leftValue.isRegular oldSampling newSampling)
            (leftAgrees newSampling))
      have productsDifferAtSlack :
          IsWithinBound
            ((mulReal leftValue rightValue).approximation slackIndex)
            ((mulReal newLeftValue newRightValue).approximation slackIndex)
            (addExact
              (mulExact (sharedBound leftValue newRightValue)
                (ratioOfNatSucc 4 slackIndex))
              (mulExact (sharedBound leftValue newRightValue)
                (ratioOfNatSucc 4 slackIndex))) :=
        isWithinBoundTriangle
          (mulExactRespectsIsWithinBoundLeft
            (leftApproximationIsWithinSharedBound leftValue newRightValue
              oldSampling)
            rightFactorsDiffer
            (ratioOfNatSuccIsNonNegative 4 slackIndex))
          (mulExactRespectsIsWithinBoundRight
            (rightApproximationIsWithinSharedBound leftValue newRightValue
              newSampling)
            leftFactorsDiffer
            (ratioOfNatSuccIsNonNegative 4 slackIndex))
      have middleBoundCollapses :
          DenotesSameAs
            (addExact
              (mulExact (sharedBound leftValue newRightValue)
                (ratioOfNatSucc 4 slackIndex))
              (mulExact (sharedBound leftValue newRightValue)
                (ratioOfNatSucc 4 slackIndex)))
            (ratioOfNatSucc
              ((sharedBoundNumeratorPredecessor leftValue newRightValue + 1) *
                  4 +
                (sharedBoundNumeratorPredecessor leftValue newRightValue + 1) *
                  4)
              slackIndex) :=
        denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (mulExactRatioRatioDenotesSame
              (sharedBoundNumeratorPredecessor leftValue newRightValue + 1) 4
              slackIndex)
            (mulExactRatioRatioDenotesSame
              (sharedBoundNumeratorPredecessor leftValue newRightValue + 1) 4
              slackIndex))
          (ratioOfNatSuccSumDenotesSame
            ((sharedBoundNumeratorPredecessor leftValue newRightValue + 1) * 4)
            ((sharedBoundNumeratorPredecessor leftValue newRightValue + 1) * 4)
            slackIndex)
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (chainedSlackBoundReshapesDenotesSame
            (reciprocalOfSucc sharedIndex) (reciprocalOfSucc slackIndex)
            (addExact
              (mulExact (sharedBound leftValue newRightValue)
                (ratioOfNatSucc 4 slackIndex))
              (mulExact (sharedBound leftValue newRightValue)
                (ratioOfNatSucc 4 slackIndex))))
          (addExactRespectsDenotesSameAs
            (ratioOfNatSuccSumDenotesSame 1 1 sharedIndex)
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                middleBoundCollapses)
              (ratioOfNatSuccSumDenotesSame 2
                ((sharedBoundNumeratorPredecessor leftValue newRightValue +
                      1) * 4 +
                  (sharedBoundNumeratorPredecessor leftValue newRightValue +
                      1) * 4)
                slackIndex))))
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            ((mulReal leftValue rightValue).isRegular sharedIndex slackIndex)
            productsDifferAtSlack)
          ((mulReal newLeftValue newRightValue).isRegular slackIndex
            sharedIndex)))

end FX1Poly.ComputerAlgebra
