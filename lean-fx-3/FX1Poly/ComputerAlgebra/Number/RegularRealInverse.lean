import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # RegularReal inverse — reciprocal kit + the inverse (NUM-R-5c/5d)

The one hard fact behind the constructive inverse: on values above a
shared margin `1/(p+1)`, the exact reciprocal is Lipschitz with the
EXPLICIT constant `(p+1)²` — `|1/a − 1/b| ≤ (p+1)²·|a−b|`.  The proof
is SIGN-FREE: the reciprocal difference and the reversed difference
share their numerator verbatim (both are the same cross-product gap),
so the bound never inspects the gap's sign — the margin inequalities
scale the DENOMINATORS only, and the bound's nonnegativity absorbs the
scaling.  The margins also force positive numerators, refuting the
zero and negative `invExact` arms outright.

`inverseReal` then assembles the inverse of a positive real from its
positivity witness: sample the value past the witness's half margin at
the `(p+1)²`-scaled index, take exact reciprocals pointwise, and the
Lipschitz bound on the sampled regularity certificate collapses
EXACTLY (the R-3b numerator cancellation) onto the required modulus.

The R-5e margin kit also lives here: a margin makes a value APART FROM
ZERO (so the exact field law applies at every sampled approximant) and
bounds its reciprocal's MAGNITUDE by `p+1` (so mismatched-sampling
drift scales by a constant that slack closure can erase).  Still ahead
in R-5: the per-index near-one estimate, the slack-closure field law
`x · inverseReal x ~ oneReal`, and the extension from positivity
witnesses to full apartness (the negative case rides `negReal`). -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- No value with a zero numerator sits above a reciprocal margin —
the cross-products collapse to `denominator ≤ 0`. -/
theorem noMarginAboveZeroNumerator {marginIndex denominatorPredecessor : Nat}
    (isAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex)
      ⟨Int.ofNat 0, denominatorPredecessor⟩) : False :=
  nomatch natLeOfIntOfNatLe (intLessEqualOfEqRight isAboveMargin
    (intZeroMul (Int.ofNat (marginIndex + 1))))

/-- No value with a negative numerator sits above a reciprocal margin —
the order hypothesis reduces to a `NonNeg` on a negative constructor. -/
theorem noMarginAboveNegativeNumerator
    {marginIndex magnitudePredecessor denominatorPredecessor : Nat}
    (isAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex)
      ⟨Int.negSucc magnitudePredecessor, denominatorPredecessor⟩) : False :=
  nomatch isAboveMargin

/-- **The scaled reciprocal-difference bound, one side**: on values above
the margin `1/(p+1)`, the reciprocal difference `1/a − 1/b` sits below
`(p+1)²` times any nonnegative bound on `b − a`.  The two differences
share their numerator (the same cross-product gap, commuted), so no
sign analysis is needed — the margins bound the DENOMINATOR swap
`(p+1)²·(numerators) ≥ denominators`, and the nonnegative bound scales. -/
theorem invExactSubLessEqualScaledOfMargins {marginIndex : Nat}
    {leftValue rightValue bound : RationalPair}
    (isLeftAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) leftValue)
    (isRightAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) rightValue)
    (isBoundNonNegative : IsNonNegative bound)
    (isReversedDiffBounded : LessEqualAs (subExact rightValue leftValue) bound) :
    LessEqualAs (subExact (invExact leftValue) (invExact rightValue))
      (mulExact (ratioOfNatSucc ((marginIndex + 1) * (marginIndex + 1)) 0)
        bound) :=
  match leftValue, rightValue, isLeftAboveMargin, isRightAboveMargin,
      isReversedDiffBounded with
  | ⟨.ofNat 0, _⟩, _, isLeftAbove, _, _ =>
      (noMarginAboveZeroNumerator isLeftAbove).elim
  | ⟨.negSucc _, _⟩, _, isLeftAbove, _, _ =>
      (noMarginAboveNegativeNumerator isLeftAbove).elim
  | ⟨.ofNat (_ + 1), _⟩, ⟨.ofNat 0, _⟩, _, isRightAbove, _ =>
      (noMarginAboveZeroNumerator isRightAbove).elim
  | ⟨.ofNat (_ + 1), _⟩, ⟨.negSucc _, _⟩, _, isRightAbove, _ =>
      (noMarginAboveNegativeNumerator isRightAbove).elim
  | ⟨.ofNat (leftMagnitude + 1), leftDenomPred⟩,
    ⟨.ofNat (rightMagnitude + 1), rightDenomPred⟩,
    isLeftAbove, isRightAbove, isDiffBounded =>
      have crossNumeratorsAgree :
          Int.ofNat (leftDenomPred + 1) * Int.ofNat (rightMagnitude + 1) +
            (-Int.ofNat (rightDenomPred + 1)) * Int.ofNat (leftMagnitude + 1) =
          Int.ofNat (rightMagnitude + 1) * Int.ofNat (leftDenomPred + 1) +
            (-Int.ofNat (leftMagnitude + 1)) * Int.ofNat (rightDenomPred + 1) :=
        (congrArg
          (· + (-Int.ofNat (rightDenomPred + 1)) * Int.ofNat (leftMagnitude + 1))
          (intMulComm (Int.ofNat (leftDenomPred + 1))
            (Int.ofNat (rightMagnitude + 1)))).trans
          (congrArg
            (Int.ofNat (rightMagnitude + 1) * Int.ofNat (leftDenomPred + 1) + ·)
            ((intNegMul (Int.ofNat (rightDenomPred + 1))
                (Int.ofNat (leftMagnitude + 1))).trans
              ((congrArg Int.neg
                  (intMulComm (Int.ofNat (rightDenomPred + 1))
                    (Int.ofNat (leftMagnitude + 1)))).trans
                (intNegMul (Int.ofNat (leftMagnitude + 1))
                  (Int.ofNat (rightDenomPred + 1))).symm)))
      have leftDenominatorBelowScaled :
          Int.ofNat (leftDenomPred + 1) ≤
            Int.ofNat (leftMagnitude + 1) * Int.ofNat (marginIndex + 1) :=
        intLessEqualOfEqLeft
          (intOneMul (Int.ofNat (leftDenomPred + 1))).symm isLeftAbove
      have rightDenominatorBelowScaled :
          Int.ofNat (rightDenomPred + 1) ≤
            Int.ofNat (rightMagnitude + 1) * Int.ofNat (marginIndex + 1) :=
        intLessEqualOfEqLeft
          (intOneMul (Int.ofNat (rightDenomPred + 1))).symm isRightAbove
      have denominatorsBelowScaled :
          Int.ofNat (rightDenomPred + 1) * Int.ofNat (leftDenomPred + 1) ≤
            Int.ofNat (rightMagnitude + 1) * Int.ofNat (marginIndex + 1) *
              (Int.ofNat (leftMagnitude + 1) * Int.ofNat (marginIndex + 1)) :=
        intLessEqualTrans
          (intMulLeMulRightOfNonNeg rightDenominatorBelowScaled
            (intZeroLeOfNat (leftDenomPred + 1)))
          (intMulLeMulLeftOfNonNeg leftDenominatorBelowScaled
            (intZeroLeOfNat ((rightMagnitude + 1) * (marginIndex + 1))))
      have scaledDenominatorsRegroup :
          Int.ofNat (rightMagnitude + 1) * Int.ofNat (marginIndex + 1) *
            (Int.ofNat (leftMagnitude + 1) * Int.ofNat (marginIndex + 1)) =
          Int.ofNat (marginIndex + 1) * Int.ofNat (marginIndex + 1) *
            (Int.ofNat (leftMagnitude + 1) * Int.ofNat (rightMagnitude + 1)) :=
        (intMulSwapMiddle (Int.ofNat (rightMagnitude + 1))
          (Int.ofNat (marginIndex + 1)) (Int.ofNat (leftMagnitude + 1))
          (Int.ofNat (marginIndex + 1))).trans
          ((intMulComm
            (Int.ofNat (rightMagnitude + 1) * Int.ofNat (leftMagnitude + 1))
            (Int.ofNat (marginIndex + 1) * Int.ofNat (marginIndex + 1))).trans
            (congrArg
              (Int.ofNat (marginIndex + 1) * Int.ofNat (marginIndex + 1) * ·)
              (intMulComm (Int.ofNat (rightMagnitude + 1))
                (Int.ofNat (leftMagnitude + 1)))))
      have boundScalesRegroup :
          bound.numerator *
            (Int.ofNat (rightMagnitude + 1) * Int.ofNat (marginIndex + 1) *
              (Int.ofNat (leftMagnitude + 1) * Int.ofNat (marginIndex + 1))) =
          Int.ofNat (marginIndex + 1) * Int.ofNat (marginIndex + 1) *
            bound.numerator *
            (Int.ofNat (leftMagnitude + 1) * Int.ofNat (rightMagnitude + 1)) :=
        (congrArg (bound.numerator * ·) scaledDenominatorsRegroup).trans
          ((intMulAssoc bound.numerator
            (Int.ofNat (marginIndex + 1) * Int.ofNat (marginIndex + 1))
            (Int.ofNat (leftMagnitude + 1) *
              Int.ofNat (rightMagnitude + 1))).symm.trans
            (congrArg
              (· * (Int.ofNat (leftMagnitude + 1) *
                Int.ofNat (rightMagnitude + 1)))
              (intMulComm bound.numerator
                (Int.ofNat (marginIndex + 1) * Int.ofNat (marginIndex + 1)))))
      have boundTimesDenominators :
          bound.numerator *
            (Int.ofNat (rightDenomPred + 1) * Int.ofNat (leftDenomPred + 1)) ≤
          bound.numerator *
            (Int.ofNat (rightMagnitude + 1) * Int.ofNat (marginIndex + 1) *
              (Int.ofNat (leftMagnitude + 1) * Int.ofNat (marginIndex + 1))) :=
        intMulLeMulLeftOfNonNeg denominatorsBelowScaled
          (numeratorNonNegativeOfIsNonNegative isBoundNonNegative)
      have leftNumeratorRewrites :
          (Int.ofNat (leftDenomPred + 1) * Int.ofNat (rightMagnitude + 1) +
              (-Int.ofNat (rightDenomPred + 1)) *
                Int.ofNat (leftMagnitude + 1)) *
            denominatorInt
              (mulExact
                (ratioOfNatSucc ((marginIndex + 1) * (marginIndex + 1)) 0)
                bound) =
          (Int.ofNat (rightMagnitude + 1) * Int.ofNat (leftDenomPred + 1) +
              (-Int.ofNat (leftMagnitude + 1)) *
                Int.ofNat (rightDenomPred + 1)) *
            denominatorInt bound :=
        (congrArg
          (· * denominatorInt
            (mulExact
              (ratioOfNatSucc ((marginIndex + 1) * (marginIndex + 1)) 0)
              bound))
          crossNumeratorsAgree).trans
          (congrArg
            ((Int.ofNat (rightMagnitude + 1) * Int.ofNat (leftDenomPred + 1) +
              (-Int.ofNat (leftMagnitude + 1)) *
                Int.ofNat (rightDenomPred + 1)) * ·)
            (intOneMul (denominatorInt bound)))
      intLessEqualOfEqLeft leftNumeratorRewrites
        (intLessEqualTrans isDiffBounded
          (intLessEqualOfEqRight boundTimesDenominators boundScalesRegroup))

/-- **The reciprocal is Lipschitz on the margin**, two-sidedly: a bound
on the difference scales by `(p+1)²` into a bound on the reciprocal
difference — both sides from the one-sided lemma with the roles
swapped. -/
theorem invExactRespectsIsWithinBound {marginIndex : Nat}
    {leftValue rightValue bound : RationalPair}
    (isLeftAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) leftValue)
    (isRightAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) rightValue)
    (isBoundNonNegative : IsNonNegative bound)
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinBound (invExact leftValue) (invExact rightValue)
      (mulExact (ratioOfNatSucc ((marginIndex + 1) * (marginIndex + 1)) 0)
        bound) :=
  ⟨invExactSubLessEqualScaledOfMargins isLeftAboveMargin isRightAboveMargin
      isBoundNonNegative isWithin.right,
    invExactSubLessEqualScaledOfMargins isRightAboveMargin isLeftAboveMargin
      isBoundNonNegative isWithin.left⟩

/-! ## The margin kit for the field law (NUM-R-5e)

The two ℚ-side facts the field law `x · x⁻¹ ~ 1` consumes at every
sampled index: a margin makes the sampled approximant apart from zero
(so the exact `mulExactInvRight` applies), and it bounds the
reciprocal's magnitude by `p+1` (so the mismatched-sampling drift
scales by a constant the slack closure can erase). -/

/-- A value above a reciprocal margin is apart from zero — sameness
with zero collapses the numerator to zero, and the margin then pins a
positive denominator below zero. -/
theorem isApartFromZeroOfMargin {marginIndex : Nat} {value : RationalPair}
    (isAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) value) :
    IsApartFromZero value :=
  fun denotesZero =>
    have numeratorIsZero : value.numerator = 0 :=
      (intMulOne value.numerator).symm.trans
        (denotesZero.trans (intZeroMul (denominatorInt value)))
    have denominatorBelowZero : denominatorInt value ≤ (0 : Int) :=
      intLessEqualOfEqLeft (intOneMul (denominatorInt value)).symm
        (intLessEqualOfEqRight isAboveMargin
          ((congrArg (· * denominatorInt (reciprocalOfSucc marginIndex))
              numeratorIsZero).trans
            (intZeroMul (denominatorInt (reciprocalOfSucc marginIndex)))))
    nomatch natLeOfIntOfNatLe denominatorBelowZero

/-- The field law under a margin — the margin supplies the apartness. -/
theorem mulExactInvRightOfMargin {marginIndex : Nat} {value : RationalPair}
    (isAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) value) :
    DenotesSameAs (mulExact value (invExact value)) oneRational :=
  mulExactInvRight (isApartFromZeroOfMargin isAboveMargin)

/-- **The reciprocal's magnitude bound**: on values above the margin
`1/(p+1)`, the exact reciprocal's magnitude sits within `p+1` — the
upper cross-product IS the margin inequality commuted, and the
negative side is a `negSucc` below an `ofNat`. -/
theorem invExactIsMagnitudeWithinOfMargin {marginIndex : Nat}
    {value : RationalPair}
    (isAboveMargin : LessEqualAs (reciprocalOfSucc marginIndex) value) :
    IsMagnitudeWithin (invExact value)
      (ratioOfNatSucc (marginIndex + 1) 0) :=
  match value, isAboveMargin with
  | ⟨.ofNat 0, _⟩, isAbove =>
      (noMarginAboveZeroNumerator isAbove).elim
  | ⟨.negSucc _, _⟩, isAbove =>
      (noMarginAboveNegativeNumerator isAbove).elim
  | ⟨.ofNat (magnitudePredecessor + 1), denominatorPredecessor⟩, isAbove =>
      have isReciprocalBelowBound :
          LessEqualAs
            ⟨Int.ofNat (denominatorPredecessor + 1), magnitudePredecessor⟩
            (ratioOfNatSucc (marginIndex + 1) 0) :=
        intLessEqualOfEqLeft
          (intMulComm (Int.ofNat (denominatorPredecessor + 1)) (Int.ofNat 1))
          (intLessEqualOfEqRight isAbove
            (intMulComm (Int.ofNat (magnitudePredecessor + 1))
              (Int.ofNat (marginIndex + 1))))
      have isNegatedReciprocalBelowBound :
          LessEqualAs
            (negExact
              ⟨Int.ofNat (denominatorPredecessor + 1), magnitudePredecessor⟩)
            (ratioOfNatSucc (marginIndex + 1) 0) :=
        intLessEqualOfEqLeft
          (intMulOne (Int.negSucc denominatorPredecessor))
          (intNegSuccLeOfNat denominatorPredecessor
            ((marginIndex + 1) * (magnitudePredecessor + 1)))
      ⟨isReciprocalBelowBound, isNegatedReciprocalBelowBound⟩

/-! ## The sampling depth (NUM-R-5d)

The inverse samples its value at a `boundScaledIndex` whose bound
predecessor is the PREDECESSOR-SHAPED square `(p+1)·p + p` — so the
scale factor's numerator is DEFINITIONALLY the Lipschitz constant
`(p+1)²`, and the R-3b exact collapse cancels it against each scaled
denominator with no inequality reasoning.  The depth lemma checks the
sampled indices clear the witness's half margin. -/

/-- The predecessor-shaped square: `squaredSuccessorPredecessor p + 1`
is DEFINITIONALLY `(p+1)·(p+1)` — the reciprocal's Lipschitz constant,
spelled so the bound-scaled index's numerator cancellation applies. -/
def squaredSuccessorPredecessor (marginIndex : Nat) : Nat :=
  (marginIndex + 1) * marginIndex + marginIndex

/-- Every squared-scaled sampling index clears the margin itself —
chain `p ≤ (p+1)·p + p ≤ 2·(…)+1 ≤ scaled` through the additive
witnesses. -/
theorem halfMarginLeBoundScaledIndex (marginIndex index : Nat) :
    marginIndex ≤
      boundScaledIndex (squaredSuccessorPredecessor marginIndex) index :=
  natLeTrans
    (natLeTrans
      (Nat.le_add_left marginIndex ((marginIndex + 1) * marginIndex))
      (natSelfLeDoubleSelfSucc (squaredSuccessorPredecessor marginIndex)))
    (Nat.le_add_left (2 * squaredSuccessorPredecessor marginIndex + 1)
      (2 * (squaredSuccessorPredecessor marginIndex + 1) * index))

end RationalPair

open RationalPair

/-- The inverse's sampling index — deep enough that every sampled
approximant clears the witness's half margin, scaled so the Lipschitz
constant collapses exactly against the sampled regularity moduli. -/
def inverseSamplingIndex {value : RegularReal}
    (witness : RealPositivityWitness value) (index : Nat) : Nat :=
  boundScaledIndex
    (squaredSuccessorPredecessor (2 * witness.marginIndex + 1)) index

/-- **The inverse of a positive real** — exact reciprocals of the
approximants sampled past the half margin.  Regularity is the
reciprocal Lipschitz bound applied to the sampled regularity
certificate: the margins come from the tail lemma at the scaled depth,
the `(p+1)²`-scaled modulus distributes and collapses EXACTLY to the
halved reciprocals (the R-3b numerator cancellation), and antitone
relaxation lands on the required `1/(n+1) + 1/(m+1)`. -/
def inverseReal {value : RegularReal}
    (witness : RealPositivityWitness value) : RegularReal :=
  { approximation := fun index =>
      invExact (value.approximation (inverseSamplingIndex witness index))
    isRegular := fun firstIndex secondIndex =>
      have scaledBoundIsWithin :
          IsWithinBound
            (invExact (value.approximation
              (inverseSamplingIndex witness firstIndex)))
            (invExact (value.approximation
              (inverseSamplingIndex witness secondIndex)))
            (mulExact
              (ratioOfNatSucc
                ((2 * witness.marginIndex + 1 + 1) *
                  (2 * witness.marginIndex + 1 + 1)) 0)
              (addExact
                (reciprocalOfSucc (inverseSamplingIndex witness firstIndex))
                (reciprocalOfSucc
                  (inverseSamplingIndex witness secondIndex)))) :=
        invExactRespectsIsWithinBound
          (tailStaysAboveHalfMargin witness.hasDoubledMargin
            (halfMarginLeBoundScaledIndex (2 * witness.marginIndex + 1)
              firstIndex))
          (tailStaysAboveHalfMargin witness.hasDoubledMargin
            (halfMarginLeBoundScaledIndex (2 * witness.marginIndex + 1)
              secondIndex))
          (addExactIsNonNegative
            (ratioOfNatSuccIsNonNegative 1
              (inverseSamplingIndex witness firstIndex))
            (ratioOfNatSuccIsNonNegative 1
              (inverseSamplingIndex witness secondIndex)))
          (value.isRegular (inverseSamplingIndex witness firstIndex)
            (inverseSamplingIndex witness secondIndex))
      have scaledBoundCollapses :
          DenotesSameAs
            (mulExact
              (ratioOfNatSucc
                ((2 * witness.marginIndex + 1 + 1) *
                  (2 * witness.marginIndex + 1 + 1)) 0)
              (addExact
                (reciprocalOfSucc (inverseSamplingIndex witness firstIndex))
                (reciprocalOfSucc
                  (inverseSamplingIndex witness secondIndex))))
            (addExact (reciprocalOfSucc (2 * firstIndex + 1))
              (reciprocalOfSucc (2 * secondIndex + 1))) :=
        denotesSameAsTrans
          (mulExactLeftDistrib
            (ratioOfNatSucc
              ((2 * witness.marginIndex + 1 + 1) *
                (2 * witness.marginIndex + 1 + 1)) 0)
            (reciprocalOfSucc (inverseSamplingIndex witness firstIndex))
            (reciprocalOfSucc (inverseSamplingIndex witness secondIndex)))
          (addExactRespectsDenotesSameAs
            (mulRatioReciprocalScaledCollapses
              (squaredSuccessorPredecessor (2 * witness.marginIndex + 1))
              firstIndex)
            (mulRatioReciprocalScaledCollapses
              (squaredSuccessorPredecessor (2 * witness.marginIndex + 1))
              secondIndex))
      isWithinBoundOfBoundLessEqual
        (addExactMonotone
          (ratioOfNatSuccAntitoneDenominator 1
            (natSelfLeDoubleSelfSucc firstIndex))
          (ratioOfNatSuccAntitoneDenominator 1
            (natSelfLeDoubleSelfSucc secondIndex)))
        (isWithinBoundCongrBound scaledBoundCollapses scaledBoundIsWithin) }

end FX1Poly.ComputerAlgebra
