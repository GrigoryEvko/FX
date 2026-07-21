import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # RegularReal inverse — reciprocal kit + the inverse

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
EXACTLY (the bound-scaled numerator cancellation) onto the required modulus.

The margin kit also lives here: a margin makes a value APART FROM
ZERO (so the exact field law applies at every sampled approximant) and
bounds its reciprocal's MAGNITUDE by `p+1` (so mismatched-sampling
drift scales by a constant that slack closure can erase), the per-index
near-one estimate composes them, and the FIELD LAW closes: `x · x⁻¹`
denotes one, by slack closure over the vanishing estimate.  The
apartness extension inverts on EITHER side of zero — the order
witnesses transport along the zero-difference bridges, negative reals
invert through `negReal` — and the HEYTING-FIELD LAW closes the
construction: `x · inverseRealOfApartness x ~ 1` on both branches, the
negative one through the sign-pull identities with their sampling
indices reconciled by the sign-blind canonical bound. -/

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

/-! ## The margin kit for the field law

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

/-! ## The sampling depth

The inverse samples its value at a `boundScaledIndex` whose bound
predecessor is the PREDECESSOR-SHAPED square `(p+1)·p + p` — so the
scale factor's numerator is DEFINITIONALLY the Lipschitz constant
`(p+1)²`, and the bound-scaled exact collapse cancels it against each
scaled denominator with no inequality reasoning.  The depth lemma checks the
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
halved reciprocals (the bound-scaled numerator cancellation), and antitone
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

/-! ## The per-index near-one estimate

At every index, the `x · x⁻¹` approximant sits within a `(p+1)`-scaled
sampled modulus of ONE.  The approximant IS `x_S · (x_{T·S})⁻¹`
definitionally (mismatched samples: the product's index against the
inverse's deeper index); the anchor `x_{T·S} · (x_{T·S})⁻¹` denotes one
by the margin-keyed field law, and the drift between the two samples is
the value's own regularity scaled through the reciprocal's magnitude
bound. -/

/-- **The near-one estimate**: the `mulReal value (inverseReal witness)`
approximant differs from one by at most `p+1` times the sampled
regularity modulus — the drift leg via the product-difference law at
the reciprocal's magnitude bound, the anchor leg exact. -/
theorem mulRealInverseApproximationNearOne {value : RegularReal}
    (witness : RealPositivityWitness value) (index : Nat) :
    IsWithinBound
      ((mulReal value (inverseReal witness)).approximation index)
      oneRational
      (mulExact (ratioOfNatSucc (2 * witness.marginIndex + 1 + 1) 0)
        (addExact
          (reciprocalOfSucc
            (productSamplingIndex value (inverseReal witness) index))
          (reciprocalOfSucc
            (inverseSamplingIndex witness
              (productSamplingIndex value (inverseReal witness) index))))) :=
  have isSampleAboveMargin :
      LessEqualAs (reciprocalOfSucc (2 * witness.marginIndex + 1))
        (value.approximation
          (inverseSamplingIndex witness
            (productSamplingIndex value (inverseReal witness) index))) :=
    tailStaysAboveHalfMargin witness.hasDoubledMargin
      (halfMarginLeBoundScaledIndex (2 * witness.marginIndex + 1)
        (productSamplingIndex value (inverseReal witness) index))
  have driftIsWithin :
      IsWithinBound
        (mulExact
          (value.approximation
            (productSamplingIndex value (inverseReal witness) index))
          (invExact (value.approximation
            (inverseSamplingIndex witness
              (productSamplingIndex value (inverseReal witness) index)))))
        (mulExact
          (value.approximation
            (inverseSamplingIndex witness
              (productSamplingIndex value (inverseReal witness) index)))
          (invExact (value.approximation
            (inverseSamplingIndex witness
              (productSamplingIndex value (inverseReal witness) index)))))
        (mulExact (ratioOfNatSucc (2 * witness.marginIndex + 1 + 1) 0)
          (addExact
            (reciprocalOfSucc
              (productSamplingIndex value (inverseReal witness) index))
            (reciprocalOfSucc
              (inverseSamplingIndex witness
                (productSamplingIndex value (inverseReal witness)
                  index))))) :=
    mulExactRespectsIsWithinBoundRight
      (invExactIsMagnitudeWithinOfMargin isSampleAboveMargin)
      (value.isRegular
        (productSamplingIndex value (inverseReal witness) index)
        (inverseSamplingIndex witness
          (productSamplingIndex value (inverseReal witness) index)))
      (addExactIsNonNegative
        (ratioOfNatSuccIsNonNegative 1
          (productSamplingIndex value (inverseReal witness) index))
        (ratioOfNatSuccIsNonNegative 1
          (inverseSamplingIndex witness
            (productSamplingIndex value (inverseReal witness) index))))
  isWithinBoundCongrRight (mulExactInvRightOfMargin isSampleAboveMargin)
    driftIsWithin

/-! ## The field law

`x · x⁻¹` DENOTES ONE.  Bishop-style slack closure at each comparison
index: chain the product's own regularity to an arbitrary slack index,
apply the near-one estimate there — its bound relaxes to a FIXED
multiple of the slack reciprocal because both sampled indices dominate
the slack index — and the vanishing remainder is erased by slack
closure.  No limit, no choice: the closure is a decision plus an
Archimedean saturation. -/

/-- **The field law**: a positive real times its inverse denotes one —
the multiplicative half of the Heyting-field package.  Regularity to
the slack sample, the near-one estimate at the slack sample, tails
relaxed by index antitonicity, the scale collapsed exactly, slack
closure. -/
theorem mulRealInverseDenotesOne {value : RegularReal}
    (witness : RealPositivityWitness value) :
    DenotesSameReal (mulReal value (inverseReal witness))
      (constantReal oneRational) :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      have isChainedThroughSlackSample :
          IsWithinBound
            ((mulReal value (inverseReal witness)).approximation
              sharedIndex)
            oneRational
            (addExact
              (addExact (reciprocalOfSucc sharedIndex)
                (reciprocalOfSucc slackIndex))
              (mulExact
                (ratioOfNatSucc (2 * witness.marginIndex + 1 + 1) 0)
                (addExact
                  (reciprocalOfSucc
                    (productSamplingIndex value (inverseReal witness)
                      slackIndex))
                  (reciprocalOfSucc
                    (inverseSamplingIndex witness
                      (productSamplingIndex value (inverseReal witness)
                        slackIndex)))))) :=
        isWithinBoundTriangle
          ((mulReal value (inverseReal witness)).isRegular sharedIndex
            slackIndex)
          (mulRealInverseApproximationNearOne witness slackIndex)
      have sampleTailsRelaxToSlack :
          LessEqualAs
            (addExact
              (reciprocalOfSucc
                (productSamplingIndex value (inverseReal witness)
                  slackIndex))
              (reciprocalOfSucc
                (inverseSamplingIndex witness
                  (productSamplingIndex value (inverseReal witness)
                    slackIndex))))
            (addExact (reciprocalOfSucc slackIndex)
              (reciprocalOfSucc slackIndex)) :=
        addExactMonotone
          (ratioOfNatSuccAntitoneDenominator 1
            (natSelfLeBoundScaledIndex
              (sharedBoundNumeratorPredecessor value (inverseReal witness))
              slackIndex))
          (ratioOfNatSuccAntitoneDenominator 1
            (natLeTrans
              (natSelfLeBoundScaledIndex
                (sharedBoundNumeratorPredecessor value
                  (inverseReal witness))
                slackIndex)
              (natSelfLeBoundScaledIndex
                (squaredSuccessorPredecessor (2 * witness.marginIndex + 1))
                (productSamplingIndex value (inverseReal witness)
                  slackIndex))))
      have scaledTailRelaxesToSlack :
          LessEqualAs
            (mulExact (ratioOfNatSucc (2 * witness.marginIndex + 1 + 1) 0)
              (addExact
                (reciprocalOfSucc
                  (productSamplingIndex value (inverseReal witness)
                    slackIndex))
                (reciprocalOfSucc
                  (inverseSamplingIndex witness
                    (productSamplingIndex value (inverseReal witness)
                      slackIndex)))))
            (ratioOfNatSucc ((2 * witness.marginIndex + 1 + 1) * 2)
              slackIndex) :=
        lessEqualAsCongrRight
          (denotesSameAsTrans
            (mulExactRespectsDenotesSameAs
              (denotesSameAsRefl
                (ratioOfNatSucc (2 * witness.marginIndex + 1 + 1) 0))
              (ratioOfNatSuccSumDenotesSame 1 1 slackIndex))
            (mulExactRatioRatioDenotesSame
              (2 * witness.marginIndex + 1 + 1) 2 slackIndex))
          (mulExactMonotoneOfNonNegative
            (lessEqualAsRefl
              (ratioOfNatSucc (2 * witness.marginIndex + 1 + 1) 0))
            sampleTailsRelaxToSlack
            (addExactIsNonNegative
              (ratioOfNatSuccIsNonNegative 1
                (productSamplingIndex value (inverseReal witness)
                  slackIndex))
              (ratioOfNatSuccIsNonNegative 1
                (inverseSamplingIndex witness
                  (productSamplingIndex value (inverseReal witness)
                    slackIndex))))
            (ratioOfNatSuccIsNonNegative
              (2 * witness.marginIndex + 1 + 1) 0))
      have boundGathersOnSlack :
          DenotesSameAs
            (addExact
              (addExact (reciprocalOfSucc sharedIndex)
                (reciprocalOfSucc slackIndex))
              (ratioOfNatSucc ((2 * witness.marginIndex + 1 + 1) * 2)
                slackIndex))
            (addExact (reciprocalOfSucc sharedIndex)
              (ratioOfNatSucc
                (1 + (2 * witness.marginIndex + 1 + 1) * 2)
                slackIndex)) :=
        denotesSameAsTrans
          (addExactAssoc (reciprocalOfSucc sharedIndex)
            (reciprocalOfSucc slackIndex)
            (ratioOfNatSucc ((2 * witness.marginIndex + 1 + 1) * 2)
              slackIndex))
          (addExactRespectsDenotesSameAs
            (denotesSameAsRefl (reciprocalOfSucc sharedIndex))
            (ratioOfNatSuccSumDenotesSame 1
              ((2 * witness.marginIndex + 1 + 1) * 2) slackIndex))
      isWithinBoundOfBoundLessEqual
        (addExactMonotone
          (ratioOfNatSuccMonotoneNumerator (Nat.le_succ 1) sharedIndex)
          (lessEqualAsRefl
            (ratioOfNatSucc
              (1 + (2 * witness.marginIndex + 1 + 1) * 2) slackIndex)))
        (isWithinBoundCongrBound boundGathersOnSlack
          (isWithinBoundOfBoundLessEqual
            (addExactMonotone
              (lessEqualAsRefl
                (addExact (reciprocalOfSucc sharedIndex)
                  (reciprocalOfSucc slackIndex)))
              scaledTailRelaxesToSlack)
            isChainedThroughSlackSample)))

/-! ## The apartness extension

A real APART FROM ZERO gets an inverse on either side.  The strict
order's witnesses live on `subReal` differences against the constant
zero, which agree with the value itself (right slot) or its negation
(left slot) up to the setoid — the zero addend collapses, and the
`subReal` sampling shift `n ↦ 2n+1` is absorbed by the value's own
regularity, pointwise, with no slack needed.  Transporting the
positivity witness along these bridges and dispatching on the
apartness sum yields the inverse: negative reals invert through
`negReal`. -/

/-- The doubled-sample drift sits within the setoid modulus —
regularity at `(2n+1, n)`, the deep reciprocal relaxed by
antitonicity, the halves recombined. -/
theorem doubledSampleDriftIsWithinSetoidBound (value : RegularReal)
    (index : Nat) :
    IsWithinBound (value.approximation (2 * index + 1))
      (value.approximation index) (ratioOfNatSucc 2 index) :=
  isWithinBoundCongrBound (ratioOfNatSuccSumDenotesSame 1 1 index)
    (isWithinBoundOfBoundLessEqual
      (addExactMonotone
        (ratioOfNatSuccAntitoneDenominator 1 (natSelfLeDoubleSelfSucc index))
        (lessEqualAsRefl (reciprocalOfSucc index)))
      (value.isRegular (2 * index + 1) index))

/-- Subtracting the constant zero denotes the value itself — the zero
addend collapses and the sampling shift is the doubled-sample drift. -/
theorem subRealZeroRightDenotesSame (value : RegularReal) :
    DenotesSameReal (subReal value (constantReal zeroRational)) value :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (addExactZeroRight (value.approximation (2 * sharedIndex + 1))))
      (doubledSampleDriftIsWithinSetoidBound value sharedIndex)

/-- Subtracting FROM the constant zero denotes the negation — the zero
addend collapses on the left and negation respects the drift. -/
theorem subRealZeroLeftDenotesSameNegReal (value : RegularReal) :
    DenotesSameReal (subReal (constantReal zeroRational) value)
      (negReal value) :=
  fun sharedIndex =>
    isWithinBoundCongrLeft
      (denotesSameAsSymm
        (addExactZeroLeft
          (negExact (value.approximation (2 * sharedIndex + 1)))))
      (negExactRespectsIsWithinBound
        (doubledSampleDriftIsWithinSetoidBound value sharedIndex))

/-- A real strictly above zero carries a positivity witness — transport
along the right-zero bridge. -/
def realPositivityWitnessOfAboveZero {value : RegularReal}
    (isAboveZero : LessThanReal (constantReal zeroRational) value) :
    RealPositivityWitness value :=
  realPositivityWitnessCongr (subRealZeroRightDenotesSame value) isAboveZero

/-- A real strictly below zero carries a positivity witness ON ITS
NEGATION — transport along the left-zero bridge. -/
def negRealPositivityWitnessOfBelowZero {value : RegularReal}
    (isBelowZero : LessThanReal value (constantReal zeroRational)) :
    RealPositivityWitness (negReal value) :=
  realPositivityWitnessCongr (subRealZeroLeftDenotesSameNegReal value)
    isBelowZero

/-- **The inverse on apartness from zero** — dispatch on the side: a
positive real inverts directly, a negative real inverts through its
negation and negates back. -/
def inverseRealOfApartness {value : RegularReal}
    (isApart : RealApartnessWitness value (constantReal zeroRational)) :
    RegularReal :=
  match isApart with
  | .inl isBelowZero =>
      negReal (inverseReal (negRealPositivityWitnessOfBelowZero isBelowZero))
  | .inr isAboveZero =>
      inverseReal (realPositivityWitnessOfAboveZero isAboveZero)

/-! ## The apartness field law

`x · x⁻¹` denotes one on BOTH sides of zero — the Heyting-field
multiplicative law in full.  The positive branch is the field law
verbatim.  The negative branch pulls the negation across the product
twice: the sign-pull identities are pointwise setoid facts, but the
two products sample at indices built from `canonicalBoundNumerator`,
which mentions `natAbs` of the head approximant's numerator — sign-
blind only PROPOSITIONALLY for an abstract real, so each pull
transports the shared-sample fact along the index equality by an
explicit-motive `Eq.rec`. -/

/-- Negation preserves the numerator magnitude — three constructor
cases, each definitional. -/
theorem intNatAbsNeg : ∀ value : Int, (-value).natAbs = value.natAbs
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

/-- The canonical bound survives negation — the magnitude is
sign-blind. -/
theorem canonicalBoundNumeratorNegReal (value : RegularReal) :
    canonicalBoundNumerator (negReal value) =
      canonicalBoundNumerator value :=
  congrArg (· + 2) (intNatAbsNeg (value.approximation 0).numerator)

/-- **Negation pulls out of the product's right factor** — pointwise
the sign-pull is exact, and the sampling indices agree by the
sign-blind canonical bound. -/
theorem mulRealNegRightDenotesSame (leftValue rightValue : RegularReal) :
    DenotesSameReal (mulReal leftValue (negReal rightValue))
      (negReal (mulReal leftValue rightValue)) :=
  fun sharedIndex =>
    have indexesAgree :
        productSamplingIndex leftValue (negReal rightValue) sharedIndex =
          productSamplingIndex leftValue rightValue sharedIndex :=
      congrArg
        (fun boundNumerator =>
          boundScaledIndex
            (canonicalBoundNumerator leftValue + boundNumerator)
            sharedIndex)
        (canonicalBoundNumeratorNegReal rightValue)
    have atSharedSample :
        IsWithinBound
          (mulExact
            (leftValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex))
            (negExact (rightValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex))))
          (negExact
            (mulExact
              (leftValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))
              (rightValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))))
          (ratioOfNatSucc 2 sharedIndex) :=
      isWithinBoundCongrRight
        (mulExactNegRightDenotesSame
          (leftValue.approximation
            (productSamplingIndex leftValue rightValue sharedIndex))
          (rightValue.approximation
            (productSamplingIndex leftValue rightValue sharedIndex)))
        (isWithinBoundSelfOfNonNegative
          (ratioOfNatSuccIsNonNegative 2 sharedIndex))
    Eq.rec
      (motive := fun sampledIndex _ =>
        IsWithinBound
          (mulExact (leftValue.approximation sampledIndex)
            (negExact (rightValue.approximation sampledIndex)))
          (negExact
            (mulExact
              (leftValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))
              (rightValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))))
          (ratioOfNatSucc 2 sharedIndex))
      atSharedSample indexesAgree.symm

/-- **Negation pulls out of the product's left factor** — mirror of
the right pull. -/
theorem mulRealNegLeftDenotesSame (leftValue rightValue : RegularReal) :
    DenotesSameReal (mulReal (negReal leftValue) rightValue)
      (negReal (mulReal leftValue rightValue)) :=
  fun sharedIndex =>
    have indexesAgree :
        productSamplingIndex (negReal leftValue) rightValue sharedIndex =
          productSamplingIndex leftValue rightValue sharedIndex :=
      congrArg
        (fun boundNumerator =>
          boundScaledIndex
            (boundNumerator + canonicalBoundNumerator rightValue)
            sharedIndex)
        (canonicalBoundNumeratorNegReal leftValue)
    have atSharedSample :
        IsWithinBound
          (mulExact
            (negExact (leftValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex)))
            (rightValue.approximation
              (productSamplingIndex leftValue rightValue sharedIndex)))
          (negExact
            (mulExact
              (leftValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))
              (rightValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))))
          (ratioOfNatSucc 2 sharedIndex) :=
      isWithinBoundCongrRight
        (mulExactNegLeftDenotesSame
          (leftValue.approximation
            (productSamplingIndex leftValue rightValue sharedIndex))
          (rightValue.approximation
            (productSamplingIndex leftValue rightValue sharedIndex)))
        (isWithinBoundSelfOfNonNegative
          (ratioOfNatSuccIsNonNegative 2 sharedIndex))
    Eq.rec
      (motive := fun sampledIndex _ =>
        IsWithinBound
          (mulExact (negExact (leftValue.approximation sampledIndex))
            (rightValue.approximation sampledIndex))
          (negExact
            (mulExact
              (leftValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))
              (rightValue.approximation
                (productSamplingIndex leftValue rightValue sharedIndex))))
          (ratioOfNatSucc 2 sharedIndex))
      atSharedSample indexesAgree.symm

/-- **The Heyting-field law**: a real apart from zero times its
apartness inverse denotes one.  The positive branch is the field law
directly; the negative branch pulls the negation across the product
and lands on the field law at the transported witness. -/
theorem mulRealInverseOfApartnessDenotesOne {value : RegularReal}
    (isApart : RealApartnessWitness value (constantReal zeroRational)) :
    DenotesSameReal (mulReal value (inverseRealOfApartness isApart))
      (constantReal oneRational) :=
  match isApart with
  | .inl isBelowZero =>
      denotesSameRealTrans
        (mulRealNegRightDenotesSame value
          (inverseReal (negRealPositivityWitnessOfBelowZero isBelowZero)))
        (denotesSameRealTrans
          (denotesSameRealSymm
            (mulRealNegLeftDenotesSame value
              (inverseReal
                (negRealPositivityWitnessOfBelowZero isBelowZero))))
          (mulRealInverseDenotesOne
            (negRealPositivityWitnessOfBelowZero isBelowZero)))
  | .inr isAboveZero =>
      mulRealInverseDenotesOne (realPositivityWitnessOfAboveZero isAboveZero)

end FX1Poly.ComputerAlgebra
