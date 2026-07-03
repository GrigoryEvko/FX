import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # RegularReal inverse — the ℚ reciprocal kit (NUM-R-5c)

The one hard fact behind the constructive inverse: on values above a
shared margin `1/(p+1)`, the exact reciprocal is Lipschitz with the
EXPLICIT constant `(p+1)²` — `|1/a − 1/b| ≤ (p+1)²·|a−b|`.  The proof
is SIGN-FREE: the reciprocal difference and the reversed difference
share their numerator verbatim (both are the same cross-product gap),
so the bound never inspects the gap's sign — the margin inequalities
scale the DENOMINATORS only, and the bound's nonnegativity absorbs the
scaling.  The margins also force positive numerators, refuting the
zero and negative `invExact` arms outright. -/

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

end RationalPair

end FX1Poly.ComputerAlgebra
