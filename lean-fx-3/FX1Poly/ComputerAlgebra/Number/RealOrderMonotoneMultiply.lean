import FX1Poly.ComputerAlgebra.Number.ComplexRealTriangleInequality

/-! # RealOrderMonotoneMultiply — ℝ-order monotone multiplication

Multiplication by a nonnegative real is monotone for the non-strict Bishop
order: `weight ≥ 0` and `x ≤ y` give `weight·x ≤ weight·y`.  The polynomial
growth bound and the integral layer both rely on it.

`mulReal a c` samples each factor at a factor-dependent
`productSamplingIndex a c index`, so `mulReal weight x` and `mulReal weight y`
sample at different depths — a pointwise lift of the ℚ product monotonicity does
not typecheck, and the clean `(y − x)·weight ≥ 0` route would need the strong
pointwise `IsNonNegativeReal (subReal y x)` from the weak vanishing-lower-bound
`LessEqualReal x y`, a bridge this development bypasses.

The crux is proved directly and pointwise
(`mulRealVanishingLowerBoundLeftNonNeg`): if `weight` is pointwise nonnegative
and the difference `d` clears the vanishing lower bound `−1/(index+1)` at every
index, then so does `mulReal weight d`.  At the comparison index `n` the product
samples both factors at `s = productSamplingIndex weight d n`; there
`weight_s ≥ 0` and `d_s ≥ −1/(s+1)`, so `weight_s·d_s ≥ −weight_s/(s+1)`.  The
deep sampling index makes this exact: the shared magnitude bound
`sharedBound = (P+1)/1` dominates `weight_s`, and `sharedBound · 1/(s+1)`
collapses (`mulRatioReciprocalScaledCollapses`, since `s + 1` is definitionally
`2·(P+1)·(n+1)`) to `1/(2n+2) ≤ 1/(n+1)` — no slack closure, no real-order case
split.

From the crux the one-sided `realMulLeftMonotone` is a distribution
(`mulReal weight (subReal y x) ~ subReal (mulReal weight y) (mulReal weight x)`)
carried across by `realNonNegativeRespectsDenotesSame`; the right-factor version
commutes; and the two-sided `realMulMonotone` chains `a·c ≤ b·c ≤ b·d` through
`lessEqualRealTrans`, which needs the upper-left `b` and the shared `c` pointwise
nonnegative (the honest hypotheses, since `a ≥ 0` and `a ≤ b` give `b ≥ 0` only
weakly).

Zero-axiom: only explicit rational witnesses and the slack/monotone ℚ kit; no
real `≤`/equality is ever case-split.  Per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- **The multiplicative crux, pointwise**: a pointwise-nonnegative `weight`
scales a vanishing-lower-bounded `difference` to a vanishing-lower-bounded
product.  At `comparisonIndex` the product samples both factors at
`sampleIndex = productSamplingIndex weight difference comparisonIndex`, where the
shared bound scaled by the deep reciprocal collapses exactly to
`1/(2·comparisonIndex+2) ≤ 1/(comparisonIndex+1)`. -/
theorem mulRealVanishingLowerBoundLeftNonNeg {weight difference : RegularReal}
    (isWeightNonNegative : IsNonNegativeReal weight)
    (isDifferenceVanishing : ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index))
        (difference.approximation index)) :
    ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index))
        ((mulReal weight difference).approximation index) :=
  fun comparisonIndex =>
    let sampleIndex := productSamplingIndex weight difference comparisonIndex
    have isWeightSampleNonNegative :
        IsNonNegative (weight.approximation sampleIndex) :=
      isWeightNonNegative sampleIndex
    have isShiftedDifferenceNonNegative :
        IsNonNegative (addExact (difference.approximation sampleIndex)
          (reciprocalOfSucc sampleIndex)) :=
      lessEqualAsCongrLeft
        (addExactNegLeftDenotesSame (reciprocalOfSucc sampleIndex))
        (addExactMonotoneLeft (reciprocalOfSucc sampleIndex)
          (isDifferenceVanishing sampleIndex))
    have isDistributedProductNonNegative :
        IsNonNegative (addExact
          (mulExact (weight.approximation sampleIndex)
            (difference.approximation sampleIndex))
          (mulExact (weight.approximation sampleIndex)
            (reciprocalOfSucc sampleIndex))) :=
      lessEqualAsCongrRight
        (mulExactLeftDistrib (weight.approximation sampleIndex)
          (difference.approximation sampleIndex) (reciprocalOfSucc sampleIndex))
        (mulExactIsNonNegative isWeightSampleNonNegative
          isShiftedDifferenceNonNegative)
    have isProductAboveNegScaled :
        LessEqualAs
          (negExact (mulExact (weight.approximation sampleIndex)
            (reciprocalOfSucc sampleIndex)))
          (mulExact (weight.approximation sampleIndex)
            (difference.approximation sampleIndex)) :=
      lessEqualAsAddRightCancel
        (lessEqualAsCongrLeft
          (denotesSameAsSymm (addExactNegLeftDenotesSame
            (mulExact (weight.approximation sampleIndex)
              (reciprocalOfSucc sampleIndex))))
          isDistributedProductNonNegative)
    have isScaledWeightBelowScaledBound :
        LessEqualAs
          (mulExact (weight.approximation sampleIndex)
            (reciprocalOfSucc sampleIndex))
          (mulExact (sharedBound weight difference)
            (reciprocalOfSucc sampleIndex)) :=
      mulExactMonotoneOfNonNegative
        (leftApproximationIsWithinSharedBound weight difference sampleIndex).left
        (lessEqualAsRefl (reciprocalOfSucc sampleIndex))
        (ratioOfNatSuccIsNonNegative 1 sampleIndex)
        (ratioOfNatSuccIsNonNegative
          (sharedBoundNumeratorPredecessor weight difference + 1) 0)
    have isProductAboveNegDeep :
        LessEqualAs (negExact (reciprocalOfSucc (2 * comparisonIndex + 1)))
          (mulExact (weight.approximation sampleIndex)
            (difference.approximation sampleIndex)) :=
      lessEqualAsTrans
        (lessEqualAsCongrLeft
          (negExactRespectsDenotesSameAs
            (mulRatioReciprocalScaledCollapses
              (sharedBoundNumeratorPredecessor weight difference)
              comparisonIndex))
          (lessEqualAsNegBoth isScaledWeightBelowScaledBound))
        isProductAboveNegScaled
    lessEqualAsTrans
      (lessEqualAsNegBoth
        (ratioOfNatSuccAntitoneDenominator 1
          (natSelfLeDoubleSelfSucc comparisonIndex)))
      isProductAboveNegDeep

/-- **Left monotone multiplication**: `weight ≥ 0` and `x ≤ y` give
`weight·x ≤ weight·y`.  The difference `subReal y x` is exactly the vanishing
lower bound `LessEqualReal x y` carries, so the crux gives the vanishing lower
bound of `mulReal weight (subReal y x)`; distributivity denotes it as
`subReal (mulReal weight y) (mulReal weight x)`, and
`realNonNegativeRespectsDenotesSame` carries the bound across. -/
theorem realMulLeftMonotone {weight leftValue rightValue : RegularReal}
    (isWeightNonNegative : IsNonNegativeReal weight)
    (isBelow : LessEqualReal leftValue rightValue) :
    LessEqualReal (mulReal weight leftValue) (mulReal weight rightValue) :=
  have distributeDenotes :
      DenotesSameReal (mulReal weight (subReal rightValue leftValue))
        (subReal (mulReal weight rightValue) (mulReal weight leftValue)) :=
    denotesSameRealTrans
      (mulRealLeftDistrib weight rightValue (negReal leftValue))
      (addRealRespectsDenotesSame (denotesSameRealRefl (mulReal weight rightValue))
        (mulRealNegRightDenotesSame weight leftValue))
  realNonNegativeRespectsDenotesSame distributeDenotes
    (mulRealVanishingLowerBoundLeftNonNeg (weight := weight)
      (difference := subReal rightValue leftValue) isWeightNonNegative isBelow)

/-- **Right monotone multiplication**: `weight ≥ 0` and `x ≤ y` give
`x·weight ≤ y·weight` — commute both products onto the left version. -/
theorem realMulRightMonotone {weight leftValue rightValue : RegularReal}
    (isWeightNonNegative : IsNonNegativeReal weight)
    (isBelow : LessEqualReal leftValue rightValue) :
    LessEqualReal (mulReal leftValue weight) (mulReal rightValue weight) :=
  lessEqualRealCongr (mulRealComm weight leftValue) (mulRealComm weight rightValue)
    (realMulLeftMonotone isWeightNonNegative isBelow)

/-- **Two-sided monotone multiplication**: from `c ≥ 0`, `b ≥ 0`, `a ≤ b`, and
`c ≤ d` conclude `a·c ≤ b·d` via `a·c ≤ b·c ≤ b·d`.  The upper-left factor `b`
must be pointwise nonnegative in its own right — `a ≥ 0` and `a ≤ b` give `b ≥ 0`
only WEAKLY (a vanishing lower bound), never the pointwise nonnegativity the
right step of the chain consumes; requiring it is honest, not a bypass. -/
theorem realMulMonotone {a b c d : RegularReal}
    (isSharedRightNonNegative : IsNonNegativeReal c)
    (isUpperLeftNonNegative : IsNonNegativeReal b)
    (isLeftBelow : LessEqualReal a b)
    (isRightBelow : LessEqualReal c d) :
    LessEqualReal (mulReal a c) (mulReal b d) :=
  lessEqualRealTrans
    (realMulRightMonotone isSharedRightNonNegative isLeftBelow)
    (realMulLeftMonotone isUpperLeftNonNegative isRightBelow)

/-- Marker: the real order carries monotone multiplication by a nonnegative
factor. -/
def fxRegularReal_hasOrderMonotoneMultiply : Bool := true

end FX1Poly.ComputerAlgebra
