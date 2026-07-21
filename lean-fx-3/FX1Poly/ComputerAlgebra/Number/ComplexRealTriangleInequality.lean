import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusLaws
import FX1Poly.ComputerAlgebra.Number.RegularRealOrderTightness
import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRootMultiplicative

/-! # ComplexRealTriangleInequality — the ℂ modulus triangle inequality

`|z + w| ≤ |z| + |w|` on the zero-axiom Bishop-real/complex setoid, a key analysis
theorem toward the Fundamental Theorem of Algebra.  Built on the real-order
tightness/monotonicity layer (`RegularRealOrderTightness`) and the multiplicative
square root (`RegularRealSquareRootMultiplicative`).

The analytic crux is square-root order reflection (`realLeOfSquareLeNonNeg`): if
`s ≥ 0` and `x² ≤ s²` then `x ≤ s`, with `x` of arbitrary sign — only the right
endpoint need be nonnegative.  The proof is the abs-free Bishop pattern of
`squareZeroImpliesZero`: at each comparison index, sample the difference `s − x`
at a quadratically deep index where the vanishing lower bound on the product
`(s − x)(s + x) = s² − x²` reflects (through the rational square-root
`lessEqualAsOfMulExactSquareLeNonNeg`, gated by a decidable-per-index sign split
that touches no real order) into a vanishing lower bound on `s − x`, and
regularity bridges the deep sample back to the comparison index under slack
closure.

From the reflection crux the rest is corollary:

* `nonNegSquareOrderReflect` — the both-endpoints-nonnegative special case;
* `sqrtRealMonotone` — `a ≤ b → √a ≤ √b`;
* `leSqrtOfSquareLe` / `selfLeSqrtRealSquare` — `x ≤ √R` from `x² ≤ R`, and `x ≤ √(x²)`;
* `cauchySchwarzReal` — `ac + bd ≤ |⟨a,b⟩| · |⟨c,d⟩|`;
* `modulusTriangleInequality` — the triangle inequality itself.

The sign split matches on `Decidable` data (`decideLessEqualAs`), never
`decide`-on-a-Prop, and never case-splits on a real order.  Zero axioms. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-! ## ℚ-level lemmas for the reflection crux -/

/-- The negation of the rational zero denotes zero — the numerator is `-0`. -/
theorem negExactZeroDenotesZero : DenotesSameAs (negExact zeroRational) zeroRational :=
  congrArg (· * denominatorInt zeroRational) intNegZero

/-- A nonnegative sum reads back as an order: `0 ≤ base + addend` gives
`−addend ≤ base`.  Replace the zero by `(−addend) + addend`, then cancel the
shared `addend`. -/
theorem lessEqualAsNegRightOfAddNonNeg {baseValue addend : RationalPair}
    (isSumNonNegative : IsNonNegative (addExact baseValue addend)) :
    LessEqualAs (negExact addend) baseValue :=
  lessEqualAsAddRightCancel
    (lessEqualAsCongrLeft (denotesSameAsSymm (addExactNegLeftDenotesSame addend))
      isSumNonNegative)

/-- The converse: `−addend ≤ base` gives `0 ≤ base + addend` — add `addend`
across the order and collapse `(−addend) + addend` to zero. -/
theorem addNonNegOfLessEqualAsNegRight {baseValue addend : RationalPair}
    (isBelow : LessEqualAs (negExact addend) baseValue) :
    IsNonNegative (addExact baseValue addend) :=
  lessEqualAsCongrLeft (addExactNegLeftDenotesSame addend)
    (addExactMonotoneLeft addend isBelow)

/-- The reflection-bridge reshaping: the accumulated bound
`((base + (1/(m+1) + 1/(n+1))) + 1/(m+1))` denotes `((base + 2/(m+1)) + 1/(n+1))`
— rotate the trailing `1/(m+1)` in past the pair and fold the two `1/(m+1)`
copies onto the shared numerator `2`. -/
theorem reflectBridgeIdentity (base : RationalPair)
    (slackPredecessor comparisonPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact base
          (addExact (reciprocalOfSucc slackPredecessor)
            (reciprocalOfSucc comparisonPredecessor)))
        (reciprocalOfSucc slackPredecessor))
      (addExact (addExact base (ratioOfNatSucc 2 slackPredecessor))
        (reciprocalOfSucc comparisonPredecessor)) :=
  have tailCollapses :
      DenotesSameAs
        (addExact
          (addExact (reciprocalOfSucc slackPredecessor)
            (reciprocalOfSucc comparisonPredecessor))
          (reciprocalOfSucc slackPredecessor))
        (addExact (ratioOfNatSucc 2 slackPredecessor)
          (reciprocalOfSucc comparisonPredecessor)) :=
    denotesSameAsTrans
      (addExactAssoc (reciprocalOfSucc slackPredecessor)
        (reciprocalOfSucc comparisonPredecessor)
        (reciprocalOfSucc slackPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (reciprocalOfSucc slackPredecessor))
          (addExactComm (reciprocalOfSucc comparisonPredecessor)
            (reciprocalOfSucc slackPredecessor)))
        (denotesSameAsTrans
          (denotesSameAsSymm
            (addExactAssoc (reciprocalOfSucc slackPredecessor)
              (reciprocalOfSucc slackPredecessor)
              (reciprocalOfSucc comparisonPredecessor)))
          (addExactRespectsDenotesSameAs
            (ratioOfNatSuccSumDenotesSame 1 1 slackPredecessor)
            (denotesSameAsRefl (reciprocalOfSucc comparisonPredecessor)))))
  denotesSameAsTrans
    (addExactAssoc base
      (addExact (reciprocalOfSucc slackPredecessor)
        (reciprocalOfSucc comparisonPredecessor))
      (reciprocalOfSucc slackPredecessor))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs (denotesSameAsRefl base) tailCollapses)
      (denotesSameAsSymm
        (addExactAssoc base (ratioOfNatSucc 2 slackPredecessor)
          (reciprocalOfSucc comparisonPredecessor))))

/-- The reflection step, rationally: given a difference `d` above `−sum`, the
product `d · sum` above `−c`, and `c ≤ ε²` with `ε ≥ 0`, conclude `d ≥ −ε`.  A
sign split on the decidable rational order of `d` against zero: the nonnegative
branch reads `−ε ≤ 0 ≤ d` directly; the negative branch takes `(−d)² ≤ (−d)·sum =
−(d·sum) ≤ c ≤ ε²` (product monotonicity on nonnegatives, since `−d ≤ sum`) and
the rational square-root reflection sends it to `−d ≤ ε`, i.e. `d ≥ −ε`.  No real
order is ever decided; the split is on `Decidable` data. -/
theorem orderReflectStep {differenceApprox sumApprox epsilon boundValue : RationalPair}
    (isDiffAboveNegSum : LessEqualAs (negExact sumApprox) differenceApprox)
    (isProductAboveNegBound :
      LessEqualAs (negExact boundValue) (mulExact differenceApprox sumApprox))
    (isEpsilonNonNegative : IsNonNegative epsilon)
    (isBoundBelowEpsilonSquare :
      LessEqualAs boundValue (mulExact epsilon epsilon)) :
    LessEqualAs (negExact epsilon) differenceApprox :=
  match decideLessEqualAs zeroRational differenceApprox with
  | .isTrue isDiffNonNegative =>
      lessEqualAsTrans (negExactNonPositiveOfNonNegative isEpsilonNonNegative)
        isDiffNonNegative
  | .isFalse isDiffNegative =>
      have isDiffBelowZero : LessEqualAs differenceApprox zeroRational :=
        lessEqualAsOfNotLessEqual isDiffNegative
      have isNegDiffNonNegative : IsNonNegative (negExact differenceApprox) :=
        lessEqualAsCongrLeft negExactZeroDenotesZero
          (lessEqualAsNegBoth isDiffBelowZero)
      have isNegDiffBelowSum : LessEqualAs (negExact differenceApprox) sumApprox :=
        lessEqualAsCongrRight (negExactNegExactDenotesSame sumApprox)
          (lessEqualAsNegBoth isDiffAboveNegSum)
      have squareBelowProduct :
          LessEqualAs
            (mulExact (negExact differenceApprox) (negExact differenceApprox))
            (mulExact (negExact differenceApprox) sumApprox) :=
        mulExactMonotoneOfNonNegative
          (lessEqualAsRefl (negExact differenceApprox)) isNegDiffBelowSum
          isNegDiffNonNegative isNegDiffNonNegative
      have productBelowBound :
          LessEqualAs (mulExact (negExact differenceApprox) sumApprox) boundValue :=
        lessEqualAsCongrLeft
          (denotesSameAsSymm
            (mulExactNegLeftDenotesSame differenceApprox sumApprox))
          (lessEqualAsCongrRight (negExactNegExactDenotesSame boundValue)
            (lessEqualAsNegBoth isProductAboveNegBound))
      have squareBelowEpsilonSquare :
          LessEqualAs
            (mulExact (negExact differenceApprox) (negExact differenceApprox))
            (mulExact epsilon epsilon) :=
        lessEqualAsTrans squareBelowProduct
          (lessEqualAsTrans productBelowBound isBoundBelowEpsilonSquare)
      have isNegDiffBelowEpsilon :
          LessEqualAs (negExact differenceApprox) epsilon :=
        lessEqualAsOfMulExactSquareLeNonNeg isEpsilonNonNegative
          squareBelowEpsilonSquare
      lessEqualAsCongrRight (negExactNegExactDenotesSame differenceApprox)
        (lessEqualAsNegBoth isNegDiffBelowEpsilon)

end RationalPair

open RationalPair

/-! ## The reflection crux -/

/-- Square-root order reflection: `s ≥ 0` and `x² ≤ s²` give `x ≤ s`, with `x` of
arbitrary sign.  With `d = s − x`, `t = s + x`, difference-of-squares turns the
squared hypothesis into a vanishing lower bound on `d · t`; `d + t = 2s ≥ 0` gives
`d ≥ −t` pointwise; and the rational reflection step (`orderReflectStep`) plus
regularity bridging under slack closure lands the vanishing lower bound on
`d = s − x` itself, i.e. `x ≤ s`.  The analytic crux of the ℂ triangle inequality;
strictly more general than `nonNegSquareOrderReflect`. -/
theorem realLeOfSquareLeNonNeg {baseValue radicandRoot : RegularReal}
    (isRootNonNegative : IsNonNegativeReal radicandRoot)
    (areSquaresOrdered :
      LessEqualReal (mulReal baseValue baseValue) (mulReal radicandRoot radicandRoot)) :
    LessEqualReal baseValue radicandRoot :=
  let differenceReal := subReal radicandRoot baseValue
  let sumReal := addReal radicandRoot baseValue
  have productHasVanishingLowerBound :
      ∀ index : Nat, LessEqualAs (negExact (reciprocalOfSucc index))
        ((mulReal differenceReal sumReal).approximation index) :=
    realNonNegativeRespectsDenotesSame
      (denotesSameRealSymm (mulRealDiffSquaresDenotesSame radicandRoot baseValue))
      areSquaresOrdered
  fun comparisonIndex =>
    lessEqualAsOfForallSlack (slackNumerator := 2) (fun slackIndex =>
      let radicandDenominator := 2 * ((slackIndex + 1) * (slackIndex + 1))
      let productSamplingDepth :=
        productSamplingIndex differenceReal sumReal radicandDenominator
      let differenceAtDepth := differenceReal.approximation productSamplingDepth
      let sumAtDepth := sumReal.approximation productSamplingDepth
      let deepBaseValue := radicandRoot.approximation (2 * productSamplingDepth + 1)
      let deepOtherValue := baseValue.approximation (2 * productSamplingDepth + 1)
      have isDeepBaseNonNegative : IsNonNegative deepBaseValue :=
        isRootNonNegative (2 * productSamplingDepth + 1)
      have differenceSumDenotesDoubleBase :
          DenotesSameAs (addExact differenceAtDepth sumAtDepth)
            (addExact deepBaseValue deepBaseValue) :=
        denotesSameAsTrans
          (addExactMedialDenotesSame deepBaseValue (negExact deepOtherValue)
            deepBaseValue deepOtherValue)
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs
              (denotesSameAsRefl (addExact deepBaseValue deepBaseValue))
              (addExactNegLeftDenotesSame deepOtherValue))
            (addExactZeroRight (addExact deepBaseValue deepBaseValue)))
      have isDifferenceAboveNegSum :
          LessEqualAs (negExact sumAtDepth) differenceAtDepth :=
        lessEqualAsNegRightOfAddNonNeg
          (lessEqualAsCongrRight (denotesSameAsSymm differenceSumDenotesDoubleBase)
            (addExactIsNonNegative isDeepBaseNonNegative isDeepBaseNonNegative))
      have isProductAboveNegBound :
          LessEqualAs (negExact (reciprocalOfSucc radicandDenominator))
            (mulExact differenceAtDepth sumAtDepth) :=
        productHasVanishingLowerBound radicandDenominator
      have isBoundBelowEpsilonSquare :
          LessEqualAs (reciprocalOfSucc radicandDenominator)
            (mulExact (reciprocalOfSucc slackIndex) (reciprocalOfSucc slackIndex)) :=
        lessEqualAsTrans
          (ratioOfNatSuccMonotoneNumerator (Nat.le_succ 1) radicandDenominator)
          (ratioTwoLeReciprocalSquare slackIndex)
      have differenceAboveNegEpsilon :
          LessEqualAs (negExact (reciprocalOfSucc slackIndex)) differenceAtDepth :=
        orderReflectStep isDifferenceAboveNegSum isProductAboveNegBound
          (ratioOfNatSuccIsNonNegative 1 slackIndex) isBoundBelowEpsilonSquare
      have isSlackBelowDepth : slackIndex ≤ productSamplingDepth :=
        natLeTrans (natSlackLeRadicand slackIndex)
          (natSelfLeBoundScaledIndex
            (sharedBoundNumeratorPredecessor differenceReal sumReal)
            radicandDenominator)
      have regularityShunt :
          LessEqualAs differenceAtDepth
            (addExact (differenceReal.approximation comparisonIndex)
              (addExact (reciprocalOfSucc productSamplingDepth)
                (reciprocalOfSucc comparisonIndex))) :=
        lessEqualAsAddOfSubLessEqual
          (differenceReal.isRegular productSamplingDepth comparisonIndex).left
      have chainRelaxed :
          LessEqualAs (negExact (reciprocalOfSucc slackIndex))
            (addExact (differenceReal.approximation comparisonIndex)
              (addExact (reciprocalOfSucc slackIndex)
                (reciprocalOfSucc comparisonIndex))) :=
        lessEqualAsTrans (lessEqualAsTrans differenceAboveNegEpsilon regularityShunt)
          (addExactMonotoneRight (differenceReal.approximation comparisonIndex)
            (addExactMonotoneLeft (reciprocalOfSucc comparisonIndex)
              (ratioOfNatSuccAntitoneDenominator 1 isSlackBelowDepth)))
      lessEqualAsNegRightOfAddNonNeg
        (lessEqualAsCongrRight
          (reflectBridgeIdentity (differenceReal.approximation comparisonIndex)
            slackIndex comparisonIndex)
          (addNonNegOfLessEqualAsNegRight chainRelaxed)))

/-- Order reflection for nonnegative squares: `u, v ≥ 0` and `u² ≤ v²` give
`u ≤ v`.  The both-endpoints-nonnegative special case of `realLeOfSquareLeNonNeg`
(the left nonnegativity is not needed). -/
theorem nonNegSquareOrderReflect {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue)
    (areSquaresOrdered :
      LessEqualReal (mulReal leftValue leftValue) (mulReal rightValue rightValue)) :
    LessEqualReal leftValue rightValue :=
  realLeOfSquareLeNonNeg isRightNonNegative areSquaresOrdered

/-! ## Square-root monotonicity and the real-abs bound -/

/-- The square root is monotone: `a ≤ b → √a ≤ √b` for nonnegative `a, b`.  Both
roots are nonnegative and square (up to the setoid) to `a` and `b`, so the squared
order `(√a)² ≤ (√b)²` is `a ≤ b` transported, and reflection concludes. -/
theorem sqrtRealMonotone {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue)
    (isBelow : LessEqualReal leftValue rightValue) :
    LessEqualReal (sqrtReal leftValue isLeftNonNegative)
      (sqrtReal rightValue isRightNonNegative) :=
  realLeOfSquareLeNonNeg
    (sqrtRealIsNonNegativeReal rightValue isRightNonNegative)
    (lessEqualRealCongr
      (denotesSameRealSymm (sqrtRealSquareDenotesSame isLeftNonNegative))
      (denotesSameRealSymm (sqrtRealSquareDenotesSame isRightNonNegative))
      isBelow)

/-- `x ≤ √R` from `x² ≤ R` and `R ≥ 0`: rewrite the radicand's root-square to `R`
and reflect. -/
theorem leSqrtOfSquareLe {baseValue radicand : RegularReal}
    (isRadicandNonNegative : IsNonNegativeReal radicand)
    (isSquareBelow : LessEqualReal (mulReal baseValue baseValue) radicand) :
    LessEqualReal baseValue (sqrtReal radicand isRadicandNonNegative) :=
  realLeOfSquareLeNonNeg
    (sqrtRealIsNonNegativeReal radicand isRadicandNonNegative)
    (lessEqualRealCongr
      (denotesSameRealRefl (mulReal baseValue baseValue))
      (denotesSameRealSymm (sqrtRealSquareDenotesSame isRadicandNonNegative))
      isSquareBelow)

/-- The real absolute-value fact `x ≤ √(x²)`: the `R = x²` instance of
`leSqrtOfSquareLe`, `x² ≤ x²` reflexively. -/
theorem selfLeSqrtRealSquare (value : RegularReal) :
    LessEqualReal value
      (sqrtReal (mulReal value value) (mulRealSelfIsNonNegativeReal value)) :=
  leSqrtOfSquareLe (mulRealSelfIsNonNegativeReal value)
    (lessEqualRealRefl (mulReal value value))

/-! ## Real ring lemmas for Cauchy–Schwarz -/

/-- A square is sign-blind on reals: `(-x)² ~ x²` — two negation passes and one
double-negation collapse (the ℝ analogue of `mulExactNegNegDenotesSame`). -/
theorem mulRealNegNegDenotesSame (value : RegularReal) :
    DenotesSameReal (mulReal (negReal value) (negReal value)) (mulReal value value) :=
  denotesSameRealTrans (mulRealNegLeftDenotesSame value (negReal value))
    (denotesSameRealTrans
      (negRealRespectsDenotesSame (mulRealNegRightDenotesSame value value))
      (negRealNegRealDenotesSame (mulReal value value)))

/-- The added value is recovered from the sum: `(x + y) - x ~ y` — commute the
sum, associate, cancel `x + (-x)`, and drop the zero. -/
theorem subRealAddLeftCancelDenotesSame (leftValue rightValue : RegularReal) :
    DenotesSameReal (subReal (addReal leftValue rightValue) leftValue) rightValue :=
  denotesSameRealTrans
    (addRealRespectsDenotesSame (addRealComm leftValue rightValue)
      (denotesSameRealRefl (negReal leftValue)))
    (denotesSameRealTrans
      (addRealAssoc rightValue leftValue (negReal leftValue))
      (denotesSameRealTrans
        (addRealRespectsDenotesSame (denotesSameRealRefl rightValue)
          (addRealNegRight leftValue))
        (addRealZeroRight rightValue)))

/-- A pointwise-nonnegative real has the vanishing lower bound at every index —
the vanishing bound sits below zero, and zero sits below the approximant. -/
theorem realVanishingLowerBoundOfNonNeg {value : RegularReal}
    (isNonNegativeReal : IsNonNegativeReal value) :
    ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index)) (value.approximation index) :=
  fun index =>
    lessEqualAsTrans
      (negExactNonPositiveOfNonNegative (ratioOfNatSuccIsNonNegative 1 index))
      (isNonNegativeReal index)

/-! ## Cauchy–Schwarz -/

/-- The Cauchy–Schwarz inequality `a·c + b·d ≤ |⟨a,b⟩| · |⟨c,d⟩|`.  The squared
form `(ac + bd)² ≤ (a²+b²)(c²+d²)` is the polynomial identity
`(a²+b²)(c²+d²) − (ac+bd)² = (ad − bc)²`, routed through the ℂ modulus rather than
expanded by hand: `|⟨a,b⟩ · conj⟨c,d⟩|² = (a²+b²)(c²+d²)` by squared-modulus
multiplicativity, and its Gauss real/imaginary parts are `ac+bd` and `−(ad−bc)`, so
the sum-of-squares gives `(a²+b²)(c²+d²) ~ (ac+bd)² + (ad−bc)²`.  Then
`ac+bd ≤ √((a²+b²)(c²+d²)) ~ |⟨a,b⟩| · |⟨c,d⟩|` by `leSqrtOfSquareLe` and the
multiplicative square root. -/
theorem cauchySchwarzReal (realA imaginaryB realC imaginaryD : RegularReal) :
    LessEqualReal (addReal (mulReal realA realC) (mulReal imaginaryB imaginaryD))
      (mulReal (modulus { realPart := realA, imaginaryPart := imaginaryB })
        (modulus { realPart := realC, imaginaryPart := imaginaryD })) :=
  let leftComplex : ComplexReal := { realPart := realA, imaginaryPart := imaginaryB }
  let rightComplex : ComplexReal := { realPart := realC, imaginaryPart := imaginaryD }
  let innerProduct := addReal (mulReal realA realC) (mulReal imaginaryB imaginaryD)
  let crossDifference := subReal (mulReal realA imaginaryD) (mulReal imaginaryB realC)
  let radicandProduct :=
    mulReal (modulusSquared leftComplex) (modulusSquared rightComplex)
  let conjugateRight := conjComplex rightComplex
  let productComplex := mulComplex leftComplex conjugateRight
  have isRadicandNonNegative : IsNonNegativeReal radicandProduct :=
    mulRealPreservesIsNonNegativeReal
      (modulusSquaredIsNonNegativeReal leftComplex)
      (modulusSquaredIsNonNegativeReal rightComplex)
  have realPartDenotesInner :
      DenotesSameReal productComplex.realPart innerProduct :=
    denotesSameRealTrans
      (subRealRespectsDenotesSame (denotesSameRealRefl (mulReal realA realC))
        (mulRealNegRightDenotesSame imaginaryB imaginaryD))
      (addRealRespectsDenotesSame (denotesSameRealRefl (mulReal realA realC))
        (negRealNegRealDenotesSame (mulReal imaginaryB imaginaryD)))
  have negCrossDenotesShifted :
      DenotesSameReal (negReal crossDifference)
        (addReal (negReal (mulReal realA imaginaryD)) (mulReal imaginaryB realC)) :=
    denotesSameRealTrans
      (negRealAddRealDenotesSame (mulReal realA imaginaryD)
        (negReal (mulReal imaginaryB realC)))
      (addRealRespectsDenotesSame
        (denotesSameRealRefl (negReal (mulReal realA imaginaryD)))
        (negRealNegRealDenotesSame (mulReal imaginaryB realC)))
  have imagPartDenotesNegCross :
      DenotesSameReal productComplex.imaginaryPart (negReal crossDifference) :=
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealNegRightDenotesSame realA imaginaryD)
        (denotesSameRealRefl (mulReal imaginaryB realC)))
      (denotesSameRealSymm negCrossDenotesShifted)
  have modulusSquaredConjRight :
      DenotesSameReal (modulusSquared conjugateRight) (modulusSquared rightComplex) :=
    addRealRespectsDenotesSame (denotesSameRealRefl (mulReal realC realC))
      (mulRealNegNegDenotesSame imaginaryD)
  have modulusSquaredProductDenotesRadicand :
      DenotesSameReal (modulusSquared productComplex) radicandProduct :=
    denotesSameRealTrans
      (modulusSquaredMulDenotesSame leftComplex conjugateRight)
      (mulRealRespectsDenotesSame
        (denotesSameRealRefl (modulusSquared leftComplex)) modulusSquaredConjRight)
  have modulusSquaredProductDenotesSumOfSquares :
      DenotesSameReal (modulusSquared productComplex)
        (addReal (mulReal innerProduct innerProduct)
          (mulReal crossDifference crossDifference)) :=
    addRealRespectsDenotesSame
      (mulRealRespectsDenotesSame realPartDenotesInner realPartDenotesInner)
      (denotesSameRealTrans
        (mulRealRespectsDenotesSame imagPartDenotesNegCross imagPartDenotesNegCross)
        (mulRealNegNegDenotesSame crossDifference))
  have polynomialIdentity :
      DenotesSameReal (subReal radicandProduct (mulReal innerProduct innerProduct))
        (mulReal crossDifference crossDifference) :=
    denotesSameRealTrans
      (subRealRespectsDenotesSame
        (denotesSameRealTrans
          (denotesSameRealSymm modulusSquaredProductDenotesRadicand)
          modulusSquaredProductDenotesSumOfSquares)
        (denotesSameRealRefl (mulReal innerProduct innerProduct)))
      (subRealAddLeftCancelDenotesSame (mulReal innerProduct innerProduct)
        (mulReal crossDifference crossDifference))
  have isSquareBelow :
      LessEqualReal (mulReal innerProduct innerProduct) radicandProduct :=
    realNonNegativeRespectsDenotesSame (denotesSameRealSymm polynomialIdentity)
      (realVanishingLowerBoundOfNonNeg
        (mulRealSelfIsNonNegativeReal crossDifference))
  have rootSplits :
      DenotesSameReal (sqrtReal radicandProduct isRadicandNonNegative)
        (mulReal (modulus leftComplex) (modulus rightComplex)) :=
    sqrtRealMulDenotesSame
      (modulusSquaredIsNonNegativeReal leftComplex)
      (modulusSquaredIsNonNegativeReal rightComplex)
      isRadicandNonNegative
  lessEqualRealCongr (denotesSameRealRefl innerProduct) rootSplits
    (leSqrtOfSquareLe isRadicandNonNegative isSquareBelow)

/-! ## Real lemmas for the triangle inequality -/

/-- The binomial square `(p + q)² ~ (p² + q²) + (pq + pq)`: right-distribute,
left-distribute each leg, and gather the two square terms and the two cross terms
by commutativity and the medial regrouping. -/
theorem squareSumExpand (leftValue rightValue : RegularReal) :
    DenotesSameReal
      (mulReal (addReal leftValue rightValue) (addReal leftValue rightValue))
      (addReal (addReal (mulReal leftValue leftValue) (mulReal rightValue rightValue))
        (addReal (mulReal leftValue rightValue) (mulReal leftValue rightValue))) :=
  denotesSameRealTrans
    (mulRealRightDistrib leftValue rightValue (addReal leftValue rightValue))
    (denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealLeftDistrib leftValue leftValue rightValue)
        (mulRealLeftDistrib rightValue leftValue rightValue))
      (denotesSameRealTrans
        (addRealRespectsDenotesSame
          (denotesSameRealRefl
            (addReal (mulReal leftValue leftValue) (mulReal leftValue rightValue)))
          (addRealComm (mulReal rightValue leftValue) (mulReal rightValue rightValue)))
        (denotesSameRealTrans
          (addRealMedial (mulReal leftValue leftValue) (mulReal leftValue rightValue)
            (mulReal rightValue rightValue) (mulReal rightValue leftValue))
          (addRealRespectsDenotesSame
            (denotesSameRealRefl
              (addReal (mulReal leftValue leftValue) (mulReal rightValue rightValue)))
            (addRealRespectsDenotesSame
              (denotesSameRealRefl (mulReal leftValue rightValue))
              (mulRealComm rightValue leftValue))))))

/-- The vanishing lower bound is additive: if both `X` and `Y` clear
`−1/(index+1)` at every index, so does `X + Y` — sample both at the doubled
index, add, and recombine the doubled halved bound to `−1/(index+1)`. -/
theorem realVanishingLowerBoundAdd {leftValue rightValue : RegularReal}
    (isLeftBelow : ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index)) (leftValue.approximation index))
    (isRightBelow : ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index)) (rightValue.approximation index)) :
    ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index))
        ((addReal leftValue rightValue).approximation index) :=
  fun index =>
    lessEqualAsCongrLeft
      (denotesSameAsTrans
        (denotesSameAsSymm
          (negExactAddExactDenotesSame (reciprocalOfSucc (2 * index + 1))
            (reciprocalOfSucc (2 * index + 1))))
        (negExactRespectsDenotesSameAs (reciprocalDoubleSumDenotesSame index)))
      (addExactMonotone (isLeftBelow (2 * index + 1)) (isRightBelow (2 * index + 1)))

/-- The real subtraction chain `(first − middle) + (middle − last) ~
first − last`: the middle term cancels through associativity and the additive
inverse. -/
theorem subRealChainDenotesSame (firstValue middleValue lastValue : RegularReal) :
    DenotesSameReal
      (addReal (subReal firstValue middleValue) (subReal middleValue lastValue))
      (subReal firstValue lastValue) :=
  denotesSameRealTrans
    (addRealAssoc firstValue (negReal middleValue)
      (addReal middleValue (negReal lastValue)))
    (addRealRespectsDenotesSame (denotesSameRealRefl firstValue)
      (denotesSameRealTrans
        (denotesSameRealSymm
          (addRealAssoc (negReal middleValue) middleValue (negReal lastValue)))
        (denotesSameRealTrans
          (addRealRespectsDenotesSame (negRealAddSelfDenotesZero middleValue)
            (denotesSameRealRefl (negReal lastValue)))
          (addRealZeroLeft (negReal lastValue)))))

/-- Transitivity of the non-strict real order: chain the two vanishing lower
bounds `c − a ~ (c − b) + (b − a)`, and the vanishing bound is additive. -/
theorem lessEqualRealTrans {firstValue middleValue lastValue : RegularReal}
    (isFirstBelow : LessEqualReal firstValue middleValue)
    (isMiddleBelow : LessEqualReal middleValue lastValue) :
    LessEqualReal firstValue lastValue :=
  realNonNegativeRespectsDenotesSame
    (subRealChainDenotesSame lastValue middleValue firstValue)
    (realVanishingLowerBoundAdd isMiddleBelow isFirstBelow)

/-- Additive compatibility with the shared summand on the left: commute onto the
right-shared `lessEqualRealAddCompat`. -/
theorem lessEqualRealAddCompatLeft (sharedValue : RegularReal)
    {leftValue rightValue : RegularReal} (isBelow : LessEqualReal leftValue rightValue) :
    LessEqualReal (addReal sharedValue leftValue) (addReal sharedValue rightValue) :=
  lessEqualRealCongr (addRealComm leftValue sharedValue)
    (addRealComm rightValue sharedValue)
    (lessEqualRealAddCompat isBelow sharedValue)

/-! ## The triangle inequality -/

/-- The triangle inequality `|z + w| ≤ |z| + |w|` on the Gaussian-real setoid.
Both `|z + w|` and `|z| + |w|` are nonnegative, so it suffices to compare squares
(`nonNegSquareOrderReflect`).  Binomial expansion gives
`|z + w|² ~ (|z|² + |w|²) + 2(ac + bd)` and `(|z| + |w|)² ~ (|z|² + |w|²) +
2·|z||w|`, and Cauchy–Schwarz `ac + bd ≤ |z||w|` lifts the shared `(|z|² + |w|²)`
prefix through `lessEqualRealAddCompatLeft` to `|z + w|² ≤ (|z| + |w|)²`.  This is
the key analysis theorem toward the Fundamental Theorem of Algebra. -/
theorem modulusTriangleInequality (leftComplex rightComplex : ComplexReal) :
    LessEqualReal (modulus (addComplex leftComplex rightComplex))
      (addReal (modulus leftComplex) (modulus rightComplex)) :=
  let sumComplex := addComplex leftComplex rightComplex
  let leftModulus := modulus leftComplex
  let rightModulus := modulus rightComplex
  let modulusSum := addReal leftModulus rightModulus
  let modulusProduct := mulReal leftModulus rightModulus
  let innerProduct :=
    addReal (mulReal leftComplex.realPart rightComplex.realPart)
      (mulReal leftComplex.imaginaryPart rightComplex.imaginaryPart)
  have modulusSquaredSumExpand :
      DenotesSameReal (modulusSquared sumComplex)
        (addReal (addReal (modulusSquared leftComplex) (modulusSquared rightComplex))
          (addReal innerProduct innerProduct)) :=
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (squareSumExpand leftComplex.realPart rightComplex.realPart)
        (squareSumExpand leftComplex.imaginaryPart rightComplex.imaginaryPart))
      (denotesSameRealTrans
        (addRealMedial
          (addReal (mulReal leftComplex.realPart leftComplex.realPart)
            (mulReal rightComplex.realPart rightComplex.realPart))
          (addReal (mulReal leftComplex.realPart rightComplex.realPart)
            (mulReal leftComplex.realPart rightComplex.realPart))
          (addReal (mulReal leftComplex.imaginaryPart leftComplex.imaginaryPart)
            (mulReal rightComplex.imaginaryPart rightComplex.imaginaryPart))
          (addReal (mulReal leftComplex.imaginaryPart rightComplex.imaginaryPart)
            (mulReal leftComplex.imaginaryPart rightComplex.imaginaryPart)))
        (addRealRespectsDenotesSame
          (addRealMedial
            (mulReal leftComplex.realPart leftComplex.realPart)
            (mulReal rightComplex.realPart rightComplex.realPart)
            (mulReal leftComplex.imaginaryPart leftComplex.imaginaryPart)
            (mulReal rightComplex.imaginaryPart rightComplex.imaginaryPart))
          (addRealMedial
            (mulReal leftComplex.realPart rightComplex.realPart)
            (mulReal leftComplex.realPart rightComplex.realPart)
            (mulReal leftComplex.imaginaryPart rightComplex.imaginaryPart)
            (mulReal leftComplex.imaginaryPart rightComplex.imaginaryPart))))
  have modulusSumSquaredExpand :
      DenotesSameReal (mulReal modulusSum modulusSum)
        (addReal (addReal (modulusSquared leftComplex) (modulusSquared rightComplex))
          (addReal modulusProduct modulusProduct)) :=
    denotesSameRealTrans (squareSumExpand leftModulus rightModulus)
      (addRealRespectsDenotesSame
        (addRealRespectsDenotesSame
          (modulusSquareDenotesModulusSquared leftComplex)
          (modulusSquareDenotesModulusSquared rightComplex))
        (denotesSameRealRefl (addReal modulusProduct modulusProduct)))
  have isInnerBelowModulusProduct :
      LessEqualReal innerProduct modulusProduct :=
    cauchySchwarzReal leftComplex.realPart leftComplex.imaginaryPart
      rightComplex.realPart rightComplex.imaginaryPart
  have isDoubledInnerBelow :
      LessEqualReal (addReal innerProduct innerProduct)
        (addReal modulusProduct modulusProduct) :=
    lessEqualRealTrans
      (lessEqualRealAddCompat isInnerBelowModulusProduct innerProduct)
      (lessEqualRealAddCompatLeft modulusProduct isInnerBelowModulusProduct)
  have isModulusSquaredSumBelow :
      LessEqualReal (modulusSquared sumComplex) (mulReal modulusSum modulusSum) :=
    lessEqualRealCongr (denotesSameRealSymm modulusSquaredSumExpand)
      (denotesSameRealSymm modulusSumSquaredExpand)
      (lessEqualRealAddCompatLeft
        (addReal (modulusSquared leftComplex) (modulusSquared rightComplex))
        isDoubledInnerBelow)
  have isSumModulusSquareBelow :
      LessEqualReal (mulReal (modulus sumComplex) (modulus sumComplex))
        (mulReal modulusSum modulusSum) :=
    lessEqualRealCongr
      (denotesSameRealSymm (modulusSquareDenotesModulusSquared sumComplex))
      (denotesSameRealRefl (mulReal modulusSum modulusSum))
      isModulusSquaredSumBelow
  nonNegSquareOrderReflect
    (sqrtRealIsNonNegativeReal (modulusSquared sumComplex)
      (modulusSquaredIsNonNegativeReal sumComplex))
    (addRealPreservesIsNonNegativeReal
      (sqrtRealIsNonNegativeReal (modulusSquared leftComplex)
        (modulusSquaredIsNonNegativeReal leftComplex))
      (sqrtRealIsNonNegativeReal (modulusSquared rightComplex)
        (modulusSquaredIsNonNegativeReal rightComplex)))
    isSumModulusSquareBelow

/-- Marker: the ℂ modulus satisfies the triangle inequality on the Gaussian-real
setoid. -/
def fxComplexReal_hasModulusTriangleInequality : Bool := true

end FX1Poly.ComputerAlgebra
