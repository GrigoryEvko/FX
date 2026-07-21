import FX1Poly.ComputerAlgebra.Number.ComplexRealModulus

/-! # FX1Poly/ComputerAlgebra/Number/RegularRealSquareRootMultiplicative — √ is
    multiplicative on nonnegative Bishop reals

`sqrt(a * b) ~ sqrt a * sqrt b` for `a, b >= 0` on the zero-axiom regular-real
setoid.  This is the ℝ-layer lemma underlying ℂ modulus multiplicativity
`|z * w| = |z| * |w|`, itself `sqrt` of a product of squared moduli.

Everything reduces to ONE analytic crux — **equal nonnegative squares have equal
bases** (`nonNegSquareCancel`).  Given the crux, sqrt-multiplicativity is a short
corollary: both `sqrt(a*b)` and `sqrt a * sqrt b` are nonnegative and square to
`a * b` (the square law twice, re-associated by the multiplicative
medial), so the crux identifies them.

The crux itself has two genuinely new pieces:

* **The rational quadratic estimate** (`squareZeroImpliesZero`): if `d * d ~ 0`
  then `d ~ 0`.  This is nonneg-free and is the hardest step.  Per comparison
  index, sample the square at the quadratically deeper index `2 * (m+1)^2`, where
  the square-zero hypothesis pins `(d.approx)^2 <= (1/(m+1))^2`; the rational
  square reflection (`lessEqualAsOfMulExactSquareLeNonNeg`) takes the
  square root of that bound to `|d.approx| <= 1/(m+1)`, and regularity bridges the
  deep sample back to the comparison index — landing exactly on the setoid
  modulus with vanishing slack.

* **The difference-of-squares reduction** to `squareZeroImpliesZero`.  With
  `d = a - b`, `t = a + b`, difference-of-squares gives `d * t ~ a^2 - b^2 ~ 0`.
  For nonnegative `a, b` the standard `|d| <= t` estimate is encoded WITHOUT any
  real absolute value or the (absent) order-tightness: `d^4 ~ -(4ab) * d^2`, and
  `d^4` is pointwise nonnegative while `-(4ab) * d^2` is pointwise nonpositive, so
  a nonnegative real setoid-equal to a nonpositive one is zero
  (`nonNegNonPosSetoidImpliesZero`).  Then `squareZeroImpliesZero` twice sends
  `d^4 -> d^2 -> d`.

The two identities `d^2 ~ 2a * d` and `d^2 ~ -(2b) * d` (used to multiply out
`d^4`) rest on the difference-of-squares fact `d * t ~ 0` and the ℝ ring
laws — no new analysis.

Zero-axiom: the slack-closure dispatch (`isWithinBoundOfForallSlack`) matches on
the `Decidable` DATA, never `decide`-on-a-Prop.  Per-declaration gated in the
audit twin. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Rational lemmas -/

/-- **The reflection target**: `2/(2(p+1)^2 + 1)` sits below the square of the
grid step `1/(p+1)` — cross-multiplication collapses to `2(p+1)^2 <= 1 * (2(p+1)^2 + 1)`,
one `Nat.le_succ`.  The rational fact the quadratic estimate reflects through. -/
theorem ratioTwoLeReciprocalSquare (predecessor : Nat) :
    LessEqualAs (ratioOfNatSucc 2 (2 * ((predecessor + 1) * (predecessor + 1))))
      (mulExact (reciprocalOfSucc predecessor) (reciprocalOfSucc predecessor)) :=
  intOfNatLeOfNat
    (Nat.le_trans (Nat.le_succ (2 * ((predecessor + 1) * (predecessor + 1))))
      (Nat.le_of_eq (Nat.one_mul (2 * ((predecessor + 1) * (predecessor + 1)) + 1)).symm))

/-- Subtracting the rational zero denotes the value — the negated zero collapses,
the zero addend drops. -/
theorem subExactZeroRightDenotesSame (value : RationalPair) :
    DenotesSameAs (subExact value zeroRational) value :=
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs (denotesSameAsRefl value)
      (show DenotesSameAs (negExact zeroRational) zeroRational from
        congrArg (· * denominatorInt zeroRational) intNegZero))
    (addExactZeroRight value)

/-- Subtracting FROM the rational zero denotes the negation. -/
theorem subExactZeroLeftDenotesSame (value : RationalPair) :
    DenotesSameAs (subExact zeroRational value) (negExact value) :=
  addExactZeroLeft (negExact value)

/-- Subtracting a negation is adding — the double negation on the subtrahend
collapses. -/
theorem subExactNegRightDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs (subExact leftValue (negExact rightValue))
      (addExact leftValue rightValue) :=
  addExactRespectsDenotesSameAs (denotesSameAsRefl leftValue)
    (negExactNegExactDenotesSame rightValue)

/-- A square is sign-blind: `(-v)^2` denotes `v^2` — two negation passes and one
double-negation collapse. -/
theorem mulExactNegNegDenotesSame (value : RationalPair) :
    DenotesSameAs (mulExact (negExact value) (negExact value)) (mulExact value value) :=
  denotesSameAsTrans (mulExactNegLeftDenotesSame value (negExact value))
    (denotesSameAsTrans
      (negExactRespectsDenotesSameAs (mulExactNegRightDenotesSame value value))
      (negExactNegExactDenotesSame (mulExact value value)))

/-- The comparison index sits below the quadratic radicand denominator
`2(p+1)^2` — `p <= p+1 <= (p+1)^2 <= 2(p+1)^2`, each step a clean additive
witness. -/
theorem natSlackLeRadicand (predecessor : Nat) :
    predecessor ≤ 2 * ((predecessor + 1) * (predecessor + 1)) :=
  have stepFactor : predecessor + 1 ≤ (predecessor + 1) * (predecessor + 1) :=
    (Nat.mul_succ (predecessor + 1) predecessor).symm ▸
      Nat.le_add_left (predecessor + 1) ((predecessor + 1) * predecessor)
  have twoMulUnfolds :
      2 * ((predecessor + 1) * (predecessor + 1)) =
        (predecessor + 1) * (predecessor + 1) + (predecessor + 1) * (predecessor + 1) :=
    (Nat.succ_mul 1 ((predecessor + 1) * (predecessor + 1))).trans
      (congrArg (· + (predecessor + 1) * (predecessor + 1))
        (Nat.one_mul ((predecessor + 1) * (predecessor + 1))))
  have stepDouble :
      (predecessor + 1) * (predecessor + 1) ≤ 2 * ((predecessor + 1) * (predecessor + 1)) :=
    twoMulUnfolds.symm ▸
      Nat.le_add_left ((predecessor + 1) * (predecessor + 1))
        ((predecessor + 1) * (predecessor + 1))
  natLeTrans (Nat.le_succ predecessor) (natLeTrans stepFactor stepDouble)

/-! ## ℝ-level nonnegativity helpers -/

/-- Pointwise nonnegativity is closed under multiplication — each product
approximant is `mulExact` of the two factors' nonnegative deep samples. -/
theorem mulRealPreservesIsNonNegativeReal {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue) :
    IsNonNegativeReal (mulReal leftValue rightValue) :=
  fun index =>
    mulExactIsNonNegative
      (isLeftNonNegative (productSamplingIndex leftValue rightValue index))
      (isRightNonNegative (productSamplingIndex leftValue rightValue index))

/-- The square root is pointwise nonnegative — every approximant is a
`rationalSqrtApprox`, whose numerator is an `ofNat` root. -/
theorem sqrtRealIsNonNegativeReal (value : RegularReal)
    (isNonNegativeReal : IsNonNegativeReal value) :
    IsNonNegativeReal (sqrtReal value isNonNegativeReal) :=
  fun index =>
    rationalSqrtApproxIsNonNegative (value.approximation (sqrtSampleIndex index))
      (sqrtGridIndex index)

/-! ## The rational quadratic estimate: square-zero cancellation -/

/-- **Square-zero cancellation** — `d * d ~ 0` forces `d ~ 0`.  The genuinely
analytic crux, nonneg-free.  Per comparison index `n` and slack index `m`, the
square-zero hypothesis at the quadratic radicand `2(m+1)^2` gives
`(d.approx q)^2 <= 2/(2(m+1)^2 + 1) <= (1/(m+1))^2`; the rational square
reflection takes the square root to `|d.approx q| <= 1/(m+1)`, and regularity
bridges the deep sample `q` back to `n`, landing on `2/(n+1)` with vanishing
`2/(m+1)` slack that slack-closure erases. -/
theorem squareZeroImpliesZero {value : RegularReal}
    (squareIsZero :
      DenotesSameReal (mulReal value value) (constantReal zeroRational)) :
    DenotesSameReal value (constantReal zeroRational) :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (slackNumerator := 2) (fun slackIndex =>
      let radicandDenominator := 2 * ((slackIndex + 1) * (slackIndex + 1))
      let productIndex := productSamplingIndex value value radicandDenominator
      let sampleValue := value.approximation productIndex
      let squareBound : LessEqualAs (mulExact sampleValue sampleValue)
            (ratioOfNatSucc 2 radicandDenominator) :=
        lessEqualAsCongrLeft
          (subExactZeroRightDenotesSame (mulExact sampleValue sampleValue))
          (squareIsZero radicandDenominator).left
      let squareLeReciprocalSquare : LessEqualAs (mulExact sampleValue sampleValue)
            (mulExact (reciprocalOfSucc slackIndex) (reciprocalOfSucc slackIndex)) :=
        lessEqualAsTrans squareBound (ratioTwoLeReciprocalSquare slackIndex)
      let sampleBelowReciprocal :
          LessEqualAs sampleValue (reciprocalOfSucc slackIndex) :=
        lessEqualAsOfMulExactSquareLeNonNeg
          (ratioOfNatSuccIsNonNegative 1 slackIndex) squareLeReciprocalSquare
      let negSampleBelowReciprocal :
          LessEqualAs (negExact sampleValue) (reciprocalOfSucc slackIndex) :=
        lessEqualAsOfMulExactSquareLeNonNeg
          (ratioOfNatSuccIsNonNegative 1 slackIndex)
          (lessEqualAsCongrLeft
            (denotesSameAsSymm (mulExactNegNegDenotesSame sampleValue))
            squareLeReciprocalSquare)
      let sampleWithinZero :
          IsWithinBound sampleValue zeroRational (reciprocalOfSucc slackIndex) :=
        ⟨lessEqualAsCongrLeft
            (denotesSameAsSymm (subExactZeroRightDenotesSame sampleValue))
            sampleBelowReciprocal,
          lessEqualAsCongrLeft
            (denotesSameAsSymm (subExactZeroLeftDenotesSame sampleValue))
            negSampleBelowReciprocal⟩
      let triangled : IsWithinBound (value.approximation sharedIndex) zeroRational
            (addExact
              (addExact (reciprocalOfSucc sharedIndex)
                (reciprocalOfSucc productIndex))
              (reciprocalOfSucc slackIndex)) :=
        isWithinBoundTriangle (value.isRegular sharedIndex productIndex)
          sampleWithinZero
      have slackBelowProduct : slackIndex ≤ productIndex :=
        natLeTrans (natSlackLeRadicand slackIndex)
          (natSelfLeBoundScaledIndex
            (sharedBoundNumeratorPredecessor value value) radicandDenominator)
      have boundRelaxes : LessEqualAs
            (addExact
              (addExact (reciprocalOfSucc sharedIndex)
                (reciprocalOfSucc productIndex))
              (reciprocalOfSucc slackIndex))
            (addExact (ratioOfNatSucc 2 sharedIndex)
              (ratioOfNatSucc 2 slackIndex)) :=
        lessEqualAsCongrLeft
          (denotesSameAsSymm
            (addExactAssoc (reciprocalOfSucc sharedIndex)
              (reciprocalOfSucc productIndex) (reciprocalOfSucc slackIndex)))
          (addExactMonotone
            (ratioOfNatSuccMonotoneNumerator (Nat.le_succ 1) sharedIndex)
            (lessEqualAsCongrRight (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
              (addExactMonotoneLeft (reciprocalOfSucc slackIndex)
                (ratioOfNatSuccAntitoneDenominator 1 slackBelowProduct))))
      isWithinBoundOfBoundLessEqual boundRelaxes triangled)

/-! ## A nonnegative real setoid-equal to a nonpositive one is zero -/

/-- **Sign clamp** — a pointwise-nonnegative real setoid-equal to a
pointwise-nonpositive one (`x ~ -z`, both `x` and `z` nonnegative) is zero.  Per
index the distance conjunct forces `x.approx <= x.approx + z.approx <= 2/(n+1)`,
and nonnegativity of `x.approx` handles the lower side.  The abs-free encoding of
`|d| <= t` used by the difference-of-squares reduction. -/
theorem nonNegNonPosSetoidImpliesZero {leftValue negatedRightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal negatedRightValue)
    (areNegated : DenotesSameReal leftValue (negReal negatedRightValue)) :
    DenotesSameReal leftValue (constantReal zeroRational) :=
  fun sharedIndex =>
    let leftSample := leftValue.approximation sharedIndex
    let rightSample := negatedRightValue.approximation sharedIndex
    have sumBound :
        LessEqualAs (addExact leftSample rightSample)
          (ratioOfNatSucc 2 sharedIndex) :=
      lessEqualAsCongrLeft (subExactNegRightDenotesSame leftSample rightSample)
        (areNegated sharedIndex).left
    have leftBound : LessEqualAs leftSample (ratioOfNatSucc 2 sharedIndex) :=
      lessEqualAsTrans
        (lessEqualAsSelfAddNonNegRight leftSample (isRightNonNegative sharedIndex))
        sumBound
    ⟨lessEqualAsCongrLeft
        (denotesSameAsSymm (subExactZeroRightDenotesSame leftSample)) leftBound,
      lessEqualAsCongrLeft
        (denotesSameAsSymm (subExactZeroLeftDenotesSame leftSample))
        (lessEqualAsTrans
          (negExactNonPositiveOfNonNegative (isLeftNonNegative sharedIndex))
          (ratioOfNatSuccIsNonNegative 2 sharedIndex))⟩

/-! ## Real ring lemmas for the cancellation -/

/-- Self-subtraction denotes zero — `v - v` IS `v + (-v)`. -/
theorem subRealSelfDenotesZero (value : RegularReal) :
    DenotesSameReal (subReal value value) (constantReal zeroRational) :=
  addRealNegRight value

/-- Adding a value onto its negation denotes zero — commute onto the
right-inverse. -/
theorem negRealAddSelfDenotesZero (value : RegularReal) :
    DenotesSameReal (addReal (negReal value) value) (constantReal zeroRational) :=
  denotesSameRealTrans (addRealComm (negReal value) value) (addRealNegRight value)

/-- The negation of the constant zero denotes zero — pointwise self-distance. -/
theorem negRealConstantZeroDenotesZero :
    DenotesSameReal (negReal (constantReal zeroRational)) (constantReal zeroRational) :=
  fun index => isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 index)

/-- A vanishing difference reads back as the setoid equality — recover
`left = (left - right) + right`, replace the difference by zero, absorb. -/
theorem denotesSameRealOfSubRealZero {leftValue rightValue : RegularReal}
    (subtractionIsZero :
      DenotesSameReal (subReal leftValue rightValue) (constantReal zeroRational)) :
    DenotesSameReal leftValue rightValue :=
  denotesSameRealTrans
    (denotesSameRealSymm
      (denotesSameRealTrans
        (addRealAssoc leftValue (negReal rightValue) rightValue)
        (denotesSameRealTrans
          (addRealRespectsDenotesSame (denotesSameRealRefl leftValue)
            (denotesSameRealTrans (addRealComm (negReal rightValue) rightValue)
              (addRealNegRight rightValue)))
          (addRealZeroRight leftValue))))
    (denotesSameRealTrans
      (addRealRespectsDenotesSame subtractionIsZero
        (denotesSameRealRefl rightValue))
      (addRealZeroLeft rightValue))

/-- A vanishing sum reads back as the negation — `left = (left + right) + (-right)`,
replace the sum by zero, absorb. -/
theorem denotesSameRealNegOfAddRealZero {leftValue rightValue : RegularReal}
    (additionIsZero :
      DenotesSameReal (addReal leftValue rightValue) (constantReal zeroRational)) :
    DenotesSameReal leftValue (negReal rightValue) :=
  denotesSameRealTrans
    (denotesSameRealSymm (addRealZeroRight leftValue))
    (denotesSameRealTrans
      (addRealRespectsDenotesSame (denotesSameRealRefl leftValue)
        (denotesSameRealSymm (addRealNegRight rightValue)))
      (denotesSameRealTrans
        (denotesSameRealSymm
          (addRealAssoc leftValue rightValue (negReal rightValue)))
        (denotesSameRealTrans
          (addRealRespectsDenotesSame additionIsZero
            (denotesSameRealRefl (negReal rightValue)))
          (addRealZeroLeft (negReal rightValue)))))

/-- **The multiplicative medial** — swap the two inner factors of a four-term
product: `(a * b) * (c * e) ~ (a * c) * (b * e)`.  Associativity out, commute the
middle pair, associativity back.  Re-associates `(uv)(uv)` to `(uu)(vv)`. -/
theorem mulRealMedial (firstValue secondValue thirdValue fourthValue : RegularReal) :
    DenotesSameReal
      (mulReal (mulReal firstValue secondValue) (mulReal thirdValue fourthValue))
      (mulReal (mulReal firstValue thirdValue) (mulReal secondValue fourthValue)) :=
  denotesSameRealTrans
    (mulRealAssoc firstValue secondValue (mulReal thirdValue fourthValue))
    (denotesSameRealTrans
      (mulRealRespectsDenotesSame (denotesSameRealRefl firstValue)
        (denotesSameRealTrans
          (denotesSameRealSymm
            (mulRealAssoc secondValue thirdValue fourthValue))
          (denotesSameRealTrans
            (mulRealRespectsDenotesSame (mulRealComm secondValue thirdValue)
              (denotesSameRealRefl fourthValue))
            (mulRealAssoc thirdValue secondValue fourthValue))))
      (denotesSameRealSymm
        (mulRealAssoc firstValue thirdValue (mulReal secondValue fourthValue))))

/-- **Difference of squares** — `(a - b)(a + b) ~ a^2 - b^2`.  Distribute the
subtracted factor, distribute each product, commute the subtrahend, cross-pair,
and drop the `a*b - b*a` term that commutes to zero. -/
theorem mulRealDiffSquaresDenotesSame (leftValue rightValue : RegularReal) :
    DenotesSameReal
      (mulReal (subReal leftValue rightValue) (addReal leftValue rightValue))
      (subReal (mulReal leftValue leftValue) (mulReal rightValue rightValue)) :=
  denotesSameRealTrans
    (mulRealSubRealRightDenotesSame leftValue rightValue (addReal leftValue rightValue))
    (denotesSameRealTrans
      (subRealRespectsDenotesSame
        (mulRealLeftDistrib leftValue leftValue rightValue)
        (mulRealLeftDistrib rightValue leftValue rightValue))
      (denotesSameRealTrans
        (subRealRespectsDenotesSame
          (denotesSameRealRefl
            (addReal (mulReal leftValue leftValue) (mulReal leftValue rightValue)))
          (addRealComm (mulReal rightValue leftValue) (mulReal rightValue rightValue)))
        (denotesSameRealTrans
          (subRealCrossPairsDenotesSame (mulReal leftValue leftValue)
            (mulReal leftValue rightValue) (mulReal rightValue rightValue)
            (mulReal rightValue leftValue))
          (denotesSameRealTrans
            (addRealRespectsDenotesSame
              (denotesSameRealRefl
                (subReal (mulReal leftValue leftValue)
                  (mulReal rightValue rightValue)))
              (denotesSameRealTrans
                (subRealRespectsDenotesSame (mulRealComm leftValue rightValue)
                  (denotesSameRealRefl (mulReal rightValue leftValue)))
                (subRealSelfDenotesZero (mulReal rightValue leftValue))))
            (addRealZeroRight
              (subReal (mulReal leftValue leftValue)
                (mulReal rightValue rightValue)))))))

/-! ## The crux: equal nonnegative squares have equal bases -/

/-- **Equal nonnegative squares have equal bases** — `a, b >= 0` and `a^2 ~ b^2`
force `a ~ b`.  With `d = a - b`, `t = a + b`: difference-of-squares plus `a^2 ~ b^2`
gives `d * t ~ 0`, whence the two identities `d^2 ~ 2a * d` and `d^2 ~ -(2b) * d`.
Multiplying them, `d^4 ~ -(2a)(2b) * d^2`, a pointwise-nonnegative real
(`d^4 = (d^2)^2`) setoid-equal to a pointwise-nonpositive one, hence `d^4 ~ 0`;
`squareZeroImpliesZero` twice sends `d^4 -> d^2 -> d`, and a vanishing difference
is the setoid equality. -/
theorem nonNegSquareCancel {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue)
    (squaresAgree :
      DenotesSameReal (mulReal leftValue leftValue) (mulReal rightValue rightValue)) :
    DenotesSameReal leftValue rightValue :=
  let difference := subReal leftValue rightValue
  let productSquare := mulReal difference difference
  have differenceProductIsZero :
      DenotesSameReal
        (mulReal difference (addReal leftValue rightValue))
        (constantReal zeroRational) :=
    denotesSameRealTrans (mulRealDiffSquaresDenotesSame leftValue rightValue)
      (denotesSameRealTrans
        (subRealRespectsDenotesSame squaresAgree
          (denotesSameRealRefl (mulReal rightValue rightValue)))
        (subRealSelfDenotesZero (mulReal rightValue rightValue)))
  have differencePlusDoubleRight :
      DenotesSameReal (addReal difference (addReal rightValue rightValue))
        (addReal leftValue rightValue) :=
    denotesSameRealTrans
      (addRealMedial leftValue (negReal rightValue) rightValue rightValue)
      (denotesSameRealTrans
        (addRealRespectsDenotesSame
          (denotesSameRealRefl (addReal leftValue rightValue))
          (negRealAddSelfDenotesZero rightValue))
        (addRealZeroRight (addReal leftValue rightValue)))
  have differenceMinusDoubleLeft :
      DenotesSameReal (subReal difference (addReal leftValue leftValue))
        (negReal (addReal leftValue rightValue)) :=
    denotesSameRealTrans
      (addRealRespectsDenotesSame (denotesSameRealRefl difference)
        (negRealAddRealDenotesSame leftValue leftValue))
      (denotesSameRealTrans
        (addRealMedial leftValue (negReal rightValue) (negReal leftValue)
          (negReal leftValue))
        (denotesSameRealTrans
          (addRealRespectsDenotesSame (addRealNegRight leftValue)
            (denotesSameRealRefl
              (addReal (negReal rightValue) (negReal leftValue))))
          (denotesSameRealTrans
            (addRealZeroLeft (addReal (negReal rightValue) (negReal leftValue)))
            (denotesSameRealTrans
              (addRealComm (negReal rightValue) (negReal leftValue))
              (denotesSameRealSymm
                (negRealAddRealDenotesSame leftValue rightValue))))))
  have bSumZero :
      DenotesSameReal
        (addReal productSquare (mulReal (addReal rightValue rightValue) difference))
        (constantReal zeroRational) :=
    denotesSameRealTrans
      (denotesSameRealSymm
        (mulRealRightDistrib difference (addReal rightValue rightValue) difference))
      (denotesSameRealTrans
        (mulRealRespectsDenotesSame differencePlusDoubleRight
          (denotesSameRealRefl difference))
        (denotesSameRealTrans
          (mulRealComm (addReal leftValue rightValue) difference)
          differenceProductIsZero))
  have bIdentity :
      DenotesSameReal productSquare
        (negReal (mulReal (addReal rightValue rightValue) difference)) :=
    denotesSameRealNegOfAddRealZero bSumZero
  have aSubZero :
      DenotesSameReal
        (subReal productSquare (mulReal (addReal leftValue leftValue) difference))
        (constantReal zeroRational) :=
    denotesSameRealTrans
      (denotesSameRealSymm
        (mulRealSubRealRightDenotesSame difference (addReal leftValue leftValue)
          difference))
      (denotesSameRealTrans
        (mulRealRespectsDenotesSame differenceMinusDoubleLeft
          (denotesSameRealRefl difference))
        (denotesSameRealTrans
          (mulRealNegLeftDenotesSame (addReal leftValue rightValue) difference)
          (denotesSameRealTrans
            (negRealRespectsDenotesSame
              (mulRealComm (addReal leftValue rightValue) difference))
            (denotesSameRealTrans
              (negRealRespectsDenotesSame differenceProductIsZero)
              negRealConstantZeroDenotesZero))))
  have aIdentity :
      DenotesSameReal productSquare (mulReal (addReal leftValue leftValue) difference) :=
    denotesSameRealOfSubRealZero aSubZero
  have productSquareSquareDenotesNeg :
      DenotesSameReal (mulReal productSquare productSquare)
        (negReal (mulReal
          (mulReal (addReal leftValue leftValue) (addReal rightValue rightValue))
          productSquare)) :=
    denotesSameRealTrans
      (mulRealRespectsDenotesSame aIdentity bIdentity)
      (denotesSameRealTrans
        (mulRealNegRightDenotesSame
          (mulReal (addReal leftValue leftValue) difference)
          (mulReal (addReal rightValue rightValue) difference))
        (negRealRespectsDenotesSame
          (mulRealMedial (addReal leftValue leftValue) difference
            (addReal rightValue rightValue) difference)))
  have productSquareSquareNonNeg :
      IsNonNegativeReal (mulReal productSquare productSquare) :=
    mulRealSelfIsNonNegativeReal productSquare
  have absorberNonNeg :
      IsNonNegativeReal (mulReal
        (mulReal (addReal leftValue leftValue) (addReal rightValue rightValue))
        productSquare) :=
    mulRealPreservesIsNonNegativeReal
      (mulRealPreservesIsNonNegativeReal
        (addRealPreservesIsNonNegativeReal isLeftNonNegative isLeftNonNegative)
        (addRealPreservesIsNonNegativeReal isRightNonNegative isRightNonNegative))
      (mulRealSelfIsNonNegativeReal difference)
  have productSquareSquareZero :
      DenotesSameReal (mulReal productSquare productSquare) (constantReal zeroRational) :=
    nonNegNonPosSetoidImpliesZero productSquareSquareNonNeg absorberNonNeg
      productSquareSquareDenotesNeg
  have productSquareZero : DenotesSameReal productSquare (constantReal zeroRational) :=
    squareZeroImpliesZero productSquareSquareZero
  have differenceZero : DenotesSameReal difference (constantReal zeroRational) :=
    squareZeroImpliesZero productSquareZero
  denotesSameRealOfSubRealZero differenceZero

/-! ## The headline: sqrt multiplicativity -/

/-- **`sqrt` is multiplicative on nonnegative reals** — `sqrt(a * b) ~ sqrt a * sqrt b`.
Both sides are nonnegative and square to `a * b` (the square law twice,
`(uv)^2` re-associated to `u^2 v^2` by the multiplicative medial), so
`nonNegSquareCancel` identifies them.  The base case for ℂ modulus
multiplicativity `|z w| = |z| |w|`. -/
theorem sqrtRealMulDenotesSame {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue)
    (isProductNonNegative : IsNonNegativeReal (mulReal leftValue rightValue)) :
    DenotesSameReal (sqrtReal (mulReal leftValue rightValue) isProductNonNegative)
      (mulReal (sqrtReal leftValue isLeftNonNegative)
        (sqrtReal rightValue isRightNonNegative)) :=
  let rootLeft := sqrtReal leftValue isLeftNonNegative
  let rootRight := sqrtReal rightValue isRightNonNegative
  have productRootSquare :
      DenotesSameReal
        (mulReal (sqrtReal (mulReal leftValue rightValue) isProductNonNegative)
          (sqrtReal (mulReal leftValue rightValue) isProductNonNegative))
        (mulReal leftValue rightValue) :=
    sqrtRealSquareDenotesSame isProductNonNegative
  have rootProductSquare :
      DenotesSameReal (mulReal (mulReal rootLeft rootRight) (mulReal rootLeft rootRight))
        (mulReal leftValue rightValue) :=
    denotesSameRealTrans (mulRealMedial rootLeft rootRight rootLeft rootRight)
      (mulRealRespectsDenotesSame (sqrtRealSquareDenotesSame isLeftNonNegative)
        (sqrtRealSquareDenotesSame isRightNonNegative))
  nonNegSquareCancel
    (sqrtRealIsNonNegativeReal (mulReal leftValue rightValue) isProductNonNegative)
    (mulRealPreservesIsNonNegativeReal
      (sqrtRealIsNonNegativeReal leftValue isLeftNonNegative)
      (sqrtRealIsNonNegativeReal rightValue isRightNonNegative))
    (denotesSameRealTrans productRootSquare (denotesSameRealSymm rootProductSquare))

/-- Marker: the constructive square root is multiplicative on nonnegative reals. -/
def fxRegularReal_hasSquareRootMultiplicativity : Bool := true

end FX1Poly.ComputerAlgebra
