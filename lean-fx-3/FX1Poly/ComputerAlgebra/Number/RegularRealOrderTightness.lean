import FX1Poly.ComputerAlgebra.Number.RegularRealOrder
import FX1Poly.ComputerAlgebra.Number.RegularRealRing

/-! # RegularReal order — tightness and setoid congruence (NUM-R-5c)

The R-5 keystone: the non-strict order `LessEqualReal` is TIGHT (mutual
`≤` collapses to the setoid) and SETOID-INVARIANT (it transports through
`DenotesSameReal` on both endpoints).  Both ride the vanishing-slack
closure `lessEqualAsOfForallSlack` — no case split on real order, no
estimate outside the shipped ℚ kit.

  * **Tightness** (`denotesSameRealOfLessEqualBoth`): the two one-sided
    bounds negate into the two-sided `IsWithinBound` at the doubled
    sample `2m+1` (each `LessEqualReal` arm gives `x_{2m+1} ≤ 1/(m+1)`
    on the SAME difference), then the ε/3 chain through the raw
    approximants collapses the four-leg bound to `2/(n+1) + 2/(m+1)` and
    slack closure erases the vanishing `2/(m+1)`.
  * **Congruence** (`lessEqualRealRespectsDenotesSame`): pointwise
    transport of the one-sided bound loses a factor (setoid distance is
    `2/(m+1)`, regularity another `1/(m+1)`), so the exact `1/(k+1)`
    modulus is recovered through slack closure at numerator `4` — the
    same discipline `denotesSameRealTrans` already uses.

The enabling ℚ move shipped here: negation is antitone on the cross-
multiplication order (`lessEqualAsNegBoth`).  Deferred to R-5d: the
monotone-add/`sqrtRealMonotone` payoff toward the ℂ triangle inequality. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- **Negation is antitone on the order**: `l ≤ r` flips to
`−r ≤ −l`.  The denominators ride along unchanged (negation keeps the
predecessor); the two cross-products are the negated originals, so the
`Int` antitone `intNegLeNegOfLe` closes it after pulling each sign out
through `intNegMul`. -/
theorem lessEqualAsNegBoth {leftValue rightValue : RationalPair}
    (isBelow : LessEqualAs leftValue rightValue) :
    LessEqualAs (negExact rightValue) (negExact leftValue) :=
  intLessEqualOfEqRight
    (intLessEqualOfEqLeft
      (intNegMul rightValue.numerator (denominatorInt leftValue))
      (intNegLeNegOfLe isBelow))
    (intNegMul leftValue.numerator (denominatorInt rightValue)).symm

/-- **The tightness ε/3 collapse**: the four-leg chain bound
`((1/(n+1) + 1/(2m+2)) + 1/(m+1)) + (1/(2m+2) + 1/(n+1))` denotes
`2/(n+1) + 2/(m+1)`.  Medial-swap the outer sum to gather the shared
denominators, associate the doubled `1/(2m+2)` pair, collapse it to
`1/(m+1)` by the doubled-index identity, cross-pair the `(a+c)+(c+a)`
block, and read each half off `ratioOfNatSuccSumDenotesSame`. -/
theorem tightnessChainBoundCollapses
    (outerPredecessor innerPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact
          (addExact (reciprocalOfSucc outerPredecessor)
            (reciprocalOfSucc (2 * innerPredecessor + 1)))
          (reciprocalOfSucc innerPredecessor))
        (addExact (reciprocalOfSucc (2 * innerPredecessor + 1))
          (reciprocalOfSucc outerPredecessor)))
      (addExact (ratioOfNatSucc 2 outerPredecessor)
        (ratioOfNatSucc 2 innerPredecessor)) :=
  denotesSameAsTrans
    (addExactMedialDenotesSame
      (addExact (reciprocalOfSucc outerPredecessor)
        (reciprocalOfSucc (2 * innerPredecessor + 1)))
      (reciprocalOfSucc innerPredecessor)
      (reciprocalOfSucc (2 * innerPredecessor + 1))
      (reciprocalOfSucc outerPredecessor))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (addExactAssoc (reciprocalOfSucc outerPredecessor)
          (reciprocalOfSucc (2 * innerPredecessor + 1))
          (reciprocalOfSucc (2 * innerPredecessor + 1)))
        (denotesSameAsRefl
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (addExactRespectsDenotesSameAs
            (denotesSameAsRefl (reciprocalOfSucc outerPredecessor))
            (reciprocalDoubleSumDenotesSame innerPredecessor))
          (denotesSameAsRefl
            (addExact (reciprocalOfSucc innerPredecessor)
              (reciprocalOfSucc outerPredecessor))))
        (denotesSameAsTrans
          (addExactCrossPairsDenotesSame (reciprocalOfSucc outerPredecessor)
            (reciprocalOfSucc innerPredecessor))
          (addExactRespectsDenotesSameAs
            (ratioOfNatSuccSumDenotesSame 1 1 outerPredecessor)
            (ratioOfNatSuccSumDenotesSame 1 1 innerPredecessor)))))

/-- `−v + v` denotes zero — commute onto the shipped right-inverse. -/
theorem addExactNegLeftDenotesSame (value : RationalPair) :
    DenotesSameAs (addExact (negExact value) value) zeroRational :=
  denotesSameAsTrans (addExactComm (negExact value) value)
    (addExactNegRight value)

/-- **The congruence slack tail**: the rational tail
`((1/(m+1) + 1/(k+1)) + 2/(m+1)) + 1/(m+1)` denotes `4/(m+1) + 1/(k+1)`
— rotate `1/(k+1)` to the far right past the three `m`-graded summands,
then fold `1/(m+1) + 2/(m+1) + 1/(m+1)` onto its shared denominator. -/
theorem congruenceSlackTailCollapses (outerPredecessor innerPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))
          (ratioOfNatSucc 2 innerPredecessor))
        (reciprocalOfSucc innerPredecessor))
      (addExact (ratioOfNatSucc 4 innerPredecessor)
        (reciprocalOfSucc outerPredecessor)) :=
  have innerSwap :
      DenotesSameAs
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))
          (ratioOfNatSucc 2 innerPredecessor))
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (ratioOfNatSucc 2 innerPredecessor))
          (reciprocalOfSucc outerPredecessor)) :=
    denotesSameAsTrans
      (addExactAssoc (reciprocalOfSucc innerPredecessor)
        (reciprocalOfSucc outerPredecessor)
        (ratioOfNatSucc 2 innerPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl (reciprocalOfSucc innerPredecessor))
          (addExactComm (reciprocalOfSucc outerPredecessor)
            (ratioOfNatSucc 2 innerPredecessor)))
        (denotesSameAsSymm
          (addExactAssoc (reciprocalOfSucc innerPredecessor)
            (ratioOfNatSucc 2 innerPredecessor)
            (reciprocalOfSucc outerPredecessor))))
  have rotateOuter :
      DenotesSameAs
        (addExact
          (addExact
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 2 innerPredecessor))
            (reciprocalOfSucc outerPredecessor))
          (reciprocalOfSucc innerPredecessor))
        (addExact
          (addExact
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 2 innerPredecessor))
            (reciprocalOfSucc innerPredecessor))
          (reciprocalOfSucc outerPredecessor)) :=
    denotesSameAsTrans
      (addExactAssoc
        (addExact (reciprocalOfSucc innerPredecessor)
          (ratioOfNatSucc 2 innerPredecessor))
        (reciprocalOfSucc outerPredecessor)
        (reciprocalOfSucc innerPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 2 innerPredecessor)))
          (addExactComm (reciprocalOfSucc outerPredecessor)
            (reciprocalOfSucc innerPredecessor)))
        (denotesSameAsSymm
          (addExactAssoc
            (addExact (reciprocalOfSucc innerPredecessor)
              (ratioOfNatSucc 2 innerPredecessor))
            (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))))
  have leftCollapse :
      DenotesSameAs
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (ratioOfNatSucc 2 innerPredecessor))
          (reciprocalOfSucc innerPredecessor))
        (ratioOfNatSucc 4 innerPredecessor) :=
    denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (ratioOfNatSuccSumDenotesSame 1 2 innerPredecessor)
        (denotesSameAsRefl (reciprocalOfSucc innerPredecessor)))
      (ratioOfNatSuccSumDenotesSame 3 1 innerPredecessor)
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs innerSwap
      (denotesSameAsRefl (reciprocalOfSucc innerPredecessor)))
    (denotesSameAsTrans rotateOuter
      (addExactRespectsDenotesSameAs leftCollapse
        (denotesSameAsRefl (reciprocalOfSucc outerPredecessor))))

/-- **The congruence slack tail, with the carried base value**: pull the
approximant `baseValue` out front over the pure-rational tail, collapse
the tail by `congruenceSlackTailCollapses`, and re-associate onto the
`(baseValue + 4/(m+1)) + 1/(k+1)` slack shape. -/
theorem congruenceSlackTailCollapsesShaped (baseValue : RationalPair)
    (outerPredecessor innerPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact
          (addExact baseValue
            (addExact (reciprocalOfSucc innerPredecessor)
              (reciprocalOfSucc outerPredecessor)))
          (ratioOfNatSucc 2 innerPredecessor))
        (reciprocalOfSucc innerPredecessor))
      (addExact (addExact baseValue (ratioOfNatSucc 4 innerPredecessor))
        (reciprocalOfSucc outerPredecessor)) :=
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs
      (addExactAssoc baseValue
        (addExact (reciprocalOfSucc innerPredecessor)
          (reciprocalOfSucc outerPredecessor))
        (ratioOfNatSucc 2 innerPredecessor))
      (denotesSameAsRefl (reciprocalOfSucc innerPredecessor)))
    (denotesSameAsTrans
      (addExactAssoc baseValue
        (addExact
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))
          (ratioOfNatSucc 2 innerPredecessor))
        (reciprocalOfSucc innerPredecessor))
      (denotesSameAsTrans
        (addExactRespectsDenotesSameAs
          (denotesSameAsRefl baseValue)
          (congruenceSlackTailCollapses outerPredecessor innerPredecessor))
        (denotesSameAsSymm
          (addExactAssoc baseValue (ratioOfNatSucc 4 innerPredecessor)
            (reciprocalOfSucc outerPredecessor)))))

end RationalPair

open RationalPair

/-! ## Tightness (NUM-R-5c) -/

/-- **Tightness**: mutual non-strict order collapses to the setoid.  Each
`LessEqualReal` arm, negated (`lessEqualAsNegBoth`) and read through the
difference-negation and double-negation setoid identities, pins the SAME
difference `l_{2m+1} − r_{2m+1}` from both sides by `1/(m+1)`, giving the
two-sided `IsWithinBound` at the doubled sample.  The ε/3 chain through
the raw approximants collapses the four-leg bound to `2/(n+1) + 2/(m+1)`,
and slack closure erases the vanishing `2/(m+1)`. -/
theorem denotesSameRealOfLessEqualBoth {leftValue rightValue : RegularReal}
    (isLeftBelowRight : LessEqualReal leftValue rightValue)
    (isRightBelowLeft : LessEqualReal rightValue leftValue) :
    DenotesSameReal leftValue rightValue :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      have forwardBound :
          LessEqualAs
            (subExact (leftValue.approximation (2 * slackIndex + 1))
              (rightValue.approximation (2 * slackIndex + 1)))
            (reciprocalOfSucc slackIndex) :=
        lessEqualAsCongrRight
          (negExactNegExactDenotesSame (reciprocalOfSucc slackIndex))
          (lessEqualAsCongrLeft
            (negExactSubExactDenotesSame
              (rightValue.approximation (2 * slackIndex + 1))
              (leftValue.approximation (2 * slackIndex + 1)))
            (lessEqualAsNegBoth (isLeftBelowRight slackIndex)))
      have backwardBound :
          LessEqualAs
            (subExact (rightValue.approximation (2 * slackIndex + 1))
              (leftValue.approximation (2 * slackIndex + 1)))
            (reciprocalOfSucc slackIndex) :=
        lessEqualAsCongrRight
          (negExactNegExactDenotesSame (reciprocalOfSucc slackIndex))
          (lessEqualAsCongrLeft
            (negExactSubExactDenotesSame
              (leftValue.approximation (2 * slackIndex + 1))
              (rightValue.approximation (2 * slackIndex + 1)))
            (lessEqualAsNegBoth (isRightBelowLeft slackIndex)))
      have middleBound :
          IsWithinBound (leftValue.approximation (2 * slackIndex + 1))
            (rightValue.approximation (2 * slackIndex + 1))
            (reciprocalOfSucc slackIndex) :=
        ⟨forwardBound, backwardBound⟩
      isWithinBoundCongrBound
        (tightnessChainBoundCollapses sharedIndex slackIndex)
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            (leftValue.isRegular sharedIndex (2 * slackIndex + 1))
            middleBound)
          (rightValue.isRegular (2 * slackIndex + 1) sharedIndex)))

/-- Tightness, named for the order side — the alias the ℂ layer cites. -/
theorem lessEqualRealTight {leftValue rightValue : RegularReal}
    (isLeftBelowRight : LessEqualReal leftValue rightValue)
    (isRightBelowLeft : LessEqualReal rightValue leftValue) :
    DenotesSameReal leftValue rightValue :=
  denotesSameRealOfLessEqualBoth isLeftBelowRight isRightBelowLeft

/-! ## Setoid congruence (NUM-R-5c) -/

/-- **Nonnegativity of a difference is setoid-invariant**: if every
approximant of `value` clears `−1/(index+1)` and `newValue` denotes the
same real, then `newValue` clears it too.  Pointwise transport loses a
factor — the setoid gap is `2/(m+1)` and one regularity step another
`1/(m+1)` — so the exact `1/(k+1)` modulus is recovered through slack
closure at numerator `4`: at every deep sample `m`, chaining
`−1/(m+1) ≤ value_m ≤ newValue_m + 2/(m+1) ≤ newValue_k + (1/(m+1) +
1/(k+1)) + 2/(m+1)` and shifting by `1/(m+1)` and `1/(k+1)` leaves
exactly `−1/(k+1) ≤ newValue_k + 4/(m+1)`. -/
theorem realNonNegativeRespectsDenotesSame {value newValue : RegularReal}
    (areSame : DenotesSameReal value newValue)
    (isNonNegative : ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index))
        (value.approximation index)) :
    ∀ index : Nat,
      LessEqualAs (negExact (reciprocalOfSucc index))
        (newValue.approximation index) :=
  fun comparisonIndex =>
    lessEqualAsOfForallSlack (slackNumerator := 4) (fun slackIndex =>
      have differenceShunted :
          LessEqualAs (value.approximation slackIndex)
            (addExact (newValue.approximation slackIndex)
              (ratioOfNatSucc 2 slackIndex)) :=
        lessEqualAsAddOfSubLessEqual (areSame slackIndex).left
      have regularityShunted :
          LessEqualAs (newValue.approximation slackIndex)
            (addExact (newValue.approximation comparisonIndex)
              (addExact (reciprocalOfSucc slackIndex)
                (reciprocalOfSucc comparisonIndex))) :=
        lessEqualAsAddOfSubLessEqual
          (newValue.isRegular slackIndex comparisonIndex).left
      have chainThroughDeepSample :
          LessEqualAs (negExact (reciprocalOfSucc slackIndex))
            (addExact
              (addExact (newValue.approximation comparisonIndex)
                (addExact (reciprocalOfSucc slackIndex)
                  (reciprocalOfSucc comparisonIndex)))
              (ratioOfNatSucc 2 slackIndex)) :=
        lessEqualAsTrans (isNonNegative slackIndex)
          (lessEqualAsTrans differenceShunted
            (addExactMonotone regularityShunted
              (lessEqualAsRefl (ratioOfNatSucc 2 slackIndex))))
      have shiftedNonNegative :
          LessEqualAs zeroRational
            (addExact
              (addExact (newValue.approximation comparisonIndex)
                (ratioOfNatSucc 4 slackIndex))
              (reciprocalOfSucc comparisonIndex)) :=
        lessEqualAsCongrLeft (addExactNegLeftDenotesSame (reciprocalOfSucc slackIndex))
          (lessEqualAsCongrRight
            (congruenceSlackTailCollapsesShaped
              (newValue.approximation comparisonIndex) comparisonIndex slackIndex)
            (addExactMonotone chainThroughDeepSample
              (lessEqualAsRefl (reciprocalOfSucc slackIndex))))
      lessEqualAsAddRightCancel
        (lessEqualAsCongrLeft
          (denotesSameAsSymm
            (addExactNegLeftDenotesSame (reciprocalOfSucc comparisonIndex)))
          shiftedNonNegative))

/-- **The non-strict order respects the setoid on both endpoints** —
transport the difference `subReal r l ↦ subReal r' l'` through the two
setoid hypotheses (`subRealRespectsDenotesSame`) and carry the
nonnegativity across by `realNonNegativeRespectsDenotesSame`. -/
theorem lessEqualRealRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue)
    (isBelow : LessEqualReal leftValue rightValue) :
    LessEqualReal newLeftValue newRightValue :=
  realNonNegativeRespectsDenotesSame
    (subRealRespectsDenotesSame rightAgrees leftAgrees) isBelow

/-- The non-strict order's setoid congruence, named to mirror the strict
order's `lessThanRealCongr`. -/
theorem lessEqualRealCongr
    {leftValue newLeftValue rightValue newRightValue : RegularReal}
    (leftAgrees : DenotesSameReal leftValue newLeftValue)
    (rightAgrees : DenotesSameReal rightValue newRightValue)
    (isBelow : LessEqualReal leftValue rightValue) :
    LessEqualReal newLeftValue newRightValue :=
  lessEqualRealRespectsDenotesSame leftAgrees rightAgrees isBelow

/-! ## Additive monotonicity — the order-layer payoff (NUM-R-5c) -/

/-- **Additive monotonicity of the non-strict order**: a shared summand
preserves `≤`.  The shared value cancels out of the difference —
`(b + c) − (a + c) ~ b − a` by the subtraction cross-pair, self-difference
to zero, and dropping the zero — and `realNonNegativeRespectsDenotesSame`
carries the nonnegativity across that setoid identity.  This is the
monotone step the ℂ triangle inequality consumes. -/
theorem lessEqualRealAddCompat {leftValue rightValue : RegularReal}
    (isBelow : LessEqualReal leftValue rightValue) (sharedValue : RegularReal) :
    LessEqualReal (addReal leftValue sharedValue)
      (addReal rightValue sharedValue) :=
  realNonNegativeRespectsDenotesSame
    (denotesSameRealSymm
      (denotesSameRealTrans
        (subRealCrossPairsDenotesSame rightValue sharedValue leftValue sharedValue)
        (denotesSameRealTrans
          (addRealRespectsDenotesSame
            (denotesSameRealRefl (subReal rightValue leftValue))
            (addRealNegRight sharedValue))
          (addRealZeroRight (subReal rightValue leftValue)))))
    isBelow

/-- Marker: the real order carries tightness (setoid antisymmetry),
setoid congruence, and additive monotonicity. -/
def fxRegularReal_hasRealOrderTightness : Bool := true

end FX1Poly.ComputerAlgebra
