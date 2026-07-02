import FX1Poly.ComputerAlgebra.Number.RationalDistance

/-! # RegularReal — Bishop regular sequences over ℚ (NUM-R-1)

The ℝ carrier: a real is a sequence of rationals with the convergence modulus
BAKED IN — `distance (x m) (x n) ≤ 1/(m+1) + 1/(n+1)`.  No choice principle is
ever needed to extract rates, and no `funext` is ever needed because sameness
of reals is the POINTWISE setoid `∀ n, distance (x n) (y n) ≤ 2/(n+1)` — never
`Eq` on the approximation functions.

The setoid is honest: reflexivity and symmetry are pointwise one-liners, but
TRANSITIVITY is the first genuinely real-analytic argument in the tower —
Bishop's ε/3: for a fixed comparison index the distance chains through any
auxiliary index `m` as `x_n → x_m → y_m → z_m → z_n`, costing
`2/(n+1) + 6/(m+1)` after the bound collapses, and the SLACK-CLOSURE principle
(`lessEqualAsOfForallSlack` — a computation, not a limit) erases the `6/(m+1)`.
Sameness of reals is NOT decidable (deciding it would decide every Π⁰₁
statement about the approximations) — recorded honestly; contrast the ℚ rung.

The ℚ ↪ ℝ constant embedding is FAITHFUL: it respects the rational setoid, and
it reflects it — a constant-vs-constant pointwise bound with every vanishing
slack collapses back to the rational setoid by slack closure. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- Nonnegative rationals are closed under addition — squash the zero sum. -/
theorem addExactIsNonNegative {leftValue rightValue : RationalPair}
    (isLeftNonNegative : IsNonNegative leftValue)
    (isRightNonNegative : IsNonNegative rightValue) :
    IsNonNegative (addExact leftValue rightValue) :=
  lessEqualAsCongrLeft (addExactZeroRight zeroRational)
    (addExactMonotone isLeftNonNegative isRightNonNegative)

/-- **Cross-pair regrouping**: `(l + r) + (r + l)` denotes `(l + l) + (r + r)`
— associate, rotate the inner triple, associate back. -/
theorem addExactCrossPairsDenotesSame (leftValue rightValue : RationalPair) :
    DenotesSameAs
      (addExact (addExact leftValue rightValue)
        (addExact rightValue leftValue))
      (addExact (addExact leftValue leftValue)
        (addExact rightValue rightValue)) :=
  denotesSameAsTrans
    (addExactAssoc leftValue rightValue (addExact rightValue leftValue))
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs (denotesSameAsRefl leftValue)
        (denotesSameAsTrans
          (denotesSameAsSymm (addExactAssoc rightValue rightValue leftValue))
          (addExactComm (addExact rightValue rightValue) leftValue)))
      (denotesSameAsSymm
        (addExactAssoc leftValue leftValue
          (addExact rightValue rightValue))))

/-- A nonpositive difference reads back as the order: move the negated
product across the bound through the additive-group kit. -/
theorem lessEqualAsOfSubNonPositive {leftValue rightValue : RationalPair}
    (isNonPositive : LessEqualAs (subExact leftValue rightValue) zeroRational) :
    LessEqualAs leftValue rightValue :=
  have differenceIsNonPositive :
      leftValue.numerator * denominatorInt rightValue +
          -rightValue.numerator * denominatorInt leftValue ≤ 0 :=
    intLessEqualOfEqLeft
      (intMulOne (leftValue.numerator * denominatorInt rightValue +
        -rightValue.numerator * denominatorInt leftValue)).symm
      (intLessEqualOfEqRight isNonPositive
        (intZeroMul (denominatorInt (subExact leftValue rightValue))))
  have negationCancels :
      leftValue.numerator * denominatorInt rightValue +
          -rightValue.numerator * denominatorInt leftValue +
          rightValue.numerator * denominatorInt leftValue =
        leftValue.numerator * denominatorInt rightValue :=
    (intAddAssoc (leftValue.numerator * denominatorInt rightValue)
        (-rightValue.numerator * denominatorInt leftValue)
        (rightValue.numerator * denominatorInt leftValue)).trans
      ((congrArg (leftValue.numerator * denominatorInt rightValue + ·)
          ((congrArg (· + rightValue.numerator * denominatorInt leftValue)
              (intNegMul rightValue.numerator (denominatorInt leftValue))).trans
            (intAddLeftNeg
              (rightValue.numerator * denominatorInt leftValue)))).trans
        (intAddZero (leftValue.numerator * denominatorInt rightValue)))
  intLessEqualOfEqLeft negationCancels.symm
    (intLessEqualOfEqRight
      (intAddLeAddRight differenceIsNonPositive
        (rightValue.numerator * denominatorInt leftValue))
      (intZeroAdd (rightValue.numerator * denominatorInt leftValue)))

/-- **The ε/3 bound collapse**: the four-leg chain bound
`((1/(n+1) + 1/(m+1)) + 2/(m+1)) + (2/(m+1) + (1/(m+1) + 1/(n+1)))` denotes
`2/(n+1) + 6/(m+1)` — collapse each half onto its shared denominator, regroup
the cross pairs, collapse again. -/
theorem regularityChainBoundCollapses
    (outerPredecessor innerPredecessor : Nat) :
    DenotesSameAs
      (addExact
        (addExact
          (addExact (reciprocalOfSucc outerPredecessor)
            (reciprocalOfSucc innerPredecessor))
          (ratioOfNatSucc 2 innerPredecessor))
        (addExact (ratioOfNatSucc 2 innerPredecessor)
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor))))
      (addExact (ratioOfNatSucc 2 outerPredecessor)
        (ratioOfNatSucc 6 innerPredecessor)) :=
  have leftHalfCollapses :
      DenotesSameAs
        (addExact
          (addExact (reciprocalOfSucc outerPredecessor)
            (reciprocalOfSucc innerPredecessor))
          (ratioOfNatSucc 2 innerPredecessor))
        (addExact (reciprocalOfSucc outerPredecessor)
          (ratioOfNatSucc 3 innerPredecessor)) :=
    denotesSameAsTrans
      (addExactAssoc (reciprocalOfSucc outerPredecessor)
        (reciprocalOfSucc innerPredecessor)
        (ratioOfNatSucc 2 innerPredecessor))
      (addExactRespectsDenotesSameAs
        (denotesSameAsRefl (reciprocalOfSucc outerPredecessor))
        (ratioOfNatSuccSumDenotesSame 1 2 innerPredecessor))
  have rightHalfCollapses :
      DenotesSameAs
        (addExact (ratioOfNatSucc 2 innerPredecessor)
          (addExact (reciprocalOfSucc innerPredecessor)
            (reciprocalOfSucc outerPredecessor)))
        (addExact (ratioOfNatSucc 3 innerPredecessor)
          (reciprocalOfSucc outerPredecessor)) :=
    denotesSameAsTrans
      (denotesSameAsSymm
        (addExactAssoc (ratioOfNatSucc 2 innerPredecessor)
          (reciprocalOfSucc innerPredecessor)
          (reciprocalOfSucc outerPredecessor)))
      (addExactRespectsDenotesSameAs
        (ratioOfNatSuccSumDenotesSame 2 1 innerPredecessor)
        (denotesSameAsRefl (reciprocalOfSucc outerPredecessor)))
  denotesSameAsTrans
    (addExactRespectsDenotesSameAs leftHalfCollapses rightHalfCollapses)
    (denotesSameAsTrans
      (addExactCrossPairsDenotesSame (reciprocalOfSucc outerPredecessor)
        (ratioOfNatSucc 3 innerPredecessor))
      (addExactRespectsDenotesSameAs
        (ratioOfNatSuccSumDenotesSame 1 1 outerPredecessor)
        (ratioOfNatSuccSumDenotesSame 3 3 innerPredecessor)))

end RationalPair

open RationalPair

/-- **A Bishop regular real**: an approximation sequence whose convergence
modulus is the regularity certificate itself. -/
structure RegularReal where
  approximation : Nat → RationalPair
  isRegular : ∀ firstIndex secondIndex : Nat,
    IsWithinBound (approximation firstIndex) (approximation secondIndex)
      (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex))

/-- **Sameness of reals** — the pointwise `2/(n+1)` bound.  UNDECIDABLE
(honestly so), and never `Eq` on the approximation functions. -/
def DenotesSameReal (leftValue rightValue : RegularReal) : Prop :=
  ∀ sharedIndex : Nat,
    IsWithinBound (leftValue.approximation sharedIndex)
      (rightValue.approximation sharedIndex)
      (ratioOfNatSucc 2 sharedIndex)

/-- Reflexivity — self-distance sits below the nonnegative bound. -/
theorem denotesSameRealRefl (value : RegularReal) :
    DenotesSameReal value value :=
  fun sharedIndex =>
    isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 sharedIndex)

/-- Symmetry — pointwise, from the two-sided bound's symmetry. -/
theorem denotesSameRealSymm {leftValue rightValue : RegularReal}
    (areSame : DenotesSameReal leftValue rightValue) :
    DenotesSameReal rightValue leftValue :=
  fun sharedIndex => isWithinBoundSymm (areSame sharedIndex)

/-- **Transitivity — Bishop's ε/3**: at each comparison index, chain through
EVERY auxiliary index (`x_n → x_m → y_m → z_m → z_n` by two regularities and
the two hypotheses), collapse the chained bound to `2/(n+1) + 6/(m+1)`, and
let slack closure erase the vanishing `6/(m+1)`. -/
theorem denotesSameRealTrans {firstValue middleValue lastValue : RegularReal}
    (isFirstSame : DenotesSameReal firstValue middleValue)
    (isLastSame : DenotesSameReal middleValue lastValue) :
    DenotesSameReal firstValue lastValue :=
  fun sharedIndex =>
    isWithinBoundOfForallSlack (fun slackIndex =>
      isWithinBoundCongrBound
        (regularityChainBoundCollapses sharedIndex slackIndex)
        (isWithinBoundTriangle
          (isWithinBoundTriangle
            (firstValue.isRegular sharedIndex slackIndex)
            (isFirstSame slackIndex))
          (isWithinBoundTriangle
            (isLastSame slackIndex)
            (lastValue.isRegular slackIndex sharedIndex))))

/-- **The ℚ ↪ ℝ constant embedding** — regularity is self-distance below the
nonnegative modulus sum. -/
def constantReal (value : RationalPair) : RegularReal :=
  { approximation := fun _ => value
    isRegular := fun firstIndex secondIndex =>
      isWithinBoundSelfOfNonNegative
        (addExactIsNonNegative
          (ratioOfNatSuccIsNonNegative 1 firstIndex)
          (ratioOfNatSuccIsNonNegative 1 secondIndex)) }

/-- The constant embedding RESPECTS the rational setoid — self-distance,
transported along the sameness. -/
theorem constantRealRespectsDenotesSame {leftValue rightValue : RationalPair}
    (areSame : DenotesSameAs leftValue rightValue) :
    DenotesSameReal (constantReal leftValue) (constantReal rightValue) :=
  fun sharedIndex =>
    isWithinBoundCongrRight areSame
      (isWithinBoundSelfOfNonNegative
        (ratioOfNatSuccIsNonNegative 2 sharedIndex))

/-- The constant embedding REFLECTS the setoid — a constant-vs-constant
pointwise bound holds with every vanishing slack, so slack closure pins both
differences below zero, and antisymmetry lands on the rational setoid. -/
theorem denotesSameAsOfConstantRealDenotesSame
    {leftValue rightValue : RationalPair}
    (areSame : DenotesSameReal (constantReal leftValue)
      (constantReal rightValue)) :
    DenotesSameAs leftValue rightValue :=
  have forwardIsNonPositive :
      LessEqualAs (subExact leftValue rightValue) zeroRational :=
    lessEqualAsOfForallSlack (fun slackIndex =>
      lessEqualAsCongrRight
        (denotesSameAsSymm (addExactZeroLeft (ratioOfNatSucc 2 slackIndex)))
        (areSame slackIndex).left)
  have backwardIsNonPositive :
      LessEqualAs (subExact rightValue leftValue) zeroRational :=
    lessEqualAsOfForallSlack (fun slackIndex =>
      lessEqualAsCongrRight
        (denotesSameAsSymm (addExactZeroLeft (ratioOfNatSucc 2 slackIndex)))
        (areSame slackIndex).right)
  denotesSameAsOfLessEqualBoth
    (lessEqualAsOfSubNonPositive forwardIsNonPositive)
    (lessEqualAsOfSubNonPositive backwardIsNonPositive)

end FX1Poly.ComputerAlgebra
