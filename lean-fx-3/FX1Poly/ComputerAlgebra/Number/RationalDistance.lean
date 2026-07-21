import FX1Poly.ComputerAlgebra.Number.RationalPair

/-! # RationalDistance — the two-sided rational distance kit

The metric substrate for the Bishop real layer over `RationalPair`, resting on
four design choices:

  * ℝ as Bishop regular sequences over `RationalPair`: a real is
    `approximation : Nat → RationalPair` with the regularity certificate
    `distance (x m) (x n) ≤ 1/(m+1) + 1/(n+1)`; the convergence modulus is built
    in, so no choice principle is needed to extract rates.
  * Two-sided bounds without absolute value: `IsWithinBound l r bound` is the
    conjunction `l − r ≤ bound ∧ r − l ≤ bound`.  Every metric obligation lands
    on the order/monotonicity corpus (`addExactMonotone`, `lessEqualAsCongr*`,
    the group laws) rather than a `natAbs` case analysis; an `absExact` can be
    characterized by this predicate rather than taken as primitive.
  * Function-extensionality-free sameness: equality of reals is the pointwise
    setoid `∀ n, IsWithinBound (x n) (y n) (2/(n+1))`, never `Eq` on the
    approximation functions, so `funext` is never needed.
  * `ratioOfNatSucc k n` denotes `k/(n+1)`; the bounds `1/(n+1)` and `2/(n+1)`
    are single constructor applications, not arithmetic.

Contents: subtraction, the structurally-positive bound constructors, the
two-sided predicate with its decidability, symmetry, bound-monotonicity,
self-distance, setoid congruence, the subtraction chain law, and the triangle
inequality, from which ℝ's ε/3 transitivity follows by instantiation. -/

namespace FX1Poly.ComputerAlgebra

namespace RationalPair

/-- Exact subtraction — addition of the negation, definitionally. -/
def subExact (leftValue rightValue : RationalPair) : RationalPair :=
  addExact leftValue (negExact rightValue)

/-- The ratio `k/(n+1)` — a structurally positive denominator by
construction, so the Bishop bounds are constructor applications. -/
def ratioOfNatSucc (numeratorNat denominatorPredecessor : Nat) : RationalPair :=
  { numerator := Int.ofNat numeratorNat
    denominatorPredecessor := denominatorPredecessor }

/-- The reciprocal `1/(n+1)` — the regularity modulus at index `n`. -/
def reciprocalOfSucc (denominatorPredecessor : Nat) : RationalPair :=
  ratioOfNatSucc 1 denominatorPredecessor

/-- The two-sided distance bound: both differences sit below the bound.  This is
`|l − r| ≤ bound` without an absolute value. -/
def IsWithinBound (leftValue rightValue bound : RationalPair) : Prop :=
  LessEqualAs (subExact leftValue rightValue) bound ∧
    LessEqualAs (subExact rightValue leftValue) bound

/-- The two-sided bound is decidable — a conjunction of decidable orders. -/
def decideIsWithinBound (leftValue rightValue bound : RationalPair) :
    Decidable (IsWithinBound leftValue rightValue bound) :=
  @instDecidableAnd _ _
    (decideLessEqualAs (subExact leftValue rightValue) bound)
    (decideLessEqualAs (subExact rightValue leftValue) bound)

/-- Symmetry — swap the conjuncts. -/
theorem isWithinBoundSymm {leftValue rightValue bound : RationalPair}
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinBound rightValue leftValue bound :=
  ⟨isWithin.right, isWithin.left⟩

/-- A bound may be relaxed upward. -/
theorem isWithinBoundOfBoundLessEqual
    {leftValue rightValue lowBound highBound : RationalPair}
    (isBoundBelow : LessEqualAs lowBound highBound)
    (isWithin : IsWithinBound leftValue rightValue lowBound) :
    IsWithinBound leftValue rightValue highBound :=
  ⟨lessEqualAsTrans isWithin.left isBoundBelow,
    lessEqualAsTrans isWithin.right isBoundBelow⟩

/-- Self-distance sits below every nonnegative bound — `v − v` denotes zero. -/
theorem isWithinBoundSelfOfNonNegative {value bound : RationalPair}
    (isBoundNonNegative : IsNonNegative bound) :
    IsWithinBound value value bound :=
  have selfDifferenceIsBounded : LessEqualAs (subExact value value) bound :=
    lessEqualAsCongrLeft (denotesSameAsSymm (addExactNegRight value))
      isBoundNonNegative
  ⟨selfDifferenceIsBounded, selfDifferenceIsBounded⟩

/-- Subtraction respects the setoid in both slots — addition and negation
congruence composed. -/
theorem subExactRespectsDenotesSameAs
    {leftValue newLeftValue rightValue newRightValue : RationalPair}
    (leftAgrees : DenotesSameAs leftValue newLeftValue)
    (rightAgrees : DenotesSameAs rightValue newRightValue) :
    DenotesSameAs (subExact leftValue rightValue)
      (subExact newLeftValue newRightValue) :=
  addExactRespectsDenotesSameAs leftAgrees
    (negExactRespectsDenotesSameAs rightAgrees)

/-- The two-sided bound respects the setoid in the left value. -/
theorem isWithinBoundCongrLeft
    {leftValue newLeftValue rightValue bound : RationalPair}
    (leftAgrees : DenotesSameAs leftValue newLeftValue)
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinBound newLeftValue rightValue bound :=
  ⟨lessEqualAsCongrLeft
      (subExactRespectsDenotesSameAs leftAgrees (denotesSameAsRefl rightValue))
      isWithin.left,
    lessEqualAsCongrLeft
      (subExactRespectsDenotesSameAs (denotesSameAsRefl rightValue) leftAgrees)
      isWithin.right⟩

/-- The two-sided bound respects the setoid in the right value. -/
theorem isWithinBoundCongrRight
    {leftValue rightValue newRightValue bound : RationalPair}
    (rightAgrees : DenotesSameAs rightValue newRightValue)
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinBound leftValue newRightValue bound :=
  isWithinBoundSymm (isWithinBoundCongrLeft rightAgrees
    (isWithinBoundSymm isWithin))

/-- The two-sided bound respects the setoid in the bound. -/
theorem isWithinBoundCongrBound
    {leftValue rightValue bound newBound : RationalPair}
    (boundsAgree : DenotesSameAs bound newBound)
    (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinBound leftValue rightValue newBound :=
  ⟨lessEqualAsCongrRight boundsAgree isWithin.left,
    lessEqualAsCongrRight boundsAgree isWithin.right⟩

/-- The subtraction chain law: `(a − b) + (b − c)` denotes `a − c`.  The middle
term cancels through the group laws (associate, collapse `−b + b` to zero, absorb
the zero). -/
theorem subExactChainDenotesSame
    (firstValue middleValue lastValue : RationalPair) :
    DenotesSameAs
      (addExact (subExact firstValue middleValue)
        (subExact middleValue lastValue))
      (subExact firstValue lastValue) :=
  have negMeetsMiddle :
      DenotesSameAs (addExact (negExact middleValue) middleValue) zeroRational :=
    denotesSameAsTrans (addExactComm (negExact middleValue) middleValue)
      (addExactNegRight middleValue)
  denotesSameAsTrans
    (addExactAssoc firstValue (negExact middleValue)
      (addExact middleValue (negExact lastValue)))
    (addExactRespectsDenotesSameAs (denotesSameAsRefl firstValue)
      (denotesSameAsTrans
        (denotesSameAsSymm (addExactAssoc (negExact middleValue) middleValue
          (negExact lastValue)))
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs negMeetsMiddle
            (denotesSameAsRefl (negExact lastValue)))
          (addExactZeroLeft (negExact lastValue)))))

/-- The triangle inequality, two-sidedly: chain two bounds through the shared
middle value.  The differences add (`addExactMonotone`) and the chain law
rewrites the sum of differences to the outer difference.  ℝ's ε/3 transitivity is
an instantiation. -/
theorem isWithinBoundTriangle
    {firstValue middleValue lastValue firstBound lastBound : RationalPair}
    (isFirstWithin : IsWithinBound firstValue middleValue firstBound)
    (isLastWithin : IsWithinBound middleValue lastValue lastBound) :
    IsWithinBound firstValue lastValue (addExact firstBound lastBound) :=
  ⟨lessEqualAsCongrLeft
      (subExactChainDenotesSame firstValue middleValue lastValue)
      (addExactMonotone isFirstWithin.left isLastWithin.left),
    lessEqualAsCongrRight (addExactComm lastBound firstBound)
      (lessEqualAsCongrLeft
        (subExactChainDenotesSame lastValue middleValue firstValue)
        (addExactMonotone isLastWithin.right isFirstWithin.right))⟩

/-! ## The slack-closure principle

Bishop's workhorse: a bound that holds with every vanishing slack holds
outright, `(∀ m, value ≤ bound + k/(m+1)) → value ≤ bound`.  Constructively this
is a computation, not a limit: decide the conclusion; if it fails, the strict
reverse bound saturates the slack hypothesis at the product index
`k·(denominator of bound)·(denominator of value)`, where cross-multiplication
collapses to `n + 1 ≤ n` on a single `ofNat`, refuted by irreflexivity.  ℝ's ε/3
setoid transitivity consumes this through the two-sided wrapper. -/

/-- The bounds `k/(n+1)` are nonnegative — the numerator IS an `ofNat`. -/
theorem ratioOfNatSuccIsNonNegative
    (numeratorNat denominatorPredecessor : Nat) :
    IsNonNegative (ratioOfNatSucc numeratorNat denominatorPredecessor) :=
  isNonNegativeOfNumeratorNonNegative (intZeroLeOfNat numeratorNat)

/-- Same-denominator bounds ADD on the numerator: `j/(n+1) + k/(n+1)`
denotes `(j+k)/(n+1)` — one refold and one associate; the numerator sum is
definitional on the `ofNat` payloads. -/
theorem ratioOfNatSuccSumDenotesSame
    (leftNumeratorNat rightNumeratorNat denominatorPredecessor : Nat) :
    DenotesSameAs
      (addExact (ratioOfNatSucc leftNumeratorNat denominatorPredecessor)
        (ratioOfNatSucc rightNumeratorNat denominatorPredecessor))
      (ratioOfNatSucc (leftNumeratorNat + rightNumeratorNat)
        denominatorPredecessor) :=
  (congrArg (· * Int.ofNat (denominatorPredecessor + 1))
      (intRightDistrib (Int.ofNat leftNumeratorNat)
        (Int.ofNat rightNumeratorNat)
        (Int.ofNat (denominatorPredecessor + 1))).symm).trans
    (intMulAssoc (Int.ofNat leftNumeratorNat + Int.ofNat rightNumeratorNat)
      (Int.ofNat (denominatorPredecessor + 1))
      (Int.ofNat (denominatorPredecessor + 1)))

/-- Slack closure: below the bound with every vanishing slack means below the
bound.  Decidability supplies the dichotomy; the failing branch scales the strict
reverse bound by the saturation denominator and cancels down to
`ofNat + 1 ≤ ofNat`, which irreflexivity refutes. -/
theorem lessEqualAsOfForallSlack {value bound : RationalPair}
    {slackNumerator : Nat}
    (isBoundedWithSlack : ∀ slackIndex : Nat,
      LessEqualAs value
        (addExact bound (ratioOfNatSucc slackNumerator slackIndex))) :
    LessEqualAs value bound :=
  match decideLessEqualAs value bound with
  | .isTrue isBounded => isBounded
  | .isFalse isNotBounded =>
      let saturationIndex : Nat :=
        slackNumerator * (bound.denominatorPredecessor + 1) *
          (value.denominatorPredecessor + 1)
      have isStrictlyAbove :
          bound.numerator * denominatorInt value + 1 ≤
            value.numerator * denominatorInt bound :=
        intLessThanOfNotLessEqual isNotBounded
      have strictScaled :
          bound.numerator * denominatorInt value *
              Int.ofNat (saturationIndex + 1) +
              Int.ofNat (saturationIndex + 1) ≤
            value.numerator * denominatorInt bound *
              Int.ofNat (saturationIndex + 1) :=
        intLessEqualOfEqLeft
          ((congrArg
              (bound.numerator * denominatorInt value *
                Int.ofNat (saturationIndex + 1) + ·)
              (intOneMul (Int.ofNat (saturationIndex + 1))).symm).trans
            (intRightDistrib (bound.numerator * denominatorInt value) 1
              (Int.ofNat (saturationIndex + 1))).symm)
          (intMulLeMulRightOfNonNeg isStrictlyAbove
            (intZeroLeOfNat (saturationIndex + 1)))
      have slackBoundRaw :
          value.numerator *
              (denominatorInt bound * Int.ofNat (saturationIndex + 1)) ≤
            (bound.numerator * Int.ofNat (saturationIndex + 1) +
                Int.ofNat slackNumerator * denominatorInt bound) *
              denominatorInt value :=
        isBoundedWithSlack saturationIndex
      have slackBoundShaped :
          value.numerator * denominatorInt bound *
              Int.ofNat (saturationIndex + 1) ≤
            bound.numerator * denominatorInt value *
                Int.ofNat (saturationIndex + 1) +
              Int.ofNat slackNumerator * denominatorInt bound *
                denominatorInt value :=
        intLessEqualOfEqLeft
          (intMulAssoc value.numerator (denominatorInt bound)
            (Int.ofNat (saturationIndex + 1)))
          (intLessEqualOfEqRight slackBoundRaw
            ((intRightDistrib
                (bound.numerator * Int.ofNat (saturationIndex + 1))
                (Int.ofNat slackNumerator * denominatorInt bound)
                (denominatorInt value)).trans
              (congrArg
                (· + Int.ofNat slackNumerator * denominatorInt bound *
                  denominatorInt value)
                (intMulRightComm bound.numerator
                  (Int.ofNat (saturationIndex + 1))
                  (denominatorInt value)))))
      have saturationOverflow :
          Int.ofNat saturationIndex + 1 ≤ Int.ofNat saturationIndex :=
        intAddLeftCancelLessEqual
          (intLessEqualTrans strictScaled slackBoundShaped)
      absurd
        (show Int.ofNat saturationIndex < Int.ofNat saturationIndex from
          saturationOverflow)
        (intLessThanIrrefl (Int.ofNat saturationIndex))

/-- Slack closure, two-sidedly — the form ℝ's setoid transitivity consumes. -/
theorem isWithinBoundOfForallSlack {leftValue rightValue bound : RationalPair}
    {slackNumerator : Nat}
    (isWithinWithSlack : ∀ slackIndex : Nat,
      IsWithinBound leftValue rightValue
        (addExact bound (ratioOfNatSucc slackNumerator slackIndex))) :
    IsWithinBound leftValue rightValue bound :=
  ⟨lessEqualAsOfForallSlack
      (fun slackIndex => (isWithinWithSlack slackIndex).left),
    lessEqualAsOfForallSlack
      (fun slackIndex => (isWithinWithSlack slackIndex).right)⟩

end RationalPair

end FX1Poly.ComputerAlgebra
