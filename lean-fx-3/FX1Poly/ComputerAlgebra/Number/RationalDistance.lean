import FX1Poly.ComputerAlgebra.Number.RationalPair

/-! # The two-sided rational distance kit (NUM-R-0)

The ℝ rung's DESIGN-LOCK, with its enabling substrate.  Locked decisions:

  * **ℝ = Bishop regular sequences over `RationalPair`**: a real will be
    `approximation : Nat → RationalPair` with the regularity certificate
    `distance (x m) (x n) ≤ 1/(m+1) + 1/(n+1)` — the convergence modulus is
    BAKED IN, so no choice principle is ever needed to extract rates.
  * **Two-sided bounds, NO absolute value**: `IsWithinBound l r bound` is the
    conjunction `l − r ≤ bound ∧ r − l ≤ bound`.  Every metric obligation then
    lands on the shipped order/monotonicity corpus (`addExactMonotone`,
    `lessEqualAsCongr*`, the group laws) instead of a `natAbs` constructor
    bash — the abs-free discipline is what keeps the ℝ layer mechanical.
    An `absExact` can be added later and CHARACTERIZED by this predicate;
    it is deliberately not the primitive.
  * **Funext-free discipline**: sameness of reals is the POINTWISE setoid
    `∀ n, IsWithinBound (x n) (y n) (2/(n+1))` — never `Eq` on the
    approximation functions.  No law about reals is ever an `Eq`, so `funext`
    can never be needed.
  * `ratioOfNatSucc k n` denotes `k/(n+1)` — the bounds `1/(n+1)` and
    `2/(n+1)` are single constructor applications, not arithmetic.

This file ships the kit that makes the ℝ setoid mechanical: subtraction, the
structurally-positive bound constructors, the two-sided predicate with its
decidability, symmetry, bound-monotonicity, self-distance, setoid congruence,
the subtraction chain law, and THE TRIANGLE — from which ℝ's ε/3
transitivity will fall out by instantiation. -/

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

/-- **The two-sided distance bound**: both differences sit below the bound.
The abs-free primitive — `|l − r| ≤ bound` without an absolute value. -/
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

/-- **The subtraction chain law**: `(a − b) + (b − c)` denotes `a − c` — the
middle term cancels through the group laws (associate, collapse `−b + b` to
zero, absorb the zero). -/
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

/-- **The triangle inequality**, two-sidedly: chain two bounds through the
shared middle value — the differences ADD (`addExactMonotone`) and the chain
law rewrites the sum of differences to the outer difference.  ℝ's ε/3
transitivity is an instantiation of this. -/
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

end RationalPair

end FX1Poly.ComputerAlgebra
