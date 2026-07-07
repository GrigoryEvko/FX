import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.ComputerAlgebra.Number.RegularRealInverse

/-! # FX1Poly/ComputerAlgebra/Number/RegularRealSquareRoot — constructive square root
    (NUM-R-SQRT #1961)

Constructive `sqrt` on nonnegative Bishop regular reals, built √-free: the true real
square root never appears as an intermediate; every step is rational `≤`/square algebra
plus the integer square-root bracket and a "squaring is monotone on nonnegatives"
surrogate for √-monotonicity.

Dependency order:

  1. `natSqrt` — integer square root by structural COUNTING recursion, an exact mirror
     of the shipped `natDivModCounting`: walk the radicand up one unit at a time, bump
     the root exactly when the count reaches the next perfect square.  Two-sided
     certificate `natSqrt v * natSqrt v ≤ v < (natSqrt v + 1) * (natSqrt v + 1)`, proved
     as ONE structural induction carrying the conjunction, then projected.

## Zero-axiom

Structural recursion on the radicand, `cond`-transport by `congrArg` over
`Nat.eq_of_beq_eq_true` / `Nat.ne_of_beq_eq_false` (both clean).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/RegularRealSquareRoot.lean`. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## natSqrt — integer square root by counting -/

/-- Transitivity of strict `<` on `Nat`: `a < b` is `a + 1 ≤ b`, relax `b < c` to
`b ≤ c` and chain. -/
theorem natLtTrans {lowValue middleValue highValue : Nat}
    (isLowMiddle : lowValue < middleValue) (isMiddleHigh : middleValue < highValue) :
    lowValue < highValue :=
  natLeTrans isLowMiddle (natLeOfLt isMiddleHigh)

/-- Squaring strictly grows across a successor step: `(s+1)² < (s+2)²`.  Two strict
factor bumps (right factor, then left via commutativity) chained by `natLtTrans`. -/
theorem natSquareStrictMonoSucc (rootValue : Nat) :
    (rootValue + 1) * (rootValue + 1) < (rootValue + 2) * (rootValue + 2) :=
  let stepRightFactor :
      (rootValue + 1) * (rootValue + 1) < (rootValue + 2) * (rootValue + 1) :=
    natMulLtMulRight (Nat.le.refl) (natSuccLeSuccOfLe (natZeroLe rootValue))
  let stepLeftFactorCommuted :
      (rootValue + 1) * (rootValue + 2) < (rootValue + 2) * (rootValue + 2) :=
    natMulLtMulRight (Nat.le.refl) (natSuccLeSuccOfLe (natZeroLe (rootValue + 1)))
  let stepLeftFactor :
      (rootValue + 2) * (rootValue + 1) < (rootValue + 2) * (rootValue + 2) :=
    (Nat.mul_comm (rootValue + 1) (rootValue + 2)) ▸ stepLeftFactorCommuted
  natLtTrans stepRightFactor stepLeftFactor

/-- One counting step: given `root = isqrt(candidate - 1)`, return `isqrt(candidate)`.
Written with `cond` so the Bool scrutinee stays exposed for `congrArg` transport. -/
def natSqrtStep (rootValue candidate : Nat) : Nat :=
  cond (((rootValue + 1) * (rootValue + 1)).beq candidate) (rootValue + 1) rootValue

/-- Integer square root by counting — structural on the radicand (no well-founded
recursion, no fuel).  Largest `s` with `s * s ≤ v`. -/
def natSqrt : Nat → Nat
  | 0 => 0
  | value + 1 => natSqrtStep (natSqrt value) (value + 1)

/-- **The two-sided certificate**, proved as ONE structural induction carrying the
conjunction: `natSqrt v * natSqrt v ≤ v` and `v < (natSqrt v + 1) * (natSqrt v + 1)`.
The step dispatches on whether the next perfect square `(root+1)²` has been reached. -/
theorem natSqrtBounds : ∀ radicand : Nat,
    natSqrt radicand * natSqrt radicand ≤ radicand ∧
      radicand < (natSqrt radicand + 1) * (natSqrt radicand + 1)
  | 0 => ⟨Nat.le.refl, Nat.le.refl⟩
  | value + 1 =>
      match natSqrtBounds value with
      | ⟨lowerBound, upperBound⟩ =>
          match beqEquation :
              ((natSqrt value + 1) * (natSqrt value + 1)).beq (value + 1) with
          | true =>
              let stepEquation : natSqrt (value + 1) = natSqrt value + 1 :=
                congrArg
                  (fun conditionBool =>
                    cond conditionBool (natSqrt value + 1) (natSqrt value))
                  beqEquation
              let squareEquation :
                  (natSqrt value + 1) * (natSqrt value + 1) = value + 1 :=
                Nat.eq_of_beq_eq_true beqEquation
              let lowerAtRoot :
                  (natSqrt value + 1) * (natSqrt value + 1) ≤ value + 1 :=
                natLeOfEqLeft squareEquation Nat.le.refl
              let upperAtRoot :
                  value + 1 < (natSqrt value + 1 + 1) * (natSqrt value + 1 + 1) :=
                squareEquation ▸ natSquareStrictMonoSucc (natSqrt value)
              stepEquation.symm ▸ ⟨lowerAtRoot, upperAtRoot⟩
          | false =>
              let stepEquation : natSqrt (value + 1) = natSqrt value :=
                congrArg
                  (fun conditionBool =>
                    cond conditionBool (natSqrt value + 1) (natSqrt value))
                  beqEquation
              let lowerAtRoot : natSqrt value * natSqrt value ≤ value + 1 :=
                natLeTrans lowerBound (Nat.le.step Nat.le.refl)
              let isNotEqual :
                  value + 1 ≠ (natSqrt value + 1) * (natSqrt value + 1) :=
                fun equalityHolds =>
                  Nat.ne_of_beq_eq_false beqEquation equalityHolds.symm
              let upperAtRoot :
                  value + 1 < (natSqrt value + 1) * (natSqrt value + 1) :=
                natLtOfLeOfNe upperBound isNotEqual
              stepEquation.symm ▸ ⟨lowerAtRoot, upperAtRoot⟩

/-- Lower half of the certificate: `natSqrt v * natSqrt v ≤ v`. -/
theorem natSqrtLowerBound (radicand : Nat) :
    natSqrt radicand * natSqrt radicand ≤ radicand :=
  (natSqrtBounds radicand).left

/-- Upper half of the certificate: `v < (natSqrt v + 1) * (natSqrt v + 1)`. -/
theorem natSqrtUpperBound (radicand : Nat) :
    radicand < (natSqrt radicand + 1) * (natSqrt radicand + 1) :=
  (natSqrtBounds radicand).right

/-- Non-strict right-scale monotonicity of `Nat` multiplication — the witness rides
through right distributivity. -/
theorem natMulLeMulRight {lowValue highValue : Nat}
    (isLessEqual : lowValue ≤ highValue) (factor : Nat) :
    lowValue * factor ≤ highValue * factor :=
  match Nat.le.dest isLessEqual with
  | ⟨difference, differenceEquation⟩ =>
      Nat.le.intro
        ((natRightDistrib lowValue difference factor).symm.trans
          (congrArg (· * factor) differenceEquation))

/-! ## rationalSqrtApprox — √q to grid precision `1/(g+1)`

`q = p/(e+1)` with `p` clamped to `pNat := p.toNat` (negatives → 0, keeping the
construction total).  Approximate `√q` on the fixed grid `1/(g+1)` by ONE integer
square root of the scaled, floored radicand `m := ⌊pNat·(g+1)² / (e+1)⌋`; the answer is
`natSqrt m / (g+1)`.  The two-sided SQUARE bracket `s² ≤ q ≤ (s+1)²/(g+1)²` is pure
`Nat`/`Int` algebra — no √ appears. -/

/-- The floored scaled radicand `m = ⌊pNat·(g+1)² / (e+1)⌋` (`pNat` the clamped
numerator). -/
def rationalSqrtRadicand (value : RationalPair) (gridPredecessor : Nat) : Nat :=
  (natDivModCounting (value.numerator.toNat * (gridPredecessor + 1) * (gridPredecessor + 1))
    (value.denominatorPredecessor + 1)).fst

/-- The rational √-approximation on the grid `1/(g+1)`: `natSqrt m / (g+1)`. -/
def rationalSqrtApprox (value : RationalPair) (gridPredecessor : Nat) : RationalPair :=
  ratioOfNatSucc (natSqrt (rationalSqrtRadicand value gridPredecessor)) gridPredecessor

/-- **Lower square bracket** `s² ≤ q` (needs `0 ≤ q`): the floored quotient underruns
the scaled radicand and `natSqrt` underruns the quotient, so the whole square is below.
As an `Int` cross-multiplication `s²·(e+1) ≤ p·(g+1)²`. -/
theorem rationalSqrtApproxSqLe {value : RationalPair} (gridPredecessor : Nat)
    (isNonNegative : IsNonNegative value) :
    LessEqualAs
      (mulExact (rationalSqrtApprox value gridPredecessor)
        (rationalSqrtApprox value gridPredecessor))
      value :=
  let clampedNumerator := value.numerator.toNat
  let gridSuccessor := gridPredecessor + 1
  let denominatorSuccessor := value.denominatorPredecessor + 1
  let scaledRadicand := clampedNumerator * gridSuccessor * gridSuccessor
  let flooredQuotient := (natDivModCounting scaledRadicand denominatorSuccessor).fst
  let rootValue := natSqrt flooredQuotient
  let numeratorEquation : value.numerator = Int.ofNat clampedNumerator :=
    (intOfNatToNatOfNonNeg (numeratorNonNegativeOfIsNonNegative isNonNegative)).symm
  let reconstruction :
      scaledRadicand = denominatorSuccessor * flooredQuotient +
        (natDivModCounting scaledRadicand denominatorSuccessor).snd :=
    natDivModCountingReconstructs scaledRadicand denominatorSuccessor
  let rootUnderQuotient : rootValue * rootValue ≤ flooredQuotient :=
    natSqrtLowerBound flooredQuotient
  let scaledRootBelowQuotientScaled :
      rootValue * rootValue * denominatorSuccessor ≤ flooredQuotient * denominatorSuccessor :=
    natMulLeMulRight rootUnderQuotient denominatorSuccessor
  let quotientScaledBelowRadicand :
      flooredQuotient * denominatorSuccessor ≤
        clampedNumerator * (gridSuccessor * gridSuccessor) :=
    natLeOfEqLeft (Nat.mul_comm flooredQuotient denominatorSuccessor)
      (natLeOfEqRight
        (Nat.le.intro (rfl : denominatorSuccessor * flooredQuotient +
          (natDivModCounting scaledRadicand denominatorSuccessor).snd =
          denominatorSuccessor * flooredQuotient +
          (natDivModCounting scaledRadicand denominatorSuccessor).snd))
        (reconstruction.symm.trans
          (natMulAssoc clampedNumerator gridSuccessor gridSuccessor)))
  let natChain :
      rootValue * rootValue * denominatorSuccessor ≤
        clampedNumerator * (gridSuccessor * gridSuccessor) :=
    natLeTrans scaledRootBelowQuotientScaled quotientScaledBelowRadicand
  intLessEqualOfEqRight
    (intOfNatLeOfNat natChain)
    (congrArg (· * (Int.ofNat gridSuccessor * Int.ofNat gridSuccessor))
      numeratorEquation.symm)

/-- **Upper square bracket** `q ≤ ((s+1)/(g+1))²` (needs `0 ≤ q`): the floored quotient
overruns `q` by less than one grid unit, and `natSqrt m < s+1`, so the successor square
overshoots.  As `p·(g+1)² ≤ (s+1)²·(e+1)`. -/
theorem rationalSqrtApproxSuccSqGe {value : RationalPair} (gridPredecessor : Nat)
    (isNonNegative : IsNonNegative value) :
    LessEqualAs value
      (mulExact
        (ratioOfNatSucc (natSqrt (rationalSqrtRadicand value gridPredecessor) + 1)
          gridPredecessor)
        (ratioOfNatSucc (natSqrt (rationalSqrtRadicand value gridPredecessor) + 1)
          gridPredecessor)) :=
  let clampedNumerator := value.numerator.toNat
  let gridSuccessor := gridPredecessor + 1
  let denominatorSuccessor := value.denominatorPredecessor + 1
  let scaledRadicand := clampedNumerator * gridSuccessor * gridSuccessor
  let flooredQuotient := (natDivModCounting scaledRadicand denominatorSuccessor).fst
  let remainder := (natDivModCounting scaledRadicand denominatorSuccessor).snd
  let rootValue := natSqrt flooredQuotient
  let numeratorEquation : value.numerator = Int.ofNat clampedNumerator :=
    (intOfNatToNatOfNonNeg (numeratorNonNegativeOfIsNonNegative isNonNegative)).symm
  let reconstruction :
      scaledRadicand = denominatorSuccessor * flooredQuotient + remainder :=
    natDivModCountingReconstructs scaledRadicand denominatorSuccessor
  let remainderBounded : remainder < denominatorSuccessor :=
    natDivModCountingRemainderIsBounded scaledRadicand denominatorSuccessor
      (Nat.le.intro (Nat.add_comm 1 value.denominatorPredecessor))
  let strictStep :
      (denominatorSuccessor * flooredQuotient + remainder) + 1 ≤
        denominatorSuccessor * flooredQuotient + denominatorSuccessor :=
    natLeOfEqLeft
      (Nat.add_assoc (denominatorSuccessor * flooredQuotient) remainder 1)
      (natAddLeAddLeft remainderBounded (denominatorSuccessor * flooredQuotient))
  let radicandBelowSuccScaled :
      scaledRadicand < denominatorSuccessor * (flooredQuotient + 1) :=
    natLeOfEqLeft (congrArg (· + 1) reconstruction) strictStep
  let quotientSuccUpperBound : flooredQuotient + 1 ≤ (rootValue + 1) * (rootValue + 1) :=
    natSqrtUpperBound flooredQuotient
  let midStep :
      denominatorSuccessor * (flooredQuotient + 1) ≤
        (rootValue + 1) * (rootValue + 1) * denominatorSuccessor :=
    natLeOfEqLeft (Nat.mul_comm denominatorSuccessor (flooredQuotient + 1))
      (natMulLeMulRight quotientSuccUpperBound denominatorSuccessor)
  let radicandBelowRootSuccScaled :
      scaledRadicand ≤ (rootValue + 1) * (rootValue + 1) * denominatorSuccessor :=
    natLeTrans (natLeOfLt radicandBelowSuccScaled) midStep
  let natChain :
      clampedNumerator * (gridSuccessor * gridSuccessor) ≤
        (rootValue + 1) * (rootValue + 1) * denominatorSuccessor :=
    natLeOfEqLeft (natMulAssoc clampedNumerator gridSuccessor gridSuccessor).symm
      radicandBelowRootSuccScaled
  intLessEqualOfEqLeft
    (congrArg (· * (Int.ofNat gridSuccessor * Int.ofNat gridSuccessor)) numeratorEquation)
    (intOfNatLeOfNat natChain)

/-! ## sqrtReal — the sampling scaffolding (NUM-R-SQRT, real layer)

The real square root samples its argument at a QUADRATICALLY deeper index and rounds to
a fixed output grid.  `sqrtSampleIndex n + 1 = (2n+2)² = 4(n+1)²` pre-shrinks the input
drift to `(½·1/(n+1))²` so that the (implicit) root lands at `½·1/(n+1)`; the remaining
half of the regularity budget is spent on the two grid-rounding errors, whose grid step
is `1/(2(n+1)) = reciprocalOfSucc (2n+1)`.

The pointwise approximation sequence `sqrtRealApproximation` is defined here and TOTAL
(the clamp in `rationalSqrtApprox` keeps it defined on every real, nonnegative or not).
Packaging it into a `RegularReal` requires the Hölder-½ regularity bound — the genuine
analytic node (see the module report). -/

/-- The quadratic-depth input sample index: `sqrtSampleIndex n + 1 = (2n+2)²`. -/
def sqrtSampleIndex (index : Nat) : Nat :=
  squaredSuccessorPredecessor (2 * index + 1)

/-- The output grid predecessor: grid step `1/(2(n+1)) = reciprocalOfSucc (2n+1)`. -/
def sqrtGridIndex (index : Nat) : Nat := 2 * index + 1

/-- The deep sample index is DEFINITIONALLY the perfect square `(2n+2)²`. -/
theorem sqrtSampleIndexSuccessor (index : Nat) :
    sqrtSampleIndex index + 1 = (2 * index + 2) * (2 * index + 2) := rfl

/-- The comparison index sits below its own deep sample index — the depth-domination
fact the Hölder regularity threads through `a`'s regularity. -/
theorem natSelfLeSqrtSampleIndex (index : Nat) : index ≤ sqrtSampleIndex index :=
  natLeTrans (natSelfLeDoubleSelfSucc index)
    (Nat.le_add_left (2 * index + 1) ((2 * index + 1 + 1) * (2 * index + 1)))

/-- The pointwise rational √-approximation of a regular real: sample deep, round to the
grid.  TOTAL on every real. -/
def sqrtRealApproximation (value : RegularReal) (index : Nat) : RationalPair :=
  rationalSqrtApprox (value.approximation (sqrtSampleIndex index)) (sqrtGridIndex index)

/-! ## The square-reflection bridge (NUM-R-SQRT brick 4)

The Hölder-½ regularity threads the two square brackets `s² ≤ q ≤ (s+grid)²` through
`a`'s own regularity and then must take a SQUARE ROOT of the resulting square bound to
recover a bound on `s` itself.  That √-back step is the rational reflection
`0 ≤ t → s² ≤ t² → s ≤ t`, whose engine is the Int-level strict square monotonicity
of NODE 1.  This section builds the reflection on `RationalPair` (the shape the
regularity consumes) plus the output-nonnegativity fact the whole chain rides on
(`natSqrt m / (g+1)` has an `ofNat` numerator). -/

/-- **Int strict square monotonicity** — `0 ≤ a < b` scales to `a*a < b*b`: below by
the nonnegative left factor (`a*a ≤ a*b`), strictly by the positive right factor
(`a*b < b*b`).  The strict companion of the reflection `intLeOfSqLeSqNonNeg`. -/
theorem intSqLtSqOfNonNegOfLt {lowValue highValue : Int}
    (isLowNonNeg : (0 : Int) ≤ lowValue) (isLessThan : lowValue < highValue) :
    lowValue * lowValue < highValue * highValue :=
  let isHighPositive : (0 : Int) < highValue :=
    intLessThanOfLessEqualOfLessThan isLowNonNeg isLessThan
  let lowSquareBelowMixed : lowValue * lowValue ≤ lowValue * highValue :=
    intMulLeMulLeftOfNonNeg (intLessEqualOfLessThan isLessThan) isLowNonNeg
  let mixedBelowHighSquare : lowValue * highValue < highValue * highValue :=
    intMulLtMulRightOfPos isLessThan isHighPositive
  intLessThanOfLessEqualOfLessThan lowSquareBelowMixed mixedBelowHighSquare

/-- The √-approximation is nonnegative — its numerator is the `ofNat` root `natSqrt m`. -/
theorem rationalSqrtApproxIsNonNegative (value : RationalPair) (gridPredecessor : Nat) :
    IsNonNegative (rationalSqrtApprox value gridPredecessor) :=
  ratioOfNatSuccIsNonNegative
    (natSqrt (rationalSqrtRadicand value gridPredecessor)) gridPredecessor

/-- **Rational strict square monotonicity** — `0 ≤ s < t` gives `s² < t²` on
`RationalPair`.  Cross-multiplication turns the mulExact square into the Int square
`(s.num·den t)² < (t.num·den s)²` after `intMulSwapMiddle` regroups the four factors;
`intSqLtSqOfNonNegOfLt` then discharges it (the cross product `s.num·den t` is
nonnegative because both factors are). -/
theorem mulExactLtSquareOfNonNegOfLt {lowValue highValue : RationalPair}
    (isLowNonNeg : IsNonNegative lowValue)
    (isLessThan : LessThanAs lowValue highValue) :
    LessThanAs (mulExact lowValue lowValue) (mulExact highValue highValue) :=
  let crossLow : Int := lowValue.numerator * denominatorInt highValue
  let crossHigh : Int := highValue.numerator * denominatorInt lowValue
  let isCrossLowNonNeg : (0 : Int) ≤ crossLow :=
    intLessEqualOfEqLeft (intZeroMul (denominatorInt highValue)).symm
      (intMulLeMulRightOfNonNeg (numeratorNonNegativeOfIsNonNegative isLowNonNeg)
        (intLessEqualOfLessThan (denominatorIntIsPositive highValue)))
  let squaresOrdered : crossLow * crossLow < crossHigh * crossHigh :=
    intSqLtSqOfNonNegOfLt isCrossLowNonNeg isLessThan
  let regroupLow :
      lowValue.numerator * lowValue.numerator *
          (denominatorInt highValue * denominatorInt highValue) =
        crossLow * crossLow :=
    intMulSwapMiddle lowValue.numerator lowValue.numerator
      (denominatorInt highValue) (denominatorInt highValue)
  let regroupHigh :
      highValue.numerator * highValue.numerator *
          (denominatorInt lowValue * denominatorInt lowValue) =
        crossHigh * crossHigh :=
    intMulSwapMiddle highValue.numerator highValue.numerator
      (denominatorInt lowValue) (denominatorInt lowValue)
  intLessThanOfEqLeft regroupLow
    (intLessThanOfEqRight squaresOrdered regroupHigh.symm)

/-- **The rational square reflection** (√-back) — `0 ≤ t` and `s² ≤ t²` give `s ≤ t`.
By trichotomy: `s < t` or `s = t` land directly; the reversed `t < s` would force
`t² < s²` (strict monotonicity above), contradicting `s² ≤ t²` by irreflexivity.
This is THE consumer of NODE 1 the Hölder regularity takes its square root with. -/
theorem lessEqualAsOfMulExactSquareLeNonNeg {lowValue highValue : RationalPair}
    (isHighNonNeg : IsNonNegative highValue)
    (areSquaresOrdered :
      LessEqualAs (mulExact lowValue lowValue) (mulExact highValue highValue)) :
    LessEqualAs lowValue highValue :=
  match lessThanAsTrichotomy lowValue highValue with
  | .inl isLess => lessEqualAsOfLessThan isLess
  | .inr (.inl isSame) => lessEqualAsOfDenotesSame isSame
  | .inr (.inr isReversed) =>
      let squaresStrict :
          LessThanAs (mulExact highValue highValue) (mulExact lowValue lowValue) :=
        mulExactLtSquareOfNonNegOfLt isHighNonNeg isReversed
      absurd
        (intLessThanOfLessThanOfLessEqual squaresStrict areSquaresOrdered)
        (intLessThanIrrefl
          ((mulExact highValue highValue).numerator *
            denominatorInt (mulExact lowValue lowValue)))

/-! ## Route-B regularity infrastructure (NUM-R-SQRT brick 5)

The honest √-regularity does NOT prove the literal `(u−v)² ≤ |a−b|` (false for
the APPROXIMATE roots — the brackets carry a grid unit of slack each).  It
instead bounds each root by the other plus the full modulus, ONE-SIDEDLY, via
the shipped square reflection: from `s_i² ≤ (s_j + budget)²` and nonnegativity
of `s_j + budget`, reflect to `s_i ≤ s_j + budget`, then shunt to the two-sided
`IsWithinBound`.  This section ships the four magnitude-free arithmetic bricks
that thread the budget: the "value sits below itself plus a nonnegative", the
`a² + b² ≤ (a + b)²` cross-term drop, the reverse shunt
`s ≤ l + b → s − l ≤ b`, and the two DEFINITIONAL modulus identities linking the
quadratic sample depth and the output grid step to the reciprocal budget. -/

/-- A value sits below itself plus any nonnegative addend — `v ≤ v + d` from
`0 ≤ d`.  The zero-addend self-distance relaxed by right monotonicity. -/
theorem lessEqualAsSelfAddNonNegRight (baseValue : RationalPair)
    {addend : RationalPair} (isAddendNonNegative : IsNonNegative addend) :
    LessEqualAs baseValue (addExact baseValue addend) :=
  lessEqualAsCongrLeft (addExactZeroRight baseValue)
    (addExactMonotoneRight baseValue isAddendNonNegative)

/-- **The cross-term drop** `a² + b² ≤ (a + b)²` for nonnegative `a, b`:
`a² ≤ (a+b)·a` and `b² ≤ (a+b)·b` (product monotonicity on nonnegatives), add,
and refold the right side by left distribution.  The whole polynomial
domination of the √-regularity is two instances of this. -/
theorem sumSquaresLeSquareSumNonNeg {leftValue rightValue : RationalPair}
    (isLeftNonNegative : IsNonNegative leftValue)
    (isRightNonNegative : IsNonNegative rightValue) :
    LessEqualAs
      (addExact (mulExact leftValue leftValue) (mulExact rightValue rightValue))
      (mulExact (addExact leftValue rightValue) (addExact leftValue rightValue)) :=
  let sumValue := addExact leftValue rightValue
  let isSumNonNegative : IsNonNegative sumValue :=
    addExactIsNonNegative isLeftNonNegative isRightNonNegative
  let isLeftBelowSum : LessEqualAs leftValue sumValue :=
    lessEqualAsSelfAddNonNegRight leftValue isRightNonNegative
  let isRightBelowSum : LessEqualAs rightValue sumValue :=
    lessEqualAsCongrRight (addExactComm rightValue leftValue)
      (lessEqualAsSelfAddNonNegRight rightValue isLeftNonNegative)
  let leftSquareBelow :
      LessEqualAs (mulExact leftValue leftValue) (mulExact sumValue leftValue) :=
    mulExactMonotoneOfNonNegative isLeftBelowSum (lessEqualAsRefl leftValue)
      isLeftNonNegative isSumNonNegative
  let rightSquareBelow :
      LessEqualAs (mulExact rightValue rightValue) (mulExact sumValue rightValue) :=
    mulExactMonotoneOfNonNegative isRightBelowSum (lessEqualAsRefl rightValue)
      isRightNonNegative isSumNonNegative
  lessEqualAsCongrRight
    (denotesSameAsSymm (mulExactLeftDistrib sumValue leftValue rightValue))
    (addExactMonotone leftSquareBelow rightSquareBelow)

/-- **The reverse shunt** `s ≤ l + b → s − l ≤ b` — the converse of the shipped
`lessEqualAsAddOfSubLessEqual`.  Add `−l` to both sides; the right side's
`(l + b) + (−l)` collapses to `b` through the additive group laws. -/
theorem lessEqualAsSubOfLessEqualAdd {highValue lowValue bound : RationalPair}
    (isBelowShifted : LessEqualAs highValue (addExact lowValue bound)) :
    LessEqualAs (subExact highValue lowValue) bound :=
  let cancels :
      DenotesSameAs (addExact (addExact lowValue bound) (negExact lowValue))
        bound :=
    denotesSameAsTrans
      (addExactRespectsDenotesSameAs (addExactComm lowValue bound)
        (denotesSameAsRefl (negExact lowValue)))
      (denotesSameAsTrans
        (addExactAssoc bound lowValue (negExact lowValue))
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs (denotesSameAsRefl bound)
            (addExactNegRight lowValue))
          (addExactZeroRight bound)))
  lessEqualAsCongrRight cancels
    (addExactMonotoneLeft (negExact lowValue) isBelowShifted)

/-- **The quadratic-depth modulus identity** — the input drift budget
`1/(sqrtSampleIndex i + 1)` IS the square of the output grid step
`1/(sqrtGridIndex i + 1)`.  DEFINITIONAL: `sqrtSampleIndex i + 1 = (2i+2)²` and
`mulExact`'s denominator IS the product of denominators, so both cross-products
are `1 · (2i+2)²`. -/
theorem recipSampleDenotesGridSquare (index : Nat) :
    DenotesSameAs (reciprocalOfSucc (sqrtSampleIndex index))
      (mulExact (reciprocalOfSucc (sqrtGridIndex index))
        (reciprocalOfSucc (sqrtGridIndex index))) :=
  rfl

/-- **The output-grid halving identity** — the reciprocal budget `1/(i+1)` at
the comparison index denotes twice the output grid step: `1/(i+1) = 2/(2i+2)`,
and the two halves re-split as the SUM of two grid steps. -/
theorem reciprocalDenotesGridSum (index : Nat) :
    DenotesSameAs (reciprocalOfSucc index)
      (addExact (reciprocalOfSucc (sqrtGridIndex index))
        (reciprocalOfSucc (sqrtGridIndex index))) :=
  denotesSameAsTrans (reciprocalHalvesDenotesSame index)
    (denotesSameAsSymm (ratioOfNatSuccSumDenotesSame 1 1 (2 * index + 1)))

/-! ## sqrtReal — the packaged regular real (NUM-R-SQRT brick 6)

Nonnegativity of the ARGUMENT enters as the pointwise predicate
`IsNonNegativeReal` — every rational approximant is nonnegative, exactly the
hypothesis the two square brackets consume.  (This is stronger than Bishop
nonnegativity and NOT setoid-stable; the mathematically-clean
`0 ≤_ℝ value → IsNonNegativeReal (canonicalise value)` reduction is deferred —
it needs a clamp-Lipschitz bracket that is out of this node's scope.)

The regularity is route B: at comparison indices `i, j`, bound each root by the
other plus the full modulus `1/(i+1) + 1/(j+1)` one-sidedly.  The magnitude-free
budget threads because the quadratic sample depth pre-shrinks the input drift to
`gridStep²` (`recipSampleDenotesGridSquare`), and the two grid roundings fit the
remaining half of the modulus (`reciprocalDenotesGridSum`); the polynomial
domination is two `sumSquaresLeSquareSumNonNeg` drops and the √-back is the
shipped `lessEqualAsOfMulExactSquareLeNonNeg`. -/

/-- **Pointwise nonnegativity** of a real — every rational approximant is
nonnegative.  The argument-side hypothesis the square brackets consume. -/
def IsNonNegativeReal (value : RegularReal) : Prop :=
  ∀ index : Nat, IsNonNegative (value.approximation index)

/-- **The one-sided √-regularity** (route B): `s_i − s_j ≤ 1/(i+1) + 1/(j+1)`.
Chain `s_i² ≤ q_i ≤ q_j + drift ≤ (s_j + gridStep)² + gridSum² ≤ (s_j + budget)²`
then reflect and shunt; the two-sided `IsWithinBound` is this with `i, j`
swapped. -/
theorem sqrtRealApproximationDifferenceBounded {value : RegularReal}
    (isNonNegativeReal : IsNonNegativeReal value) (firstIndex secondIndex : Nat) :
    LessEqualAs
      (subExact (sqrtRealApproximation value firstIndex)
        (sqrtRealApproximation value secondIndex))
      (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex)) :=
  let gridStepFirst := reciprocalOfSucc (sqrtGridIndex firstIndex)
  let gridStepSecond := reciprocalOfSucc (sqrtGridIndex secondIndex)
  let rootFirst := sqrtRealApproximation value firstIndex
  let rootSecond := sqrtRealApproximation value secondIndex
  let sampleFirst := value.approximation (sqrtSampleIndex firstIndex)
  let sampleSecond := value.approximation (sqrtSampleIndex secondIndex)
  let inputBound := addExact (reciprocalOfSucc (sqrtSampleIndex firstIndex))
    (reciprocalOfSucc (sqrtSampleIndex secondIndex))
  let successorRoot := addExact rootSecond gridStepSecond
  let remainingBudget :=
    addExact (addExact gridStepFirst gridStepFirst) gridStepSecond
  let budgetHalf := addExact (addExact gridStepFirst gridStepFirst)
    (addExact gridStepSecond gridStepSecond)
  let isSampleFirstNonNeg : IsNonNegative sampleFirst :=
    isNonNegativeReal (sqrtSampleIndex firstIndex)
  let isSampleSecondNonNeg : IsNonNegative sampleSecond :=
    isNonNegativeReal (sqrtSampleIndex secondIndex)
  let isRootSecondNonNeg : IsNonNegative rootSecond :=
    rationalSqrtApproxIsNonNegative sampleSecond (sqrtGridIndex secondIndex)
  let isGridFirstNonNeg : IsNonNegative gridStepFirst :=
    ratioOfNatSuccIsNonNegative 1 (sqrtGridIndex firstIndex)
  let isGridSecondNonNeg : IsNonNegative gridStepSecond :=
    ratioOfNatSuccIsNonNegative 1 (sqrtGridIndex secondIndex)
  let isSuccessorRootNonNeg : IsNonNegative successorRoot :=
    addExactIsNonNegative isRootSecondNonNeg isGridSecondNonNeg
  let isRemainingBudgetNonNeg : IsNonNegative remainingBudget :=
    addExactIsNonNegative
      (addExactIsNonNegative isGridFirstNonNeg isGridFirstNonNeg)
      isGridSecondNonNeg
  let isBudgetHalfNonNeg : IsNonNegative budgetHalf :=
    addExactIsNonNegative
      (addExactIsNonNegative isGridFirstNonNeg isGridFirstNonNeg)
      (addExactIsNonNegative isGridSecondNonNeg isGridSecondNonNeg)
  let lowerBracket : LessEqualAs (mulExact rootFirst rootFirst) sampleFirst :=
    rationalSqrtApproxSqLe (sqrtGridIndex firstIndex) isSampleFirstNonNeg
  let successorToRoot :
      DenotesSameAs
        (ratioOfNatSucc
          (natSqrt
              (rationalSqrtRadicand sampleSecond (sqrtGridIndex secondIndex)) + 1)
          (sqrtGridIndex secondIndex))
        successorRoot :=
    denotesSameAsSymm
      (ratioOfNatSuccSumDenotesSame
        (natSqrt (rationalSqrtRadicand sampleSecond (sqrtGridIndex secondIndex)))
        1 (sqrtGridIndex secondIndex))
  let upperBracket :
      LessEqualAs sampleSecond (mulExact successorRoot successorRoot) :=
    lessEqualAsCongrRight
      (mulExactRespectsDenotesSameAs successorToRoot successorToRoot)
      (rationalSqrtApproxSuccSqGe (sqrtGridIndex secondIndex)
        isSampleSecondNonNeg)
  let inputRegular : IsWithinBound sampleFirst sampleSecond inputBound :=
    value.isRegular (sqrtSampleIndex firstIndex) (sqrtSampleIndex secondIndex)
  let sampleFirstShifted :
      LessEqualAs sampleFirst (addExact sampleSecond inputBound) :=
    lessEqualAsAddOfSubLessEqual inputRegular.left
  let inputBoundAsSquares :
      DenotesSameAs inputBound
        (addExact (mulExact gridStepFirst gridStepFirst)
          (mulExact gridStepSecond gridStepSecond)) :=
    addExactRespectsDenotesSameAs (recipSampleDenotesGridSquare firstIndex)
      (recipSampleDenotesGridSquare secondIndex)
  let gridSumBelowRemaining :
      LessEqualAs (addExact gridStepFirst gridStepSecond) remainingBudget :=
    addExactMonotoneLeft gridStepSecond
      (lessEqualAsSelfAddNonNegRight gridStepFirst isGridFirstNonNeg)
  let isGridSumNonNeg : IsNonNegative (addExact gridStepFirst gridStepSecond) :=
    addExactIsNonNegative isGridFirstNonNeg isGridSecondNonNeg
  let squareOfGridSumBelow :
      LessEqualAs
        (mulExact (addExact gridStepFirst gridStepSecond)
          (addExact gridStepFirst gridStepSecond))
        (mulExact remainingBudget remainingBudget) :=
    mulExactMonotoneOfNonNegative gridSumBelowRemaining gridSumBelowRemaining
      isGridSumNonNeg isRemainingBudgetNonNeg
  let inputBoundBelowRemainingSquare :
      LessEqualAs inputBound (mulExact remainingBudget remainingBudget) :=
    lessEqualAsCongrLeft (denotesSameAsSymm inputBoundAsSquares)
      (lessEqualAsTrans
        (sumSquaresLeSquareSumNonNeg isGridFirstNonNeg isGridSecondNonNeg)
        squareOfGridSumBelow)
  let radicandBelowSquare :
      LessEqualAs (mulExact rootFirst rootFirst)
        (mulExact (addExact successorRoot remainingBudget)
          (addExact successorRoot remainingBudget)) :=
    lessEqualAsTrans lowerBracket
      (lessEqualAsTrans sampleFirstShifted
        (lessEqualAsTrans (addExactMonotoneLeft inputBound upperBracket)
          (lessEqualAsTrans
            (addExactMonotoneRight (mulExact successorRoot successorRoot)
              inputBoundBelowRemainingSquare)
            (sumSquaresLeSquareSumNonNeg isSuccessorRootNonNeg
              isRemainingBudgetNonNeg))))
  let sumReassociates :
      DenotesSameAs (addExact successorRoot remainingBudget)
        (addExact rootSecond budgetHalf) :=
    denotesSameAsTrans
      (addExactAssoc rootSecond gridStepSecond remainingBudget)
      (addExactRespectsDenotesSameAs (denotesSameAsRefl rootSecond)
        (denotesSameAsTrans (addExactComm gridStepSecond remainingBudget)
          (addExactAssoc (addExact gridStepFirst gridStepFirst) gridStepSecond
            gridStepSecond)))
  let radicandBelowBudgetSquare :
      LessEqualAs (mulExact rootFirst rootFirst)
        (mulExact (addExact rootSecond budgetHalf)
          (addExact rootSecond budgetHalf)) :=
    lessEqualAsCongrRight
      (mulExactRespectsDenotesSameAs sumReassociates sumReassociates)
      radicandBelowSquare
  let rootBelowShifted :
      LessEqualAs rootFirst (addExact rootSecond budgetHalf) :=
    lessEqualAsOfMulExactSquareLeNonNeg
      (addExactIsNonNegative isRootSecondNonNeg isBudgetHalfNonNeg)
      radicandBelowBudgetSquare
  let differenceBelowBudgetHalf :
      LessEqualAs (subExact rootFirst rootSecond) budgetHalf :=
    lessEqualAsSubOfLessEqualAdd rootBelowShifted
  lessEqualAsCongrRight
    (denotesSameAsSymm
      (addExactRespectsDenotesSameAs (reciprocalDenotesGridSum firstIndex)
        (reciprocalDenotesGridSum secondIndex)))
    differenceBelowBudgetHalf

/-- **The √-approximation sequence is regular** — the two-sided bound from the
one-sided route-B lemma and its index swap. -/
theorem sqrtRealApproximationIsRegular {value : RegularReal}
    (isNonNegativeReal : IsNonNegativeReal value) (firstIndex secondIndex : Nat) :
    IsWithinBound (sqrtRealApproximation value firstIndex)
      (sqrtRealApproximation value secondIndex)
      (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex)) :=
  ⟨sqrtRealApproximationDifferenceBounded isNonNegativeReal firstIndex
      secondIndex,
    lessEqualAsCongrRight
      (addExactComm (reciprocalOfSucc secondIndex) (reciprocalOfSucc firstIndex))
      (sqrtRealApproximationDifferenceBounded isNonNegativeReal secondIndex
        firstIndex)⟩

/-- **The constructive square root** on a pointwise-nonnegative regular real —
a genuine `RegularReal` with a real `isRegular` field. -/
def sqrtReal (value : RegularReal) (isNonNegativeReal : IsNonNegativeReal value) :
    RegularReal :=
  { approximation := sqrtRealApproximation value
    isRegular := sqrtRealApproximationIsRegular isNonNegativeReal }

end FX1Poly.ComputerAlgebra
