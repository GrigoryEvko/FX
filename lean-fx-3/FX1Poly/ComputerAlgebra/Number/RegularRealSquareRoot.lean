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

end FX1Poly.ComputerAlgebra
