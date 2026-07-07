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

end FX1Poly.ComputerAlgebra
