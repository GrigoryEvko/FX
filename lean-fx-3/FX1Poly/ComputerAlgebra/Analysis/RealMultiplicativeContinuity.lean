import FX1Poly.ComputerAlgebra.Analysis.RealMultiplicativeLimit
import FX1Poly.ComputerAlgebra.Analysis.RealContinuity

/-! # Real multiplicative continuity — bounded-domain and fixed-factor
    (ANALYSIS-MULCONT-1)

The continuity face of the multiplicative rung, resting on the same real-level
product-difference law `mulRealRespectsIsWithinRealBound`.  Two honest
statements, matching the `RealContinuity` scope note ("`mulReal` uniformly
continuous only on bounded subdomains"):

  * **Bounded-domain, two-variable**: when the left first factor and the right
    second factor are uniformly magnitude-bounded by `(p+1)/1`, shrinking both
    input pairs to `1/(boundScaledIndex p k + 1)` forces the products within
    `1/(k+1)` — the two `(p+1)/1 * eps` legs each collapse to `1/(2k+2)` and
    recombine EXACTLY.  This is the genuine `mulReal` continuity content: no
    fixed modulus works globally (the slope grows), so the domain bound `p`
    enters the modulus.

  * **Fixed-factor, global**: `value |-> factor * value` is globally uniformly
    continuous (Lipschitz-`|factor|`), because the second telescope leg
    `(factor - factor) * value` vanishes.  With the factor magnitude-bounded by
    `(p+1)/1`, the single surviving leg `(p+1)/1 * eps` collapses EXACTLY to
    `1/(k+1)` at the factor-scaled input precision, and the vanishing leg's
    `L * 0` drops.  Packaged as `IsUniformlyContinuous`.

Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Fixed-factor scale collapse and the zero-leg drop -/

namespace RationalPair

/-- The factor-scaled sampling index: `factorScaledIndex bp i + 1` is
DEFINITIONALLY `(bp+1)*(i+1)` — the single-leg analogue of `boundScaledIndex`
(no factor of two), so the bound's numerator cancels the scaled denominator to
the reciprocal ON THE NOSE. -/
def factorScaledIndex (boundPredecessor index : Nat) : Nat :=
  (boundPredecessor + 1) * index + boundPredecessor

/-- **The fixed-factor scale collapse**: `(bp+1)/1 * 1/(factorScaledIndex bp i + 1)`
denotes `1/(i+1)` — the numerator `bp+1` cancels the scaled denominator
`(bp+1)*(i+1)`.  A setoid identity, not an estimate. -/
theorem factorReciprocalScaledCollapses (boundPredecessor index : Nat) :
    DenotesSameAs
      (mulExact (ratioOfNatSucc (boundPredecessor + 1) 0)
        (reciprocalOfSucc (factorScaledIndex boundPredecessor index)))
      (reciprocalOfSucc index) :=
  congrArg Int.ofNat
    (((congrArg (· * (index + 1)) (Nat.mul_one (boundPredecessor + 1))).trans
        (Nat.mul_succ (boundPredecessor + 1) index)).trans
      ((congrArg (· + 1)
          (Nat.one_mul (factorScaledIndex boundPredecessor index)).symm).trans
        (Nat.one_mul (1 * factorScaledIndex boundPredecessor index + 1)).symm))

/-- **The zero right factor drops**: `value * 0` denotes `0` — the numerator
annihilates, so both cross-products vanish. -/
theorem mulExactZeroRightDenotesSame (value : RationalPair) :
    DenotesSameAs (mulExact value zeroRational) zeroRational :=
  (congrArg (· * denominatorInt zeroRational) (intMulZero value.numerator)).trans
    ((intZeroMul (denominatorInt zeroRational)).trans
      (intZeroMul (denominatorInt (mulExact value zeroRational))).symm)

end RationalPair

/-! ## Bounded-domain two-variable continuity -/

/-- **Multiplication is uniformly continuous on a bounded domain** (two
variables).  With the left first factor and the right second factor uniformly
magnitude-bounded by `(boundPredecessor+1)/1`, shrinking both input pairs within
`1/(boundScaledIndex boundPredecessor outputPrecision + 1)` forces the two
products within `1/(outputPrecision+1)`.  The two product-difference legs
`(boundPredecessor+1)/1 * eps` each collapse to `1/(2k+2)` and recombine to
`1/(k+1)`. -/
theorem mulRealIsWithinRealBoundOnBounded
    {leftFirst leftSecond rightFirst rightSecond : RegularReal}
    (boundPredecessor : Nat)
    (leftFirstBounded : ∀ index,
      IsMagnitudeWithin (leftFirst.approximation index)
        (ratioOfNatSucc (boundPredecessor + 1) 0))
    (rightSecondBounded : ∀ index,
      IsMagnitudeWithin (rightSecond.approximation index)
        (ratioOfNatSucc (boundPredecessor + 1) 0))
    (outputPrecision : Nat)
    (isFirstClose : IsWithinRealBound leftFirst rightFirst
      (reciprocalOfSucc (boundScaledIndex boundPredecessor outputPrecision)))
    (isSecondClose : IsWithinRealBound leftSecond rightSecond
      (reciprocalOfSucc (boundScaledIndex boundPredecessor outputPrecision))) :
    IsWithinRealBound (mulReal leftFirst leftSecond)
      (mulReal rightFirst rightSecond) (reciprocalOfSucc outputPrecision) :=
  isWithinRealBoundCongrBound
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (mulRatioReciprocalScaledCollapses boundPredecessor outputPrecision)
        (mulRatioReciprocalScaledCollapses boundPredecessor outputPrecision))
      (reciprocalDoubleSumDenotesSame outputPrecision))
    (mulRealRespectsIsWithinRealBound (boundPredecessor + 1) (boundPredecessor + 1)
      leftFirstBounded rightSecondBounded isFirstClose isSecondClose
      (ratioOfNatSuccIsNonNegative 1
        (boundScaledIndex boundPredecessor outputPrecision))
      (ratioOfNatSuccIsNonNegative 1
        (boundScaledIndex boundPredecessor outputPrecision)))

/-! ## Fixed-factor global continuity -/

/-- **Fixed-factor multiplication respects the real-level bound**, globally:
`factor * leftValue` vs `factor * rightValue` land within `1/(outputPrecision+1)`
whenever the inputs sit within `1/(factorScaledIndex p outputPrecision + 1)`,
for `factor` magnitude-bounded by `(p+1)/1`.  Only the `factor`-leg survives (the
`(factor - factor)`-leg is fed the zero bound and drops), so the single collapse
lands EXACTLY on `1/(outputPrecision+1)`. -/
theorem scalarMulRealIsWithinRealBound {factor leftValue rightValue : RegularReal}
    (factorBoundPredecessor : Nat)
    (factorBounded : ∀ index,
      IsMagnitudeWithin (factor.approximation index)
        (ratioOfNatSucc (factorBoundPredecessor + 1) 0))
    (outputPrecision : Nat)
    (isClose : IsWithinRealBound leftValue rightValue
      (reciprocalOfSucc (factorScaledIndex factorBoundPredecessor outputPrecision))) :
    IsWithinRealBound (mulReal factor leftValue) (mulReal factor rightValue)
      (reciprocalOfSucc outputPrecision) :=
  isWithinRealBoundCongrBound
    (denotesSameAsTrans
      (addExactRespectsDenotesSameAs
        (factorReciprocalScaledCollapses factorBoundPredecessor outputPrecision)
        (mulExactZeroRightDenotesSame
          (ratioOfNatSucc (canonicalBoundNumerator rightValue) 0)))
      (addExactZeroRight (reciprocalOfSucc outputPrecision)))
    (mulRealRespectsIsWithinRealBound (factorBoundPredecessor + 1)
      (canonicalBoundNumerator rightValue) factorBounded
      (fun index => approximationIsWithinCanonicalBound rightValue index)
      (isWithinRealBoundOfDenotesSameReal (denotesSameRealRefl factor)
        (lessEqualAsRefl zeroRational))
      isClose (lessEqualAsRefl zeroRational)
      (ratioOfNatSuccIsNonNegative 1
        (factorScaledIndex factorBoundPredecessor outputPrecision)))

/-- **Fixed-factor multiplication is uniformly continuous**, globally, with the
factor-scaled modulus — `value |-> factor * value` is Lipschitz-`|factor|`. -/
theorem scalarMulRealIsUniformlyContinuous {factor : RegularReal}
    (factorBoundPredecessor : Nat)
    (factorBounded : ∀ index,
      IsMagnitudeWithin (factor.approximation index)
        (ratioOfNatSucc (factorBoundPredecessor + 1) 0)) :
    IsUniformlyContinuous (fun value => mulReal factor value)
      (fun outputPrecision =>
        factorScaledIndex factorBoundPredecessor outputPrecision) :=
  fun leftValue rightValue outputPrecision isClose =>
    scalarMulRealIsWithinRealBound factorBoundPredecessor factorBounded
      outputPrecision isClose

end FX1Poly.ComputerAlgebra
