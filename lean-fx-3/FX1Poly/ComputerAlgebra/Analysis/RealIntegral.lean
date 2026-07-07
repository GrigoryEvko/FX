import FX1Poly.ComputerAlgebra.Analysis.RealFiniteSum
import FX1Poly.ComputerAlgebra.Analysis.RealContinuity

/-! # The constructive integral — Riemann sums of a uniformly continuous map
    (ANALYSIS-INTEGRAL-1)

The calculus rung above the finite sum.  For a rational interval
`[lowerBound, upperBound]` cut into `cellCountPredecessor + 1` equal cells, the
LEFT-endpoint Riemann sum of a function `RegularReal -> RegularReal` is

    meshWidth * Sigma_{cell} function (sample cell)

with `meshWidth = (upperBound - lowerBound) / cellCount` a RATIONAL scale (all
division symbolic in the `RationalPair` denominator, never evaluated) and the
sample points rational, embedded through `constantReal`.

This file lands the Riemann-sum FUNCTIONAL and its exact algebraic laws — the
half of the integral that is pure ring reshaping over the shipped finite-sum
corpus, no analysis:

  * the constant-real homomorphisms `constantReal (p + q) ~ constantReal p +
    constantReal q` and `constantReal (p * q) ~ constantReal p * constantReal q`
    (both hold by DEFINITIONAL reduction of the constant approximations —
    self-distance closes them), and the natural-scaling law
    `Sigma_{k} X ~ (natRational k) * X`;
  * **linearity of the Riemann sum** in the integrand
    `R(f + g) = R f + R g` and `R(c * f) = c * R f` — left-distribution and
    associativity/commutativity over the sampled finite sum;
  * **the exact constant Riemann sum** `R (fun _ => c) ~ (upperBound -
    lowerBound) * c` — the mesh times the cell count telescopes to the interval
    width EXACTLY, independent of the partition, so the constant integrand's
    Riemann sequence is setoid-constant.

The analytic half — the uniform-continuity Cauchy estimate that turns the
Riemann sequence into a `RegularRealSequence` and feeds `limitReal` to build
`integralOfUC` — is the genuine common-refinement content and is NOT in this
file (see the module note at the end).  Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Constant-real homomorphisms -/

/-- **The constant embedding carries addition** — both approximations reduce
DEFINITIONALLY to `addExact p q`, so the setoid bound is self-distance. -/
theorem constantRealAddExact (leftValue rightValue : RationalPair) :
    DenotesSameReal (constantReal (addExact leftValue rightValue))
      (addReal (constantReal leftValue) (constantReal rightValue)) :=
  fun index =>
    isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 index)

/-- **The constant embedding carries multiplication** — both approximations
reduce DEFINITIONALLY to `mulExact p q`, so the setoid bound is self-distance. -/
theorem constantRealMulExact (leftValue rightValue : RationalPair) :
    DenotesSameReal (constantReal (mulExact leftValue rightValue))
      (mulReal (constantReal leftValue) (constantReal rightValue)) :=
  fun index =>
    isWithinBoundSelfOfNonNegative (ratioOfNatSuccIsNonNegative 2 index)

/-- The natural number as a rational — `count / 1`. -/
def natRational (count : Nat) : RationalPair :=
  ratioOfNatSucc count 0

/-- `count + 1` as a rational denotes `count` plus one — the numerator
successor is definitional on the `ofNat` payload. -/
theorem natRationalSuccDenotesSame (count : Nat) :
    DenotesSameAs (natRational (count + 1))
      (addExact (natRational count) oneRational) :=
  (intMulOne (Int.ofNat (count + 1))).trans
    (((intMulOne (Int.ofNat count * Int.ofNat 1 + 1 * Int.ofNat 1)).trans
        ((congrArg (· + (1 : Int) * Int.ofNat 1)
            (intMulOne (Int.ofNat count))).trans
          (congrArg (Int.ofNat count + ·) (intMulOne (1 : Int))))).symm)

/-- **The natural scaling law**: summing `count` copies of a real denotes that
real times the natural `count`.  Induction on `count`, closing the step by
right-distribution and the one-identity. -/
theorem replicateRealEqScale (value : RegularReal) (count : Nat) :
    DenotesSameReal (sumReal count (fun _ => value))
      (mulReal (constantReal (natRational count)) value) :=
  match count with
  | 0 => denotesSameRealSymm (mulRealZeroLeft value)
  | count + 1 =>
      denotesSameRealTrans
        (addRealRespectsDenotesSame
          (replicateRealEqScale value count)
          (denotesSameRealRefl value))
        (denotesSameRealSymm
          (denotesSameRealTrans
            (mulRealRespectsDenotesSame
              (denotesSameRealTrans
                (constantRealRespectsDenotesSame
                  (natRationalSuccDenotesSame count))
                (constantRealAddExact (natRational count) oneRational))
              (denotesSameRealRefl value))
            (denotesSameRealTrans
              (mulRealRightDistrib (constantReal (natRational count))
                (constantReal oneRational) value)
              (addRealRespectsDenotesSame
                (denotesSameRealRefl
                  (mulReal (constantReal (natRational count)) value))
                (mulRealOneLeft value)))))

/-! ## The rational mesh and sample points -/

/-- **The mesh width** — the interval width scaled by `1 / cellCount`, a purely
symbolic rational (the denominator carries the division, never evaluated). -/
def meshWidth (lowerBound upperBound : RationalPair) (cellCountPredecessor : Nat) :
    RationalPair :=
  mulExact (subExact upperBound lowerBound)
    (reciprocalOfSucc cellCountPredecessor)

/-- **The left endpoint of cell `cellIndex`** — `lowerBound + cellIndex *
meshWidth`. -/
def samplePoint (lowerBound upperBound : RationalPair)
    (cellCountPredecessor cellIndex : Nat) : RationalPair :=
  addExact lowerBound
    (mulExact (natRational cellIndex)
      (meshWidth lowerBound upperBound cellCountPredecessor))

/-- **The cell count times the mesh width telescopes to the interval width** —
`(cellCount) * (upperBound - lowerBound)/cellCount ~ upperBound - lowerBound`. -/
theorem cellCountMeshWidthDenotesSame (lowerBound upperBound : RationalPair)
    (cellCountPredecessor : Nat) :
    DenotesSameAs
      (mulExact (natRational (cellCountPredecessor + 1))
        (meshWidth lowerBound upperBound cellCountPredecessor))
      (subExact upperBound lowerBound) :=
  have reciprocalCancels :
      DenotesSameAs
        (mulExact (natRational (cellCountPredecessor + 1))
          (reciprocalOfSucc cellCountPredecessor))
        oneRational :=
    have oneMulReducesDenominator :
        (1 : Int) *
            denominatorInt
              (mulExact (natRational (cellCountPredecessor + 1))
                (reciprocalOfSucc cellCountPredecessor)) =
          Int.ofNat (cellCountPredecessor + 1) :=
      (intOneMul
          (denominatorInt
            (mulExact (natRational (cellCountPredecessor + 1))
              (reciprocalOfSucc cellCountPredecessor)))).trans
        (congrArg Int.ofNat
          (congrArg (· + 1) (Nat.one_mul cellCountPredecessor)))
    (((intMulOne (Int.ofNat (cellCountPredecessor + 1) * Int.ofNat 1)).trans
          (intMulOne (Int.ofNat (cellCountPredecessor + 1)))).trans
      oneMulReducesDenominator.symm)
  denotesSameAsTrans
    (denotesSameAsSymm
      (mulExactAssoc (natRational (cellCountPredecessor + 1))
        (subExact upperBound lowerBound)
        (reciprocalOfSucc cellCountPredecessor)))
    (denotesSameAsTrans
      (mulExactCongrLeft (reciprocalOfSucc cellCountPredecessor)
        (mulExactComm (natRational (cellCountPredecessor + 1))
          (subExact upperBound lowerBound)))
      (denotesSameAsTrans
        (mulExactAssoc (subExact upperBound lowerBound)
          (natRational (cellCountPredecessor + 1))
          (reciprocalOfSucc cellCountPredecessor))
        (denotesSameAsTrans
          (mulExactCongrRight (subExact upperBound lowerBound) reciprocalCancels)
          (mulExactOneRight (subExact upperBound lowerBound)))))

/-! ## The Riemann sum functional -/

/-- **The left-endpoint Riemann sum** — `meshWidth` times the sum of the
function at the `cellCount` left endpoints. -/
def riemannSum (function : RegularReal → RegularReal)
    (lowerBound upperBound : RationalPair) (cellCountPredecessor : Nat) :
    RegularReal :=
  mulReal (constantReal (meshWidth lowerBound upperBound cellCountPredecessor))
    (sumReal (cellCountPredecessor + 1)
      (fun cellIndex =>
        function
          (constantReal
            (samplePoint lowerBound upperBound cellCountPredecessor cellIndex))))

/-- **Linearity — additivity**: the Riemann sum of a pointwise sum is the sum of
the Riemann sums.  The mesh distributes over the additive finite sum. -/
theorem riemannSumAddReal (leftFunction rightFunction : RegularReal → RegularReal)
    (lowerBound upperBound : RationalPair) (cellCountPredecessor : Nat) :
    DenotesSameReal
      (riemannSum (fun value => addReal (leftFunction value) (rightFunction value))
        lowerBound upperBound cellCountPredecessor)
      (addReal (riemannSum leftFunction lowerBound upperBound cellCountPredecessor)
        (riemannSum rightFunction lowerBound upperBound cellCountPredecessor)) :=
  denotesSameRealTrans
    (mulRealRespectsDenotesSame
      (denotesSameRealRefl
        (constantReal (meshWidth lowerBound upperBound cellCountPredecessor)))
      (sumRealAddReal
        (fun cellIndex =>
          leftFunction
            (constantReal
              (samplePoint lowerBound upperBound cellCountPredecessor cellIndex)))
        (fun cellIndex =>
          rightFunction
            (constantReal
              (samplePoint lowerBound upperBound cellCountPredecessor cellIndex)))
        (cellCountPredecessor + 1)))
    (mulRealLeftDistrib
      (constantReal (meshWidth lowerBound upperBound cellCountPredecessor))
      (sumReal (cellCountPredecessor + 1)
        (fun cellIndex =>
          leftFunction
            (constantReal
              (samplePoint lowerBound upperBound cellCountPredecessor cellIndex))))
      (sumReal (cellCountPredecessor + 1)
        (fun cellIndex =>
          rightFunction
            (constantReal
              (samplePoint lowerBound upperBound cellCountPredecessor cellIndex)))))

/-- **Linearity — homogeneity**: the Riemann sum of a scaled function is the
scaled Riemann sum.  The scalar pulls through the finite sum, then commutes past
the mesh factor. -/
theorem riemannSumScalarMulReal (factor : RegularReal)
    (function : RegularReal → RegularReal)
    (lowerBound upperBound : RationalPair) (cellCountPredecessor : Nat) :
    DenotesSameReal
      (riemannSum (fun value => mulReal factor (function value))
        lowerBound upperBound cellCountPredecessor)
      (mulReal factor
        (riemannSum function lowerBound upperBound cellCountPredecessor)) :=
  let meshFactor :=
    constantReal (meshWidth lowerBound upperBound cellCountPredecessor)
  let sampledSum :=
    sumReal (cellCountPredecessor + 1)
      (fun cellIndex =>
        function
          (constantReal
            (samplePoint lowerBound upperBound cellCountPredecessor cellIndex)))
  denotesSameRealTrans
    (mulRealRespectsDenotesSame (denotesSameRealRefl meshFactor)
      (sumRealScalarMulReal factor
        (fun cellIndex =>
          function
            (constantReal
              (samplePoint lowerBound upperBound cellCountPredecessor cellIndex)))
        (cellCountPredecessor + 1)))
    (denotesSameRealTrans
      (denotesSameRealSymm (mulRealAssoc meshFactor factor sampledSum))
      (denotesSameRealTrans
        (mulRealRespectsDenotesSame (mulRealComm meshFactor factor)
          (denotesSameRealRefl sampledSum))
        (mulRealAssoc factor meshFactor sampledSum)))

/-- **The exact constant Riemann sum** — the Riemann sum of a constant function
denotes `(upperBound - lowerBound) * constantValue`, independent of the
partition.  The mesh times the cell count telescopes to the interval width. -/
theorem riemannSumConstant (constantValue : RegularReal)
    (lowerBound upperBound : RationalPair) (cellCountPredecessor : Nat) :
    DenotesSameReal
      (riemannSum (fun _ => constantValue) lowerBound upperBound
        cellCountPredecessor)
      (mulReal (constantReal (subExact upperBound lowerBound)) constantValue) :=
  denotesSameRealTrans
    (mulRealRespectsDenotesSame
      (denotesSameRealRefl
        (constantReal (meshWidth lowerBound upperBound cellCountPredecessor)))
      (replicateRealEqScale constantValue (cellCountPredecessor + 1)))
    (denotesSameRealTrans
      (denotesSameRealSymm
        (mulRealAssoc
          (constantReal (meshWidth lowerBound upperBound cellCountPredecessor))
          (constantReal (natRational (cellCountPredecessor + 1)))
          constantValue))
      (mulRealRespectsDenotesSame
        (denotesSameRealTrans
          (mulRealRespectsDenotesSame
            (denotesSameRealRefl
              (constantReal
                (meshWidth lowerBound upperBound cellCountPredecessor)))
            (denotesSameRealRefl
              (constantReal (natRational (cellCountPredecessor + 1)))))
          (denotesSameRealTrans
            (denotesSameRealSymm
              (constantRealMulExact
                (meshWidth lowerBound upperBound cellCountPredecessor)
                (natRational (cellCountPredecessor + 1))))
            (constantRealRespectsDenotesSame
              (denotesSameAsTrans
                (mulExactComm
                  (meshWidth lowerBound upperBound cellCountPredecessor)
                  (natRational (cellCountPredecessor + 1)))
                (cellCountMeshWidthDenotesSame lowerBound upperBound
                  cellCountPredecessor)))))
        (denotesSameRealRefl constantValue)))

end FX1Poly.ComputerAlgebra
