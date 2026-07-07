import FX1Poly.ComputerAlgebra.Analysis.RealFiniteSum
import FX1Poly.ComputerAlgebra.Analysis.RealContinuity
import FX1Poly.ComputerAlgebra.Analysis.RealDerivative

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

/-! ## Exact nonnegative-constant scaling (the refinement estimate's ℚ core)

The refinement estimate multiplies a per-term oscillation bound by the mesh
width — a NONNEGATIVE rational constant.  The shipped product-difference law
`mulExactRespectsIsWithinBoundLeft` scales a distance by a MAGNITUDE bound on
the multiplier; feeding it the constant AS ITS OWN magnitude bound
(`IsMagnitudeWithin c c`, which holds exactly when `c ≥ 0`) yields the EXACT
scaled bound `c · q` with no integer-ceiling blow-up.  This is the load-bearing
ℚ-level piece the mesh/count cancellation needs. -/

/-- **A nonnegative rational bounds its own magnitude** — `|c| ≤ c` when
`0 ≤ c`, since `-c ≤ 0 ≤ c`.  This turns the shipped product-difference law
into an EXACT constant scaling. -/
theorem isMagnitudeWithinSelfOfNonNegative {value : RationalPair}
    (isNonNegative : IsNonNegative value) : IsMagnitudeWithin value value :=
  have negativeNumeratorBelowZero : -value.numerator ≤ (0 : Int) :=
    intLessEqualOfEqRight
      (intNegLeNegOfLe (numeratorNonNegativeOfIsNonNegative isNonNegative))
      intNegZero
  have negValueBelowZero : LessEqualAs (negExact value) zeroRational :=
    intLessEqualOfEqRight
      (intMulLeMulRightOfNonNeg negativeNumeratorBelowZero
        (intLessEqualOfLessThan (denominatorIntIsPositive zeroRational)))
      ((intZeroMul (denominatorInt zeroRational)).trans
        (intZeroMul (denominatorInt (negExact value))).symm)
  ⟨lessEqualAsRefl value, lessEqualAsTrans negValueBelowZero isNonNegative⟩

/-- **The exact nonnegative-constant distance scaling**, at ℚ — a within-bound
pair scaled by a nonnegative constant lands within the EXACTLY scaled bound. -/
theorem mulExactRespectsIsWithinBoundConstantLeft {constant leftValue rightValue
    diffBound : RationalPair} (isConstantNonNegative : IsNonNegative constant)
    (isWithin : IsWithinBound leftValue rightValue diffBound)
    (isDiffBoundNonNegative : IsNonNegative diffBound) :
    IsWithinBound (mulExact constant leftValue) (mulExact constant rightValue)
      (mulExact constant diffBound) :=
  mulExactRespectsIsWithinBoundLeft
    (isMagnitudeWithinSelfOfNonNegative isConstantNonNegative) isWithin
    isDiffBoundNonNegative

/-! ## The count-scale telescoping (ℚ) -/

/-- The zeroth natural rational denotes zero — `0/1 ~ 0/1`. -/
theorem natRationalZeroDenotesZero :
    DenotesSameAs (natRational 0) zeroRational := rfl

/-- **The count-scale IS the scalar product** — `count` copies of `bound` added
denote `natRational count · bound`.  Induction on `count`: the base collapses
`0 · bound`, the step adds one `bound` by right-distribution and the one-identity
(the ℚ sibling of the shipped real-level `replicateRealEqScale`). -/
theorem natScaleRationalDenotesScale (count : Nat) (bound : RationalPair) :
    DenotesSameAs (natScaleRational count bound)
      (mulExact (natRational count) bound) :=
  match count with
  | 0 =>
      denotesSameAsSymm
        (denotesSameAsTrans
          (mulExactCongrLeft bound natRationalZeroDenotesZero)
          (mulExactZeroLeftDenotesSame bound))
  | count + 1 =>
      denotesSameAsTrans
        (addExactCongrLeft bound (natScaleRationalDenotesScale count bound))
        (denotesSameAsSymm
          (denotesSameAsTrans
            (mulExactCongrLeft bound (natRationalSuccDenotesSame count))
            (denotesSameAsTrans
              (mulExactRightDistrib bound (natRational count) oneRational)
              (addExactCongrRight (mulExact (natRational count) bound)
                (mulExactOneLeft bound)))))

/-! ## The exact nonnegative-constant real-scale bridge (B1)

Multiplying a real-level distance by a NONNEGATIVE rational constant scales the
bound EXACTLY — `IsWithinRealBound x y q` lifts to `IsWithinRealBound (c·x)(c·y)
(c·q)`.  The shipped `mulRealRespectsIsWithinRealBound` scales by an INTEGER
magnitude ceiling, which blows up the mesh/count cancellation; this bridge keeps
the exact `c·q` by feeding the ℚ product-difference law the constant as its own
magnitude (§`mulExactRespectsIsWithinBoundConstantLeft`).

Both products share the SAME left factor `constantReal c` but sample the right
factor at factor-dependent scaled indices, so the proof is one slack closure:
per shared index, chain both products to the deep slack index by their own
regularity; there the right factors bridge their sampling mismatch by regularity
onto the fixed `bound` plus a vanishing `4/(slack+1)`; the exact ℚ scaling lands
`c·(bound + 4/slack)`; the constant slack piece `c·4/slack` relaxes to the
integer-ceiling `(M·4)/slack` (harmless — it VANISHES), and the chain reshapes
onto `c·bound + 2/(shared+1)` plus that vanishing slack. -/

/-- **Exact nonnegative-constant real-scale** — a real-level within-bound pair,
scaled by a nonnegative rational constant, lands within the EXACTLY scaled
bound `c · bound`. -/
theorem scalarMulRealExactBoundOfNonNegative {constant : RationalPair}
    (isConstantNonNegative : IsNonNegative constant)
    {leftValue rightValue : RegularReal} {bound : RationalPair}
    (isWithin : IsWithinRealBound leftValue rightValue bound)
    (isBoundNonNegative : IsNonNegative bound) :
    IsWithinRealBound (mulReal (constantReal constant) leftValue)
      (mulReal (constantReal constant) rightValue)
      (mulExact constant bound) :=
  let constantFactor := constantReal constant
  let magnitudeNumerator := canonicalBoundNumerator constantFactor
  have constantMagnitude :
      IsMagnitudeWithin constant (ratioOfNatSucc magnitudeNumerator 0) :=
    approximationIsWithinCanonicalBound constantFactor 0
  fun sharedIndex =>
    isWithinBoundOfForallSlack
      (slackNumerator := 2 + magnitudeNumerator * 4)
      (fun slackIndex =>
        let oldSampling := productSamplingIndex constantFactor leftValue slackIndex
        let newSampling := productSamplingIndex constantFactor rightValue slackIndex
        let slackTerm := ratioOfNatSucc (magnitudeNumerator * 4) slackIndex
        let middleBound := mulExact constant (addExact bound (ratioOfNatSucc 4 slackIndex))
        have tailBoundToFourSlack :
            LessEqualAs
              (addExact
                (addExact (reciprocalOfSucc oldSampling)
                  (reciprocalOfSucc newSampling))
                (ratioOfNatSucc 2 newSampling))
              (ratioOfNatSucc 4 slackIndex) :=
          lessEqualAsCongrRight
            (denotesSameAsTrans
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                (denotesSameAsRefl (ratioOfNatSucc 2 slackIndex)))
              (ratioOfNatSuccSumDenotesSame 2 2 slackIndex))
            (addExactMonotone
              (addExactMonotone
                (ratioOfNatSuccAntitoneDenominator 1
                  (natSelfLeBoundScaledIndex
                    (sharedBoundNumeratorPredecessor constantFactor leftValue)
                    slackIndex))
                (ratioOfNatSuccAntitoneDenominator 1
                  (natSelfLeBoundScaledIndex
                    (sharedBoundNumeratorPredecessor constantFactor rightValue)
                    slackIndex)))
              (ratioOfNatSuccAntitoneDenominator 2
                (natSelfLeBoundScaledIndex
                  (sharedBoundNumeratorPredecessor constantFactor rightValue)
                  slackIndex)))
        have factorsDiffer :
            IsWithinBound (leftValue.approximation oldSampling)
              (rightValue.approximation newSampling)
              (addExact bound (ratioOfNatSucc 4 slackIndex)) :=
          isWithinBoundOfBoundLessEqual
            (lessEqualAsCongrLeft
              (denotesSameAsSymm
                (addExactSwapOuterIntoInner
                  (addExact (reciprocalOfSucc oldSampling)
                    (reciprocalOfSucc newSampling))
                  bound (ratioOfNatSucc 2 newSampling)))
              (addExactMonotone (lessEqualAsRefl bound) tailBoundToFourSlack))
            (isWithinBoundTriangle
              (leftValue.isRegular oldSampling newSampling)
              (isWithin newSampling))
        have productsDifferAtSlack :
            IsWithinBound
              ((mulReal constantFactor leftValue).approximation slackIndex)
              ((mulReal constantFactor rightValue).approximation slackIndex)
              middleBound :=
          mulExactRespectsIsWithinBoundConstantLeft isConstantNonNegative
            factorsDiffer
            (addExactIsNonNegative isBoundNonNegative
              (ratioOfNatSuccIsNonNegative 4 slackIndex))
        have middleRelaxes :
            LessEqualAs middleBound
              (addExact (mulExact constant bound) slackTerm) :=
          lessEqualAsCongrLeft
            (denotesSameAsSymm
              (mulExactLeftDistrib constant bound (ratioOfNatSucc 4 slackIndex)))
            (addExactMonotone (lessEqualAsRefl (mulExact constant bound))
              (lessEqualAsCongrRight
                (mulExactRatioRatioDenotesSame magnitudeNumerator 4 slackIndex)
                (mulExactMonotoneOfNonNegative constantMagnitude.left
                  (lessEqualAsRefl (ratioOfNatSucc 4 slackIndex))
                  (ratioOfNatSuccIsNonNegative 4 slackIndex)
                  (ratioOfNatSuccIsNonNegative magnitudeNumerator 0))))
        have reshapeToGathered :
            DenotesSameAs
              (addExact
                (addExact (addExact (reciprocalOfSucc sharedIndex)
                  (reciprocalOfSucc slackIndex)) middleBound)
                (addExact (reciprocalOfSucc slackIndex)
                  (reciprocalOfSucc sharedIndex)))
              (addExact (ratioOfNatSucc 2 sharedIndex)
                (addExact (ratioOfNatSucc 2 slackIndex) middleBound)) :=
          denotesSameAsTrans
            (chainedSlackBoundReshapesDenotesSame (reciprocalOfSucc sharedIndex)
              (reciprocalOfSucc slackIndex) middleBound)
            (addExactRespectsDenotesSameAs
              (ratioOfNatSuccSumDenotesSame 1 1 sharedIndex)
              (addExactRespectsDenotesSameAs
                (ratioOfNatSuccSumDenotesSame 1 1 slackIndex)
                (denotesSameAsRefl middleBound)))
        have gatheredToTarget :
            DenotesSameAs
              (addExact (ratioOfNatSucc 2 sharedIndex)
                (addExact (ratioOfNatSucc 2 slackIndex)
                  (addExact (mulExact constant bound) slackTerm)))
              (addExact (addExact (mulExact constant bound)
                (ratioOfNatSucc 2 sharedIndex))
                (ratioOfNatSucc (2 + magnitudeNumerator * 4) slackIndex)) :=
          denotesSameAsTrans
            (addExactGatherDenotesSame (ratioOfNatSucc 2 sharedIndex)
              (ratioOfNatSucc 2 slackIndex) (mulExact constant bound) slackTerm)
            (addExactRespectsDenotesSameAs
              (denotesSameAsRefl
                (addExact (mulExact constant bound) (ratioOfNatSucc 2 sharedIndex)))
              (ratioOfNatSuccSumDenotesSame 2 (magnitudeNumerator * 4) slackIndex))
        have boundLessEqual :
            LessEqualAs
              (addExact
                (addExact (addExact (reciprocalOfSucc sharedIndex)
                  (reciprocalOfSucc slackIndex)) middleBound)
                (addExact (reciprocalOfSucc slackIndex)
                  (reciprocalOfSucc sharedIndex)))
              (addExact (addExact (mulExact constant bound)
                (ratioOfNatSucc 2 sharedIndex))
                (ratioOfNatSucc (2 + magnitudeNumerator * 4) slackIndex)) :=
          lessEqualAsCongrLeft (denotesSameAsSymm reshapeToGathered)
            (lessEqualAsCongrRight gatheredToTarget
              (addExactMonotone
                (lessEqualAsRefl (ratioOfNatSucc 2 sharedIndex))
                (addExactMonotone
                  (lessEqualAsRefl (ratioOfNatSucc 2 slackIndex)) middleRelaxes)))
        isWithinBoundOfBoundLessEqual boundLessEqual
          (isWithinBoundTriangle
            (isWithinBoundTriangle
              ((mulReal constantFactor leftValue).isRegular sharedIndex slackIndex)
              productsDifferAtSlack)
            ((mulReal constantFactor rightValue).isRegular slackIndex sharedIndex)))

/-! ## Bounded-range sum bound -/

/-- **The sum respects a per-term bound that holds only on the summed range** —
the range-restricted sibling of `sumRealRespectsIsWithinRealBound`.  Needed
because the refinement's per-subcell oscillation bound holds only for inner
indices BELOW the block size. -/
theorem sumRealRespectsIsWithinRealBoundOnRange {leftTerm rightTerm : Nat → RegularReal}
    {bound : RationalPair} (count : Nat)
    (termsWithin : ∀ position, position < count →
      IsWithinRealBound (leftTerm position) (rightTerm position) bound) :
    IsWithinRealBound (sumReal count leftTerm) (sumReal count rightTerm)
      (natScaleRational count bound) :=
  match count with
  | 0 =>
      isWithinRealBoundOfDenotesSameReal
        (denotesSameRealRefl (constantReal zeroRational))
        (lessEqualAsRefl zeroRational)
  | count + 1 =>
      addRealRespectsIsWithinRealBound
        (sumRealRespectsIsWithinRealBoundOnRange count
          (fun position isBelow =>
            termsWithin position (Nat.lt_succ_of_lt isBelow)))
        (termsWithin count (Nat.lt_succ_self count))

/-! ## The block-refinement mesh and sample identities (R1, R2, R3) -/

/-- The refined cell-count predecessor — `(blockSizePred+1)·cellCountPredecessor
+ blockSizePred`, spelled so `refinedCellCountPredecessor + 1` reduces
DEFINITIONALLY to `(blockSizePred+1)·(cellCountPredecessor+1)`. -/
def refinedCellCountPredecessor (blockSizePredecessor cellCountPredecessor : Nat) :
    Nat :=
  (blockSizePredecessor + 1) * cellCountPredecessor + blockSizePredecessor

/-- **The natural rationals are multiplicative** — `a/1 · b/1 ~ (a·b)/1`. -/
theorem natRationalMul (leftCount rightCount : Nat) :
    DenotesSameAs (mulExact (natRational leftCount) (natRational rightCount))
      (natRational (leftCount * rightCount)) :=
  mulExactRatioRatioDenotesSame leftCount rightCount 0

/-- **The block reciprocal cancels** — `(blockSize)/1 · 1/(refined+1) ~ 1/(coarse
+1)`, since `refined+1` is definitionally `blockSize·(coarse+1)`. -/
theorem reciprocalBlockCancels (blockSizePredecessor cellCountPredecessor : Nat) :
    DenotesSameAs
      (mulExact (natRational (blockSizePredecessor + 1))
        (reciprocalOfSucc
          (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor)))
      (reciprocalOfSucc cellCountPredecessor) :=
  denotesSameAsTrans
    (mulExactRatioRatioDenotesSame (blockSizePredecessor + 1) 1
      (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor))
    (congrArg Int.ofNat
      ((congrArg (· * (cellCountPredecessor + 1))
          (Nat.mul_one (blockSizePredecessor + 1))).trans
        (Nat.one_mul
          (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor
            + 1)).symm))

/-- **The coarse mesh is the block-scaled fine mesh** (R1) — refining each cell
into `blockSize` subcells scales the mesh down by `blockSize`. -/
theorem meshWidthRefinesByBlock (lowerBound upperBound : RationalPair)
    (blockSizePredecessor cellCountPredecessor : Nat) :
    DenotesSameAs (meshWidth lowerBound upperBound cellCountPredecessor)
      (mulExact (natRational (blockSizePredecessor + 1))
        (meshWidth lowerBound upperBound
          (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor))) :=
  let intervalWidth := subExact upperBound lowerBound
  let refinedPredecessor :=
    refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor
  denotesSameAsSymm
    (denotesSameAsTrans
      (denotesSameAsSymm
        (mulExactAssoc (natRational (blockSizePredecessor + 1)) intervalWidth
          (reciprocalOfSucc refinedPredecessor)))
      (denotesSameAsTrans
        (mulExactCongrLeft (reciprocalOfSucc refinedPredecessor)
          (mulExactComm (natRational (blockSizePredecessor + 1)) intervalWidth))
        (denotesSameAsTrans
          (mulExactAssoc intervalWidth (natRational (blockSizePredecessor + 1))
            (reciprocalOfSucc refinedPredecessor))
          (mulExactCongrRight intervalWidth
            (reciprocalBlockCancels blockSizePredecessor cellCountPredecessor)))))

/-- **The coarse left endpoint IS the refined block-base endpoint** (R2) — the
`blockIndex`-th coarse sample equals the `(blockSize·blockIndex)`-th fine sample. -/
theorem samplePointBaseRefines (lowerBound upperBound : RationalPair)
    (blockSizePredecessor cellCountPredecessor blockIndex : Nat) :
    DenotesSameAs (samplePoint lowerBound upperBound cellCountPredecessor blockIndex)
      (samplePoint lowerBound upperBound
        (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor)
        ((blockSizePredecessor + 1) * blockIndex)) :=
  let refinedPredecessor :=
    refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor
  let refinedMesh := meshWidth lowerBound upperBound refinedPredecessor
  addExactCongrRight lowerBound
    (denotesSameAsTrans
      (mulExactCongrRight (natRational blockIndex)
        (meshWidthRefinesByBlock lowerBound upperBound blockSizePredecessor
          cellCountPredecessor))
      (denotesSameAsTrans
        (denotesSameAsSymm
          (mulExactAssoc (natRational blockIndex)
            (natRational (blockSizePredecessor + 1)) refinedMesh))
        (denotesSameAsTrans
          (mulExactCongrLeft refinedMesh
            (mulExactComm (natRational blockIndex)
              (natRational (blockSizePredecessor + 1))))
          (mulExactCongrLeft refinedMesh
            (natRationalMul (blockSizePredecessor + 1) blockIndex)))))

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
