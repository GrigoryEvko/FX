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

/-- **The natural rationals are additive** — `(a+b)/1 ~ a/1 + b/1`. -/
theorem natRationalAddDenotesSame (leftCount rightCount : Nat) :
    DenotesSameAs (natRational (leftCount + rightCount))
      (addExact (natRational leftCount) (natRational rightCount)) :=
  denotesSameAsSymm (ratioOfNatSuccSumDenotesSame leftCount rightCount 0)

/-- `base + (value − base)` on the RIGHT collapses — `base − (base+value)`
denotes `−value`. -/
theorem subExactSelfAddRightDenotesSame (base value : RationalPair) :
    DenotesSameAs (subExact base (addExact base value)) (negExact value) :=
  denotesSameAsTrans
    (addExactCongrRight base (negExactAddExactDenotesSame base value))
    (denotesSameAsTrans
      (denotesSameAsSymm (addExactAssoc base (negExact base) (negExact value)))
      (denotesSameAsTrans
        (addExactCongrLeft (negExact value) (addExactNegRight base))
        (addExactZeroLeft (negExact value))))

/-- **The fine offset sample shifts the block base by `inner · fineMesh`** — the
`(blockSize·blockIndex + innerIndex)`-th fine sample is the block-base sample
plus `innerIndex` fine mesh steps. -/
theorem samplePointOffsetShift (lowerBound upperBound : RationalPair)
    (blockSizePredecessor cellCountPredecessor blockIndex innerIndex : Nat) :
    DenotesSameAs
      (samplePoint lowerBound upperBound
        (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor)
        ((blockSizePredecessor + 1) * blockIndex + innerIndex))
      (addExact
        (samplePoint lowerBound upperBound
          (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor)
          ((blockSizePredecessor + 1) * blockIndex))
        (mulExact (natRational innerIndex)
          (meshWidth lowerBound upperBound
            (refinedCellCountPredecessor blockSizePredecessor
              cellCountPredecessor)))) :=
  let refinedPredecessor :=
    refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor
  let refinedMesh := meshWidth lowerBound upperBound refinedPredecessor
  let blockBase := (blockSizePredecessor + 1) * blockIndex
  denotesSameAsTrans
    (addExactCongrRight lowerBound
      (denotesSameAsTrans
        (mulExactCongrLeft refinedMesh
          (natRationalAddDenotesSame blockBase innerIndex))
        (mulExactRightDistrib refinedMesh (natRational blockBase)
          (natRational innerIndex))))
    (denotesSameAsSymm
      (addExactAssoc lowerBound (mulExact (natRational blockBase) refinedMesh)
        (mulExact (natRational innerIndex) refinedMesh)))

/-- **The per-subcell sample gap is within the coarse mesh** (R3) — inside one
coarse cell, the fine sample `blockSize·blockIndex + innerIndex` sits within one
coarse mesh width of the block base, provided `innerIndex ≤ blockSize` and the
interval is nondegenerate.  This is the input hypothesis the uniform-continuity
modulus consumes. -/
theorem samplePointGapWithinMesh (lowerBound upperBound : RationalPair)
    (blockSizePredecessor cellCountPredecessor blockIndex innerIndex : Nat)
    (isInnerWithinBlock : innerIndex ≤ blockSizePredecessor + 1)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound)) :
    IsWithinBound
      (samplePoint lowerBound upperBound
        (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor)
        ((blockSizePredecessor + 1) * blockIndex))
      (samplePoint lowerBound upperBound
        (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor)
        ((blockSizePredecessor + 1) * blockIndex + innerIndex))
      (meshWidth lowerBound upperBound cellCountPredecessor) :=
  let refinedPredecessor :=
    refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor
  let refinedMesh := meshWidth lowerBound upperBound refinedPredecessor
  let gap := mulExact (natRational innerIndex) refinedMesh
  let blockBase := (blockSizePredecessor + 1) * blockIndex
  have isRefinedMeshNonNegative : IsNonNegative refinedMesh :=
    mulExactIsNonNegative isIntervalNonNegative
      (ratioOfNatSuccIsNonNegative 1 refinedPredecessor)
  have isGapNonNegative : IsNonNegative gap :=
    mulExactIsNonNegative
      (ratioOfNatSuccIsNonNegative innerIndex 0) isRefinedMeshNonNegative
  have gapWithinMesh :
      LessEqualAs gap (meshWidth lowerBound upperBound cellCountPredecessor) :=
    lessEqualAsCongrRight
      (denotesSameAsSymm
        (meshWidthRefinesByBlock lowerBound upperBound blockSizePredecessor
          cellCountPredecessor))
      (mulExactMonotoneOfNonNegative
        (ratioOfNatSuccMonotoneNumerator isInnerWithinBlock 0)
        (lessEqualAsRefl refinedMesh) isRefinedMeshNonNegative
        (ratioOfNatSuccIsNonNegative (blockSizePredecessor + 1) 0))
  have gapMagnitude :
      IsMagnitudeWithin gap
        (meshWidth lowerBound upperBound cellCountPredecessor) :=
    isMagnitudeWithinOfBoundLessEqual gapWithinMesh
      (isMagnitudeWithinSelfOfNonNegative isGapNonNegative)
  isWithinBoundOfIsMagnitudeWithinSubExact
    (isMagnitudeWithinCongrValue
      (denotesSameAsSymm
        (denotesSameAsTrans
          (subExactRespectsDenotesSameAs
            (denotesSameAsRefl
              (samplePoint lowerBound upperBound refinedPredecessor blockBase))
            (samplePointOffsetShift lowerBound upperBound blockSizePredecessor
              cellCountPredecessor blockIndex innerIndex))
          (subExactSelfAddRightDenotesSame
            (samplePoint lowerBound upperBound refinedPredecessor blockBase)
            gap)))
      (isMagnitudeWithinNegExact gapMagnitude))

/-- **The ℚ→ℝ constant re-read** — a ℚ-level distance between two rationals IS a
real-level distance between their constant embeddings (the constant approximants
never move, so the setoid modulus is pure headroom). -/
theorem constantRealIsWithinRealBoundOfIsWithinBound {leftValue rightValue bound :
    RationalPair} (isWithin : IsWithinBound leftValue rightValue bound) :
    IsWithinRealBound (constantReal leftValue) (constantReal rightValue) bound :=
  fun index =>
    isWithinBoundOfBoundLessEqual
      (lessEqualAsCongrLeft (addExactZeroRight bound)
        (addExactMonotoneRight bound (ratioOfNatSuccIsNonNegative 2 index)))
      isWithin

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

/-! ## The common-refinement Cauchy estimate -/

/-- **The refinement estimate** — the analytic core.  For a uniformly continuous
integrand and a coarse partition whose mesh is finer than the UC tolerance
`1/(modulus outputPrecision + 1)`, the coarse Riemann sum and its
`blockSize`-refinement sit within `(upperBound - lowerBound)/(outputPrecision+1)`
in the real-level distance.

Decomposition: the fine sum regroups into `cellCount` outer blocks of `blockSize`
inner subcells (`sumRealRegroupProduct`), and the coarse sum re-expresses as the
same double sum with the inner term held at the coarse left endpoint (each coarse
term replicated `blockSize`-fold, mesh rescaled by R1).  Oscillation: per subcell
the two sample points sit within the coarse mesh (R3), hence within the UC
tolerance (mesh condition), so the integrand values sit within `1/(k+1)` (UC).
Assembly: the per-subcell bounds sum to `(cellCount·blockSize)·(1/(k+1))`; scaling
by the shared fine mesh (B1) and telescoping the cell count against the mesh
(`cellCountMeshWidthDenotesSame`) collapses to the interval width over `k+1`. -/
theorem refinementEstimate {function : RegularReal → RegularReal}
    {modulus : Nat → Nat}
    (isUniformlyContinuousFunction : IsUniformlyContinuous function modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound))
    (blockSizePredecessor cellCountPredecessor outputPrecision : Nat)
    (meshCondition :
      LessEqualAs (meshWidth lowerBound upperBound cellCountPredecessor)
        (reciprocalOfSucc (modulus outputPrecision))) :
    IsWithinRealBound
      (riemannSum function lowerBound upperBound cellCountPredecessor)
      (riemannSum function lowerBound upperBound
        (refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor))
      (mulExact (subExact upperBound lowerBound)
        (reciprocalOfSucc outputPrecision)) :=
  let blockCount := cellCountPredecessor + 1
  let blockSize := blockSizePredecessor + 1
  let refinedPredecessor :=
    refinedCellCountPredecessor blockSizePredecessor cellCountPredecessor
  let refinedMesh := meshWidth lowerBound upperBound refinedPredecessor
  let coarseTerm : Nat → RegularReal :=
    fun blockIndex =>
      function (constantReal
        (samplePoint lowerBound upperBound cellCountPredecessor blockIndex))
  let fineTerm : Nat → RegularReal :=
    fun position =>
      function (constantReal
        (samplePoint lowerBound upperBound refinedPredecessor position))
  let doubleCoarse : RegularReal :=
    sumReal blockCount
      (fun blockIndex => sumReal blockSize (fun _ => coarseTerm blockIndex))
  let doubleFine : RegularReal :=
    sumReal blockCount
      (fun blockIndex =>
        sumReal blockSize
          (fun innerIndex => fineTerm (blockSize * blockIndex + innerIndex)))
  let outputReciprocal := reciprocalOfSucc outputPrecision
  let doubleBoundValue :=
    natScaleRational blockCount (natScaleRational blockSize outputReciprocal)
  have isRefinedMeshNonNegative : IsNonNegative refinedMesh :=
    mulExactIsNonNegative isIntervalNonNegative
      (ratioOfNatSuccIsNonNegative 1 refinedPredecessor)
  -- The fine Riemann sum regroups into the block double sum.
  have riemannFineRewrite :
      DenotesSameReal
        (riemannSum function lowerBound upperBound refinedPredecessor)
        (mulReal (constantReal refinedMesh) doubleFine) :=
    mulRealRespectsDenotesSame (denotesSameRealRefl (constantReal refinedMesh))
      (sumRealRegroupProduct blockSize blockCount fineTerm)
  -- The coarse Riemann sum re-expresses over the SAME fine mesh and double sum.
  have riemannCoarseRewrite :
      DenotesSameReal
        (riemannSum function lowerBound upperBound cellCountPredecessor)
        (mulReal (constantReal refinedMesh) doubleCoarse) :=
    denotesSameRealSymm
      (denotesSameRealTrans
        (mulRealRespectsDenotesSame (denotesSameRealRefl (constantReal refinedMesh))
          (sumRealRespectsDenotesSame
            (fun blockIndex => replicateRealEqScale (coarseTerm blockIndex) blockSize)
            blockCount))
        (denotesSameRealTrans
          (mulRealRespectsDenotesSame (denotesSameRealRefl (constantReal refinedMesh))
            (sumRealScalarMulReal (constantReal (natRational blockSize))
              coarseTerm blockCount))
          (denotesSameRealTrans
            (denotesSameRealSymm
              (mulRealAssoc (constantReal refinedMesh)
                (constantReal (natRational blockSize))
                (sumReal blockCount coarseTerm)))
            (mulRealRespectsDenotesSame
              (denotesSameRealTrans
                (denotesSameRealSymm
                  (constantRealMulExact refinedMesh (natRational blockSize)))
                (constantRealRespectsDenotesSame
                  (denotesSameAsTrans
                    (mulExactComm refinedMesh (natRational blockSize))
                    (denotesSameAsSymm
                      (meshWidthRefinesByBlock lowerBound upperBound
                        blockSizePredecessor cellCountPredecessor)))))
              (denotesSameRealRefl (sumReal blockCount coarseTerm))))))
  -- Per subcell: uniform continuity forces the integrand values within 1/(k+1).
  have perTermBound :
      ∀ blockIndex innerIndex, innerIndex < blockSize →
        IsWithinRealBound (coarseTerm blockIndex)
          (fineTerm (blockSize * blockIndex + innerIndex)) outputReciprocal :=
    fun blockIndex innerIndex isInnerBelowBlock =>
      isUniformlyContinuousFunction
        (constantReal
          (samplePoint lowerBound upperBound cellCountPredecessor blockIndex))
        (constantReal
          (samplePoint lowerBound upperBound refinedPredecessor
            (blockSize * blockIndex + innerIndex)))
        outputPrecision
        (constantRealIsWithinRealBoundOfIsWithinBound
          (isWithinBoundCongrLeft
            (denotesSameAsSymm
              (samplePointBaseRefines lowerBound upperBound blockSizePredecessor
                cellCountPredecessor blockIndex))
            (isWithinBoundOfBoundLessEqual meshCondition
              (samplePointGapWithinMesh lowerBound upperBound blockSizePredecessor
                cellCountPredecessor blockIndex innerIndex
                (Nat.le_of_lt isInnerBelowBlock) isIntervalNonNegative))))
  -- Sum the oscillation bounds over the double index.
  have doubleBound :
      IsWithinRealBound doubleCoarse doubleFine doubleBoundValue :=
    sumRealRespectsIsWithinRealBound
      (fun blockIndex =>
        sumRealRespectsIsWithinRealBoundOnRange blockSize
          (fun innerIndex isInnerBelowBlock =>
            perTermBound blockIndex innerIndex isInnerBelowBlock))
      blockCount
  -- Collapse the nested count scale into a product of naturals.
  have doubleBoundReshape :
      DenotesSameAs doubleBoundValue
        (mulExact (natRational blockCount)
          (mulExact (natRational blockSize) outputReciprocal)) :=
    denotesSameAsTrans
      (natScaleRationalDenotesScale blockCount
        (natScaleRational blockSize outputReciprocal))
      (mulExactCongrRight (natRational blockCount)
        (natScaleRationalDenotesScale blockSize outputReciprocal))
  have isDoubleBoundNonNegative : IsNonNegative doubleBoundValue :=
    lessEqualAsCongrRight (denotesSameAsSymm doubleBoundReshape)
      (mulExactIsNonNegative (ratioOfNatSuccIsNonNegative blockCount 0)
        (mulExactIsNonNegative (ratioOfNatSuccIsNonNegative blockSize 0)
          (ratioOfNatSuccIsNonNegative 1 outputPrecision)))
  -- Scale the double-sum bound by the shared fine mesh (B1).
  have scaledBound :
      IsWithinRealBound (mulReal (constantReal refinedMesh) doubleCoarse)
        (mulReal (constantReal refinedMesh) doubleFine)
        (mulExact refinedMesh doubleBoundValue) :=
    scalarMulRealExactBoundOfNonNegative isRefinedMeshNonNegative doubleBound
      isDoubleBoundNonNegative
  -- Telescope the mesh against the cell count.
  have refinedCountEq :
      blockCount * blockSize = refinedPredecessor + 1 :=
    Nat.mul_comm (cellCountPredecessor + 1) (blockSizePredecessor + 1)
  have natRationalRefinedEq :
      DenotesSameAs (natRational (blockCount * blockSize))
        (natRational (refinedPredecessor + 1)) :=
    congrArg (fun scaledCount => Int.ofNat scaledCount * Int.ofNat 1)
      refinedCountEq
  have boundReshape :
      DenotesSameAs (mulExact refinedMesh doubleBoundValue)
        (mulExact (subExact upperBound lowerBound) outputReciprocal) :=
    denotesSameAsTrans
      (mulExactCongrRight refinedMesh doubleBoundReshape)
      (denotesSameAsTrans
        (mulExactCongrRight refinedMesh
          (denotesSameAsSymm
            (mulExactAssoc (natRational blockCount) (natRational blockSize)
              outputReciprocal)))
        (denotesSameAsTrans
          (mulExactCongrRight refinedMesh
            (mulExactCongrLeft outputReciprocal
              (natRationalMul blockCount blockSize)))
          (denotesSameAsTrans
            (denotesSameAsSymm
              (mulExactAssoc refinedMesh (natRational (blockCount * blockSize))
                outputReciprocal))
            (mulExactCongrLeft outputReciprocal
              (denotesSameAsTrans
                (mulExactComm refinedMesh (natRational (blockCount * blockSize)))
                (denotesSameAsTrans
                  (mulExactCongrLeft refinedMesh natRationalRefinedEq)
                  (cellCountMeshWidthDenotesSame lowerBound upperBound
                    refinedPredecessor)))))))
  isWithinRealBoundCongrLeftDenotesSameReal riemannCoarseRewrite
    (isWithinRealBoundCongrRightDenotesSameReal riemannFineRewrite
      (isWithinRealBoundCongrBound boundReshape scaledBound))

/-! ## The Archimedean mesh bound (the ℚ core of the schedule)

The mesh condition `refinementEstimate` consumes reduces to a single `Int`
inequality: for a nonnegative interval width `W`, the mesh
`W · 1/(largeCount)` sits below `1/(smallCount)` as soon as the fine cell
count dominates the Archimedean bound `N = |W.numerator| + 1` scaled by the
coarse count — `N · smallCount ≤ largeCount`.  The chain mirrors
`lessThanArchimedeanBound`: `W.numerator ≤ N`, scale by the coarse count,
push through the cell-count bound, and pad by the positive denominator. -/

/-- **The Archimedean mesh bound** — with `intervalWidth` nonnegative, the mesh
`intervalWidth · 1/(largePredecessor+1)` lands below `1/(smallPredecessor+1)`
whenever the fine cell count dominates the Archimedean bound times the coarse
count.  Pure `Int` monotonicity over the cross-multiplication order. -/
theorem meshLessEqualReciprocalOfCellBound (intervalWidth : RationalPair)
    (smallPredecessor largePredecessor : Nat)
    (cellBound :
      archimedeanBound intervalWidth * (smallPredecessor + 1) ≤ largePredecessor + 1) :
    LessEqualAs (mulExact intervalWidth (reciprocalOfSucc largePredecessor))
      (reciprocalOfSucc smallPredecessor) :=
  have numeratorBelowBound :
      intervalWidth.numerator ≤ Int.ofNat (archimedeanBound intervalWidth) :=
    intLessEqualTrans (intSelfLessEqualOfNatNatAbs intervalWidth.numerator)
      (intOfNatLeOfNat (Nat.le_succ intervalWidth.numerator.natAbs))
  have leftScaled :
      intervalWidth.numerator * Int.ofNat (smallPredecessor + 1) ≤
        Int.ofNat (archimedeanBound intervalWidth) * Int.ofNat (smallPredecessor + 1) :=
    intMulLeMulRightOfNonNeg numeratorBelowBound (intZeroLeOfNat (smallPredecessor + 1))
  have midStep :
      Int.ofNat (archimedeanBound intervalWidth) * Int.ofNat (smallPredecessor + 1) ≤
        Int.ofNat (largePredecessor + 1) :=
    intOfNatLeOfNat cellBound
  have rightScaled :
      Int.ofNat (largePredecessor + 1) ≤
        denominatorInt intervalWidth * Int.ofNat (largePredecessor + 1) :=
    intLessEqualOfEqLeft (intOneMul (Int.ofNat (largePredecessor + 1))).symm
      (intMulLeMulRightOfNonNeg
        (show (1 : Int) ≤ denominatorInt intervalWidth from
          denominatorIntIsPositive intervalWidth)
        (intZeroLeOfNat (largePredecessor + 1)))
  have coreChain :
      intervalWidth.numerator * Int.ofNat (smallPredecessor + 1) ≤
        denominatorInt intervalWidth * Int.ofNat (largePredecessor + 1) :=
    intLessEqualTrans (intLessEqualTrans leftScaled midStep) rightScaled
  intLessEqualOfEqLeft
    (congrArg (· * Int.ofNat (smallPredecessor + 1)) (intMulOne intervalWidth.numerator))
    (intLessEqualOfEqRight coreChain
      (intOneMul (denominatorInt intervalWidth * Int.ofNat (largePredecessor + 1))).symm)

/-! ## The Archimedean cell-count schedule

A modulus-driven running product.  Member `index` refines every earlier member
(the product structure gives nested block refinement), and its cell count is
large enough that the mesh at that member beats the uniform-continuity tolerance
for output precision `N·(index+1)` — exactly what the leg estimate needs to drive
the produced bound `(U-L)/(outputPrecision+1)` down to `1/(index+1)`.  The whole
schedule is spelled predecessor-form over the shipped `refinedCellCountPredecessor`,
whose `+1` reduces DEFINITIONALLY to the product, so the block/product identities
are all `rfl`. -/

/-- Composition of refinements is a refinement — the block predecessors multiply,
by the definitional `+1` product identity plus one clean `natMulAssoc`. -/
theorem refinedCellCountPredecessorAssoc
    (outerPredecessor middlePredecessor innerPredecessor : Nat) :
    refinedCellCountPredecessor outerPredecessor
        (refinedCellCountPredecessor middlePredecessor innerPredecessor) =
      refinedCellCountPredecessor
        (refinedCellCountPredecessor outerPredecessor middlePredecessor) innerPredecessor :=
  Nat.succ.inj
    (show (outerPredecessor + 1) * ((middlePredecessor + 1) * (innerPredecessor + 1)) =
        (outerPredecessor + 1) * (middlePredecessor + 1) * (innerPredecessor + 1) from
      (natMulAssoc (outerPredecessor + 1) (middlePredecessor + 1)
        (innerPredecessor + 1)).symm)

/-- Setoid sameness of reals from raw equality — reflexivity transported. -/
theorem denotesSameRealOfEq {leftValue rightValue : RegularReal}
    (areEqual : leftValue = rightValue) : DenotesSameReal leftValue rightValue :=
  areEqual ▸ denotesSameRealRefl leftValue

/-- The per-step block predecessor — its `+1` is `N·(modulus(N·(index+1))+1)`, the
cell count that makes the mesh at member `index` beat the UC tolerance for output
precision `N·(index+1)`. -/
def scheduleBlockPredecessor (boundPredecessor : Nat) (modulus : Nat → Nat)
    (index : Nat) : Nat :=
  refinedCellCountPredecessor boundPredecessor
    (modulus (refinedCellCountPredecessor boundPredecessor index))

/-- The running-product schedule, predecessor form — each member folds the next
block factor onto the previous cell count. -/
def scheduleCellCountPredecessor (boundPredecessor : Nat) (modulus : Nat → Nat) :
    Nat → Nat
  | 0 => scheduleBlockPredecessor boundPredecessor modulus 0
  | (index + 1) =>
      refinedCellCountPredecessor
        (scheduleBlockPredecessor boundPredecessor modulus (index + 1))
        (scheduleCellCountPredecessor boundPredecessor modulus index)

/-- The interval-specialized schedule — the bound predecessor is the interval
width's numerator magnitude, so `boundPredecessor + 1 = archimedeanBound (U-L)`. -/
def integralSchedulePredecessor (lowerBound upperBound : RationalPair)
    (modulus : Nat → Nat) (index : Nat) : Nat :=
  scheduleCellCountPredecessor (subExact upperBound lowerBound).numerator.natAbs
    modulus index

/-- The output precision predecessor at member `index` — `+1 = archimedeanBound
(U-L) · (index+1)`, chosen so the produced bound `(U-L)/(this+1) ≤ 1/(index+1)`. -/
def integralOutputPrecisionPredecessor (lowerBound upperBound : RationalPair)
    (index : Nat) : Nat :=
  refinedCellCountPredecessor (subExact upperBound lowerBound).numerator.natAbs index

/-- **The schedule cell count dominates its own block factor** — the running
product is at least its last factor, since the earlier product is positive. -/
theorem scheduleCellCountSelfGeStepFactor (boundPredecessor : Nat)
    (modulus : Nat → Nat) (index : Nat) :
    scheduleBlockPredecessor boundPredecessor modulus index + 1 ≤
      scheduleCellCountPredecessor boundPredecessor modulus index + 1 :=
  match index with
  | 0 => Nat.le_refl _
  | (predecessorIndex + 1) =>
      Nat.le_add_left
        (scheduleBlockPredecessor boundPredecessor modulus (predecessorIndex + 1) + 1)
        ((scheduleBlockPredecessor boundPredecessor modulus (predecessorIndex + 1) + 1) *
          scheduleCellCountPredecessor boundPredecessor modulus predecessorIndex)

/-- **The mesh condition at each schedule member** — the schedule cell count is
built to make the mesh beat the UC tolerance at output precision
`integralOutputPrecisionPredecessor`.  Its cell-count bound IS
`scheduleCellCountSelfGeStepFactor` up to the definitional block/product identity. -/
theorem integralScheduleMeshCondition (lowerBound upperBound : RationalPair)
    (modulus : Nat → Nat) (index : Nat) :
    LessEqualAs
      (meshWidth lowerBound upperBound
        (integralSchedulePredecessor lowerBound upperBound modulus index))
      (reciprocalOfSucc
        (modulus (integralOutputPrecisionPredecessor lowerBound upperBound index))) :=
  meshLessEqualReciprocalOfCellBound (subExact upperBound lowerBound)
    (modulus (integralOutputPrecisionPredecessor lowerBound upperBound index))
    (integralSchedulePredecessor lowerBound upperBound modulus index)
    (scheduleCellCountSelfGeStepFactor
      (subExact upperBound lowerBound).numerator.natAbs modulus index)

/-- **The schedule refines by an integer block over a fixed gap** — member
`baseIndex + gap` is a `refinedCellCountPredecessor` of member `baseIndex`.
Induction on the gap: the base is the trivial refinement, the step folds the new
block factor and re-associates the composition (`refinedCellCountPredecessorAssoc`). -/
theorem scheduleRefinementFromGap (boundPredecessor : Nat) (modulus : Nat → Nat)
    (baseIndex gap : Nat) :
    ∃ blockPredecessor : Nat,
      scheduleCellCountPredecessor boundPredecessor modulus (baseIndex + gap) =
        refinedCellCountPredecessor blockPredecessor
          (scheduleCellCountPredecessor boundPredecessor modulus baseIndex) :=
  match gap with
  | 0 =>
      ⟨0,
        (Nat.one_mul
          (scheduleCellCountPredecessor boundPredecessor modulus baseIndex)).symm⟩
  | (predecessorGap + 1) =>
      match scheduleRefinementFromGap boundPredecessor modulus baseIndex predecessorGap with
      | ⟨blockPredecessorInductive, refinementInductive⟩ =>
          ⟨refinedCellCountPredecessor
              (scheduleBlockPredecessor boundPredecessor modulus
                (baseIndex + predecessorGap + 1))
              blockPredecessorInductive,
            Eq.trans
              (congrArg
                (refinedCellCountPredecessor
                  (scheduleBlockPredecessor boundPredecessor modulus
                    (baseIndex + predecessorGap + 1)))
                refinementInductive)
              (refinedCellCountPredecessorAssoc
                (scheduleBlockPredecessor boundPredecessor modulus
                  (baseIndex + predecessorGap + 1))
                blockPredecessorInductive
                (scheduleCellCountPredecessor boundPredecessor modulus baseIndex))⟩

/-- **The schedule refines by an integer block between ordered members** — the
gap form re-expressed through `Nat.le.dest`. -/
theorem scheduleRefinementBetween (boundPredecessor : Nat) (modulus : Nat → Nat)
    {firstIndex secondIndex : Nat} (isBelow : firstIndex ≤ secondIndex) :
    ∃ blockPredecessor : Nat,
      scheduleCellCountPredecessor boundPredecessor modulus secondIndex =
        refinedCellCountPredecessor blockPredecessor
          (scheduleCellCountPredecessor boundPredecessor modulus firstIndex) :=
  match Nat.le.dest isBelow with
  | ⟨gap, gapEquation⟩ =>
      gapEquation ▸ scheduleRefinementFromGap boundPredecessor modulus firstIndex gap

/-- **The forward schedule leg** — for `firstIndex ≤ secondIndex`, the coarser
Riemann sum sits within `1/(firstIndex+1)` of the finer one.  The finer member is
a block refinement of the coarser (transport), so `refinementEstimate` applies at
output precision `integralOutputPrecisionPredecessor firstIndex`; its produced
bound `(U-L)/(that+1)` relaxes to `1/(firstIndex+1)` by the Archimedean mesh
bound with an equality cell count. -/
theorem scheduleRiemannLegBelow
    {function : RegularReal → RegularReal} {modulus : Nat → Nat}
    (isUniformlyContinuousFunction : IsUniformlyContinuous function modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound))
    {firstIndex secondIndex : Nat} (isBelow : firstIndex ≤ secondIndex) :
    IsWithinRealBound
      (riemannSum function lowerBound upperBound
        (integralSchedulePredecessor lowerBound upperBound modulus firstIndex))
      (riemannSum function lowerBound upperBound
        (integralSchedulePredecessor lowerBound upperBound modulus secondIndex))
      (reciprocalOfSucc firstIndex) :=
  match scheduleRefinementBetween (subExact upperBound lowerBound).numerator.natAbs
      modulus isBelow with
  | ⟨blockPredecessor, transportEquation⟩ =>
      isWithinRealBoundOfBoundLessEqual
        (meshLessEqualReciprocalOfCellBound (subExact upperBound lowerBound) firstIndex
          (integralOutputPrecisionPredecessor lowerBound upperBound firstIndex)
          (Nat.le_refl _))
        (isWithinRealBoundCongrRightDenotesSameReal
          (denotesSameRealOfEq
            (congrArg (riemannSum function lowerBound upperBound) transportEquation))
          (refinementEstimate isUniformlyContinuousFunction lowerBound upperBound
            isIntervalNonNegative blockPredecessor
            (integralSchedulePredecessor lowerBound upperBound modulus firstIndex)
            (integralOutputPrecisionPredecessor lowerBound upperBound firstIndex)
            (integralScheduleMeshCondition lowerBound upperBound modulus firstIndex)))

/-- A reciprocal sits below its sum with another — the left summand witness. -/
theorem reciprocalLeAddReciprocalLeft (leftIndex rightIndex : Nat) :
    LessEqualAs (reciprocalOfSucc leftIndex)
      (addExact (reciprocalOfSucc leftIndex) (reciprocalOfSucc rightIndex)) :=
  lessEqualAsCongrLeft (addExactZeroRight (reciprocalOfSucc leftIndex))
    (addExactMonotoneRight (reciprocalOfSucc leftIndex)
      (ratioOfNatSuccIsNonNegative 1 rightIndex))

/-- A reciprocal sits below its sum with another — the right summand witness. -/
theorem reciprocalLeAddReciprocalRight (leftIndex rightIndex : Nat) :
    LessEqualAs (reciprocalOfSucc rightIndex)
      (addExact (reciprocalOfSucc leftIndex) (reciprocalOfSucc rightIndex)) :=
  lessEqualAsCongrLeft (addExactZeroLeft (reciprocalOfSucc rightIndex))
    (addExactMonotoneLeft (reciprocalOfSucc rightIndex)
      (ratioOfNatSuccIsNonNegative 1 leftIndex))

/-- **The schedule Riemann sequence is Cauchy** — the load-bearing brick.  For any
two members, the forward leg (ordered by `Nat.le_total`) gives a bound
`1/(min+1)`, relaxed to the regular Cauchy shape `1/(i+1) + 1/(j+1)`; the reversed
case rides `isWithinRealBoundSymm`. -/
theorem scheduleRiemannSumIsCauchy
    {function : RegularReal → RegularReal} {modulus : Nat → Nat}
    (isUniformlyContinuousFunction : IsUniformlyContinuous function modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound))
    (firstIndex secondIndex : Nat) :
    IsWithinRealBound
      (riemannSum function lowerBound upperBound
        (integralSchedulePredecessor lowerBound upperBound modulus firstIndex))
      (riemannSum function lowerBound upperBound
        (integralSchedulePredecessor lowerBound upperBound modulus secondIndex))
      (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex)) :=
  match Nat.le_total firstIndex secondIndex with
  | .inl isBelow =>
      isWithinRealBoundOfBoundLessEqual
        (reciprocalLeAddReciprocalLeft firstIndex secondIndex)
        (scheduleRiemannLegBelow isUniformlyContinuousFunction lowerBound upperBound
          isIntervalNonNegative isBelow)
  | .inr isAbove =>
      isWithinRealBoundOfBoundLessEqual
        (reciprocalLeAddReciprocalRight firstIndex secondIndex)
        (isWithinRealBoundSymm
          (scheduleRiemannLegBelow isUniformlyContinuousFunction lowerBound upperBound
            isIntervalNonNegative isAbove))

/-- **The schedule Riemann sequence** — the regular Cauchy sequence of Riemann
sums whose diagonal limit is the integral. -/
def riemannSumScheduleSequence
    {function : RegularReal → RegularReal} {modulus : Nat → Nat}
    (isUniformlyContinuousFunction : IsUniformlyContinuous function modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound)) :
    RegularRealSequence :=
  { values := fun index =>
      riemannSum function lowerBound upperBound
        (integralSchedulePredecessor lowerBound upperBound modulus index)
    isCauchy := scheduleRiemannSumIsCauchy isUniformlyContinuousFunction
      lowerBound upperBound isIntervalNonNegative }

/-- **The constructive integral of a uniformly continuous integrand** — the
diagonal limit of the Archimedean-schedule Riemann sums.  This OPENS the integral
layer: the analytic Cauchy witness is discharged, so the integral EXISTS as a
`RegularReal`, zero axioms. -/
def integralOfUC
    {function : RegularReal → RegularReal} {modulus : Nat → Nat}
    (isUniformlyContinuousFunction : IsUniformlyContinuous function modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound)) :
    RegularReal :=
  limitReal (riemannSumScheduleSequence isUniformlyContinuousFunction
    lowerBound upperBound isIntervalNonNegative)

/-! ## Integral laws — constant and additivity -/

/-- A constant map is uniformly continuous at the zero modulus — self-distance
meets every reciprocal tolerance. -/
theorem isUniformlyContinuousConstantReal (value : RegularReal) :
    IsUniformlyContinuous (fun _ => value) (fun _ => 0) :=
  fun _ _ outputPrecision _ =>
    isWithinRealBoundOfDenotesSameReal (denotesSameRealRefl value)
      (ratioOfNatSuccIsNonNegative 1 outputPrecision)

/-- **The exact constant integral** — `integralOfUC (fun _ => c) ~ (U-L)·c`.
Independent of the partition: `riemannSumConstant` makes every schedule member
setoid-equal to `(U-L)·c`, so the sequence converges to it, and the diagonal limit
is unique. -/
theorem integralOfUCConstant (value : RegularReal)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound)) :
    DenotesSameReal
      (integralOfUC (isUniformlyContinuousConstantReal value) lowerBound upperBound
        isIntervalNonNegative)
      (mulReal (constantReal (subExact upperBound lowerBound)) value) :=
  denotesSameRealOfConvergesToBoth
    (convergesToLimitReal
      (riemannSumScheduleSequence (isUniformlyContinuousConstantReal value)
        lowerBound upperBound isIntervalNonNegative))
    (convergesToOfPointwiseDenotesSameReal
      (fun index =>
        riemannSumConstant value lowerBound upperBound
          (integralSchedulePredecessor lowerBound upperBound (fun _ => 0) index))
      (convergesToConstant
        (mulReal (constantReal (subExact upperBound lowerBound)) value)))

/-- **Integral additivity** — at a SHARED modulus, `integralOfUC (f + g) ~
integralOfUC f + integralOfUC g`.  The shared modulus forces the SAME schedule for
all three, so `riemannSumAddReal` aligns pointwise; the shipped sum-limit law sends
the pointwise Riemann sums to the sum of limits, and diagonal-limit uniqueness
closes it. -/
theorem integralOfUCAddReal
    {leftFunction rightFunction : RegularReal → RegularReal} {modulus : Nat → Nat}
    (isLeftUC : IsUniformlyContinuous leftFunction modulus)
    (isRightUC : IsUniformlyContinuous rightFunction modulus)
    (isSumUC : IsUniformlyContinuous
      (fun value => addReal (leftFunction value) (rightFunction value)) modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound)) :
    DenotesSameReal
      (integralOfUC isSumUC lowerBound upperBound isIntervalNonNegative)
      (addReal
        (integralOfUC isLeftUC lowerBound upperBound isIntervalNonNegative)
        (integralOfUC isRightUC lowerBound upperBound isIntervalNonNegative)) :=
  denotesSameRealOfConvergesToBoth
    (convergesToLimitReal
      (riemannSumScheduleSequence isSumUC lowerBound upperBound isIntervalNonNegative))
    (convergesToOfPointwiseDenotesSameReal
      (fun index =>
        riemannSumAddReal leftFunction rightFunction lowerBound upperBound
          (integralSchedulePredecessor lowerBound upperBound modulus index))
      (convergesToAddReal
        (convergesToLimitReal
          (riemannSumScheduleSequence isLeftUC lowerBound upperBound
            isIntervalNonNegative))
        (convergesToLimitReal
          (riemannSumScheduleSequence isRightUC lowerBound upperBound
            isIntervalNonNegative))))

/-- **Integral homogeneity** — at a SHARED modulus, `integralOfUC (c * f) ~
c * integralOfUC f`.  The shared modulus forces the SAME schedule for both, so
`riemannSumScalarMulReal` aligns the scaled Riemann sums pointwise with the scaled
originals; the shipped scalar-limit law `convergesToScalarMulReal` sends the
original Riemann sequence's limit to `c` times it, and diagonal-limit uniqueness
closes it.  Like additivity, the scaled certificate `isScalarUC` is demanded at
the shared modulus — `integralOfUC` has no schedule-independence lemma, so the
honest Lipschitz modulus of `c * f` (which differs) cannot feed it directly. -/
theorem integralOfUCScalarMul
    {function : RegularReal → RegularReal} {modulus : Nat → Nat}
    (factor : RegularReal)
    (isFunctionUC : IsUniformlyContinuous function modulus)
    (isScalarUC : IsUniformlyContinuous
      (fun value => mulReal factor (function value)) modulus)
    (lowerBound upperBound : RationalPair)
    (isIntervalNonNegative : IsNonNegative (subExact upperBound lowerBound)) :
    DenotesSameReal
      (integralOfUC isScalarUC lowerBound upperBound isIntervalNonNegative)
      (mulReal factor
        (integralOfUC isFunctionUC lowerBound upperBound isIntervalNonNegative)) :=
  denotesSameRealOfConvergesToBoth
    (convergesToLimitReal
      (riemannSumScheduleSequence isScalarUC lowerBound upperBound
        isIntervalNonNegative))
    (convergesToOfPointwiseDenotesSameReal
      (fun index =>
        riemannSumScalarMulReal factor function lowerBound upperBound
          (integralSchedulePredecessor lowerBound upperBound modulus index))
      (convergesToScalarMulReal
        (convergesToLimitReal
          (riemannSumScheduleSequence isFunctionUC lowerBound upperBound
            isIntervalNonNegative))))

end FX1Poly.ComputerAlgebra
