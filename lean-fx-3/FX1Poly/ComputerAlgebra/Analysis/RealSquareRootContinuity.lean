import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRoot
import FX1Poly.ComputerAlgebra.Analysis.RealContinuity

/-! # Real square-root continuity — Hölder-1/2 with a quadratic modulus
    (ANALYSIS-SQRTCONT-1)

The square root is uniformly continuous on the nonnegative reals with the
QUADRATIC modulus `omega k = sqrtSampleIndex k = (2k+2)^2 - 1`.  The shipped
Hölder-1/2 difference bound `sqrtApproxPairDifferenceBounded` does NOT lift
directly: at running index `i` it demands the TIGHT input hypothesis
`|a_i - b_i| <= 2/(deep+1)`, but a fixed continuity bound only delivers
`recip(modulus k) + 2/(deep+1)` — looser by the fixed `recip(modulus k)`, which
no fixed modulus can shed as `i -> infinity`.  That is exactly the
shrinking->fixed rework the `RealContinuity` scope note flagged.

It closes with NO analytic wall: the fixed input slack enters as an exact
grid-square `recip(modulus k) = (recip(sqrtGridIndex k))^2` (the shipped
`recipSampleDenotesGridSquare`), and `sqrtApproxPairDifferenceBoundedWithSlack`
— a faithful sibling of the shipped bound carrying that extra grid-square
through a THREE-term sum-of-squares drop — outputs the extra
`recip(sqrtGridIndex k) + recip(sqrtGridIndex k)`, which the shipped
`reciprocalDenotesGridSum` recombines with the running budget to
`recip k`.  Every ingredient is shipped and zero-axiom.

`sqrtReal` is a DEPENDENT map (`(value) -> IsNonNegativeReal value -> RegularReal`),
so it cannot inhabit the total-map `IsUniformlyContinuous`; the predicate
`IsUniformlyContinuousOnNonNeg` quantifies over nonnegative reals with their
proofs. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The three-term sum-of-squares drop -/

/-- **Three nonnegative squares sit below the square of the sum**:
`(a^2 + b^2) + c^2 <= ((a+b)+c)^2` — two applications of the shipped two-term
`sumSquaresLeSquareSumNonNeg`, folding `(a+b)` into one value. -/
theorem sumThreeSquaresLeSquareSumNonNeg {firstValue secondValue thirdValue :
    RationalPair}
    (isFirstNonNegative : IsNonNegative firstValue)
    (isSecondNonNegative : IsNonNegative secondValue)
    (isThirdNonNegative : IsNonNegative thirdValue) :
    LessEqualAs
      (addExact
        (addExact (mulExact firstValue firstValue) (mulExact secondValue secondValue))
        (mulExact thirdValue thirdValue))
      (mulExact (addExact (addExact firstValue secondValue) thirdValue)
        (addExact (addExact firstValue secondValue) thirdValue)) :=
  lessEqualAsTrans
    (addExactMonotoneLeft (mulExact thirdValue thirdValue)
      (sumSquaresLeSquareSumNonNeg isFirstNonNegative isSecondNonNegative))
    (sumSquaresLeSquareSumNonNeg
      (addExactIsNonNegative isFirstNonNegative isSecondNonNegative)
      isThirdNonNegative)

/-! ## The slack-carrying Hölder-1/2 difference bound -/

/-- **The one-sided sqrt-difference bound with a fixed grid-square slack** — the
shrinking->fixed sibling of `sqrtApproxPairDifferenceBounded`.  The input
regularity carries an extra `(recip slackGridPredecessor)^2`, and the output
carries the extra `recip slackGridPredecessor + recip slackGridPredecessor`.
The proof is the shipped skeleton with the fixed grid threaded: the input bound
resolves to `(gridFirst^2 + gridSecond^2) + slackGrid^2`, dominated by
`((gridFirst + gridSecond) + slackGrid)^2` via the three-term sum-of-squares,
and the remaining budget and half budget each absorb the doubled slack grid so
the reflect-and-shunt lands on `(recip firstIndex + recip secondIndex) +
(slackGrid + slackGrid)`. -/
theorem sqrtApproxPairDifferenceBoundedWithSlack {sampleFirst sampleSecond :
    RationalPair}
    (isSampleFirstNonNeg : IsNonNegative sampleFirst)
    (isSampleSecondNonNeg : IsNonNegative sampleSecond)
    (firstIndex secondIndex slackGridPredecessor : Nat)
    (inputRegular : IsWithinBound sampleFirst sampleSecond
      (addExact
        (addExact (reciprocalOfSucc (sqrtSampleIndex firstIndex))
          (reciprocalOfSucc (sqrtSampleIndex secondIndex)))
        (mulExact (reciprocalOfSucc slackGridPredecessor)
          (reciprocalOfSucc slackGridPredecessor)))) :
    LessEqualAs
      (subExact (rationalSqrtApprox sampleFirst (sqrtGridIndex firstIndex))
        (rationalSqrtApprox sampleSecond (sqrtGridIndex secondIndex)))
      (addExact
        (addExact (reciprocalOfSucc firstIndex) (reciprocalOfSucc secondIndex))
        (addExact (reciprocalOfSucc slackGridPredecessor)
          (reciprocalOfSucc slackGridPredecessor))) :=
  let gridStepFirst := reciprocalOfSucc (sqrtGridIndex firstIndex)
  let gridStepSecond := reciprocalOfSucc (sqrtGridIndex secondIndex)
  let slackGrid := reciprocalOfSucc slackGridPredecessor
  let rootFirst := rationalSqrtApprox sampleFirst (sqrtGridIndex firstIndex)
  let rootSecond := rationalSqrtApprox sampleSecond (sqrtGridIndex secondIndex)
  let inputBound :=
    addExact
      (addExact (reciprocalOfSucc (sqrtSampleIndex firstIndex))
        (reciprocalOfSucc (sqrtSampleIndex secondIndex)))
      (mulExact slackGrid slackGrid)
  let successorRoot := addExact rootSecond gridStepSecond
  let remainingBudget :=
    addExact (addExact (addExact gridStepFirst gridStepFirst) gridStepSecond)
      (addExact slackGrid slackGrid)
  let budgetHalf :=
    addExact
      (addExact (addExact gridStepFirst gridStepFirst)
        (addExact gridStepSecond gridStepSecond))
      (addExact slackGrid slackGrid)
  let isRootSecondNonNeg : IsNonNegative rootSecond :=
    rationalSqrtApproxIsNonNegative sampleSecond (sqrtGridIndex secondIndex)
  let isGridFirstNonNeg : IsNonNegative gridStepFirst :=
    ratioOfNatSuccIsNonNegative 1 (sqrtGridIndex firstIndex)
  let isGridSecondNonNeg : IsNonNegative gridStepSecond :=
    ratioOfNatSuccIsNonNegative 1 (sqrtGridIndex secondIndex)
  let isSlackGridNonNeg : IsNonNegative slackGrid :=
    ratioOfNatSuccIsNonNegative 1 slackGridPredecessor
  let isSuccessorRootNonNeg : IsNonNegative successorRoot :=
    addExactIsNonNegative isRootSecondNonNeg isGridSecondNonNeg
  let isDoubleSlackNonNeg : IsNonNegative (addExact slackGrid slackGrid) :=
    addExactIsNonNegative isSlackGridNonNeg isSlackGridNonNeg
  let isRemainingBudgetNonNeg : IsNonNegative remainingBudget :=
    addExactIsNonNegative
      (addExactIsNonNegative
        (addExactIsNonNegative isGridFirstNonNeg isGridFirstNonNeg)
        isGridSecondNonNeg)
      isDoubleSlackNonNeg
  let isBudgetHalfNonNeg : IsNonNegative budgetHalf :=
    addExactIsNonNegative
      (addExactIsNonNegative
        (addExactIsNonNegative isGridFirstNonNeg isGridFirstNonNeg)
        (addExactIsNonNegative isGridSecondNonNeg isGridSecondNonNeg))
      isDoubleSlackNonNeg
  let lowerBracket : LessEqualAs (mulExact rootFirst rootFirst) sampleFirst :=
    rationalSqrtApproxSqLe (sqrtGridIndex firstIndex) isSampleFirstNonNeg
  let successorToRoot :
      DenotesSameAs
        (ratioOfNatSucc
          (natSqrt (rationalSqrtRadicand sampleSecond (sqrtGridIndex secondIndex)) + 1)
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
      (rationalSqrtApproxSuccSqGe (sqrtGridIndex secondIndex) isSampleSecondNonNeg)
  let sampleFirstShifted :
      LessEqualAs sampleFirst (addExact sampleSecond inputBound) :=
    lessEqualAsAddOfSubLessEqual inputRegular.left
  let inputBoundAsSquares :
      DenotesSameAs inputBound
        (addExact
          (addExact (mulExact gridStepFirst gridStepFirst)
            (mulExact gridStepSecond gridStepSecond))
          (mulExact slackGrid slackGrid)) :=
    addExactRespectsDenotesSameAs
      (addExactRespectsDenotesSameAs (recipSampleDenotesGridSquare firstIndex)
        (recipSampleDenotesGridSquare secondIndex))
      (denotesSameAsRefl (mulExact slackGrid slackGrid))
  let gridSumSlack := addExact (addExact gridStepFirst gridStepSecond) slackGrid
  let isGridSumSlackNonNeg : IsNonNegative gridSumSlack :=
    addExactIsNonNegative
      (addExactIsNonNegative isGridFirstNonNeg isGridSecondNonNeg)
      isSlackGridNonNeg
  let gridSumSlackBelowRemaining : LessEqualAs gridSumSlack remainingBudget :=
    addExactMonotone
      (addExactMonotoneLeft gridStepSecond
        (lessEqualAsSelfAddNonNegRight gridStepFirst isGridFirstNonNeg))
      (lessEqualAsSelfAddNonNegRight slackGrid isSlackGridNonNeg)
  let squareOfGridSumBelow :
      LessEqualAs (mulExact gridSumSlack gridSumSlack)
        (mulExact remainingBudget remainingBudget) :=
    mulExactMonotoneOfNonNegative gridSumSlackBelowRemaining
      gridSumSlackBelowRemaining isGridSumSlackNonNeg isRemainingBudgetNonNeg
  let inputBoundBelowRemainingSquare :
      LessEqualAs inputBound (mulExact remainingBudget remainingBudget) :=
    lessEqualAsCongrLeft (denotesSameAsSymm inputBoundAsSquares)
      (lessEqualAsTrans
        (sumThreeSquaresLeSquareSumNonNeg isGridFirstNonNeg isGridSecondNonNeg
          isSlackGridNonNeg)
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
  let subReassociates :
      DenotesSameAs (addExact gridStepSecond remainingBudget) budgetHalf :=
    denotesSameAsTrans
      (denotesSameAsSymm
        (addExactAssoc gridStepSecond
          (addExact (addExact gridStepFirst gridStepFirst) gridStepSecond)
          (addExact slackGrid slackGrid)))
      (addExactRespectsDenotesSameAs
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs (denotesSameAsRefl gridStepSecond)
            (addExactComm (addExact gridStepFirst gridStepFirst) gridStepSecond))
          (denotesSameAsTrans
            (denotesSameAsSymm
              (addExactAssoc gridStepSecond gridStepSecond
                (addExact gridStepFirst gridStepFirst)))
            (addExactComm (addExact gridStepSecond gridStepSecond)
              (addExact gridStepFirst gridStepFirst))))
        (denotesSameAsRefl (addExact slackGrid slackGrid)))
  let sumReassociates :
      DenotesSameAs (addExact successorRoot remainingBudget)
        (addExact rootSecond budgetHalf) :=
    denotesSameAsTrans
      (addExactAssoc rootSecond gridStepSecond remainingBudget)
      (addExactRespectsDenotesSameAs (denotesSameAsRefl rootSecond) subReassociates)
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
    (addExactRespectsDenotesSameAs
      (denotesSameAsSymm
        (addExactRespectsDenotesSameAs (reciprocalDenotesGridSum firstIndex)
          (reciprocalDenotesGridSum secondIndex)))
      (denotesSameAsRefl (addExact slackGrid slackGrid)))
    differenceBelowBudgetHalf

/-! ## Uniform continuity on the nonnegative reals -/

/-- **Uniform continuity of a partial (nonnegativity-dependent) map** with an
explicit modulus — the total-map `IsUniformlyContinuous` cannot host `sqrtReal`
because it takes a nonnegativity proof, so the predicate quantifies over
nonnegative reals with their witnesses. -/
def IsUniformlyContinuousOnNonNeg
    (function : (value : RegularReal) → IsNonNegativeReal value → RegularReal)
    (modulus : Nat → Nat) : Prop :=
  ∀ (leftValue rightValue : RegularReal)
    (isLeftNonNeg : IsNonNegativeReal leftValue)
    (isRightNonNeg : IsNonNegativeReal rightValue) (outputPrecision : Nat),
    IsWithinRealBound leftValue rightValue
        (reciprocalOfSucc (modulus outputPrecision)) →
      IsWithinRealBound (function leftValue isLeftNonNeg)
        (function rightValue isRightNonNeg) (reciprocalOfSucc outputPrecision)

/-- **The square root is uniformly continuous on the nonnegative reals** with
the quadratic modulus `sqrtSampleIndex`.  At each running index the fixed input
slack `recip(sqrtSampleIndex k)` resolves to the grid-square
`recip(sqrtGridIndex k)^2`, the slack-carrying difference bound absorbs it, and
the output slack `recip(sqrtGridIndex k) + recip(sqrtGridIndex k)` recombines to
`recip k` — no residual analytic wall. -/
theorem sqrtRealIsUniformlyContinuous :
    IsUniformlyContinuousOnNonNeg sqrtReal (fun outputPrecision => sqrtSampleIndex outputPrecision) :=
  fun leftValue rightValue isLeftNonNeg isRightNonNeg outputPrecision isClose index =>
    let deepIndex := sqrtSampleIndex index
    let slackGrid := reciprocalOfSucc (sqrtGridIndex outputPrecision)
    let inputReshaped :
        IsWithinBound (leftValue.approximation deepIndex)
          (rightValue.approximation deepIndex)
          (addExact
            (addExact (reciprocalOfSucc (sqrtSampleIndex index))
              (reciprocalOfSucc (sqrtSampleIndex index)))
            (mulExact slackGrid slackGrid)) :=
      isWithinBoundCongrBound
        (denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (recipSampleDenotesGridSquare outputPrecision)
            (denotesSameAsSymm (ratioOfNatSuccSumDenotesSame 1 1 deepIndex)))
          (addExactComm (mulExact slackGrid slackGrid)
            (addExact (reciprocalOfSucc deepIndex) (reciprocalOfSucc deepIndex))))
        (isClose deepIndex)
    let outputReshape :
        DenotesSameAs
          (addExact
            (addExact (reciprocalOfSucc index) (reciprocalOfSucc index))
            (addExact slackGrid slackGrid))
          (addExact (reciprocalOfSucc outputPrecision) (ratioOfNatSucc 2 index)) :=
      denotesSameAsTrans
        (addExactRespectsDenotesSameAs (ratioOfNatSuccSumDenotesSame 1 1 index)
          (denotesSameAsSymm (reciprocalDenotesGridSum outputPrecision)))
        (addExactComm (ratioOfNatSucc 2 index) (reciprocalOfSucc outputPrecision))
    ⟨lessEqualAsCongrRight outputReshape
        (sqrtApproxPairDifferenceBoundedWithSlack (isLeftNonNeg deepIndex)
          (isRightNonNeg deepIndex) index index (sqrtGridIndex outputPrecision)
          inputReshaped),
      lessEqualAsCongrRight outputReshape
        (sqrtApproxPairDifferenceBoundedWithSlack (isRightNonNeg deepIndex)
          (isLeftNonNeg deepIndex) index index (sqrtGridIndex outputPrecision)
          (isWithinBoundSymm inputReshaped))⟩

end FX1Poly.ComputerAlgebra
