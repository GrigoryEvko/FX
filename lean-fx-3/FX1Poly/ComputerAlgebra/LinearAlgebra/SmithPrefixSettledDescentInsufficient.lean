import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithFoldDescentRefuted
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachablePrefixConfinement

/-! # Smith prefix-settled descent is insufficient; the corrected guard is below-pivot-column confinement

The proposed guard `SmithPrefixSettled` for the one-round `pivotMagnitudeWithin` descent is false: it is
vacuous at `pivotIndex = 0` (`smithPrefixSettledZero` holds for every matrix), so the counterexample
`[[2,0],[4,3]]` satisfies it yet the fold raises the magnitude from 2 to 3. The load-bearing replacement is
`belowPivotColumnConfined` (`|entry(pivotIndex+1, pivotIndex)| <= |pivot|`), which excludes the
counterexample and holds on the reachable dirty-found-column carrier, where the fold descends. The
corrected one-round candidate `SmithFoldDescendsOnConfinedNonzeroPivot` and the fuel-driver instantiation
`smithClearingOutputFindNoneFromConfinedFoldDescent` are stated, the latter consuming the confined descent
and a confinement-preservation invariant as hypotheses. `SmithReduceCompleteDriverStatement` is not
inhabited here. Raw Lean 4 (`Init` only), structural, zero axioms with a per-declaration audit twin. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The corrected lever and the refutation of the prefix-settled gate -/

/-- The below-pivot pivot-column magnitude confinement: the fill-in entry `(pivotIndex+1, pivotIndex)`
does not exceed the pivot in magnitude. On the reachable carrier this holds with equality; the
counterexample `[[2,0],[4,3]]` violates it (`4 > 2`). Strictly sharper than `SmithPrefixSettled`, which
constrains nothing in column `pivotIndex`. -/
def belowPivotColumnConfined (matrix : IntMatrix) (pivotIndex : Nat) : Prop :=
  (matrix.entryAt (pivotIndex + 1) pivotIndex).natAbs ≤ (matrix.diagonalEntryAt pivotIndex).natAbs

/-- The proposed guard: the raw single-fold `pivotMagnitudeWithin` descent obligation
`SmithFoldDescendsOnNonzeroPivot` additionally guarded by the confinement invariant `SmithPrefixSettled`.
A `Prop`, refuted below. -/
def SmithFoldDescendsOnPrefixSettledNonzeroPivot : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    SmithPrefixSettled work pivotIndex height width →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

/-- The prefix-settled guard is false. `SmithPrefixSettled work pivotIndex ...` is vacuous at
`pivotIndex = 0` (`smithPrefixSettledZero` holds for every matrix), so the counterexample `[[2,0],[4,3]]`
satisfies the guard together with the other preconditions (rectangular, positive pivot, `find = some 1`),
yet the fold raises the magnitude from 2 to 3. The same matrix that refutes the raw obligation refutes the
guarded one; the corrected lever `belowPivotColumnConfined` is what excludes it. -/
theorem smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted :
    ¬ SmithFoldDescendsOnPrefixSettledNonzeroPivot := by
  intro foldDescends
  exact smithFoldStepRaisesPivotOnCounterexample
    (foldDescends smithFoldDescentCounterexample 1 0 2 2
      smithFoldDescentCounterexampleIsRectangular
      (smithPrefixSettledZero smithFoldDescentCounterexample 2 2)
      smithFoldDescentCounterexamplePivotPositive
      smithFoldDescentCounterexampleFindsSome)

/-! ## The confinement guard separates the counterexample from the reachable witness -/

/-- The confinement guard rejects the counterexample: `¬ belowPivotColumnConfined [[2,0],[4,3]] 0`, since
the below-pivot entry `(1,0) = 4` exceeds the pivot `|2| = 2` in magnitude. Where the vacuous
`SmithPrefixSettled` admitted it, confinement puts the descent-raising shape out of scope of the corrected
candidate. -/
theorem smithConfinedGuardExcludesRefuter :
    ¬ belowPivotColumnConfined smithFoldDescentCounterexample 0 := by
  unfold belowPivotColumnConfined; decide

/-- The reachable dirty-found-column state satisfies the confinement guard. On
`smithDirtyFoundColumnDriverWitness` (the pivot-2 sweep-start state the corrected driver reaches on
`diag(4,6,9,7)`, with `find = some 3` and nonzero fill-in `entry(3,2) = -126`), the fill-in magnitude
equals the pivot magnitude, so `belowPivotColumnConfined ... 2` holds even where the pivot column is
dirty. -/
theorem smithDriverWitnessConfined :
    belowPivotColumnConfined smithDirtyFoundColumnDriverWitness 2 := by
  unfold belowPivotColumnConfined; decide

set_option maxRecDepth 100000 in
/-- The descent conclusion holds on that reachable witness. On the dirty-found-column obstruction state
(`smithDirtyFoundColumnDriverWitness`, pivot 2, `find = some 3`), which satisfies the confinement guard,
the fold strictly descends `pivotMagnitudeWithin` from 126 to 12: the corrected candidate's conclusion is
true precisely where the raw obligation was refuted, once the state is confined. Evidence on the reachable
carrier, not a proof of the universal. -/
theorem smithConfinedFoldDescendsOnDriverWitness :
    pivotMagnitudeWithin (smithClearingFoldStep smithDirtyFoundColumnDriverWitness 3 2 4 4) 2
      < pivotMagnitudeWithin smithDirtyFoundColumnDriverWitness 2 := by decide

/-! ## The corrected one-round candidate -/

/-- The corrected one-round candidate: the `belowPivotColumnConfined`-guarded single-fold
`pivotMagnitudeWithin` descent, asserting strict descent on every confined nonzero-pivot fold. Unlike the
refuted `SmithPrefixSettled` gate, confinement excludes the counterexample
(`smithConfinedGuardExcludesRefuter`) and holds on the reachable dirty-column carrier
(`smithDriverWitnessConfined`, `smithConfinedFoldDescendsOnDriverWitness`). A `Prop`, not proved here: its
universal proof is the cascade-output-magnitude descent under confinement, and the shipped output bound
reaches only the minimum-magnitude entry, short of the gcd. -/
def SmithFoldDescendsOnConfinedNonzeroPivot : Prop :=
  ∀ (work : IntMatrix) (foundPos pivotIndex height width : Nat), work.IsRectangular height width →
    belowPivotColumnConfined work pivotIndex →
    0 < (work.diagonalEntryAt pivotIndex).natAbs →
    smithFindNonDividingLaterDiagonal work pivotIndex
        (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
    pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
      < pivotMagnitudeWithin work pivotIndex

/-! ## The fuel-driver instantiation on the confined invariant -/

/-- The fuel-driver instantiation on the confined invariant. Instantiates the shipped strong-induction
driver `smithClearingSweepReachesFindNoneOfGuardedDescent` (structural `Nat.rec` on the `natAbs` budget,
never `WellFounded.fix`) with `measure := pivotMagnitudeWithin` and `invariant := ZeroTrailingDiagonalsFrom
∧ belowPivotColumnConfined`; the zero-pivot base is discharged by `smithZeroPivotImpliesFindNone`, the
budget by `pivotMagnitudeLeMinorAbsSum`. The clearing sweep reports `find = none` given, as hypotheses, the
confined descent (`foldDescends`), the preservation invariant (`foldKeepsInvariant`), and terminal
preservation (`terminalKeepsFindNone`). -/
theorem smithClearingOutputFindNoneFromConfinedFoldDescent
    (pivotIndex height width : Nat)
    (foldDescends : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnConfined work pivotIndex) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          pivotMagnitudeWithin (smithClearingFoldStep work foundPos pivotIndex height width) pivotIndex
            < pivotMagnitudeWithin work pivotIndex)
    (foldKeepsInvariant : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnConfined work pivotIndex) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        ∀ foundPos, smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some foundPos →
          (ZeroTrailingDiagonalsFrom pivotIndex height width
              (smithClearingFoldStep work foundPos pivotIndex height width)
            ∧ belowPivotColumnConfined (smithClearingFoldStep work foundPos pivotIndex height width)
                pivotIndex))
    (terminalKeepsFindNone : ∀ (work : IntMatrix),
        (ZeroTrailingDiagonalsFrom pivotIndex height width work
          ∧ belowPivotColumnConfined work pivotIndex) →
        work.IsRectangular height width → pivotIndex < height → pivotIndex < width →
        smithFindNonDividingLaterDiagonal work pivotIndex
            (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none →
          smithFindNonDividingLaterDiagonal (smithClearingTerminalStep work pivotIndex height width)
            pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none)
    (matrix : IntMatrix)
    (baseZeroTrailing : ZeroTrailingDiagonalsFrom pivotIndex height width matrix)
    (baseConfined : belowPivotColumnConfined matrix pivotIndex)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width) :
    smithFindNonDividingLaterDiagonal
      (matrix.applyOperations (smithRepairPositionSweepClearing
        (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width))
      pivotIndex (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = none :=
  smithClearingSweepReachesFindNoneOfGuardedDescent pivotIndex height width
    (fun work => pivotMagnitudeWithin work pivotIndex)
    (fun work => ZeroTrailingDiagonalsFrom pivotIndex height width work
      ∧ belowPivotColumnConfined work pivotIndex)
    (fun work invHolds pivotMag0 =>
      smithZeroPivotImpliesFindNone work pivotIndex height width (invHolds.1 pivotMag0) pivotMag0)
    terminalKeepsFindNone
    foldDescends
    foldKeepsInvariant
    (smithMinorAbsSum matrix pivotIndex height width) matrix ⟨baseZeroTrailing, baseConfined⟩
    isRect pRowLt pColLt
    (pivotMagnitudeLeMinorAbsSum matrix pivotIndex height width pRowLt pColLt)

/-! ## Open obligations

No hypothesis-free inhabitant of `SmithReduceCompleteDriverStatement` is produced. The confined fuel route
rests on two open legs: the confined one-round descent `SmithFoldDescendsOnConfinedNonzeroPivot`, whose gap
from the minimum-magnitude entry to the gcd is the multi-round Euclid reduction; and the
confinement-preservation invariant, that the fold keeps `belowPivotColumnConfined` along the sweep (not
supplied by `reachableImpliesPrefixSettled`, which leaves column `pivotIndex` unconstrained). The
off-diagonal half `SmithClearingOutputOffDiagonalDivides` remains separate, and the round-level divisor
chain `pivot(n+1) | pivot(n)` is refuted, not stated. -/

end FX1Poly.ComputerAlgebra
