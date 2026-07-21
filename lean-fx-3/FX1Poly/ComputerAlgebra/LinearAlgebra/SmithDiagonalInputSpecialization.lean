import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction

/-! # SmithDiagonalInputSpecialization — the diagonal-input specialization of the Smith keystone

The corrected-driver totality (`SmithReduceCompleteDriverStatement`) reduces to the single residual
`SmithCascadeLandedPivotDividesMinor`: the pivot-`p` clearing sweep lands, at the pivot, a divisor of
every entry of the input's `[p, ·)` minor.  This module specializes that keystone to window-diagonal
inputs — the shape the Phase-A output provably has (`smithReduceTotalSweepDiagonalizes`) — and shows the
specialization does not close the chain.  On a window-diagonal input the keystone's off-diagonal cells
are `0`, so its input-minor divisibility collapses to the diagonal half alone; but
`chainWindowedThroughPivots` invokes the keystone on the advanced matrix at every pivot `p ≥ 1`, and the
advanced matrix is generally non-diagonal (`smithDiagonalInputPivotOneInputNotWindowDiagonal` refutes
window-diagonality of the pivot-0 sweep output of `diag(15, 10, 6, 4)` at floor `1`, where its `[1, ·)`
minor carries `-20` at `(3, 1)`).  So the specialization discharges only the pivot-0 evaluation.  Also
shipped: the pairwise-gcd contract `IntPairwiseGcdSpec` and the iterated-pairwise-gcd common-divisor fact
`intGcdFoldrDividesAll`, the arithmetic half of the diagonal-common-divisor obligation.  The residual
`SmithCascadeLandedPivotDividesMinor` stays open.

Zero-axiom: `decide` on small `Int`/matrix literals, structural `List.foldr` recursion, explicit-witness
arithmetic over the shipped `intGcd*` / `intMulAssoc` / `entryAtBeyondZero` /
`matrixEntriesDivisibleByWithinOfHalves`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in the `FX1PolyAudit` twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The pairwise-gcd contract and value probes

The pairwise gcd `intGcd a b` and its structural facts are shipped elsewhere, riding the counting-Euclid
induction.  Here the values are probed on the battery by `decide`, then the shipped facts are bundled
into the reusable contract `IntPairwiseGcdSpec` (nonnegative common divisor, greatest).  The conditional
magnitude-descent half is the shipped `smithRepairDecreasesPivotSize` (`(intGcd a b).natAbs < a.natAbs`
when `0 < a.natAbs ∧ a ∤ b`), so it stays a companion rather than a contract field. -/

/-- `gcd(15, 10) = 5`. -/
theorem intGcdFifteenTen : intGcd 15 10 = 5 := by decide

/-- `gcd(6, 10) = 2`. -/
theorem intGcdSixTen : intGcd 6 10 = 2 := by decide

/-- `gcd(0, 4) = 4`: zero contributes nothing, the gcd is the other magnitude. -/
theorem intGcdZeroFour : intGcd 0 4 = 4 := by decide

/-- `gcd(-6, -4) = 2`: signs fold into magnitudes. -/
theorem intGcdNegSixNegFour : intGcd (-6) (-4) = 2 := by decide

/-- `gcd(6, -4) = 2` (the nonnegative representative). -/
theorem intGcdSixNegFour : intGcd 6 (-4) = 2 := by decide

/-- `gcd(-15, 10) = 5`. -/
theorem intGcdNegFifteenTen : intGcd (-15) 10 = 5 := by decide

/-- The pairwise-gcd contract over `Int`: `intGcd a b` is a nonnegative common divisor of the pair that
is greatest (every common divisor divides it).  The reusable cash-out of the counting-Euclid induction;
the conditional magnitude-descent half is the companion `smithRepairDecreasesPivotSize`. -/
structure IntPairwiseGcdSpec (leftValue rightValue : Int) : Prop where
  /-- The gcd is nonnegative (the canonical sign choice). -/
  isNonnegative : (0 : Int) ≤ intGcd leftValue rightValue
  /-- The gcd divides the left argument. -/
  dividesLeft : IntDivides (intGcd leftValue rightValue) leftValue
  /-- The gcd divides the right argument. -/
  dividesRight : IntDivides (intGcd leftValue rightValue) rightValue
  /-- Every common divisor of the pair divides the gcd. -/
  isGreatest : ∀ {commonDivisor : Int}, IntDivides commonDivisor leftValue →
    IntDivides commonDivisor rightValue → IntDivides commonDivisor (intGcd leftValue rightValue)

/-- `intGcd` satisfies the pairwise-gcd contract: assembles the shipped `intGcdIsNonnegative`,
`intGcdDividesLeft`, `intGcdDividesRight`, `intGcdGreatest` into the single contract object. -/
theorem intGcdSatisfiesPairwiseSpec (leftValue rightValue : Int) :
    IntPairwiseGcdSpec leftValue rightValue :=
  ⟨intGcdIsNonnegative leftValue rightValue,
   intGcdDividesLeft leftValue rightValue,
   intGcdDividesRight leftValue rightValue,
   fun dividesLeft dividesRight => intGcdGreatest dividesLeft dividesRight⟩

/-! ## The diagonal-input narrowing and the re-plumb refutation

On a window-diagonal input the keystone's input off-diagonal cells are `0`, so the input-minor
divisibility narrows to the diagonal common-divisor obligation alone.  This narrowing discharges only the
pivot-0 evaluation (the Phase-A output is window-diagonal); the chain carrier
`chainWindowedThroughPivots` needs the keystone on the pivot-`p ≥ 1` advanced matrices, which are
non-diagonal, as refuted below. -/

/-- On a window-diagonal input the off-diagonal half is free: every off-diagonal cell of the `[lo, ·)²`
quadrant of a window-diagonal rectangular matrix is `0` (in-window by `IsWindowDiagonal`, beyond-window by
`entryAtBeyondZero`), hence divisible by any `divisor`. -/
theorem subBlockOffDiagonalDivisibleOfWindowDiagonal {height width : Nat} (divisor : Int)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width) (lo : Nat)
    (isDiag : IsWindowDiagonal matrix lo height width) :
    SubBlockOffDiagonalDivisibleFrom divisor lo matrix := by
  intro rowIndex colIndex rowGe colGe rowNeCol
  cases Nat.lt_or_ge rowIndex height with
  | inl rowLt =>
      cases Nat.lt_or_ge colIndex width with
      | inl colLt =>
          rw [isDiag rowIndex colIndex rowGe rowLt colGe colLt rowNeCol]
          exact dividesExactlyZero divisor
      | inr colGeWidth =>
          rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inr colGeWidth)]
          exact dividesExactlyZero divisor
  | inr rowGeHeight =>
      rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inl rowGeHeight)]
      exact dividesExactlyZero divisor

/-- The keystone's input-minor obligation `MatrixEntriesDivisibleByWithin divisor lo matrix` on a
window-diagonal rectangular input follows from the diagonal-common-divisor obligation
`SubBlockDiagonalDivisibleFrom divisor lo matrix` alone, the off-diagonal half supplied by
`subBlockOffDiagonalDivisibleOfWindowDiagonal`. -/
theorem matrixEntriesDivisibleByWithinOfDiagonalInput {height width : Nat} (divisor : Int)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width) (lo : Nat)
    (isDiag : IsWindowDiagonal matrix lo height width)
    (diagDivisible : SubBlockDiagonalDivisibleFrom divisor lo matrix) :
    MatrixEntriesDivisibleByWithin divisor lo matrix :=
  matrixEntriesDivisibleByWithinOfHalves divisor lo matrix diagDivisible
    (subBlockOffDiagonalDivisibleOfWindowDiagonal divisor matrix isRect lo isDiag)

/-- The `SmithCascadeLandedPivotDividesMinor` obligation restricted to window-diagonal inputs and
narrowed to its diagonal-common-divisor content: on such an input, the pivot-`p` clearing-sweep landed
pivot divides every input diagonal entry of the `[p, ·)` window.  Strictly weaker than the unrestricted
keystone, and not enough to feed `chainWindowedThroughPivots`
(`smithDiagonalInputPivotOneInputNotWindowDiagonal`). -/
def SmithDiagonalInputLandedPivotDividesDiagonal : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    IsWindowDiagonal matrix pivotIndex height width →
    SubBlockDiagonalDivisibleFrom
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      matrix

/-- Given the diagonal-input-scoped keystone, the full input-minor divisibility
`MatrixEntriesDivisibleByWithin (landed pivot) pivotIndex matrix` holds on window-diagonal inputs,
composing the scoped obligation with `matrixEntriesDivisibleByWithinOfDiagonalInput`.  This is the
pivot-0 evaluation; it does not generalize to the chain, whose advanced matrices are non-diagonal. -/
theorem landedPivotDividesMinorOnDiagonalInput
    (diagonalCase : SmithDiagonalInputLandedPivotDividesDiagonal)
    (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pRowLt : pivotIndex < height) (pColLt : pivotIndex < width)
    (isDiag : IsWindowDiagonal matrix pivotIndex height width) :
    MatrixEntriesDivisibleByWithin
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      pivotIndex
      matrix :=
  matrixEntriesDivisibleByWithinOfDiagonalInput _ matrix isRect pivotIndex isDiag
    (diagonalCase matrix pivotIndex height width isRect pRowLt pColLt isDiag)

/-- The Phase-A total cross-clear sweep output is window-diagonal at floor `0`
(`smithReduceTotalSweepDiagonalizes`, the `0 ≤ ·` guards trivial).  So at pivot `0` the diagonal-input
hypothesis of the scoped keystone is discharged, not assumed. -/
theorem phaseAOutputIsWindowDiagonalAtZero (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    IsWindowDiagonal
      (matrix.applyOperations (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
      0 height width :=
  fun rowIndex colIndex _rowGe rowLt _colGe colLt rowNeCol =>
    smithReduceTotalSweepDiagonalizes matrix height width isRect rowIndex colIndex rowLt colLt rowNeCol

/-- Fixture `diag(15, 10, 6, 4)`: its pivot-0 clearing sweep sends the `(3, 1)` cell to `-20`, planting a
nonzero off-diagonal inside the pivot-1 window `[1, ·)²`. -/
def smithDiagonalInputReplumbFixture : IntMatrix :=
  { rows := [[15, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 4]] }

set_option maxRecDepth 8000 in
/-- The re-plumb refutation: the pivot-0 clearing-sweep output of `diag(15, 10, 6, 4)` is not
window-diagonal at floor `1`, its `[1, ·)` minor carrying `-20` at `(3, 1)` (`1 ≤ 3 < 4`, `1 ≤ 1 < 4`,
`3 ≠ 1`).  So `chainWindowedThroughPivots`, whose induction advances the matrix by the pivot-0 sweep,
cannot obtain `IsWindowDiagonal (advanced) 1 · ·` to invoke the diagonal-input keystone at pivot 1 — the
specialization discharges only pivot 0. -/
theorem smithDiagonalInputPivotOneInputNotWindowDiagonal :
    ¬ IsWindowDiagonal
        (smithDiagonalInputReplumbFixture.applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum smithDiagonalInputReplumbFixture 0 4 4)
            smithDiagonalInputReplumbFixture 0 4 4))
        1 4 4 :=
  fun isDiag =>
    absurd (isDiag 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-! ## The iterated pairwise gcd is a common divisor of the whole list

On a diagonal input the diagonal-common-divisor obligation is "the landed pivot divides each diagonal
entry `a_p … a_{n-1}`"; the value dividing all of them is the iterated pairwise gcd `foldr intGcd 0
[a_p, …]`.  This section proves the arithmetic half — that iterated gcd is a common divisor of every list
element — independent of the cascade.  The remaining gap (the cascade's landed pivot equals this fold) is
the open keystone: the fold does not compute the pairwise gcd of its two operands, only the whole-minor
min-abs descent lands the diagonal gcd. -/

/-- Transitivity of `IntDivides`: `a | b` and `b | c` give `a | c`, the cofactors multiplied through
`intMulAssoc`. -/
theorem intDividesTrans {leftValue midValue rightValue : Int}
    (leftDividesMid : IntDivides leftValue midValue)
    (midDividesRight : IntDivides midValue rightValue) :
    IntDivides leftValue rightValue :=
  match leftDividesMid, midDividesRight with
  | ⟨leftCofactor, midEquation⟩, ⟨midCofactor, rightEquation⟩ =>
      ⟨leftCofactor * midCofactor,
        rightEquation.trans
          ((congrArg (· * midCofactor) midEquation).trans
            (intMulAssoc leftValue leftCofactor midCofactor))⟩

/-- `divisor` divides every entry of a list, as a structural conjunction (`True` at the empty list). -/
def IntDividesAll (divisor : Int) : List Int → Prop
  | [] => True
  | head :: tail => IntDivides divisor head ∧ IntDividesAll divisor tail

/-- `IntDividesAll` is monotone under divisor descent: if `newDivisor | oldDivisor` and `oldDivisor`
divides every entry, then so does `newDivisor`.  Transitivity lifted pointwise over the list. -/
theorem intDividesAllMono {newDivisor oldDivisor : Int}
    (newDividesOld : IntDivides newDivisor oldDivisor) :
    ∀ {values : List Int}, IntDividesAll oldDivisor values → IntDividesAll newDivisor values
  | [], _ => trivial
  | _ :: _, ⟨headDivisible, tailDivisible⟩ =>
      ⟨intDividesTrans newDividesOld headDivisible, intDividesAllMono newDividesOld tailDivisible⟩

/-- The iterated pairwise gcd `foldr intGcd 0 values` divides every entry of `values`.  Structural on the
list: the head via `intGcdDividesLeft`, the tail via `intGcdDividesRight` and `intDividesAllMono`.  This
is the value dividing the diagonal; it does not assert the cascade lands it. -/
theorem intGcdFoldrDividesAll :
    ∀ values : List Int, IntDividesAll (List.foldr intGcd 0 values) values
  | [] => trivial
  | head :: tail =>
      ⟨intGcdDividesLeft head (List.foldr intGcd 0 tail),
       intDividesAllMono (intGcdDividesRight head (List.foldr intGcd 0 tail))
         (intGcdFoldrDividesAll tail)⟩

/-- `foldr intGcd 0 [6, 10, 8] = 2`, matching the cascade's landed pivot `2` on `diag(6, 10, 8)`
(`smithClearingSweepLandsMinorGcdOnConcreteWindow`). -/
theorem intGcdFoldrLandsDiagonalGcdOnConcreteWindow : List.foldr intGcd 0 [6, 10, 8] = 2 := by decide

/-- `2` divides every diagonal entry `6, 10, 8`, read off `intGcdFoldrDividesAll [6, 10, 8]` at the
reduced fold value `2`. -/
theorem intGcdFoldrDividesDiagonalOnConcreteWindow : IntDividesAll (2 : Int) [6, 10, 8] :=
  intGcdFoldrDividesAll [6, 10, 8]

/-! ## The pivot-0 firing

The chain does not close.  What is delivered is the pivot-0 firing: the diagonal-input-scoped keystone
discharges the input-minor divisibility on the Phase-A output for any rectangular input, hypothesis-free
in the diagonal condition (the Phase-A output is provably window-diagonal).  It stays conditional on the
open diagonal obligation `SmithDiagonalInputLandedPivotDividesDiagonal`; no hypothesis-free inhabitant of
`SmithReduceCompleteDriverStatement` is produced. -/

/-- The pivot-0 firing: given the diagonal-input-scoped keystone, the keystone's input-minor divisibility
holds on the Phase-A output at pivot `0`, the diagonal-input hypothesis discharged by
`phaseAOutputIsWindowDiagonalAtZero`.  Covers pivot 0 for any rectangular input; does not lift to pivots
`≥ 1` (`smithDiagonalInputPivotOneInputNotWindowDiagonal`), so does not close
`SmithReduceCompleteDriverStatement`. -/
theorem landedPivotDividesMinorOnPhaseAOutputAtZero
    (diagonalCase : SmithDiagonalInputLandedPivotDividesDiagonal)
    (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (heightPos : 0 < height) (widthPos : 0 < width) :
    MatrixEntriesDivisibleByWithin
      (((matrix.applyOperations
              (smithReduceTotalSweep (Nat.min height width) matrix 0 height width)).applyOperations
          (smithRepairPositionSweepClearing
            (smithMinorAbsSum
              (matrix.applyOperations
                (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
              0 height width)
            (matrix.applyOperations
              (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
            0 height width)).diagonalEntryAt 0)
      0
      (matrix.applyOperations
        (smithReduceTotalSweep (Nat.min height width) matrix 0 height width)) :=
  landedPivotDividesMinorOnDiagonalInput diagonalCase
    (matrix.applyOperations (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
    0 height width
    (applyOperationsPreservesRectangular _ matrix isRect)
    heightPos widthPos
    (phaseAOutputIsWindowDiagonalAtZero matrix height width isRect)

/-! ## Summary

The diagonal-input specialization narrows the keystone (on a window-diagonal input the off-diagonal half
is free) and covers pivot 0 (the Phase-A output is window-diagonal), but cannot re-plumb the chain:
`smithDiagonalInputPivotOneInputNotWindowDiagonal` refutes window-diagonality of the pivot-0 sweep output
at floor `1`, so `chainWindowedThroughPivots` cannot invoke the diagonal-input keystone at pivot `≥ 1`.
`SmithReduceCompleteDriverStatement` stays uninhabited hypothesis-free.  Two nested residuals survive: the
unrestricted keystone `SmithCascadeLandedPivotDividesMinor` (refuted as stated by
`SmithLandedMagnitudeRefuted` — seed `[[0,6,0],[0,0,10],[0,0,0]]` lands `6` vs minor gcd `2` — so it holds
only in restricted form), and its diagonal-input evaluation `SmithDiagonalInputLandedPivotDividesDiagonal`
(arithmetic half discharged by `intGcdFoldrDividesAll`; the surviving content is the
cascade-lands-the-diagonal-gcd correctness, the min-abs-descent wall).  The prior world stays byte-intact
(additive only). -/

end FX1Poly.ComputerAlgebra
