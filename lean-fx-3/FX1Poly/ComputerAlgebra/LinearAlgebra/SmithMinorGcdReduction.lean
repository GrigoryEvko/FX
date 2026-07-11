import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithInteriorConfinement
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowGcdInvariance

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithMinorGcdReduction — the keystone sharpened to a
    ONE-dimensional diagonal residual: `landed | gcd(minor)` (H2-SMITH r29, #2261)

The corrected-driver totality rests (since r22) on the single Prop
`SmithCascadeLandedPivotDividesMinor` (`SmithWindowedChainReduction`): the landed pivot
`g := M'.diagonalEntryAt p` divides EVERY entry of the input's `[p, ·) × [p, ·)` minor — the
transient interior fill-in INCLUDED (the r26 confinement witness `diag(1,-12,-18,10)` shows genuine
fill-in `(3,2) = -90` with `g = 2 ∣ -90`).

The r25 gcd-invariance brick `commonDivisorOfInputMinorDividesLandedPivot`
(`SmithWindowGcdInvariance`) already delivers the CONTAINMENT direction `gcd(minor) ∣ g` (every
common divisor of the minor divides the landed pivot).  This module supplies the concrete gcd of the
minor and both universal-property halves, and reads off the equivalence:

  `SmithCascadeLandedPivotDividesMinor  ↔  (landed pivot ∣ gcd(minor))`   (`keystoneIffLandedDividesMinorGcd`)

so the keystone — a 2-D whole-block `∀` over the minor, interior fill-in and all — SHARPENS to the
1-D scalar `g ∣ gcd(minor)`.  Combined with the SHIPPED converse `gcd(minor) ∣ g`, the residual is the
symmetric magnitude equality `|g| = gcd(minor)` (`landedMagnitudeEqMinorGcdOfKeystone`, conditional on
the keystone): the classic "min-abs Euclid diagonal descent reaches the gcd".

**What this ships (all zero-axiom, additive; the r18–r28 world byte-intact).**

  * `dividesExactlyTrans` — transitivity of `dividesExactly` (not previously shipped).
  * `minorGcdWithin` — the gcd of the `[p, ·) × [p, ·)` window minor (nested `intGcd`-fold mirroring
    `smithMinorAbsSum`'s shape), with its TWO universal-property halves:
      - `minorGcdWithinDividesWithin` — `minorGcdWithin ∣ every minor entry` (interior fill-in
        included; out-of-window cells are `0` by `entryAtBeyondZero`).
      - `minorGcdWithinGreatest` — every common divisor of the minor divides `minorGcdWithin`.
  * `keystoneIffLandedDividesMinorGcd` — the keystone ⟺ `landed ∣ gcd(minor)` equivalence.
  * `minorGcdDividesLanded` — `gcd(minor) ∣ landed`, HYPOTHESIS-FREE (the r25 converse instantiated at
    `divisor := minorGcdWithin`).
  * `landedMagnitudeEqMinorGcdOfKeystone` — `keystone → |landed| = gcd(minor)` (the symmetric residual).

**HONEST SIZING — this does NOT flip the driver.**  The keystone stays OPEN; nothing here inhabits
`SmithReduceCompleteDriverStatement` hypothesis-free.  This file RETIRES the interior-fill-in worry
(the 2-D block obligation is proven a spectator, auto-confined) and pins the surviving wall to the
single diagonal fact `landed ∣ gcd(minor)`.  The surviving wall is named at the foot of the file.

Raw Lean 4 + `Init`, STRUCTURAL only; no `axiom`/`sorry`/`propext`/`Quot.sound`/`Classical`/`omega`/
`native_decide`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithMinorGcdReduction.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## B1 — transitivity of exact divisibility -/

/-- **Transitivity of `dividesExactly`** — if `leftValue ∣ midValue` and `midValue ∣ rightValue`, then
`leftValue ∣ rightValue`.  The cofactor is the product of the two witnesses, associated by
`intMulAssoc`.  Not previously shipped (only `dividesExactlyZero`/`Neg`/`AddScaled`/`TransportsUnderSign`
exist). -/
theorem dividesExactlyTrans {leftValue midValue rightValue : Int}
    (leftDividesMid : dividesExactly leftValue midValue)
    (midDividesRight : dividesExactly midValue rightValue) :
    dividesExactly leftValue rightValue :=
  match leftDividesMid, midDividesRight with
  | ⟨factorLeft, midEquation⟩, ⟨factorRight, rightEquation⟩ =>
      ⟨factorLeft * factorRight,
        rightEquation.trans
          ((congrArg (· * factorRight) midEquation).trans
            (intMulAssoc leftValue factorLeft factorRight))⟩

/-! ## B2 — the minor gcd and its two universal-property halves -/

/-- The gcd of `colCount` entries of row `rowIndex` starting at column `colStart` — nested `intGcd`
fold, structural on `colCount` (the empty fold is `0`, the neutral gcd element). -/
def minorGcdRow (matrix : IntMatrix) (rowIndex : Nat) : Nat → Nat → Int
  | 0, _ => 0
  | colCount + 1, colStart =>
      intGcd (matrix.entryAt rowIndex colStart)
        (minorGcdRow matrix rowIndex colCount (colStart + 1))

/-- The gcd over `rowCount` rows from `rowStart`, each folding `colCount` columns from `colStart` —
structural on `rowCount`. -/
def minorGcdRows (matrix : IntMatrix) (colStart colCount : Nat) : Nat → Nat → Int
  | 0, _ => 0
  | rowCount + 1, rowStart =>
      intGcd (minorGcdRow matrix rowStart colCount colStart)
        (minorGcdRows matrix colStart colCount rowCount (rowStart + 1))

/-- **The gcd of the `[pivotIndex, ·) × [pivotIndex, ·)` window minor** — mirrors `smithMinorAbsSum`'s
`(colStart, colCount, rowCount, rowStart) = (pivotIndex, width - pivotIndex, height - pivotIndex,
pivotIndex)` shape, but folds `intGcd` instead of magnitude-sum. -/
def minorGcdWithin (matrix : IntMatrix) (pivotIndex height width : Nat) : Int :=
  minorGcdRows matrix pivotIndex (width - pivotIndex) (height - pivotIndex) pivotIndex

/-- **The row gcd divides each entry in its window** — for every `colIndex` in
`[colStart, colStart + colCount)`, `minorGcdRow matrix rowIndex colCount colStart ∣ entryAt rowIndex
colIndex`.  Structural on `colCount`: the head is `intGcdDividesLeft`, the tail rides `dividesExactlyTrans`
through `intGcdDividesRight`. -/
theorem minorGcdRowDividesEntry (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart colIndex : Nat), colStart ≤ colIndex → colIndex < colStart + colCount →
      dividesExactly (minorGcdRow matrix rowIndex colCount colStart) (matrix.entryAt rowIndex colIndex) := by
  intro colCount
  induction colCount with
  | zero =>
      intro colStart colIndex colGe colLt
      exact absurd (Nat.lt_of_lt_of_le colLt colGe) (Nat.lt_irrefl colIndex)
  | succ colCount ih =>
      intro colStart colIndex colGe colLt
      show dividesExactly (intGcd (matrix.entryAt rowIndex colStart)
        (minorGcdRow matrix rowIndex colCount (colStart + 1))) (matrix.entryAt rowIndex colIndex)
      cases Nat.eq_or_lt_of_le colGe with
      | inl atHead =>
          rw [← atHead]
          exact intGcdDividesLeft (matrix.entryAt rowIndex colStart)
            (minorGcdRow matrix rowIndex colCount (colStart + 1))
      | inr beyondHead =>
          have colGeSucc : colStart + 1 ≤ colIndex := beyondHead
          have colLtShift : colIndex < (colStart + 1) + colCount := by
            rw [Nat.succ_add]; exact colLt
          exact dividesExactlyTrans
            (intGcdDividesRight (matrix.entryAt rowIndex colStart)
              (minorGcdRow matrix rowIndex colCount (colStart + 1)))
            (ih (colStart + 1) colIndex colGeSucc colLtShift)

/-- **The rows gcd divides each row gcd in its window** — for every `rowIndex` in
`[rowStart, rowStart + rowCount)`, `minorGcdRows ∣ minorGcdRow matrix rowIndex colCount colStart`.
Structural on `rowCount`, dual to `minorGcdRowDividesEntry`. -/
theorem minorGcdRowsDividesRow (matrix : IntMatrix) (colStart colCount : Nat) :
    ∀ (rowCount rowStart rowIndex : Nat), rowStart ≤ rowIndex → rowIndex < rowStart + rowCount →
      dividesExactly (minorGcdRows matrix colStart colCount rowCount rowStart)
        (minorGcdRow matrix rowIndex colCount colStart) := by
  intro rowCount
  induction rowCount with
  | zero =>
      intro rowStart rowIndex rowGe rowLt
      exact absurd (Nat.lt_of_lt_of_le rowLt rowGe) (Nat.lt_irrefl rowIndex)
  | succ rowCount ih =>
      intro rowStart rowIndex rowGe rowLt
      show dividesExactly (intGcd (minorGcdRow matrix rowStart colCount colStart)
        (minorGcdRows matrix colStart colCount rowCount (rowStart + 1)))
        (minorGcdRow matrix rowIndex colCount colStart)
      cases Nat.eq_or_lt_of_le rowGe with
      | inl atHead =>
          rw [← atHead]
          exact intGcdDividesLeft (minorGcdRow matrix rowStart colCount colStart)
            (minorGcdRows matrix colStart colCount rowCount (rowStart + 1))
      | inr beyondHead =>
          have rowGeSucc : rowStart + 1 ≤ rowIndex := beyondHead
          have rowLtShift : rowIndex < (rowStart + 1) + rowCount := by
            rw [Nat.succ_add]; exact rowLt
          exact dividesExactlyTrans
            (intGcdDividesRight (minorGcdRow matrix rowStart colCount colStart)
              (minorGcdRows matrix colStart colCount rowCount (rowStart + 1)))
            (ih (rowStart + 1) rowIndex rowGeSucc rowLtShift)

/-- **The rows gcd divides each entry of the window block** — composition of the two window-divides
folds through `dividesExactlyTrans`. -/
theorem minorGcdRowsDividesEntry (matrix : IntMatrix)
    (colStart colCount rowCount rowStart rowIndex colIndex : Nat)
    (rowGe : rowStart ≤ rowIndex) (rowLt : rowIndex < rowStart + rowCount)
    (colGe : colStart ≤ colIndex) (colLt : colIndex < colStart + colCount) :
    dividesExactly (minorGcdRows matrix colStart colCount rowCount rowStart)
      (matrix.entryAt rowIndex colIndex) :=
  dividesExactlyTrans
    (minorGcdRowsDividesRow matrix colStart colCount rowCount rowStart rowIndex rowGe rowLt)
    (minorGcdRowDividesEntry matrix rowIndex colCount colStart colIndex colGe colLt)

/-- **The minor gcd divides every cell of the `[pivotIndex, ·)²` quadrant** (the FIRST universal-property
half): `MatrixEntriesDivisibleByWithin (minorGcdWithin matrix pivotIndex height width) pivotIndex matrix`.
In-window cells are divided by the fold (`minorGcdRowsDividesEntry`, ranges bridged by the propext-clean
`natLtAddSubOfLt`); beyond-window cells read `0` (`entryAtBeyondZero`), divisible by anything. -/
theorem minorGcdWithinDividesWithin (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    MatrixEntriesDivisibleByWithin (minorGcdWithin matrix pivotIndex height width) pivotIndex matrix := by
  intro rowIndex rowGe colIndex colGe
  show dividesExactly (minorGcdWithin matrix pivotIndex height width) (matrix.entryAt rowIndex colIndex)
  cases Nat.lt_or_ge rowIndex height with
  | inr rowGeHeight =>
      rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inl rowGeHeight)]
      exact dividesExactlyZero (minorGcdWithin matrix pivotIndex height width)
  | inl rowLt =>
      cases Nat.lt_or_ge colIndex width with
      | inr colGeWidth =>
          rw [entryAtBeyondZero matrix isRect rowIndex colIndex (Or.inr colGeWidth)]
          exact dividesExactlyZero (minorGcdWithin matrix pivotIndex height width)
      | inl colLt =>
          exact minorGcdRowsDividesEntry matrix pivotIndex (width - pivotIndex) (height - pivotIndex)
            pivotIndex rowIndex colIndex rowGe (natLtAddSubOfLt pivotIndex rowIndex height rowGe rowLt)
            colGe (natLtAddSubOfLt pivotIndex colIndex width colGe colLt)

/-- **Every common divisor of the row window divides its row gcd** (the greatest half, row level).
Structural on `colCount` through `intGcdGreatest`; the hypothesis need only cover the upper set
`colStart ≤ colIndex` (an `intGcd` fold touches only those columns). -/
theorem minorGcdRowGreatest (matrix : IntMatrix) (rowIndex : Nat) (divisor : Int) :
    ∀ (colCount colStart : Nat),
      (∀ colIndex, colStart ≤ colIndex → dividesExactly divisor (matrix.entryAt rowIndex colIndex)) →
      dividesExactly divisor (minorGcdRow matrix rowIndex colCount colStart) := by
  intro colCount
  induction colCount with
  | zero => intro colStart _; exact dividesExactlyZero divisor
  | succ colCount ih =>
      intro colStart dividesUpperColumns
      show dividesExactly divisor (intGcd (matrix.entryAt rowIndex colStart)
        (minorGcdRow matrix rowIndex colCount (colStart + 1)))
      exact intGcdGreatest
        (dividesUpperColumns colStart (Nat.le_refl colStart))
        (ih (colStart + 1)
          (fun colIndex colGeSucc => dividesUpperColumns colIndex (Nat.le_of_succ_le colGeSucc)))

/-- **Every common divisor of the block divides its rows gcd** (the greatest half, rows level).
Structural on `rowCount` through `intGcdGreatest` and `minorGcdRowGreatest`. -/
theorem minorGcdRowsGreatest (matrix : IntMatrix) (colStart colCount : Nat) (divisor : Int) :
    ∀ (rowCount rowStart : Nat),
      (∀ rowIndex, rowStart ≤ rowIndex →
        ∀ colIndex, colStart ≤ colIndex → dividesExactly divisor (matrix.entryAt rowIndex colIndex)) →
      dividesExactly divisor (minorGcdRows matrix colStart colCount rowCount rowStart) := by
  intro rowCount
  induction rowCount with
  | zero => intro rowStart _; exact dividesExactlyZero divisor
  | succ rowCount ih =>
      intro rowStart dividesUpperRows
      show dividesExactly divisor (intGcd (minorGcdRow matrix rowStart colCount colStart)
        (minorGcdRows matrix colStart colCount rowCount (rowStart + 1)))
      exact intGcdGreatest
        (minorGcdRowGreatest matrix rowStart divisor colCount colStart
          (fun colIndex colGe => dividesUpperRows rowStart (Nat.le_refl rowStart) colIndex colGe))
        (ih (rowStart + 1)
          (fun rowIndex rowGeSucc colIndex colGe =>
            dividesUpperRows rowIndex (Nat.le_of_succ_le rowGeSucc) colIndex colGe))

/-- **The minor gcd is greatest** (the SECOND universal-property half): any `divisor` dividing every
`[pivotIndex, ·)²` cell divides `minorGcdWithin`.  Reads the whole-block divisibility off
`MatrixEntriesDivisibleByWithin` (upper set at `pivotIndex`) into `minorGcdRowsGreatest`.  No
rectangularity needed — the greatest direction folds only in-range cells. -/
theorem minorGcdWithinGreatest (matrix : IntMatrix) (pivotIndex height width : Nat) (divisor : Int)
    (dividesMinor : MatrixEntriesDivisibleByWithin divisor pivotIndex matrix) :
    dividesExactly divisor (minorGcdWithin matrix pivotIndex height width) :=
  minorGcdRowsGreatest matrix pivotIndex (width - pivotIndex) divisor (height - pivotIndex) pivotIndex
    (fun rowIndex rowGe colIndex colGe =>
      matrixEntriesDivisibleByWithinAt dividesMinor rowIndex colIndex rowGe colGe)

/-! ## B3 — the keystone sharpened to `landed | gcd(minor)` -/

/-- **The 1-D sharpened residual**: after the pivot-`pivotIndex` clearing repair sweep, the landed pivot
divides the gcd of the input's `[pivotIndex, ·)` minor.  Equivalent to the whole-block keystone
`SmithCascadeLandedPivotDividesMinor` (`keystoneIffLandedDividesMinorGcd`) — the 2-D minor `∀` collapses
to this scalar. -/
def LandedPivotDividesMinorGcd : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width → pivotIndex < height → pivotIndex < width →
    dividesExactly
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (minorGcdWithin matrix pivotIndex height width)

/-- **The keystone ⟺ `landed ∣ gcd(minor)`.**  Forward: the keystone says the landed pivot divides every
minor entry, so it is a common divisor, so it divides the gcd (`minorGcdWithinGreatest`).  Backward: from
`landed ∣ gcd` and `gcd ∣ every minor entry` (`minorGcdWithinDividesWithin`), transitivity gives `landed`
divides every minor entry — the keystone body.  The 2-D whole-block obligation is thus equivalent to the
1-D scalar, retiring the interior-fill-in worry. -/
theorem keystoneIffLandedDividesMinorGcd :
    SmithCascadeLandedPivotDividesMinor ↔ LandedPivotDividesMinorGcd := by
  constructor
  · intro keystone matrix pivotIndex height width isRect pRowLt pColLt
    exact minorGcdWithinGreatest matrix pivotIndex height width
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (keystone matrix pivotIndex height width isRect pRowLt pColLt)
  · intro landedDividesGcd matrix pivotIndex height width isRect pRowLt pColLt
    intro rowIndex rowGe colIndex colGe
    show dividesExactly
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
      (matrix.entryAt rowIndex colIndex)
    exact dividesExactlyTrans
      (landedDividesGcd matrix pivotIndex height width isRect pRowLt pColLt)
      (minorGcdWithinDividesWithin matrix pivotIndex height width isRect rowIndex rowGe colIndex colGe)

/-! ## B4 — the shipped converse `gcd | landed` and the symmetric magnitude residual -/

/-- **`gcd(minor) ∣ landed`, HYPOTHESIS-FREE** — the r25 gcd-invariance converse
`commonDivisorOfInputMinorDividesLandedPivot` instantiated at `divisor := minorGcdWithin`, discharging its
premise with `minorGcdWithinDividesWithin`.  This is the SHIPPED half of the symmetric `|landed| =
gcd(minor)`; the other half `landed ∣ gcd(minor)` is exactly the open keystone. -/
theorem minorGcdDividesLanded (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height)
    (pColLt : pivotIndex < width) :
    dividesExactly (minorGcdWithin matrix pivotIndex height width)
      ((matrix.applyOperations
          (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).diagonalEntryAt pivotIndex) :=
  commonDivisorOfInputMinorDividesLandedPivot matrix pivotIndex height width
    (minorGcdWithin matrix pivotIndex height width) pRowLt pColLt
    (minorGcdWithinDividesWithin matrix pivotIndex height width isRect)

/-- **`keystone → |landed| = gcd(minor)`** — the symmetric magnitude equality.  Given the keystone,
`landed ∣ gcd` (`keystoneIffLandedDividesMinorGcd`) and, unconditionally, `gcd ∣ landed`
(`minorGcdDividesLanded`); descend both to `natAbs` and close by `natDividesAntisymm`.  The final content
of the wall: the min-abs Euclid diagonal descent lands a value whose magnitude IS the minor gcd. -/
theorem landedMagnitudeEqMinorGcdOfKeystone (keystone : SmithCascadeLandedPivotDividesMinor)
    (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width) (pRowLt : pivotIndex < height)
    (pColLt : pivotIndex < width) :
    ((matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).diagonalEntryAt pivotIndex).natAbs
      = (minorGcdWithin matrix pivotIndex height width).natAbs :=
  natDividesAntisymm
    (natDividesNatAbsOfIntDivides
      ((keystoneIffLandedDividesMinorGcd.mp keystone) matrix pivotIndex height width isRect pRowLt pColLt))
    (natDividesNatAbsOfIntDivides
      (minorGcdDividesLanded matrix pivotIndex height width isRect pRowLt pColLt))

/-! ## SURVIVING WALL (H2-SMITH r29, #2261)

After r29 the corrected-driver totality residual is UNCHANGED in strength but SHARPENED in shape.
`keystoneIffLandedDividesMinorGcd` reduces the 2-D whole-block keystone
`SmithCascadeLandedPivotDividesMinor` — a `∀` over EVERY cell of the `[pivotIndex, ·)²` minor, the
transient interior fill-in included — to the single 1-D scalar `landed ∣ gcd(minor)`.  The interior
fill-in is thereby RETIRED as a spectator: it is auto-confined to the landed pivot's ideal by the shipped
forward tower (`applyOperationsPreservesEntriesDivisibleWithin`, used inside
`commonDivisorOfInputMinorDividesLandedPivot`), never an obstacle.

The SHIPPED half `minorGcdDividesLanded` gives `gcd(minor) ∣ landed` hypothesis-free.  The OPEN half is
`landed ∣ gcd(minor)` — equivalently (with the shipped half) `|landed| = gcd(minor)`
(`landedMagnitudeEqMinorGcdOfKeystone`, conditional on the keystone).  This is the r11+ "min-abs Euclid
diagonal descent reaches the gcd" wall: the landed pivot's magnitude is minimal in the minor's gcd-ideal.
It is NOT closed by any gcd-invariance argument (which only bounds the ideal from one side) and is a
standalone multi-round descent arc (`SmithMinNonzeroAbsDescent` attacks the `minNonzeroAbsWithin` measure
directly).  `SmithReduceCompleteDriverStatement` therefore stays UNINHABITED hypothesis-free after r29;
it is inhabited GIVEN the keystone via `smithReduceCompleteDriverOfLandedPivotDividesMinor` (wired at
r22), and — now — GIVEN `LandedPivotDividesMinorGcd` via `keystoneIffLandedDividesMinorGcd.mpr`.  The
shipped `smithReduceComplete`, its refutation, and the r18–r28 world stay byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra
