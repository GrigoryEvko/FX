import FX1Poly.ComputerAlgebra.IntMatrix
import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidDeterminant
import FX1Poly.ComputerAlgebra.Algebra.SetoidRingTower

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntFractionFree — the exact integer determinant, two ways

Two computational tracks meet at ℤ, where the `intCommutativeRingWitness` setoid is plain `Eq`, so
determinants are honest `Int` literals a reader can machine-check.

  * **Exact cofactor determinant** — `cofactorDet intCommutativeRingWitness` (from `SetoidDeterminant`)
    instantiated at ℤ.  Division-free, hence integer-stable; its correctness (`det I = 1`, congruence,
    small base cases) is already proved generically, so those theorems transport to ℤ for free.

  * **Fraction-free Bareiss / Sasaki–Murao recurrence** — the short straight-line recurrence
    `phi a (Mat m L C N) = phi m ((m*N - C*L) / a)`, run with seed pivot `1`.  Over an integral
    domain the divisor is the previous pivot and, by Sylvester's identity, the division is exact —
    so every intermediate stays in ℤ (no fractions).  This file ships the recurrence as a computable,
    structurally-recursive function, proves its `1 × 1` base case, and MACHINE-CHECKS (`decide`) that
    it agrees with the proved exact cofactor determinant on concrete 2×2 and 3×3 inputs.

## Honest residual

The GENERAL equality `sasakiMuraoDet = cofactorDet` is exactly Sylvester's identity / the
`related`-invariant induction (Coquand–Mörtberg–Siles, JFR 2012); it is NOT proved here — the
concrete `decide` agreements are evidence, not a theorem.  Likewise rank (needs a decidable pivot
search + rank-invariance) and Smith normal form over ℤ (needs gcd-descent termination + the
`d_k = Delta_k / Delta_{k-1}` determinantal-divisor certificate) remain downstream residuals toward
the homology engine.

## Zero-axiom design

`sasakiMurao` recurses structurally on the size `Nat`; `Int` division is Lean's total `Int.div`
(exact on the Bareiss divisibilities).  Concrete agreements use `decide` (structural `DecidableEq
Int`, no `native_decide`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated in the audit twin.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## Concrete integer matrices from row literals -/

/-- Read a row-major list of integer rows as a total grid (`0` off the listed entries). -/
def gridOfRows (rows : List IntRow) (rowIndex colIndex : Nat) : Int :=
  listGetWithDefault 0 (listGetWithDefault [] rows rowIndex) colIndex

/-- Build a `SetoidMatrix Int` from a row-major list; the column count is read off the first row. -/
def setoidMatrixOfRows (rows : List IntRow) : SetoidMatrix Int :=
  { rowCount := rows.length,
    colCount := match rows with
      | [] => 0
      | firstRow :: _ => firstRow.length,
    entry := gridOfRows rows }

/-! ## The exact cofactor determinant at ℤ -/

/-- The exact, integer-stable determinant of a `size × size` matrix over ℤ. -/
def intCofactorDet (size : Nat) (matrix : SetoidMatrix Int) : Int :=
  SetoidMatrix.cofactorDet intCommutativeRingWitness size matrix

/-- The determinant of the integer identity matrix is `1` (transported from the generic proof). -/
theorem intCofactorDetIdentity (size : Nat) :
    intCofactorDet size (SetoidMatrix.identityMatrix intCommutativeRingWitness size) = 1 :=
  SetoidMatrix.cofactorDetIdentity intCommutativeRingWitness size

/-- Concrete evaluation: `det [[1,2],[3,4]] = -2`. -/
theorem intCofactorDetTwoByTwoExample :
    intCofactorDet 2 (setoidMatrixOfRows [[1, 2], [3, 4]]) = -2 := by decide

/-- Concrete evaluation: a diagonal `3×3` determinant is the product of the diagonal. -/
theorem intCofactorDetDiagonalExample :
    intCofactorDet 3 (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]]) = 24 := by decide

/-- Concrete evaluation: a dense `3×3` determinant. -/
theorem intCofactorDetDenseExample :
    intCofactorDet 3 (setoidMatrixOfRows [[1, 2, 3], [4, 5, 6], [7, 8, 10]]) = -3 := by decide

/-! ## The fraction-free Bareiss / Sasaki–Murao recurrence -/

/-- One Bareiss reduction of the trailing block: `reduced[i][j] = (m * grid[i+1][j+1] - grid[i+1][0]
* grid[0][j+1]) / priorPivot`, with `m = grid[0][0]` the new pivot.  Over an integral domain the
division is exact (Sylvester's identity). -/
def bareissReduceBlock (priorPivot : Int) (grid : Nat → Nat → Int) :
    Nat → Nat → Int :=
  fun rowIndex colIndex =>
    (grid 0 0 * grid (rowIndex + 1) (colIndex + 1)
        - grid (rowIndex + 1) 0 * grid 0 (colIndex + 1)) / priorPivot

/-- The Sasaki–Murao determinant engine: fold the block reduction, carrying the previous pivot,
structurally on the remaining size. -/
def sasakiMurao : Nat → Int → (Nat → Nat → Int) → Int
  | 0, priorPivot, _ => priorPivot
  | Nat.succ predecessor, priorPivot, grid =>
      sasakiMurao predecessor (grid 0 0) (bareissReduceBlock priorPivot grid)

/-- The fraction-free determinant: run Sasaki–Murao with the seed pivot `1`. -/
def sasakiMuraoDet (size : Nat) (grid : Nat → Nat → Int) : Int :=
  sasakiMurao size 1 grid

/-- Base case: the `1 × 1` fraction-free determinant is the single entry (matching the exact one). -/
theorem sasakiMuraoDetOne (grid : Nat → Nat → Int) : sasakiMuraoDet 1 grid = grid 0 0 :=
  rfl

/-- Machine-checked agreement with the exact cofactor determinant on a `2×2` input. -/
theorem sasakiMuraoAgreesTwoByTwo :
    sasakiMuraoDet 2 (gridOfRows [[1, 2], [3, 4]])
      = intCofactorDet 2 (setoidMatrixOfRows [[1, 2], [3, 4]]) := by decide

/-- Machine-checked agreement on a diagonal `3×3` input (exercises the exact division by a non-unit
prior pivot). -/
theorem sasakiMuraoAgreesDiagonal :
    sasakiMuraoDet 3 (gridOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]])
      = intCofactorDet 3 (setoidMatrixOfRows [[2, 0, 0], [0, 3, 0], [0, 0, 4]]) := by decide

/-- Machine-checked agreement on a dense `3×3` input. -/
theorem sasakiMuraoAgreesDense :
    sasakiMuraoDet 3 (gridOfRows [[1, 2, 3], [4, 5, 6], [7, 8, 10]])
      = intCofactorDet 3 (setoidMatrixOfRows [[1, 2, 3], [4, 5, 6], [7, 8, 10]]) := by decide

end FX1Poly.ComputerAlgebra
