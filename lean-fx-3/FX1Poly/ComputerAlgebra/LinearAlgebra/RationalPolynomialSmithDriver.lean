import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithDriver — the ℚ[x] Smith re-pivot driver
and the all-zero cross

The committed descent lever (`RationalPolynomialSmithDescent`) shipped `rpxMul` degree additivity
(`rsdDegreeMul`), the fact a nonzero pivot-multiple has degree `≥` the pivot (`rsdMultipleDegreeGePivot`),
and the fact a nonzero residue is strictly below the pivot (`rsdResidueBelowPivotWhenNonzero`) — the
termination CONTENT of the textbook Smith RE-PIVOT.  It WALLED the full re-pivot DRIVER owner-false
(`rsdHasRepivotDriver := false`), naming the missing piece: the moving-position ARITY bookkeeping — after
swapping the achieving off-pivot residue into the pivot slot, track which `(row, col)` the pivot now occupies
and re-clear about that moving position.  This module supplies exactly that bookkeeping, in the
MOVING-POSITION model (no row/column swap: the residue's ORIGINAL position becomes the new pivot position,
and the re-clear happens about it), and closes the wall.

## The moving-position model (no swap)

The textbook algorithm swaps a smaller residue into a FIXED pivot slot.  The equivalent, plumbing-lighter
model tracks the pivot POSITION as data: after clearing the cross about `(pivotRow, pivotCol)`, a nonzero
off-pivot cross residue sits at some cross position `(newRow, newCol)` (either `newRow = pivotRow` on the
pivot row, or `newCol = pivotCol` on the pivot column).  The re-pivot re-clears the cross about
`(newRow, newCol)` — that position becomes the new pivot.  No swap is defined; the moving position is just
the pair `(newRow, newCol)` carried through the recursion.

## T1 — the re-pivot step (`rseRepivotStep`)

`rseRepivotStep matrix pivotRow pivotCol newRow newCol` clears the cross about `(pivotRow, pivotCol)` and then
re-clears about `(newRow, newCol)`.  The step is an ELEMENTARY-OP COMPOSITE (both passes are
reconstruction-certified cross clears, `rsmCrossClear*Reconstructs`), and it STRICTLY DROPS the pivot-degree
measure `rsePivotDegree` when `(newRow, newCol)` is a nonzero cross residue:

  * **column arm** (`rseStepColumnStrictDrop`): `newCol = pivotCol`, `newRow ≠ pivotRow` — the re-cleared
    matrix's new pivot at `(newRow, pivotCol)` has degree strictly below the old pivot's, from
    `rsmCrossClearColMeasure` (annihilate OR drop) resolved by nonzero;
  * **row arm** (`rseStepRowStrictDrop`): `newRow = pivotRow`, `newCol ≠ pivotCol` — symmetric, from
    `rsmCrossClearRowMeasure`.

The moved pivot RECONSTRUCTS the old cross entry as a `pivot`-multiple residue
(`rseStepColumnReconstructs`), the elementary-op legitimacy of the swap.

## T2 — the re-pivot driver (`rseRepivotDriver`) and the all-zero cross

`rseRepivotDriver fuel matrix pivotRow pivotCol` iterates: clear the cross, search it for a nonzero residue
(`rseCrossSearch`, first off-pivot cross entry), and — if one is found — re-pivot to it and recurse with one
less fuel.  The fuel is the pivot degree, which strictly drops each round (the residue is below the pivot).
The base case `fuel = 0` is a CONSTANT pivot, which over the field ℚ divides every entry, so one clear
annihilates the whole cross (`rseConstantPivotClearsCross`, the measure's `degree < 0` disjunct being
absurd).  The driver reaches the ALL-ZERO cross (`rseRepivotDriverReachesAllZeroCross`, structural fuel
induction: the search's soundness gives the terminal on `none` and a below-pivot-degree residue on `some`,
so the invariant `pivot degree ≤ fuel` is preserved).  Mints `rseHasAllZeroCrossViaRepivot := true`; the
committed `rsfHasAllZeroCrossFixedPoint := false`, `rsmHasCrossFixedPoint := false`, and
`rsdHasAllZeroCrossViaRepivot := false` stay byte-intact.

## Zero-axiom design

Every definition is structural on the list (row/column), the positional index, or the `Nat` fuel; every
specification routes through the committed cross-clear measure/reconstruction lemmas and the calibrated-clean
`Nat` order lemmas (`Nat.not_lt_zero`, `Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`, `Nat.lt_succ_of_le`,
`Or.resolve_left`, `Nat.le_refl`).  The only non-list case analyses are `Option`/`Prod` projection and the
`rpxTrim` nil/cons split (full enumeration, no wildcard arms over enumerable scrutinees).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithDriver.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The pivot-degree measure and the all-zero cross predicate -/

/-- **The pivot-degree measure.**  The degree of the entry at the pivot position — the driver's terminating
`Nat`.  Each re-pivot swaps in a residue of strictly smaller degree, so this strictly drops. -/
def rsePivotDegree (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) : Nat :=
  rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol)

/-- **The all-zero cross predicate.**  Every off-pivot entry of the pivot's row AND column trims to the zero
polynomial — the terminal state the re-pivot driver reaches (strictly stronger than `rsfCrossIsReduced`,
which allows below-pivot nonzero residues). -/
def rseCrossIsAllZero (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) : Prop :=
  (∀ colPosition : Nat, colPosition ≠ pivotCol →
      rpxTrim (rbzMatrixEntry matrix pivotRow colPosition) = [])
    ∧ (∀ rowPosition : Nat, rowPosition ≠ pivotRow →
      rpxTrim (rbzMatrixEntry matrix rowPosition pivotCol) = [])

/-! ## T1 — the re-pivot step -/

/-- **The re-pivot step.**  Clear the cross about `(pivotRow, pivotCol)`, then re-clear about the moving
position `(newRow, newCol)` — the residue there becomes the new pivot.  A composite of two elementary
cross-clears. -/
def rseRepivotStep (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol newRow newCol : Nat) : List (List (List QnfRat)) :=
  let cleared := rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow
  rsmCrossClear (rbzMatrixEntry cleared newRow newCol) newCol cleared newRow

/-- **The cleared cross-column residue.**  Reading the pivot-column entry at row `newRow ≠ pivotRow` after
one cross clear returns the Euclidean residue of the original entry against the pivot.  The bridge the strict
drop and the reconstruction both consume. -/
theorem rseClearedColumnEntry (matrix : List (List (List QnfRat))) (pivotRow pivotCol newRow : Nat)
    (hne : newRow ≠ pivotRow) :
    rbzMatrixEntry (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        newRow pivotCol
      = rsmClearAgainst (rbzMatrixEntry matrix pivotRow pivotCol)
          (rbzMatrixEntry matrix newRow pivotCol) := by
  show rbzEntryGet (rbzRowGet
      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow) newRow) pivotCol
    = rsmClearAgainst (rbzMatrixEntry matrix pivotRow pivotCol)
        (rbzEntryGet (rbzRowGet matrix newRow) pivotCol)
  rw [rsmCrossClearRowGetOther (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow newRow hne,
    rsmClearRowAtColGetAt]

/-- **The cleared cross-row residue.**  Reading the pivot-row entry at column `newCol ≠ pivotCol` after one
cross clear returns the Euclidean residue of the original entry against the pivot. -/
theorem rseClearedRowEntry (matrix : List (List (List QnfRat))) (pivotRow pivotCol newCol : Nat)
    (hne : newCol ≠ pivotCol) :
    rbzMatrixEntry (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        pivotRow newCol
      = rsmClearAgainst (rbzMatrixEntry matrix pivotRow pivotCol)
          (rbzMatrixEntry matrix pivotRow newCol) := by
  show rbzEntryGet (rbzRowGet
      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow) pivotRow) newCol
    = rsmClearAgainst (rbzMatrixEntry matrix pivotRow pivotCol)
        (rbzEntryGet (rbzRowGet matrix pivotRow) newCol)
  rw [rsmCrossClearRowGetPivot,
    rsmRowClearExceptGetOther (rbzMatrixEntry matrix pivotRow pivotCol)
      (rbzRowGet matrix pivotRow) pivotCol newCol hne]

/-- **T1 — the column-arm strict drop.**  Re-pivoting to a NONZERO pivot-column residue at
`(newRow, pivotCol)` (row `newRow ≠ pivotRow`) yields a new pivot of degree strictly below the old pivot's.
The re-clear preserves the new pivot (`rsmCrossClearPivotPreserved`), so the moved pivot's degree equals the
residue's, which the cross-clear measure (`rsmCrossClearColMeasure`) drops below the pivot once the residue
is nonzero. -/
theorem rseStepColumnStrictDrop (matrix : List (List (List QnfRat))) (pivotRow pivotCol newRow : Nat)
    (pivotNonzero : rpxTrim (rbzMatrixEntry matrix pivotRow pivotCol) ≠ [])
    (hne : newRow ≠ pivotRow)
    (residueNonzero :
      rpxTrim (rbzMatrixEntry
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        newRow pivotCol) ≠ []) :
    rsePivotDegree (rseRepivotStep matrix pivotRow pivotCol newRow pivotCol) newRow pivotCol
      < rsePivotDegree matrix pivotRow pivotCol := by
  show rpxDegree (rbzMatrixEntry (rseRepivotStep matrix pivotRow pivotCol newRow pivotCol) newRow pivotCol)
    < rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol)
  have movedPreserved :
      rbzMatrixEntry (rseRepivotStep matrix pivotRow pivotCol newRow pivotCol) newRow pivotCol
        = rbzMatrixEntry
            (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
            newRow pivotCol :=
    rsmCrossClearPivotPreserved
      (rbzMatrixEntry
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow) newRow pivotCol)
      pivotCol newRow
      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
  rw [movedPreserved]
  exact (rsmCrossClearColMeasure (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow matrix
    pivotNonzero newRow hne).resolve_left residueNonzero

/-- **T1 — the row-arm strict drop.**  Symmetric to `rseStepColumnStrictDrop`: re-pivoting to a NONZERO
pivot-row residue at `(pivotRow, newCol)` (column `newCol ≠ pivotCol`) yields a new pivot of degree strictly
below the old pivot's, via `rsmCrossClearRowMeasure`. -/
theorem rseStepRowStrictDrop (matrix : List (List (List QnfRat))) (pivotRow pivotCol newCol : Nat)
    (pivotNonzero : rpxTrim (rbzMatrixEntry matrix pivotRow pivotCol) ≠ [])
    (hne : newCol ≠ pivotCol)
    (residueNonzero :
      rpxTrim (rbzMatrixEntry
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        pivotRow newCol) ≠ []) :
    rsePivotDegree (rseRepivotStep matrix pivotRow pivotCol pivotRow newCol) pivotRow newCol
      < rsePivotDegree matrix pivotRow pivotCol := by
  show rpxDegree (rbzMatrixEntry (rseRepivotStep matrix pivotRow pivotCol pivotRow newCol) pivotRow newCol)
    < rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol)
  have movedPreserved :
      rbzMatrixEntry (rseRepivotStep matrix pivotRow pivotCol pivotRow newCol) pivotRow newCol
        = rbzMatrixEntry
            (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
            pivotRow newCol :=
    rsmCrossClearPivotPreserved
      (rbzMatrixEntry
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow) pivotRow newCol)
      newCol pivotRow
      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
  rw [movedPreserved]
  exact (rsmCrossClearRowMeasure (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow matrix
    pivotNonzero newCol hne).resolve_left residueNonzero

/-- **T1 — the moved pivot reconstructs the old cross entry.**  The new pivot at `(newRow, pivotCol)` is the
Euclidean residue of the original entry against the old pivot, so `quotient·pivot + newPivot ≡ original`
(the committed `rsmCrossClearColReconstructs`), the elementary-operation legitimacy of the re-pivot. -/
theorem rseStepColumnReconstructs (matrix : List (List (List QnfRat))) (pivotRow pivotCol newRow : Nat)
    (hne : newRow ≠ pivotRow) :
    rpxTrim (rpxAdd
        (rpxMul (rpxDivMod (rbzMatrixEntry matrix newRow pivotCol).length
          (rbzMatrixEntry matrix pivotRow pivotCol) (rbzMatrixEntry matrix newRow pivotCol)).1
          (rbzMatrixEntry matrix pivotRow pivotCol))
        (rbzMatrixEntry
          (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
          newRow pivotCol))
      = rpxTrim (rbzMatrixEntry matrix newRow pivotCol) :=
  rsmCrossClearColReconstructs (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow matrix newRow hne

/-! ## T2a — the cross search (first nonzero off-pivot residue)

The driver needs to find ONE nonzero off-pivot cross residue (any will do — every cross residue after a
clear has degree below the pivot, so any is a valid re-pivot target).  A search over the pivot row (skipping
the pivot column) and, failing that, the pivot column (skipping the pivot row).  The `All` variants search
without a skip; the `Except` variants skip the pivot's own slot (which after a clear holds the untouched,
nonzero pivot — searching it unskipped would wrongly re-pivot to the pivot). -/

/-- First nonzero entry of a row (no skip); returns its column index or `none` when the whole row is zero. -/
def rseRowSearchAll : List (List QnfRat) → Option Nat
  | [] => none
  | entry :: rest =>
      match rpxTrim entry with
      | [] =>
          match rseRowSearchAll rest with
          | none => none
          | some foundCol => some (foundCol + 1)
      | _ :: _ => some 0

/-- First nonzero entry of a row skipping the entry at `skipCol` (the pivot column); returns its column index
or `none` when every entry other than `skipCol` is zero. -/
def rseRowSearchExcept : List (List QnfRat) → Nat → Option Nat
  | [], _ => none
  | _entry :: rest, 0 =>
      match rseRowSearchAll rest with
      | none => none
      | some foundCol => some (foundCol + 1)
  | entry :: rest, skipCol + 1 =>
      match rpxTrim entry with
      | [] =>
          match rseRowSearchExcept rest skipCol with
          | none => none
          | some foundCol => some (foundCol + 1)
      | _ :: _ => some 0

/-- First row whose pivot-column entry is nonzero (no skip); returns its row index or `none` when the whole
column is zero. -/
def rseColumnSearchAll : List (List (List QnfRat)) → Nat → Option Nat
  | [], _ => none
  | row :: rest, pivotCol =>
      match rpxTrim (rbzEntryGet row pivotCol) with
      | [] =>
          match rseColumnSearchAll rest pivotCol with
          | none => none
          | some foundRow => some (foundRow + 1)
      | _ :: _ => some 0

/-- First row whose pivot-column entry is nonzero, skipping the row at `skipRow` (the pivot row); returns its
row index or `none` when every column entry other than `skipRow` is zero. -/
def rseColumnSearchExcept : List (List (List QnfRat)) → Nat → Nat → Option Nat
  | [], _, _ => none
  | _row :: rest, pivotCol, 0 =>
      match rseColumnSearchAll rest pivotCol with
      | none => none
      | some foundRow => some (foundRow + 1)
  | row :: rest, pivotCol, skipRow + 1 =>
      match rpxTrim (rbzEntryGet row pivotCol) with
      | [] =>
          match rseColumnSearchExcept rest pivotCol skipRow with
          | none => none
          | some foundRow => some (foundRow + 1)
      | _ :: _ => some 0

/-- **The cross search.**  A nonzero off-pivot cross position `(rowIndex, colIndex)` — the pivot row (skipping
the pivot column) is searched first, then the pivot column (skipping the pivot row); `none` certifies the
cross is all-zero. -/
def rseCrossSearch (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) : Option (Nat × Nat) :=
  match rseRowSearchExcept (rbzRowGet matrix pivotRow) pivotCol with
  | some foundCol => some (pivotRow, foundCol)
  | none =>
      match rseColumnSearchExcept matrix pivotCol pivotRow with
      | some foundRow => some (foundRow, pivotCol)
      | none => none

/-! ### Search step equations (two-level matches reduce under `rw`) -/

theorem rseRowSearchAllConsZeroNone (entry : List QnfRat) (rest : List (List QnfRat))
    (hTrim : rpxTrim entry = []) (hRest : rseRowSearchAll rest = none) :
    rseRowSearchAll (entry :: rest) = none := by
  dsimp only [rseRowSearchAll]; rw [hTrim, hRest]

theorem rseRowSearchAllConsZeroSome (entry : List QnfRat) (rest : List (List QnfRat))
    (foundCol : Nat) (hTrim : rpxTrim entry = []) (hRest : rseRowSearchAll rest = some foundCol) :
    rseRowSearchAll (entry :: rest) = some (foundCol + 1) := by
  dsimp only [rseRowSearchAll]; rw [hTrim, hRest]

theorem rseRowSearchAllConsNonzero (entry : List QnfRat) (rest : List (List QnfRat))
    (trimHead : QnfRat) (trimTail : List QnfRat) (hTrim : rpxTrim entry = trimHead :: trimTail) :
    rseRowSearchAll (entry :: rest) = some 0 := by
  dsimp only [rseRowSearchAll]; rw [hTrim]

theorem rseRowSearchExceptConsSkipNone (entry : List QnfRat) (rest : List (List QnfRat))
    (hRest : rseRowSearchAll rest = none) : rseRowSearchExcept (entry :: rest) 0 = none := by
  dsimp only [rseRowSearchExcept]; rw [hRest]

theorem rseRowSearchExceptConsSkipSome (entry : List QnfRat) (rest : List (List QnfRat))
    (foundCol : Nat) (hRest : rseRowSearchAll rest = some foundCol) :
    rseRowSearchExcept (entry :: rest) 0 = some (foundCol + 1) := by
  dsimp only [rseRowSearchExcept]; rw [hRest]

theorem rseRowSearchExceptConsZeroNone (entry : List QnfRat) (rest : List (List QnfRat)) (skipCol : Nat)
    (hTrim : rpxTrim entry = []) (hRest : rseRowSearchExcept rest skipCol = none) :
    rseRowSearchExcept (entry :: rest) (skipCol + 1) = none := by
  dsimp only [rseRowSearchExcept]; rw [hTrim, hRest]

theorem rseRowSearchExceptConsZeroSome (entry : List QnfRat) (rest : List (List QnfRat))
    (skipCol foundCol : Nat) (hTrim : rpxTrim entry = [])
    (hRest : rseRowSearchExcept rest skipCol = some foundCol) :
    rseRowSearchExcept (entry :: rest) (skipCol + 1) = some (foundCol + 1) := by
  dsimp only [rseRowSearchExcept]; rw [hTrim, hRest]

theorem rseRowSearchExceptConsNonzero (entry : List QnfRat) (rest : List (List QnfRat)) (skipCol : Nat)
    (trimHead : QnfRat) (trimTail : List QnfRat) (hTrim : rpxTrim entry = trimHead :: trimTail) :
    rseRowSearchExcept (entry :: rest) (skipCol + 1) = some 0 := by
  dsimp only [rseRowSearchExcept]; rw [hTrim]

theorem rseColumnSearchAllConsZeroNone (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol : Nat) (hTrim : rpxTrim (rbzEntryGet row pivotCol) = [])
    (hRest : rseColumnSearchAll rest pivotCol = none) :
    rseColumnSearchAll (row :: rest) pivotCol = none := by
  dsimp only [rseColumnSearchAll]; rw [hTrim, hRest]

theorem rseColumnSearchAllConsZeroSome (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol foundRow : Nat) (hTrim : rpxTrim (rbzEntryGet row pivotCol) = [])
    (hRest : rseColumnSearchAll rest pivotCol = some foundRow) :
    rseColumnSearchAll (row :: rest) pivotCol = some (foundRow + 1) := by
  dsimp only [rseColumnSearchAll]; rw [hTrim, hRest]

theorem rseColumnSearchAllConsNonzero (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol : Nat) (trimHead : QnfRat) (trimTail : List QnfRat)
    (hTrim : rpxTrim (rbzEntryGet row pivotCol) = trimHead :: trimTail) :
    rseColumnSearchAll (row :: rest) pivotCol = some 0 := by
  dsimp only [rseColumnSearchAll]; rw [hTrim]

theorem rseColumnSearchExceptConsSkipNone (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol : Nat) (hRest : rseColumnSearchAll rest pivotCol = none) :
    rseColumnSearchExcept (row :: rest) pivotCol 0 = none := by
  dsimp only [rseColumnSearchExcept]; rw [hRest]

theorem rseColumnSearchExceptConsSkipSome (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol foundRow : Nat) (hRest : rseColumnSearchAll rest pivotCol = some foundRow) :
    rseColumnSearchExcept (row :: rest) pivotCol 0 = some (foundRow + 1) := by
  dsimp only [rseColumnSearchExcept]; rw [hRest]

theorem rseColumnSearchExceptConsZeroNone (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol skipRow : Nat) (hTrim : rpxTrim (rbzEntryGet row pivotCol) = [])
    (hRest : rseColumnSearchExcept rest pivotCol skipRow = none) :
    rseColumnSearchExcept (row :: rest) pivotCol (skipRow + 1) = none := by
  dsimp only [rseColumnSearchExcept]; rw [hTrim, hRest]

theorem rseColumnSearchExceptConsZeroSome (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol skipRow foundRow : Nat) (hTrim : rpxTrim (rbzEntryGet row pivotCol) = [])
    (hRest : rseColumnSearchExcept rest pivotCol skipRow = some foundRow) :
    rseColumnSearchExcept (row :: rest) pivotCol (skipRow + 1) = some (foundRow + 1) := by
  dsimp only [rseColumnSearchExcept]; rw [hTrim, hRest]

theorem rseColumnSearchExceptConsNonzero (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (pivotCol skipRow : Nat) (trimHead : QnfRat) (trimTail : List QnfRat)
    (hTrim : rpxTrim (rbzEntryGet row pivotCol) = trimHead :: trimTail) :
    rseColumnSearchExcept (row :: rest) pivotCol (skipRow + 1) = some 0 := by
  dsimp only [rseColumnSearchExcept]; rw [hTrim]

/-! ### Search soundness -/

/-- Soundness bar for the no-skip row search: `none` certifies the whole row zero; `some foundCol` reads a
nonzero entry there. -/
def rseRowSearchAllSound (row : List (List QnfRat)) : Option Nat → Prop
  | none => ∀ position : Nat, rpxTrim (rbzEntryGet row position) = []
  | some foundCol => rpxTrim (rbzEntryGet row foundCol) ≠ []

/-- **The no-skip row search is sound** at every row. -/
theorem rseRowSearchAllSoundHolds : ∀ row : List (List QnfRat), rseRowSearchAllSound row (rseRowSearchAll row)
  | [] => fun _position => rfl
  | entry :: rest => by
      have ih := rseRowSearchAllSoundHolds rest
      cases hTrim : rpxTrim entry with
      | nil =>
          cases hRest : rseRowSearchAll rest with
          | none =>
              rw [rseRowSearchAllConsZeroNone entry rest hTrim hRest]
              rw [hRest] at ih
              intro position
              cases position with
              | zero => exact hTrim
              | succ prior => exact ih prior
          | some foundCol =>
              rw [rseRowSearchAllConsZeroSome entry rest foundCol hTrim hRest]
              rw [hRest] at ih
              show rpxTrim (rbzEntryGet rest foundCol) ≠ []
              exact ih
      | cons trimHead trimTail =>
          rw [rseRowSearchAllConsNonzero entry rest trimHead trimTail hTrim]
          show rpxTrim entry ≠ []
          rw [hTrim]
          exact List.cons_ne_nil trimHead trimTail

/-- Soundness bar for the skip row search: `none` certifies every off-`skipCol` entry zero; `some foundCol`
reads a nonzero off-`skipCol` entry. -/
def rseRowSearchExceptSound (row : List (List QnfRat)) (skipCol : Nat) : Option Nat → Prop
  | none => ∀ position : Nat, position ≠ skipCol → rpxTrim (rbzEntryGet row position) = []
  | some foundCol => foundCol ≠ skipCol ∧ rpxTrim (rbzEntryGet row foundCol) ≠ []

/-- **The skip row search is sound** at every row and skip column. -/
theorem rseRowSearchExceptSoundHolds :
    ∀ (row : List (List QnfRat)) (skipCol : Nat),
      rseRowSearchExceptSound row skipCol (rseRowSearchExcept row skipCol)
  | [], _skipCol => fun _position _hne => rfl
  | entry :: rest, 0 => by
      have ih := rseRowSearchAllSoundHolds rest
      cases hRest : rseRowSearchAll rest with
      | none =>
          rw [rseRowSearchExceptConsSkipNone entry rest hRest]
          rw [hRest] at ih
          intro position hne
          cases position with
          | zero => exact absurd rfl hne
          | succ prior => exact ih prior
      | some foundCol =>
          rw [rseRowSearchExceptConsSkipSome entry rest foundCol hRest]
          rw [hRest] at ih
          refine ⟨fun h => Nat.noConfusion h, ?_⟩
          show rpxTrim (rbzEntryGet rest foundCol) ≠ []
          exact ih
  | entry :: rest, skipCol + 1 => by
      have ih := rseRowSearchExceptSoundHolds rest skipCol
      cases hTrim : rpxTrim entry with
      | nil =>
          cases hRest : rseRowSearchExcept rest skipCol with
          | none =>
              rw [rseRowSearchExceptConsZeroNone entry rest skipCol hTrim hRest]
              rw [hRest] at ih
              intro position hne
              cases position with
              | zero => exact hTrim
              | succ prior => exact ih prior (fun heq => hne (congrArg Nat.succ heq))
          | some foundCol =>
              rw [rseRowSearchExceptConsZeroSome entry rest skipCol foundCol hTrim hRest]
              rw [hRest] at ih
              refine ⟨fun heq => ih.1 (Nat.succ.inj heq), ?_⟩
              show rpxTrim (rbzEntryGet rest foundCol) ≠ []
              exact ih.2
      | cons trimHead trimTail =>
          rw [rseRowSearchExceptConsNonzero entry rest skipCol trimHead trimTail hTrim]
          refine ⟨fun h => Nat.noConfusion h, ?_⟩
          show rpxTrim entry ≠ []
          rw [hTrim]
          exact List.cons_ne_nil trimHead trimTail

/-- Soundness bar for the no-skip column search: `none` certifies the whole column zero; `some foundRow`
reads a nonzero column entry there. -/
def rseColumnSearchAllSound (matrix : List (List (List QnfRat))) (pivotCol : Nat) : Option Nat → Prop
  | none => ∀ rowPosition : Nat, rpxTrim (rbzMatrixEntry matrix rowPosition pivotCol) = []
  | some foundRow => rpxTrim (rbzMatrixEntry matrix foundRow pivotCol) ≠ []

/-- **The no-skip column search is sound** at every matrix and pivot column. -/
theorem rseColumnSearchAllSoundHolds :
    ∀ (matrix : List (List (List QnfRat))) (pivotCol : Nat),
      rseColumnSearchAllSound matrix pivotCol (rseColumnSearchAll matrix pivotCol)
  | [], _pivotCol => fun _rowPosition => rfl
  | row :: rest, pivotCol => by
      have ih := rseColumnSearchAllSoundHolds rest pivotCol
      cases hTrim : rpxTrim (rbzEntryGet row pivotCol) with
      | nil =>
          cases hRest : rseColumnSearchAll rest pivotCol with
          | none =>
              rw [rseColumnSearchAllConsZeroNone row rest pivotCol hTrim hRest]
              rw [hRest] at ih
              intro rowPosition
              cases rowPosition with
              | zero => exact hTrim
              | succ prior => exact ih prior
          | some foundRow =>
              rw [rseColumnSearchAllConsZeroSome row rest pivotCol foundRow hTrim hRest]
              rw [hRest] at ih
              show rpxTrim (rbzMatrixEntry rest foundRow pivotCol) ≠ []
              exact ih
      | cons trimHead trimTail =>
          rw [rseColumnSearchAllConsNonzero row rest pivotCol trimHead trimTail hTrim]
          show rpxTrim (rbzEntryGet row pivotCol) ≠ []
          rw [hTrim]
          exact List.cons_ne_nil trimHead trimTail

/-- Soundness bar for the skip column search: `none` certifies every off-`skipRow` column entry zero; `some
foundRow` reads a nonzero off-`skipRow` column entry. -/
def rseColumnSearchExceptSound (matrix : List (List (List QnfRat))) (pivotCol skipRow : Nat) :
    Option Nat → Prop
  | none => ∀ rowPosition : Nat, rowPosition ≠ skipRow →
      rpxTrim (rbzMatrixEntry matrix rowPosition pivotCol) = []
  | some foundRow => foundRow ≠ skipRow ∧ rpxTrim (rbzMatrixEntry matrix foundRow pivotCol) ≠ []

/-- **The skip column search is sound** at every matrix, pivot column, and skip row. -/
theorem rseColumnSearchExceptSoundHolds :
    ∀ (matrix : List (List (List QnfRat))) (pivotCol skipRow : Nat),
      rseColumnSearchExceptSound matrix pivotCol skipRow (rseColumnSearchExcept matrix pivotCol skipRow)
  | [], _pivotCol, _skipRow => fun _rowPosition _hne => rfl
  | row :: rest, pivotCol, 0 => by
      have ih := rseColumnSearchAllSoundHolds rest pivotCol
      cases hRest : rseColumnSearchAll rest pivotCol with
      | none =>
          rw [rseColumnSearchExceptConsSkipNone row rest pivotCol hRest]
          rw [hRest] at ih
          intro rowPosition hne
          cases rowPosition with
          | zero => exact absurd rfl hne
          | succ prior => exact ih prior
      | some foundRow =>
          rw [rseColumnSearchExceptConsSkipSome row rest pivotCol foundRow hRest]
          rw [hRest] at ih
          refine ⟨fun h => Nat.noConfusion h, ?_⟩
          show rpxTrim (rbzMatrixEntry rest foundRow pivotCol) ≠ []
          exact ih
  | row :: rest, pivotCol, skipRow + 1 => by
      have ih := rseColumnSearchExceptSoundHolds rest pivotCol skipRow
      cases hTrim : rpxTrim (rbzEntryGet row pivotCol) with
      | nil =>
          cases hRest : rseColumnSearchExcept rest pivotCol skipRow with
          | none =>
              rw [rseColumnSearchExceptConsZeroNone row rest pivotCol skipRow hTrim hRest]
              rw [hRest] at ih
              intro rowPosition hne
              cases rowPosition with
              | zero => exact hTrim
              | succ prior => exact ih prior (fun heq => hne (congrArg Nat.succ heq))
          | some foundRow =>
              rw [rseColumnSearchExceptConsZeroSome row rest pivotCol skipRow foundRow hTrim hRest]
              rw [hRest] at ih
              refine ⟨fun heq => ih.1 (Nat.succ.inj heq), ?_⟩
              show rpxTrim (rbzMatrixEntry rest foundRow pivotCol) ≠ []
              exact ih.2
      | cons trimHead trimTail =>
          rw [rseColumnSearchExceptConsNonzero row rest pivotCol skipRow trimHead trimTail hTrim]
          refine ⟨fun h => Nat.noConfusion h, ?_⟩
          show rpxTrim (rbzEntryGet row pivotCol) ≠ []
          rw [hTrim]
          exact List.cons_ne_nil trimHead trimTail

/-- **The cross search's `none` certifies an all-zero cross.**  Both the row search (off the pivot column)
and the column search (off the pivot row) returned `none`, so every off-pivot cross entry is zero. -/
theorem rseCrossSearchNoneAllZero (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat)
    (hNone : rseCrossSearch matrix pivotRow pivotCol = none) :
    rseCrossIsAllZero matrix pivotRow pivotCol := by
  have rowSpec := rseRowSearchExceptSoundHolds (rbzRowGet matrix pivotRow) pivotCol
  have colSpec := rseColumnSearchExceptSoundHolds matrix pivotCol pivotRow
  cases hRow : rseRowSearchExcept (rbzRowGet matrix pivotRow) pivotCol with
  | some foundCol =>
      dsimp only [rseCrossSearch] at hNone
      rw [hRow] at hNone
      nomatch hNone
  | none =>
      rw [hRow] at rowSpec
      cases hCol : rseColumnSearchExcept matrix pivotCol pivotRow with
      | some foundRow =>
          dsimp only [rseCrossSearch] at hNone
          rw [hRow, hCol] at hNone
          nomatch hNone
      | none =>
          rw [hCol] at colSpec
          refine ⟨fun colPosition hne => ?_, fun rowPosition hne => colSpec rowPosition hne⟩
          show rpxTrim (rbzEntryGet (rbzRowGet matrix pivotRow) colPosition) = []
          exact rowSpec colPosition hne

/-- **The cross search's `some` is a nonzero off-pivot cross residue.**  The found position lies on the pivot
row (a `≠ pivotCol` residue) or the pivot column (a `≠ pivotRow` residue), and reads back nonzero — a valid
re-pivot target. -/
theorem rseCrossSearchSomeCross (matrix : List (List (List QnfRat))) (pivotRow pivotCol newRow newCol : Nat)
    (hSome : rseCrossSearch matrix pivotRow pivotCol = some (newRow, newCol)) :
    (newRow = pivotRow ∧ newCol ≠ pivotCol ∧ rpxTrim (rbzMatrixEntry matrix pivotRow newCol) ≠ [])
      ∨ (newCol = pivotCol ∧ newRow ≠ pivotRow ∧ rpxTrim (rbzMatrixEntry matrix newRow pivotCol) ≠ []) := by
  have rowSpec := rseRowSearchExceptSoundHolds (rbzRowGet matrix pivotRow) pivotCol
  have colSpec := rseColumnSearchExceptSoundHolds matrix pivotCol pivotRow
  cases hRow : rseRowSearchExcept (rbzRowGet matrix pivotRow) pivotCol with
  | some foundCol =>
      rw [hRow] at rowSpec
      have hEq : rseCrossSearch matrix pivotRow pivotCol = some (pivotRow, foundCol) := by
        dsimp only [rseCrossSearch]; rw [hRow]
      rw [hEq] at hSome
      have hPair : (pivotRow, foundCol) = (newRow, newCol) := Option.some.inj hSome
      have hRowEq : pivotRow = newRow := congrArg Prod.fst hPair
      have hColEq : foundCol = newCol := congrArg Prod.snd hPair
      refine Or.inl ⟨hRowEq.symm, ?_, ?_⟩
      · rw [← hColEq]; exact rowSpec.1
      · show rpxTrim (rbzMatrixEntry matrix pivotRow newCol) ≠ []
        rw [← hColEq]
        show rpxTrim (rbzEntryGet (rbzRowGet matrix pivotRow) foundCol) ≠ []
        exact rowSpec.2
  | none =>
      rw [hRow] at rowSpec
      cases hCol : rseColumnSearchExcept matrix pivotCol pivotRow with
      | some foundRow =>
          rw [hCol] at colSpec
          have hEq : rseCrossSearch matrix pivotRow pivotCol = some (foundRow, pivotCol) := by
            dsimp only [rseCrossSearch]; rw [hRow, hCol]
          rw [hEq] at hSome
          have hPair : (foundRow, pivotCol) = (newRow, newCol) := Option.some.inj hSome
          have hRowEq : foundRow = newRow := congrArg Prod.fst hPair
          have hColEq : pivotCol = newCol := congrArg Prod.snd hPair
          refine Or.inr ⟨hColEq.symm, ?_, ?_⟩
          · rw [← hRowEq]; exact colSpec.1
          · rw [← hRowEq]; exact colSpec.2
      | none =>
          dsimp only [rseCrossSearch] at hSome
          rw [hRow, hCol] at hSome
          nomatch hSome

/-! ## T2b — the re-pivot driver and the all-zero cross -/

/-- **The re-pivot driver.**  Iterate: clear the cross about the pivot, search it for a nonzero residue, and
re-pivot to it with one less fuel; on an empty search (or when the fuel runs out on a constant pivot) return
the cleared matrix with its final pivot position.  Structural on `Nat` fuel = the pivot degree. -/
def rseRepivotDriver :
    Nat → List (List (List QnfRat)) → Nat → Nat → List (List (List QnfRat)) × Nat × Nat
  | 0, matrix, pivotRow, pivotCol =>
      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow, pivotRow, pivotCol)
  | fuel + 1, matrix, pivotRow, pivotCol =>
      match rseCrossSearch
          (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
          pivotRow pivotCol with
      | none =>
          (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow,
           pivotRow, pivotCol)
      | some newPos =>
          rseRepivotDriver fuel
            (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
            newPos.1 newPos.2

/-- The driver at `fuel = 0` clears once and returns. -/
theorem rseRepivotDriverZero (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) :
    rseRepivotDriver 0 matrix pivotRow pivotCol
      = (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow,
         pivotRow, pivotCol) := rfl

/-- The driver at a successor fuel with an empty cross search clears once and returns. -/
theorem rseRepivotDriverSuccNone (fuel : Nat) (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat)
    (hSearch : rseCrossSearch
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        pivotRow pivotCol = none) :
    rseRepivotDriver (fuel + 1) matrix pivotRow pivotCol
      = (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow,
         pivotRow, pivotCol) := by
  dsimp only [rseRepivotDriver]; rw [hSearch]

/-- The driver at a successor fuel with a found residue at `(newRow, newCol)` recurses on the cleared
matrix about that moving position. -/
theorem rseRepivotDriverSuccSome (fuel : Nat) (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol newRow newCol : Nat)
    (hSearch : rseCrossSearch
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        pivotRow pivotCol = some (newRow, newCol)) :
    rseRepivotDriver (fuel + 1) matrix pivotRow pivotCol
      = rseRepivotDriver fuel
          (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
          newRow newCol := by
  dsimp only [rseRepivotDriver]; rw [hSearch]

/-- **A constant pivot clears its whole cross in one pass.**  A nonzero pivot of degree `≤ 0` is a nonzero
constant, which over the field ℚ divides every entry: the cross-clear measure's `degree < degree pivot`
disjunct is then `degree < 0`, absurd, so every off-pivot cross entry annihilates.  The driver's fuel-`0`
base case. -/
theorem rseConstantPivotClearsCross (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat)
    (pivotNonzero : rpxTrim (rbzMatrixEntry matrix pivotRow pivotCol) ≠ [])
    (pivotDegreeLeZero : rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol) ≤ 0) :
    rseCrossIsAllZero
      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
      pivotRow pivotCol := by
  refine ⟨fun colPosition hne => ?_, fun rowPosition hne => ?_⟩
  · cases rsmCrossClearRowMeasure (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow matrix
        pivotNonzero colPosition hne with
    | inl residueZero => exact residueZero
    | inr degreeBelow =>
        exact absurd (Nat.lt_of_lt_of_le degreeBelow pivotDegreeLeZero) (Nat.not_lt_zero _)
  · cases rsmCrossClearColMeasure (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow matrix
        pivotNonzero rowPosition hne with
    | inl residueZero => exact residueZero
    | inr degreeBelow =>
        exact absurd (Nat.lt_of_lt_of_le degreeBelow pivotDegreeLeZero) (Nat.not_lt_zero _)

/-- **T2 — the re-pivot driver reaches the all-zero cross.**  Under the invariant that the pivot degree is
`≤ fuel` (and the pivot is nonzero), the driver terminates at a matrix whose cross about the final pivot
position is entirely zero.  Structural fuel induction: the `fuel = 0` base is `rseConstantPivotClearsCross`;
at a successor, the cross search's soundness gives the terminal all-zero cross on `none`
(`rseCrossSearchNoneAllZero`) and, on `some`, a below-pivot-degree nonzero residue
(`rseCrossSearchSomeCross` + the cross-clear measure), whose degree is `< fuel + 1`, hence `≤ fuel` — so the
invariant is preserved and the inductive hypothesis closes the recursion. -/
theorem rseRepivotDriverReachesAllZeroCross :
    ∀ (fuel : Nat) (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat),
      rpxTrim (rbzMatrixEntry matrix pivotRow pivotCol) ≠ [] →
      rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol) ≤ fuel →
      rseCrossIsAllZero (rseRepivotDriver fuel matrix pivotRow pivotCol).1
        (rseRepivotDriver fuel matrix pivotRow pivotCol).2.1
        (rseRepivotDriver fuel matrix pivotRow pivotCol).2.2
  | 0, matrix, pivotRow, pivotCol, pivotNonzero, pivotDegreeLe => by
      rw [rseRepivotDriverZero]
      show rseCrossIsAllZero
        (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
        pivotRow pivotCol
      exact rseConstantPivotClearsCross matrix pivotRow pivotCol pivotNonzero pivotDegreeLe
  | fuel + 1, matrix, pivotRow, pivotCol, pivotNonzero, pivotDegreeLe => by
      cases hSearch : rseCrossSearch
          (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
          pivotRow pivotCol with
      | none =>
          rw [rseRepivotDriverSuccNone fuel matrix pivotRow pivotCol hSearch]
          show rseCrossIsAllZero
            (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
            pivotRow pivotCol
          exact rseCrossSearchNoneAllZero
            (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
            pivotRow pivotCol hSearch
      | some newPos =>
          obtain ⟨newRow, newCol⟩ := newPos
          rw [rseRepivotDriverSuccSome fuel matrix pivotRow pivotCol newRow newCol hSearch]
          cases rseCrossSearchSomeCross
              (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
              pivotRow pivotCol newRow newCol hSearch with
          | inl rowArm =>
              obtain ⟨hRowEq, hColNe, hNonzero⟩ := rowArm
              subst newRow
              have degreeBelow :
                  rpxDegree (rbzMatrixEntry
                      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
                      pivotRow newCol)
                    < rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol) :=
                (rsmCrossClearRowMeasure (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow
                  matrix pivotNonzero newCol hColNe).resolve_left hNonzero
              exact rseRepivotDriverReachesAllZeroCross fuel
                (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
                pivotRow newCol hNonzero
                (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le degreeBelow pivotDegreeLe))
          | inr colArm =>
              obtain ⟨hColEq, hRowNe, hNonzero⟩ := colArm
              subst newCol
              have degreeBelow :
                  rpxDegree (rbzMatrixEntry
                      (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
                      newRow pivotCol)
                    < rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol) :=
                (rsmCrossClearColMeasure (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol pivotRow
                  matrix pivotNonzero newRow hRowNe).resolve_left hNonzero
              exact rseRepivotDriverReachesAllZeroCross fuel
                (rsmCrossClear (rbzMatrixEntry matrix pivotRow pivotCol) pivotCol matrix pivotRow)
                newRow pivotCol hNonzero
                (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le degreeBelow pivotDegreeLe))

/-! ## Groundings (fires)

The genuine-re-pivot fire matrix `[[x², x² + x], [x² + x, x²]]` — every entry has degree `2`, so the
minimum-degree pivot search picks `x²` at `(0, 0)`, but `x²` does NOT divide the cross entry `x² + x`
(residue `x`), so one clear leaves a nonzero residue and the driver MUST re-pivot to `x` (degree `1 < 2`)
before the cross clears.  Magnitudes ≤ 3 (all coefficients `0`/`1`). -/

set_option maxRecDepth 8192

/-- The genuine-re-pivot fire matrix `[[x², x² + x], [x² + x, x²]]`. -/
def rseFireMatrix : List (List (List QnfRat)) :=
  [[[qnfOfInt 0, qnfOfInt 0, qnfOfInt 1], [qnfOfInt 0, qnfOfInt 1, qnfOfInt 1]],
   [[qnfOfInt 0, qnfOfInt 1, qnfOfInt 1], [qnfOfInt 0, qnfOfInt 0, qnfOfInt 1]]]

/-- Fire (pivot degree): the minimum-degree pivot `x²` at `(0, 0)` has degree `2`, the driver's fuel. -/
theorem rseFirePivotDegreeTwo : rsePivotDegree rseFireMatrix 0 0 = 2 := rfl

/-- Fire (pivot search): the minimum-degree nonzero entry is `x²` at `(0, 0)` (all four entries have degree
`2`; the tie breaks to the earliest position). -/
theorem rseFirePivotSearch : rsmPivotSearch rseFireMatrix = some (0, 0) := rfl

/-- Fire (genuine re-pivot demand): ONE cross clear about the pivot `x²` at `(0, 0)` does NOT clear the
cross — the search still finds a nonzero residue `x` at `(0, 1)` (since `x² + x` mod `x² = x`), so a re-pivot
is genuinely required, not the trivial constant-pivot terminal. -/
theorem rseFireFirstClearLeavesResidue :
    rseCrossSearch (rsmCrossClear (rbzMatrixEntry rseFireMatrix 0 0) 0 rseFireMatrix 0) 0 0 = some (0, 1) :=
  rfl

/-- Fire (re-pivot step new pivot degree, value): after the re-pivot step swaps the residue `x` into the
`(0, 1)` slot and re-clears, the new pivot has degree `1`. -/
theorem rseFireStepNewPivotDegree : rsePivotDegree (rseRepivotStep rseFireMatrix 0 0 0 1) 0 1 = 1 := rfl

/-- Fire (re-pivot step strict drop, theorem): the row-arm re-pivot to the nonzero residue `x` at `(0, 1)`
strictly drops the pivot degree (`1 < 2`) via `rseStepRowStrictDrop`. -/
theorem rseFireStepStrictDrop :
    rsePivotDegree (rseRepivotStep rseFireMatrix 0 0 0 1) 0 1 < rsePivotDegree rseFireMatrix 0 0 :=
  rseStepRowStrictDrop rseFireMatrix 0 0 1
    (by
      show rpxTrim (rbzMatrixEntry rseFireMatrix 0 0) ≠ []
      rw [show rbzMatrixEntry rseFireMatrix 0 0 = [qnfOfInt 0, qnfOfInt 0, qnfOfInt 1] from rfl]
      exact List.cons_ne_nil (qnfOfInt 0) [qnfOfInt 0, qnfOfInt 1])
    (fun h => Nat.noConfusion h)
    (by
      rw [show rpxTrim (rbzMatrixEntry
            (rsmCrossClear (rbzMatrixEntry rseFireMatrix 0 0) 0 rseFireMatrix 0) 0 1)
            = [qnfOfInt 0, qnfOfInt 1] from rfl]
      exact List.cons_ne_nil (qnfOfInt 0) [qnfOfInt 1])

/-- Fire (driver final pivot position): the driver at fuel `2` terminates with its final pivot at `(0, 1)` —
the re-pivoted position `x`. -/
theorem rseFireDriverFinalPosition : (rseRepivotDriver 2 rseFireMatrix 0 0).2 = (0, 1) := rfl

/-- Fire (driver cross annihilated, off-pivot row): the `(0, 0)` entry (off the final pivot `(0, 1)` on its
row) trims to the zero polynomial after the driver runs. -/
theorem rseFireDriverCrossZeroRow :
    rpxTrim (rbzMatrixEntry (rseRepivotDriver 2 rseFireMatrix 0 0).1 0 0) = [] := rfl

/-- Fire (driver cross annihilated, off-pivot column): the `(1, 1)` entry (off the final pivot `(0, 1)` on
its column) trims to the zero polynomial after the driver runs. -/
theorem rseFireDriverCrossZeroCol :
    rpxTrim (rbzMatrixEntry (rseRepivotDriver 2 rseFireMatrix 0 0).1 1 1) = [] := rfl

/-- Fire (driver reaches the all-zero cross, theorem): the driver at the adequate fuel `2 = deg(x²)` reaches
a matrix whose cross about the final pivot position is entirely zero, via
`rseRepivotDriverReachesAllZeroCross`. -/
theorem rseFireDriverReachesAllZeroCross :
    rseCrossIsAllZero (rseRepivotDriver 2 rseFireMatrix 0 0).1
      (rseRepivotDriver 2 rseFireMatrix 0 0).2.1
      (rseRepivotDriver 2 rseFireMatrix 0 0).2.2 :=
  rseRepivotDriverReachesAllZeroCross 2 rseFireMatrix 0 0
    (by
      show rpxTrim (rbzMatrixEntry rseFireMatrix 0 0) ≠ []
      rw [show rbzMatrixEntry rseFireMatrix 0 0 = [qnfOfInt 0, qnfOfInt 0, qnfOfInt 1] from rfl]
      exact List.cons_ne_nil (qnfOfInt 0) [qnfOfInt 0, qnfOfInt 1])
    (Nat.le_refl 2)

/-! ## Content markers -/

/-- DECIDED: the ℚ[x] Smith RE-PIVOT STEP — `rseRepivotStep` clears the cross about the pivot then re-clears
about the moving position `(newRow, newCol)`, and STRICTLY DROPS the pivot-degree measure `rsePivotDegree`
when that position is a nonzero cross residue (`rseStepColumnStrictDrop` on the pivot column,
`rseStepRowStrictDrop` on the pivot row), from the committed cross-clear measure lemmas
(`rsmCrossClearRowMeasure`/`rsmCrossClearColMeasure`) resolved by nonzero.  The step is an ELEMENTARY-OP
COMPOSITE: the moved pivot reconstructs the old cross entry as a `pivot`-multiple residue
(`rseStepColumnReconstructs`, from `rsmCrossClearColReconstructs`) — the legitimacy of the swap. -/
def rseHasRepivotStepStrictDrop : Bool := true

/-- DECIDED: the ℚ[x] Smith CROSS SEARCH — `rseCrossSearch` returns the first nonzero off-pivot cross residue
(the pivot row skipping the pivot column, then the pivot column skipping the pivot row), with the full
soundness: `none` certifies the all-zero cross (`rseCrossSearchNoneAllZero`) and `some` a nonzero cross
position on a definite arm (`rseCrossSearchSomeCross`), built on the four structural search-soundness lemmas
(`rseRowSearchAllSoundHolds`/`rseRowSearchExceptSoundHolds`/`rseColumnSearchAllSoundHolds`/
`rseColumnSearchExceptSoundHolds`). -/
def rseHasCrossSearch : Bool := true

/-- DECIDED (supersedes the committed owner-false `rsfHasAllZeroCrossFixedPoint`, `rsmHasCrossFixedPoint`, and
`rsdHasAllZeroCrossViaRepivot`, all byte-intact false): the ALL-ZERO cleared cross over ℚ[x] via the re-pivot
DRIVER.  `rseRepivotDriver` iterates clear + `rseCrossSearch` + re-pivot with structural `Nat` fuel = the
pivot degree, which strictly drops each round (the residue is below the pivot); the base `fuel = 0` is a
CONSTANT pivot, which over the field ℚ divides every entry, so one clear annihilates the whole cross
(`rseConstantPivotClearsCross`, the measure's `degree < 0` disjunct being absurd).  The driver reaches the
all-zero cross under the invariant `pivot degree ≤ fuel` (`rseRepivotDriverReachesAllZeroCross`, structural
fuel induction).  This closes the wall the committed descent kit named: the moving-position ARITY bookkeeping,
handled in the swap-free moving-position model.  The termination lever `rpxMul` degree additivity (rung 7,
`rsdDegreeMul`) makes the iteration terminate; the driver's index bookkeeping is now decided. -/
def rseHasAllZeroCrossViaRepivot : Bool := true

/-- WALLED (owner-false; the committed `rsfHasSubmatrixDescent := false`, `rsmHasSmithNormalForm := false`,
`rbzHasSmithNormalForm := false`, and `rsdHasInvariantFactorChain := false` stay byte-intact): the FULL Smith
normal form over ℚ[x] — the diagonal `diag(d₁, …, dᵣ, 0, …)` with the invariant-factor divisibility chain
`d₁ | d₂ | ⋯ | dᵣ`.  With the all-zero cross now DECIDED (`rseHasAllZeroCrossViaRepivot`) the matrix is
block-diagonal `[[pivot, 0…], [0…, submatrix]]`, and the `(r-1)×(c-1)` extractor `rsfSubmatrix` (committed)
is the recursion target.  Two pieces remain, neither attempted here:
  (1) the DIAGONALIZATION DRIVER — a fresh `Nat` measure = matrix size (`rsfSubmatrix` strictly shrinks the
      matrix), recursing pivot-search → re-pivot driver → `rsfSubmatrix`, accumulating the diagonal;
  (2) the INVARIANT-FACTOR CHAIN `dₖ | dₖ₊₁` — this needs the pivot to divide EVERY entry of the trailing
      submatrix (not merely its all-zero cross); when it does not, the textbook remedy adds the offending
      row into the pivot row and re-clears, producing a still-smaller residue (a SECOND descent on top of the
      cross clear), after which `rpeGcdDividesBoth` (each `dᵢ` is a gcd of the surviving minors) composed
      with `rbzDividesTrans` (transitivity of `rpeDivides`) delivers the chain.  Both divisibility
      ingredients ship; the pivot-divides-all-submatrix descent and the size-measure diagonalizer are the
      open bookkeeping. -/
def rseHasSubmatrixDescent : Bool := false

end FX1Poly.ComputerAlgebra
