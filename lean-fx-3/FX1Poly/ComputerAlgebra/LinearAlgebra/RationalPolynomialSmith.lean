import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialBezout

/-! # RationalPolynomialSmith — the Smith pivot search and cross clear over ℚ[x] matrices

Building on the pivot-clear seed of `RationalPolynomialBezout` (the ℚ[x]-matrix carrier with accessors, the
single-entry clear `rbzClearEntry`, the first pivot lemma `rbzClearEntryReducesDegree`, and the reconstruction
`rbzClearEntryReconstructs`), this module ships the minimum-degree pivot search and the one-pass cross clear.

`rsmPivotSearch` is a total function returning the position of a minimum-degree nonzero entry, or `none` for an
all-zero matrix, built from a single-row minimum (`rsmRowMin`) and a matrix minimum (`rsmMatrixMin`) comparing
degrees through `Nat.decLt`. Its bundled soundness gives: the found entry is nonzero (`rsmPivotSearchNonzero`),
has degree `≤` every nonzero entry (`rsmPivotSearchMinimal`), and `none` certifies an all-zero matrix
(`rsmPivotSearchNoneAllZero`).

`rsmCrossClear` clears the pivot's row and column against the pivot via the per-entry clear
`rsmClearAgainst pivot entry := rbzClearEntry entry.length pivot entry` (`rsmRowClearExcept` on the pivot row,
`rsmColumnClearBelow` on the pivot column). It preserves the pivot (`rsmCrossClearPivotPreserved`); every
off-pivot entry of the pivot row (`rsmCrossClearRowMeasure`) and column (`rsmCrossClearColMeasure`) trims to
zero or drops below the pivot degree; and each cleared entry differs from the original by a `pivot`-multiple
(`rsmCrossClearRowReconstructs`/`rsmCrossClearColReconstructs`), the elementary-op legitimacy. The reduced
cross fixed point, the all-zero cross, and the full Smith normal form are supplied or walled downstream
(`rsfHasReducedCrossFixedPoint`, `rseHasAllZeroCrossViaRepivot`, `rsiHasSmithNormalForm`).

Every definition is structural on the list and the positional index; case analyses are `Nat.decLt` and
Option/Prod projection (full enumeration). No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`, `funext`, or `WellFounded.fix`. Per-declaration audit twin in the matching
`FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## T1 — the minimum-degree nonzero pivot search -/

/-- Pick the smaller-degree of two indexed candidates (the second component is the polynomial).  Factored out
of `rsmRowMin` so the recursion is only two `match` levels deep — a three-level nested `match` compiles to a
multi-discriminant matcher that does not iota-reduce under `rw`, which this factoring avoids. -/
def rsmMinByDegree (candA candB : Nat × List QnfRat) : Nat × List QnfRat :=
  match Nat.decLt (rpxDegree candB.2) (rpxDegree candA.2) with
  | isTrue _ => candB
  | isFalse _ => candA

/-- Pick the smaller-degree of two doubly-indexed candidates (the third component is the polynomial).  The
matrix analogue of `rsmMinByDegree`. -/
def rsmMinByDegreeTriple (candA candB : Nat × Nat × List QnfRat) : Nat × Nat × List QnfRat :=
  match Nat.decLt (rpxDegree candB.2.2) (rpxDegree candA.2.2) with
  | isTrue _ => candB
  | isFalse _ => candA

/-- Minimum-degree nonzero entry of one row.  Returns the local column index and the entry itself, or `none`
when every entry of the row is the zero polynomial.  A nonzero head competes with the recursive minimum of
the tail via `rsmMinByDegree`; a zero head is skipped (its index shifting the tail's answer up by one). -/
def rsmRowMin : List (List QnfRat) → Option (Nat × List QnfRat)
  | [] => none
  | entry :: rest =>
      match rpxTrim entry with
      | [] =>
          match rsmRowMin rest with
          | none => none
          | some (localCol, foundEntry) => some (localCol + 1, foundEntry)
      | _ :: _ =>
          match rsmRowMin rest with
          | none => some (0, entry)
          | some (localCol, foundEntry) => some (rsmMinByDegree (0, entry) (localCol + 1, foundEntry))

/-- Minimum-degree nonzero entry of a whole matrix.  Returns `(rowIndex, colIndex, entry)`, or `none` for an
all-zero matrix.  Each row's minimum (`rsmRowMin`) competes with the recursive matrix minimum of the trailing
rows via `rsmMinByDegreeTriple`; an all-zero row is skipped (its row index shifting the trailing answer up by
one). -/
def rsmMatrixMin : List (List (List QnfRat)) → Option (Nat × Nat × List QnfRat)
  | [] => none
  | row :: rest =>
      match rsmRowMin row with
      | none =>
          match rsmMatrixMin rest with
          | none => none
          | some (foundRow, foundCol, foundEntry) => some (foundRow + 1, foundCol, foundEntry)
      | some (col, entry) =>
          match rsmMatrixMin rest with
          | none => some (0, col, entry)
          | some (foundRow, foundCol, foundEntry) =>
              some (rsmMinByDegreeTriple (0, col, entry) (foundRow + 1, foundCol, foundEntry))

/-- **The pivot search.**  Position `(rowIndex, colIndex)` of a minimum-degree nonzero entry, or `none` for
an all-zero matrix.  The entry itself is dropped (recoverable via `rbzMatrixEntry`). -/
def rsmPivotSearch (matrix : List (List (List QnfRat))) : Option (Nat × Nat) :=
  match rsmMatrixMin matrix with
  | none => none
  | some (foundRow, foundCol, _) => some (foundRow, foundCol)

/-! ### The `rsmMinByDegree` picking laws -/

/-- The pair-min result is one of the two candidates. -/
theorem rsmMinByDegreeEq (candA candB : Nat × List QnfRat) :
    rsmMinByDegree candA candB = candA ∨ rsmMinByDegree candA candB = candB := by
  dsimp only [rsmMinByDegree]
  cases Nat.decLt (rpxDegree candB.2) (rpxDegree candA.2) with
  | isTrue _ => exact Or.inr rfl
  | isFalse _ => exact Or.inl rfl

/-- The pair-min degree is at most the first candidate's. -/
theorem rsmMinByDegreeLeA (candA candB : Nat × List QnfRat) :
    rpxDegree (rsmMinByDegree candA candB).2 ≤ rpxDegree candA.2 := by
  dsimp only [rsmMinByDegree]
  cases Nat.decLt (rpxDegree candB.2) (rpxDegree candA.2) with
  | isTrue hLt => exact Nat.le_of_lt hLt
  | isFalse _ => exact Nat.le_refl _

/-- The pair-min degree is at most the second candidate's. -/
theorem rsmMinByDegreeLeB (candA candB : Nat × List QnfRat) :
    rpxDegree (rsmMinByDegree candA candB).2 ≤ rpxDegree candB.2 := by
  dsimp only [rsmMinByDegree]
  cases hCmp : Nat.decLt (rpxDegree candB.2) (rpxDegree candA.2) with
  | isTrue _ => exact Nat.le_refl _
  | isFalse hNot => exact (Nat.lt_or_ge (rpxDegree candB.2) (rpxDegree candA.2)).resolve_left hNot

/-- The triple-min result is one of the two candidates. -/
theorem rsmMinByDegreeTripleEq (candA candB : Nat × Nat × List QnfRat) :
    rsmMinByDegreeTriple candA candB = candA ∨ rsmMinByDegreeTriple candA candB = candB := by
  dsimp only [rsmMinByDegreeTriple]
  cases Nat.decLt (rpxDegree candB.2.2) (rpxDegree candA.2.2) with
  | isTrue _ => exact Or.inr rfl
  | isFalse _ => exact Or.inl rfl

/-- The triple-min degree is at most the first candidate's. -/
theorem rsmMinByDegreeTripleLeA (candA candB : Nat × Nat × List QnfRat) :
    rpxDegree (rsmMinByDegreeTriple candA candB).2.2 ≤ rpxDegree candA.2.2 := by
  dsimp only [rsmMinByDegreeTriple]
  cases Nat.decLt (rpxDegree candB.2.2) (rpxDegree candA.2.2) with
  | isTrue hLt => exact Nat.le_of_lt hLt
  | isFalse _ => exact Nat.le_refl _

/-- The triple-min degree is at most the second candidate's. -/
theorem rsmMinByDegreeTripleLeB (candA candB : Nat × Nat × List QnfRat) :
    rpxDegree (rsmMinByDegreeTriple candA candB).2.2 ≤ rpxDegree candB.2.2 := by
  dsimp only [rsmMinByDegreeTriple]
  cases hCmp : Nat.decLt (rpxDegree candB.2.2) (rpxDegree candA.2.2) with
  | isTrue _ => exact Nat.le_refl _
  | isFalse hNot => exact (Nat.lt_or_ge (rpxDegree candB.2.2) (rpxDegree candA.2.2)).resolve_left hNot

/-! ### `rsmRowMin` / `rsmMatrixMin` step equations (two-level matches reduce under `rw`) -/

/-- `rsmRowMin` on a cons with a zero head and an all-zero tail is `none`. -/
theorem rsmRowMinConsZeroNone (entry : List QnfRat) (rest : List (List QnfRat))
    (hTrim : rpxTrim entry = []) (hRest : rsmRowMin rest = none) :
    rsmRowMin (entry :: rest) = none := by
  dsimp only [rsmRowMin]; rw [hTrim, hRest]

/-- `rsmRowMin` on a cons with a zero head shifts the tail's answer up by one column. -/
theorem rsmRowMinConsZeroSome (entry : List QnfRat) (rest : List (List QnfRat))
    (localCol : Nat) (foundEntry : List QnfRat)
    (hTrim : rpxTrim entry = []) (hRest : rsmRowMin rest = some (localCol, foundEntry)) :
    rsmRowMin (entry :: rest) = some (localCol + 1, foundEntry) := by
  dsimp only [rsmRowMin]; rw [hTrim, hRest]

/-- `rsmRowMin` on a cons with a nonzero head and an all-zero tail is the head at column `0`. -/
theorem rsmRowMinConsNonzeroNone (entry : List QnfRat) (rest : List (List QnfRat))
    (trimHead : QnfRat) (trimTail : List QnfRat)
    (hTrim : rpxTrim entry = trimHead :: trimTail) (hRest : rsmRowMin rest = none) :
    rsmRowMin (entry :: rest) = some (0, entry) := by
  dsimp only [rsmRowMin]; rw [hTrim, hRest]

/-- `rsmRowMin` on a cons with a nonzero head competes head vs. tail via `rsmMinByDegree`. -/
theorem rsmRowMinConsNonzeroSome (entry : List QnfRat) (rest : List (List QnfRat))
    (trimHead : QnfRat) (trimTail : List QnfRat) (localCol : Nat) (foundEntry : List QnfRat)
    (hTrim : rpxTrim entry = trimHead :: trimTail) (hRest : rsmRowMin rest = some (localCol, foundEntry)) :
    rsmRowMin (entry :: rest) = some (rsmMinByDegree (0, entry) (localCol + 1, foundEntry)) := by
  dsimp only [rsmRowMin]; rw [hTrim, hRest]

/-- `rsmMatrixMin` on a cons with an all-zero row and all-zero trailing block is `none`. -/
theorem rsmMatrixMinConsZeroNone (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (hRow : rsmRowMin row = none) (hRest : rsmMatrixMin rest = none) :
    rsmMatrixMin (row :: rest) = none := by
  dsimp only [rsmMatrixMin]; rw [hRow, hRest]

/-- `rsmMatrixMin` on a cons with an all-zero row shifts the trailing answer up by one row. -/
theorem rsmMatrixMinConsZeroSome (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (foundRow foundCol : Nat) (foundEntry : List QnfRat)
    (hRow : rsmRowMin row = none) (hRest : rsmMatrixMin rest = some (foundRow, foundCol, foundEntry)) :
    rsmMatrixMin (row :: rest) = some (foundRow + 1, foundCol, foundEntry) := by
  dsimp only [rsmMatrixMin]; rw [hRow, hRest]

/-- `rsmMatrixMin` on a cons with a nonzero row and all-zero trailing block is that row's minimum at row
`0`. -/
theorem rsmMatrixMinConsNonzeroNone (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (col : Nat) (entry : List QnfRat)
    (hRow : rsmRowMin row = some (col, entry)) (hRest : rsmMatrixMin rest = none) :
    rsmMatrixMin (row :: rest) = some (0, col, entry) := by
  dsimp only [rsmMatrixMin]; rw [hRow, hRest]

/-- `rsmMatrixMin` on a cons with a nonzero row competes row vs. trailing block via `rsmMinByDegreeTriple`. -/
theorem rsmMatrixMinConsNonzeroSome (row : List (List QnfRat)) (rest : List (List (List QnfRat)))
    (col : Nat) (entry : List QnfRat) (foundRow foundCol : Nat) (foundEntry : List QnfRat)
    (hRow : rsmRowMin row = some (col, entry))
    (hRest : rsmMatrixMin rest = some (foundRow, foundCol, foundEntry)) :
    rsmMatrixMin (row :: rest)
      = some (rsmMinByDegreeTriple (0, col, entry) (foundRow + 1, foundCol, foundEntry)) := by
  dsimp only [rsmMatrixMin]; rw [hRow, hRest]

/-! ### The bundled soundness predicates and their proofs -/

/-- The soundness bar for a single-row minimum: on `none` the whole row is zero; on `some result` the entry
reads back at its column, is nonzero, and its degree bounds every nonzero entry's degree. -/
def rsmRowMinSound (row : List (List QnfRat)) : Option (Nat × List QnfRat) → Prop
  | none => ∀ position : Nat, rpxTrim (rbzEntryGet row position) = []
  | some result =>
      rbzEntryGet row result.1 = result.2
        ∧ rpxTrim result.2 ≠ []
        ∧ ∀ position : Nat, rpxTrim (rbzEntryGet row position) ≠ []
            → rpxDegree result.2 ≤ rpxDegree (rbzEntryGet row position)

/-- **The single-row minimum satisfies its soundness bar** at every row — reads-back, nonzero, minimal, and
the all-zero characterization of `none`.  Structural induction on the row, casing the head's trim, the
tail's minimum, and the degree comparison. -/
theorem rsmRowMinSoundHolds : ∀ row : List (List QnfRat), rsmRowMinSound row (rsmRowMin row)
  | [] => fun _position => rfl
  | entry :: rest => by
      have ih := rsmRowMinSoundHolds rest
      cases hTrim : rpxTrim entry with
      | nil =>
          cases hRest : rsmRowMin rest with
          | none =>
              rw [rsmRowMinConsZeroNone entry rest hTrim hRest]
              rw [hRest] at ih
              intro position
              cases position with
              | zero => exact hTrim
              | succ prior => exact ih prior
          | some res =>
              obtain ⟨localCol, foundEntry⟩ := res
              rw [rsmRowMinConsZeroSome entry rest localCol foundEntry hTrim hRest]
              rw [hRest] at ih
              refine ⟨ih.1, ih.2.1, ?_⟩
              intro position hnz
              cases position with
              | zero => exact absurd hTrim hnz
              | succ prior => exact ih.2.2 prior hnz
      | cons trimHead trimTail =>
          cases hRest : rsmRowMin rest with
          | none =>
              rw [rsmRowMinConsNonzeroNone entry rest trimHead trimTail hTrim hRest]
              rw [hRest] at ih
              refine ⟨rfl, ?_, ?_⟩
              · rw [hTrim]; exact List.cons_ne_nil trimHead trimTail
              · intro position hnz
                cases position with
                | zero => exact Nat.le_refl _
                | succ prior => exact absurd (ih prior) hnz
          | some res =>
              obtain ⟨localCol, foundEntry⟩ := res
              rw [rsmRowMinConsNonzeroSome entry rest trimHead trimTail localCol foundEntry hTrim hRest]
              rw [hRest] at ih
              refine ⟨?_, ?_, ?_⟩
              · cases rsmMinByDegreeEq (0, entry) (localCol + 1, foundEntry) with
                | inl hPick => rw [hPick]; rfl
                | inr hPick => rw [hPick]; exact ih.1
              · cases rsmMinByDegreeEq (0, entry) (localCol + 1, foundEntry) with
                | inl hPick => rw [hPick, hTrim]; exact List.cons_ne_nil trimHead trimTail
                | inr hPick => rw [hPick]; exact ih.2.1
              · intro position hnz
                cases position with
                | zero => exact rsmMinByDegreeLeA (0, entry) (localCol + 1, foundEntry)
                | succ prior =>
                    exact Nat.le_trans (rsmMinByDegreeLeB (0, entry) (localCol + 1, foundEntry))
                      (ih.2.2 prior hnz)

/-- The soundness bar for a matrix minimum: on `none` every entry is zero; on `some result` the entry reads
back at `(row, col)`, is nonzero, and its degree bounds every nonzero entry's degree. -/
def rsmMatrixMinSound (matrix : List (List (List QnfRat))) : Option (Nat × Nat × List QnfRat) → Prop
  | none => ∀ rowIndex colIndex : Nat, rpxTrim (rbzMatrixEntry matrix rowIndex colIndex) = []
  | some result =>
      rbzMatrixEntry matrix result.1 result.2.1 = result.2.2
        ∧ rpxTrim result.2.2 ≠ []
        ∧ ∀ rowIndex colIndex : Nat, rpxTrim (rbzMatrixEntry matrix rowIndex colIndex) ≠ []
            → rpxDegree result.2.2 ≤ rpxDegree (rbzMatrixEntry matrix rowIndex colIndex)

/-- **The matrix minimum satisfies its soundness bar** at every matrix — reads-back, nonzero, minimal, and
the all-zero characterization of `none`.  Structural induction on the rows, using the single-row soundness
(`rsmRowMinSoundHolds`) for the current row and the inductive matrix soundness for the trailing rows, casing
the row minimum, the trailing matrix minimum, and the degree comparison.  Reads back through
`rbzMatrixEntry (row :: rest) 0 j = rbzEntryGet row j` and `rbzMatrixEntry (row :: rest) (i+1) j =
rbzMatrixEntry rest i j`. -/
theorem rsmMatrixMinSoundHolds :
    ∀ matrix : List (List (List QnfRat)), rsmMatrixMinSound matrix (rsmMatrixMin matrix)
  | [] => fun _rowIndex _colIndex => rfl
  | row :: rest => by
      have ihMatrix := rsmMatrixMinSoundHolds rest
      have rowSpec := rsmRowMinSoundHolds row
      cases hRow : rsmRowMin row with
      | none =>
          rw [hRow] at rowSpec
          cases hRest : rsmMatrixMin rest with
          | none =>
              rw [rsmMatrixMinConsZeroNone row rest hRow hRest]
              rw [hRest] at ihMatrix
              intro rowIndex colIndex
              cases rowIndex with
              | zero => exact rowSpec colIndex
              | succ prior => exact ihMatrix prior colIndex
          | some res =>
              obtain ⟨foundRow, foundCol, foundEntry⟩ := res
              rw [rsmMatrixMinConsZeroSome row rest foundRow foundCol foundEntry hRow hRest]
              rw [hRest] at ihMatrix
              refine ⟨ihMatrix.1, ihMatrix.2.1, ?_⟩
              intro rowIndex colIndex hnz
              cases rowIndex with
              | zero => exact absurd (rowSpec colIndex) hnz
              | succ prior => exact ihMatrix.2.2 prior colIndex hnz
      | some rowRes =>
          obtain ⟨col, entry⟩ := rowRes
          rw [hRow] at rowSpec
          cases hRest : rsmMatrixMin rest with
          | none =>
              rw [rsmMatrixMinConsNonzeroNone row rest col entry hRow hRest]
              rw [hRest] at ihMatrix
              refine ⟨rowSpec.1, rowSpec.2.1, ?_⟩
              intro rowIndex colIndex hnz
              cases rowIndex with
              | zero => exact rowSpec.2.2 colIndex hnz
              | succ prior => exact absurd (ihMatrix prior colIndex) hnz
          | some res =>
              obtain ⟨foundRow, foundCol, foundEntry⟩ := res
              rw [rsmMatrixMinConsNonzeroSome row rest col entry foundRow foundCol foundEntry hRow hRest]
              rw [hRest] at ihMatrix
              refine ⟨?_, ?_, ?_⟩
              · cases rsmMinByDegreeTripleEq (0, col, entry) (foundRow + 1, foundCol, foundEntry) with
                | inl hPick => rw [hPick]; exact rowSpec.1
                | inr hPick => rw [hPick]; exact ihMatrix.1
              · cases rsmMinByDegreeTripleEq (0, col, entry) (foundRow + 1, foundCol, foundEntry) with
                | inl hPick => rw [hPick]; exact rowSpec.2.1
                | inr hPick => rw [hPick]; exact ihMatrix.2.1
              · intro rowIndex colIndex hnz
                cases rowIndex with
                | zero =>
                    exact Nat.le_trans
                      (rsmMinByDegreeTripleLeA (0, col, entry) (foundRow + 1, foundCol, foundEntry))
                      (rowSpec.2.2 colIndex hnz)
                | succ prior =>
                    exact Nat.le_trans
                      (rsmMinByDegreeTripleLeB (0, col, entry) (foundRow + 1, foundCol, foundEntry))
                      (ihMatrix.2.2 prior colIndex hnz)

/-! ### The top-level pivot-search corollaries -/

/-- `rsmPivotSearch matrix = none` when `rsmMatrixMin matrix = none`. -/
theorem rsmPivotSearchEqNone (matrix : List (List (List QnfRat)))
    (hMin : rsmMatrixMin matrix = none) : rsmPivotSearch matrix = none := by
  dsimp only [rsmPivotSearch]; rw [hMin]

/-- `rsmPivotSearch matrix = some (rowIndex, colIndex)` when `rsmMatrixMin matrix = some (rowIndex, colIndex,
entry)`. -/
theorem rsmPivotSearchEqSome (matrix : List (List (List QnfRat)))
    (rowIndex colIndex : Nat) (entry : List QnfRat)
    (hMin : rsmMatrixMin matrix = some (rowIndex, colIndex, entry)) :
    rsmPivotSearch matrix = some (rowIndex, colIndex) := by
  dsimp only [rsmPivotSearch]; rw [hMin]

/-- **The found pivot is sound.**  From `rsmPivotSearch matrix = some (pivotRow, pivotCol)`, the pivot entry
is nonzero and has degree `≤` every nonzero entry — the bundled corollary of `rsmMatrixMinSoundHolds`.  Casing
`rsmMatrixMin matrix` is harmless here because the goal does not mention it; the `some` case reads back the
entry through `rsmPivotSearchEqSome` and the matrix soundness. -/
theorem rsmPivotSearchSomeSound (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat) (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    rpxTrim (rbzMatrixEntry matrix pivotRow pivotCol) ≠ []
      ∧ ∀ rowIndex colIndex : Nat, rpxTrim (rbzMatrixEntry matrix rowIndex colIndex) ≠ []
          → rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol)
              ≤ rpxDegree (rbzMatrixEntry matrix rowIndex colIndex) := by
  have spec := rsmMatrixMinSoundHolds matrix
  cases hMin : rsmMatrixMin matrix with
  | none =>
      rw [rsmPivotSearchEqNone matrix hMin] at hPivot
      nomatch hPivot
  | some res =>
      obtain ⟨foundRow, foundCol, foundEntry⟩ := res
      rw [hMin] at spec
      rw [rsmPivotSearchEqSome matrix foundRow foundCol foundEntry hMin] at hPivot
      have hPair : (foundRow, foundCol) = (pivotRow, pivotCol) := Option.some.inj hPivot
      have hRow : foundRow = pivotRow := congrArg Prod.fst hPair
      have hCol : foundCol = pivotCol := congrArg Prod.snd hPair
      have hEntryEq : rbzMatrixEntry matrix pivotRow pivotCol = foundEntry := by
        rw [← hRow, ← hCol]; exact spec.1
      refine ⟨?_, ?_⟩
      · rw [hEntryEq]; exact spec.2.1
      · intro rowIndex colIndex hnz
        rw [hEntryEq]
        exact spec.2.2 rowIndex colIndex hnz

/-- **The found pivot is a nonzero entry.** -/
theorem rsmPivotSearchNonzero (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat) (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    rpxTrim (rbzMatrixEntry matrix pivotRow pivotCol) ≠ [] :=
  (rsmPivotSearchSomeSound matrix pivotRow pivotCol hPivot).1

/-- **The found pivot has minimum degree among nonzero entries.**  Every nonzero entry of the matrix has
degree at least the pivot's. -/
theorem rsmPivotSearchMinimal (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat) (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    ∀ rowIndex colIndex : Nat, rpxTrim (rbzMatrixEntry matrix rowIndex colIndex) ≠ [] →
      rpxDegree (rbzMatrixEntry matrix pivotRow pivotCol)
        ≤ rpxDegree (rbzMatrixEntry matrix rowIndex colIndex) :=
  (rsmPivotSearchSomeSound matrix pivotRow pivotCol hPivot).2

/-- **No pivot means an all-zero matrix.**  When the search returns `none`, every entry trims to the zero
polynomial. -/
theorem rsmPivotSearchNoneAllZero (matrix : List (List (List QnfRat)))
    (hNone : rsmPivotSearch matrix = none) :
    ∀ rowIndex colIndex : Nat, rpxTrim (rbzMatrixEntry matrix rowIndex colIndex) = [] := by
  have spec := rsmMatrixMinSoundHolds matrix
  cases hMin : rsmMatrixMin matrix with
  | none => rw [hMin] at spec; exact spec
  | some res =>
      obtain ⟨foundRow, foundCol, foundEntry⟩ := res
      rw [rsmPivotSearchEqSome matrix foundRow foundCol foundEntry hMin] at hNone
      nomatch hNone

/-! ## T2 — the cross clear (clearing the pivot's row and column) -/

/-- Clear one entry against a pivot at the adequate per-entry fuel `entry.length`: the Euclidean residue
`entry mod pivot`, i.e. the elementary operation `entry ↦ entry − quotient·pivot`.  The fuel matches the
committed `rbzClearEntryReducesDegree`/`rbzClearEntryReconstructs`. -/
def rsmClearAgainst (pivot entry : List QnfRat) : List QnfRat :=
  rbzClearEntry entry.length pivot entry

/-- Clear every entry of a column (a list of entries) against a pivot. -/
def rsmColumnClearAll (pivot : List QnfRat) : List (List QnfRat) → List (List QnfRat)
  | [] => []
  | entry :: rest => rsmClearAgainst pivot entry :: rsmColumnClearAll pivot rest

/-- Clear every entry of a row against a pivot EXCEPT the one at `skipCol` (the pivot column, left
untouched).  Structural on the row (matched first so `rsmRowClearExcept pivot [] skipCol` reduces for a
symbolic `skipCol`). -/
def rsmRowClearExcept (pivot : List QnfRat) : List (List QnfRat) → Nat → List (List QnfRat)
  | [], _ => []
  | entry :: rest, 0 => entry :: rsmColumnClearAll pivot rest
  | entry :: rest, skipCol + 1 => rsmClearAgainst pivot entry :: rsmRowClearExcept pivot rest skipCol

/-- Clear only the entry at `targetCol` of a row against a pivot, leaving every other entry untouched.
Structural on the row (matched first). -/
def rsmClearRowAtCol (pivot : List QnfRat) : List (List QnfRat) → Nat → List (List QnfRat)
  | [], _ => []
  | entry :: rest, 0 => rsmClearAgainst pivot entry :: rest
  | entry :: rest, targetCol + 1 => entry :: rsmClearRowAtCol pivot rest targetCol

/-- Clear the pivot-column entry of every row in a block (the rows away from the pivot row). -/
def rsmColumnClearBelow (pivot : List QnfRat) (pivotCol : Nat) :
    List (List (List QnfRat)) → List (List (List QnfRat))
  | [] => []
  | row :: rest => rsmClearRowAtCol pivot row pivotCol :: rsmColumnClearBelow pivot pivotCol rest

/-- **The cross clear.**  One pass clearing the pivot's row (everywhere except the pivot column) and the
pivot's column (every other row).  Structural on the matrix (matched first); the pivot row is located by the
counting index `pivotRow`, and every other row has only its pivot-column entry cleared. -/
def rsmCrossClear (pivot : List QnfRat) (pivotCol : Nat) :
    List (List (List QnfRat)) → Nat → List (List (List QnfRat))
  | [], _ => []
  | row :: rest, 0 => rsmRowClearExcept pivot row pivotCol :: rsmColumnClearBelow pivot pivotCol rest
  | row :: rest, pivotRow + 1 =>
      rsmClearRowAtCol pivot row pivotCol :: rsmCrossClear pivot pivotCol rest pivotRow

/-! ### Accessor lemmas -/

/-- Reading a cleared column reads the clear of the original entry (uniformly, past-end included since
`rsmClearAgainst pivot [] = []`). -/
theorem rsmColumnClearAllGet :
    ∀ (pivot : List QnfRat) (column : List (List QnfRat)) (position : Nat),
      rbzEntryGet (rsmColumnClearAll pivot column) position
        = rsmClearAgainst pivot (rbzEntryGet column position)
  | _pivot, [], _position => rfl
  | pivot, _entry :: rest, position => by
      cases position with
      | zero => rfl
      | succ prior => exact rsmColumnClearAllGet pivot rest prior

/-- **Column-clear measure.**  Against a nonzero pivot, every cleared column entry trims to the zero
polynomial or has degree strictly below the pivot's. -/
theorem rsmColumnClearAllMeasure (pivot : List QnfRat) (column : List (List QnfRat))
    (pivotNonzero : rpxTrim pivot ≠ []) (position : Nat) :
    rpxTrim (rbzEntryGet (rsmColumnClearAll pivot column) position) = []
      ∨ rpxDegree (rbzEntryGet (rsmColumnClearAll pivot column) position) < rpxDegree pivot := by
  rw [rsmColumnClearAllGet]
  exact rbzClearEntryReducesDegree pivot (rbzEntryGet column position) pivotNonzero

/-- **Column-clear reconstruction.**  Each cleared column entry differs from the original by a
`pivot`-multiple: `quotient·pivot + cleared ≡ original`. -/
theorem rsmColumnClearAllReconstructs (pivot : List QnfRat) (column : List (List QnfRat)) (position : Nat) :
    rpxTrim (rpxAdd
        (rpxMul (rpxDivMod (rbzEntryGet column position).length pivot
          (rbzEntryGet column position)).1 pivot)
        (rbzEntryGet (rsmColumnClearAll pivot column) position))
      = rpxTrim (rbzEntryGet column position) := by
  rw [rsmColumnClearAllGet]
  exact rbzClearEntryReconstructs (rbzEntryGet column position).length pivot
    (rbzEntryGet column position)

/-- Reading the pivot column of a row cleared with `rsmRowClearExcept` returns the untouched entry. -/
theorem rsmRowClearExceptGetSkip :
    ∀ (pivot : List QnfRat) (row : List (List QnfRat)) (skipCol : Nat),
      rbzEntryGet (rsmRowClearExcept pivot row skipCol) skipCol = rbzEntryGet row skipCol
  | _pivot, [], _skipCol => rfl
  | _pivot, _entry :: _rest, 0 => rfl
  | pivot, _entry :: rest, skipCol + 1 => by
      show rbzEntryGet (rsmRowClearExcept pivot rest skipCol) skipCol = rbzEntryGet rest skipCol
      exact rsmRowClearExceptGetSkip pivot rest skipCol

/-- Reading any off-pivot column of a row cleared with `rsmRowClearExcept` returns the clear of the original
entry. -/
theorem rsmRowClearExceptGetOther :
    ∀ (pivot : List QnfRat) (row : List (List QnfRat)) (skipCol position : Nat),
      position ≠ skipCol →
      rbzEntryGet (rsmRowClearExcept pivot row skipCol) position
        = rsmClearAgainst pivot (rbzEntryGet row position)
  | _pivot, [], _skipCol, _position, _hne => rfl
  | pivot, _entry :: rest, 0, position, hne => by
      cases position with
      | zero => exact absurd rfl hne
      | succ prior =>
          show rbzEntryGet (rsmColumnClearAll pivot rest) prior
            = rsmClearAgainst pivot (rbzEntryGet rest prior)
          exact rsmColumnClearAllGet pivot rest prior
  | pivot, _entry :: rest, skipCol + 1, position, hne => by
      cases position with
      | zero => rfl
      | succ prior =>
          have hne' : prior ≠ skipCol := fun heq => hne (congrArg Nat.succ heq)
          show rbzEntryGet (rsmRowClearExcept pivot rest skipCol) prior
            = rsmClearAgainst pivot (rbzEntryGet rest prior)
          exact rsmRowClearExceptGetOther pivot rest skipCol prior hne'

/-- Reading the target column of a row cleared with `rsmClearRowAtCol` returns the clear of the original
entry. -/
theorem rsmClearRowAtColGetAt :
    ∀ (pivot : List QnfRat) (row : List (List QnfRat)) (targetCol : Nat),
      rbzEntryGet (rsmClearRowAtCol pivot row targetCol) targetCol
        = rsmClearAgainst pivot (rbzEntryGet row targetCol)
  | _pivot, [], _targetCol => rfl
  | _pivot, _entry :: _rest, 0 => rfl
  | pivot, _entry :: rest, targetCol + 1 => by
      show rbzEntryGet (rsmClearRowAtCol pivot rest targetCol) targetCol
        = rsmClearAgainst pivot (rbzEntryGet rest targetCol)
      exact rsmClearRowAtColGetAt pivot rest targetCol

/-- Reading any row of `rsmColumnClearBelow` returns that row with only its pivot-column entry cleared. -/
theorem rsmColumnClearBelowGet :
    ∀ (pivot : List QnfRat) (pivotCol : Nat) (matrix : List (List (List QnfRat))) (position : Nat),
      rbzRowGet (rsmColumnClearBelow pivot pivotCol matrix) position
        = rsmClearRowAtCol pivot (rbzRowGet matrix position) pivotCol
  | _pivot, _pivotCol, [], _position => rfl
  | pivot, pivotCol, _row :: rest, position => by
      cases position with
      | zero => rfl
      | succ prior => exact rsmColumnClearBelowGet pivot pivotCol rest prior

/-- Reading the pivot row of a cross-cleared matrix returns the pivot row cleared with `rsmRowClearExcept`. -/
theorem rsmCrossClearRowGetPivot :
    ∀ (pivot : List QnfRat) (pivotCol : Nat) (matrix : List (List (List QnfRat))) (pivotRow : Nat),
      rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow
        = rsmRowClearExcept pivot (rbzRowGet matrix pivotRow) pivotCol
  | _pivot, _pivotCol, [], _pivotRow => rfl
  | _pivot, _pivotCol, _row :: _rest, 0 => rfl
  | pivot, pivotCol, _row :: rest, pivotRow + 1 => by
      show rbzRowGet (rsmCrossClear pivot pivotCol rest pivotRow) pivotRow
        = rsmRowClearExcept pivot (rbzRowGet rest pivotRow) pivotCol
      exact rsmCrossClearRowGetPivot pivot pivotCol rest pivotRow

/-- Reading any non-pivot row of a cross-cleared matrix returns that row with only its pivot-column entry
cleared. -/
theorem rsmCrossClearRowGetOther :
    ∀ (pivot : List QnfRat) (pivotCol : Nat) (matrix : List (List (List QnfRat))) (pivotRow position : Nat),
      position ≠ pivotRow →
      rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) position
        = rsmClearRowAtCol pivot (rbzRowGet matrix position) pivotCol
  | _pivot, _pivotCol, [], _pivotRow, _position, _hne => rfl
  | pivot, pivotCol, _row :: rest, 0, position, hne => by
      cases position with
      | zero => exact absurd rfl hne
      | succ prior =>
          show rbzRowGet (rsmColumnClearBelow pivot pivotCol rest) prior
            = rsmClearRowAtCol pivot (rbzRowGet rest prior) pivotCol
          exact rsmColumnClearBelowGet pivot pivotCol rest prior
  | pivot, pivotCol, _row :: rest, pivotRow + 1, position, hne => by
      cases position with
      | zero => rfl
      | succ prior =>
          have hne' : prior ≠ pivotRow := fun heq => hne (congrArg Nat.succ heq)
          show rbzRowGet (rsmCrossClear pivot pivotCol rest pivotRow) prior
            = rsmClearRowAtCol pivot (rbzRowGet rest prior) pivotCol
          exact rsmCrossClearRowGetOther pivot pivotCol rest pivotRow prior hne'

/-! ### The cross-clear specification -/

/-- **The pivot is preserved.**  The cross clear leaves the pivot entry `(pivotRow, pivotCol)` untouched. -/
theorem rsmCrossClearPivotPreserved (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) :
    rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow pivotCol
      = rbzMatrixEntry matrix pivotRow pivotCol := by
  show rbzEntryGet (rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow) pivotCol
    = rbzEntryGet (rbzRowGet matrix pivotRow) pivotCol
  rw [rsmCrossClearRowGetPivot, rsmRowClearExceptGetSkip]

/-- **Pivot-row measure.**  Against a nonzero pivot, every off-pivot entry of the pivot row, after the cross
clear, trims to the zero polynomial or has degree strictly below the pivot's — the Euclidean degree drop. -/
theorem rsmCrossClearRowMeasure (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) (pivotNonzero : rpxTrim pivot ≠ [])
    (colPosition : Nat) (hne : colPosition ≠ pivotCol) :
    rpxTrim (rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow colPosition) = []
      ∨ rpxDegree (rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow colPosition)
          < rpxDegree pivot := by
  have hEntry : rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow colPosition
      = rsmClearAgainst pivot (rbzMatrixEntry matrix pivotRow colPosition) := by
    show rbzEntryGet (rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow) colPosition
      = rsmClearAgainst pivot (rbzEntryGet (rbzRowGet matrix pivotRow) colPosition)
    rw [rsmCrossClearRowGetPivot,
      rsmRowClearExceptGetOther pivot (rbzRowGet matrix pivotRow) pivotCol colPosition hne]
  rw [hEntry]
  exact rbzClearEntryReducesDegree pivot (rbzMatrixEntry matrix pivotRow colPosition) pivotNonzero

/-- **Pivot-column measure.**  Against a nonzero pivot, every off-pivot entry of the pivot column, after the
cross clear, trims to the zero polynomial or has degree strictly below the pivot's. -/
theorem rsmCrossClearColMeasure (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) (pivotNonzero : rpxTrim pivot ≠ [])
    (rowPosition : Nat) (hne : rowPosition ≠ pivotRow) :
    rpxTrim (rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition pivotCol) = []
      ∨ rpxDegree (rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition pivotCol)
          < rpxDegree pivot := by
  have hEntry : rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition pivotCol
      = rsmClearAgainst pivot (rbzMatrixEntry matrix rowPosition pivotCol) := by
    show rbzEntryGet (rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition) pivotCol
      = rsmClearAgainst pivot (rbzEntryGet (rbzRowGet matrix rowPosition) pivotCol)
    rw [rsmCrossClearRowGetOther pivot pivotCol matrix pivotRow rowPosition hne, rsmClearRowAtColGetAt]
  rw [hEntry]
  exact rbzClearEntryReducesDegree pivot (rbzMatrixEntry matrix rowPosition pivotCol) pivotNonzero

/-- **Pivot-row reconstruction.**  Each cleared entry of the pivot row differs from the original by a
`pivot`-multiple — elementary-op legitimacy: `quotient·pivot + cleared ≡ original`. -/
theorem rsmCrossClearRowReconstructs (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) (colPosition : Nat) (hne : colPosition ≠ pivotCol) :
    rpxTrim (rpxAdd
        (rpxMul (rpxDivMod (rbzMatrixEntry matrix pivotRow colPosition).length pivot
          (rbzMatrixEntry matrix pivotRow colPosition)).1 pivot)
        (rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow colPosition))
      = rpxTrim (rbzMatrixEntry matrix pivotRow colPosition) := by
  have hEntry : rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow colPosition
      = rsmClearAgainst pivot (rbzMatrixEntry matrix pivotRow colPosition) := by
    show rbzEntryGet (rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) pivotRow) colPosition
      = rsmClearAgainst pivot (rbzEntryGet (rbzRowGet matrix pivotRow) colPosition)
    rw [rsmCrossClearRowGetPivot,
      rsmRowClearExceptGetOther pivot (rbzRowGet matrix pivotRow) pivotCol colPosition hne]
  rw [hEntry]
  exact rbzClearEntryReconstructs (rbzMatrixEntry matrix pivotRow colPosition).length pivot
    (rbzMatrixEntry matrix pivotRow colPosition)

/-- **Pivot-column reconstruction.**  Each cleared entry of the pivot column differs from the original by a
`pivot`-multiple. -/
theorem rsmCrossClearColReconstructs (pivot : List QnfRat) (pivotCol pivotRow : Nat)
    (matrix : List (List (List QnfRat))) (rowPosition : Nat) (hne : rowPosition ≠ pivotRow) :
    rpxTrim (rpxAdd
        (rpxMul (rpxDivMod (rbzMatrixEntry matrix rowPosition pivotCol).length pivot
          (rbzMatrixEntry matrix rowPosition pivotCol)).1 pivot)
        (rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition pivotCol))
      = rpxTrim (rbzMatrixEntry matrix rowPosition pivotCol) := by
  have hEntry : rbzMatrixEntry (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition pivotCol
      = rsmClearAgainst pivot (rbzMatrixEntry matrix rowPosition pivotCol) := by
    show rbzEntryGet (rbzRowGet (rsmCrossClear pivot pivotCol matrix pivotRow) rowPosition) pivotCol
      = rsmClearAgainst pivot (rbzEntryGet (rbzRowGet matrix rowPosition) pivotCol)
    rw [rsmCrossClearRowGetOther pivot pivotCol matrix pivotRow rowPosition hne, rsmClearRowAtColGetAt]
  rw [hEntry]
  exact rbzClearEntryReconstructs (rbzMatrixEntry matrix rowPosition pivotCol).length pivot
    (rbzMatrixEntry matrix rowPosition pivotCol)

/-! ## Groundings (fires)

Closed-value kernel pins.  The search/clear pipeline reduces to canonical `QnfRat` normal forms, so the
pivot position, the cross-clear residues, and the pivot preservation hold by `rfl`, and the general theorems
fire at the difference-of-squares matrix. -/

set_option maxRecDepth 8192

/-- The fire matrix `[[x² − 1, x − 1], [x + 1, 1]]` (magnitudes ≤ 3). -/
def rsmFireMatrix : List (List (List QnfRat)) :=
  [[[qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1], [qnfOfInt (-1), qnfOfInt 1]],
   [[qnfOfInt 1, qnfOfInt 1], [qnfOfInt 1]]]

/-- The all-zero 2×2 fire matrix. -/
def rsmFireZeroMatrix : List (List (List QnfRat)) :=
  [[[], []], [[], []]]

/-- Fire (pivot search): the minimum-degree nonzero entry of `[[x² − 1, x − 1], [x + 1, 1]]` is the constant
`1` at position `(1, 1)`. -/
theorem rsmFirePivotSearchFindsConstant : rsmPivotSearch rsmFireMatrix = some (1, 1) := rfl

/-- Fire (pivot read-back): the found pivot entry `(1, 1)` is the constant `1`. -/
theorem rsmFirePivotEntry : rbzMatrixEntry rsmFireMatrix 1 1 = [qnfOfInt 1] := rfl

/-- Fire (all-zero ⟹ none): the pivot search on the all-zero matrix returns `none`. -/
theorem rsmFirePivotSearchNoneOnZero : rsmPivotSearch rsmFireZeroMatrix = none := rfl

/-- Fire (FALSE control): the all-zero matrix has no pivot, so `isSome` is `false` — the search does not
hallucinate a pivot where every entry vanishes. -/
theorem rsmFirePivotSearchZeroIsSomeFalse : (rsmPivotSearch rsmFireZeroMatrix).isSome = false := rfl

/-- Fire (positive control): the search does find a pivot in a matrix with a nonzero entry. -/
theorem rsmFirePivotSearchNonzeroIsSomeTrue :
    (rsmPivotSearch rsmFireMatrix).isSome = true := rfl

/-- Fire (nonzero spec, instantiated): the found pivot `(1, 1)` is a nonzero entry. -/
theorem rsmFirePivotSearchNonzero : rpxTrim (rbzMatrixEntry rsmFireMatrix 1 1) ≠ [] :=
  rsmPivotSearchNonzero rsmFireMatrix 1 1 rfl

/-- Fire (minimal spec, instantiated): the pivot degree (`0`) bounds the degree of the nonzero corner entry
`x² − 1` (degree `2`) — `0 ≤ 2`, via `rsmPivotSearchMinimal`. -/
theorem rsmFirePivotSearchMinimalAtCorner :
    rpxDegree (rbzMatrixEntry rsmFireMatrix 1 1) ≤ rpxDegree (rbzMatrixEntry rsmFireMatrix 0 0) :=
  rsmPivotSearchMinimal rsmFireMatrix 1 1 rfl 0 0 (by
    show rpxTrim (rbzMatrixEntry rsmFireMatrix 0 0) ≠ []
    exact List.cons_ne_nil (qnfOfInt (-1)) [qnfOfInt 0, qnfOfInt 1])

/-- Fire (none-all-zero spec, instantiated): the all-zero matrix reads the zero polynomial at `(0, 0)`. -/
theorem rsmFirePivotSearchNoneAllZeroAt :
    rpxTrim (rbzMatrixEntry rsmFireZeroMatrix 0 0) = [] :=
  rsmPivotSearchNoneAllZero rsmFireZeroMatrix rfl 0 0

/-- Fire (cross clear, pivot row): clearing the cross about the pivot `1` at `(1, 1)` annihilates the
pivot-row entry `(1, 0)` (`x + 1` mod `1 = 0`). -/
theorem rsmFireCrossClearRowAnnihilates :
    rpxTrim (rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 1 0) = [] := rfl

/-- Fire (cross clear, pivot column): clearing the cross about the pivot `1` at `(1, 1)` annihilates the
pivot-column entry `(0, 1)` (`x − 1` mod `1 = 0`). -/
theorem rsmFireCrossClearColAnnihilates :
    rpxTrim (rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 0 1) = [] := rfl

/-- Fire (cross clear, pivot preserved): the pivot `(1, 1)` survives the cross clear unchanged. -/
theorem rsmFireCrossClearPivotPreserved :
    rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 1 1 = [qnfOfInt 1] := rfl

/-- Fire (cross clear, off-cross untouched): the off-cross entry `(0, 0) = x² − 1` is left untouched by the
cross clear. -/
theorem rsmFireCrossClearOffCrossUntouched :
    rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 0 0
      = [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] := rfl

/-- Fire (cross-clear column measure, instantiated): the cross clear about the pivot `1` drives the
pivot-column entry `(0, 1)` to a residue that trims to `[]` or drops below the pivot degree. -/
theorem rsmFireCrossClearColMeasure :
    rpxTrim (rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 0 1) = []
      ∨ rpxDegree (rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 0 1)
          < rpxDegree [qnfOfInt 1] :=
  rsmCrossClearColMeasure [qnfOfInt 1] 1 1 rsmFireMatrix
    (by show rpxTrim [qnfOfInt 1] ≠ []; exact List.cons_ne_nil (qnfOfInt 1) [])
    0 (fun h => Nat.noConfusion h)

/-- Fire (degree-drop cross clear, magnitudes ≤ 3): clearing `[[x² + 1, x − 1], [x + 1, x − 1]]` about the
pivot `x − 1` at `(0, 1)` drops the pivot-row corner `(0, 0) = x² + 1` to the constant `2` (degree `0 < 1`),
a genuine degree drop rather than annihilation. -/
theorem rsmFireCrossClearDegreeDrops :
    rpxTrim (rbzMatrixEntry (rsmCrossClear [qnfOfInt (-1), qnfOfInt 1] 1
        [[[qnfOfInt 1, qnfOfInt 0, qnfOfInt 1], [qnfOfInt (-1), qnfOfInt 1]],
         [[qnfOfInt 1, qnfOfInt 1], [qnfOfInt (-1), qnfOfInt 1]]] 0) 0 0) = [qnfOfInt 2] := rfl

/-- Fire (cross-clear reconstruction, instantiated): the cleared pivot-column entry `(0, 1)` reconstructs
`x − 1` as `quotient·1 + cleared`. -/
theorem rsmFireCrossClearReconstructs :
    rpxTrim (rpxAdd
        (rpxMul (rpxDivMod (rbzMatrixEntry rsmFireMatrix 0 1).length [qnfOfInt 1]
          (rbzMatrixEntry rsmFireMatrix 0 1)).1 [qnfOfInt 1])
        (rbzMatrixEntry (rsmCrossClear [qnfOfInt 1] 1 rsmFireMatrix 1) 0 1))
      = rpxTrim (rbzMatrixEntry rsmFireMatrix 0 1) :=
  rsmCrossClearColReconstructs [qnfOfInt 1] 1 1 rsmFireMatrix 0 (fun h => Nat.noConfusion h)

/-! ## Content marker -/

/-- The ℚ[x] Smith pivot search and cross clear are decided. `rsmPivotSearch` is a total minimum-degree
nonzero-entry search with full soundness (`rsmPivotSearchNonzero`/`rsmPivotSearchMinimal`/
`rsmPivotSearchNoneAllZero`). `rsmCrossClear` clears the pivot's row and column against the pivot, preserving
the pivot (`rsmCrossClearPivotPreserved`), with the elementary-op reconstruction on both arms
(`rsmCrossClearRowReconstructs`/`rsmCrossClearColReconstructs`) and the degree-drop measure on both arms
(`rsmCrossClearRowMeasure`/`rsmCrossClearColMeasure`, from `rbzClearEntryReducesDegree`). The reduced cross
fixed point, the all-zero cross, and the full Smith normal form are supplied or walled downstream
(`rsfHasReducedCrossFixedPoint`, `rseHasAllZeroCrossViaRepivot`, `rsiHasSmithNormalForm`). -/
def rsmHasPivotSearch : Bool := true

end FX1Poly.ComputerAlgebra
