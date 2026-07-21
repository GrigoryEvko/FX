import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismSimilarity

/-! # EndomorphismMinorSelector — the general k×k minor selector

The `2×2` rank separator (`endomorphismRank2`) reaches only `2×2`, because the shipped determinant
(`intCofactorDet`) reads the leading `size × size` block: it can delete row `0` but cannot select an
arbitrary `k × k` sub-block.  Rank is `max { k : some k×k minor ≠ 0 }`, a similarity invariant, so a
general minor selector closes rank certification at `n ≥ 3`.  Because `SetoidMatrix` carries a total
`entry : Nat → Nat → carrier`, the selector is a reindexing: `selectSubmatrix` reads through
function-valued row/column index functions (keeping the substrate propext-free — `List.getD` pulls
`propext`), `intMinorDet` takes the determinant of the selected block, and `endomorphismRank3`
classifies rank at dimension `3` by the nine `2×2` minors.

The scope is per-input; no general rank decision is claimed, and the complete similarity separator
(invariant-factor Smith over ℚ[x]) is still open.

Raw Lean 4 + Init; every declaration axiom-free (per-declaration gated in the audit twin). -/

namespace FX1Poly.ComputerAlgebra

/-! ## The general minor selector (function-valued index selection) -/

/-- The submatrix reading through row/column index functions: entry `(i, j)` is the original entry at
`(rowSelect i, colSelect j)`.  Function-valued so the substrate stays propext-free; the shape is the
caller's declared `selectedRowCount × selectedColCount`. -/
def selectSubmatrix (matrix : SetoidMatrix Int) (selectedRowCount selectedColCount : Nat)
    (rowSelect colSelect : Nat → Nat) : SetoidMatrix Int :=
  { rowCount := selectedRowCount
    colCount := selectedColCount
    entry := fun rowIndex colIndex => matrix.entry (rowSelect rowIndex) (colSelect colIndex) }

/-- The `k × k` minor determinant: pick `k` rows and `k` columns (via the selection functions), take
the determinant of the selected square sub-block. -/
def intMinorDet (matrix : SetoidMatrix Int) (minorSize : Nat)
    (rowSelect colSelect : Nat → Nat) : Int :=
  intCofactorDet minorSize (selectSubmatrix matrix minorSize minorSize rowSelect colSelect)

/-! ## The three `2`-index selections of `{0, 1, 2}` (function-valued) -/

/-- Select the pair `{0, 1}` — the leading two indices. -/
def selectPairLow : Nat → Nat := fun index => index

/-- Select the pair `{0, 2}` — skip the middle index. -/
def selectPairOuter : Nat → Nat
  | 0 => 0
  | _ => 2

/-- Select the pair `{1, 2}` — the trailing two indices. -/
def selectPairHigh : Nat → Nat
  | 0 => 1
  | _ => 2

/-- Grounding: the top-left `2×2` minor of a rank-`2` `3×3` matrix has determinant `1 ≠ 0` — a
rank-`≥ 2` witness the shipped `2×2` determinant could not reach on a `3×3` carrier. -/
theorem intMinorDetTopLeftTwoOfThreeExample :
    intMinorDet (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 0]]) 2 selectPairLow selectPairLow
      = 1 := rfl

/-- Grounding: the outer `2×2` minor (rows `{0,2}`, cols `{0,2}`) of the same matrix is `0` — the
bottom-right strand carries no rank. -/
theorem intMinorDetOuterTwoOfThreeExample :
    intMinorDet (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 0]]) 2 selectPairOuter selectPairOuter
      = 0 := rfl

/-! ## Rank at dimension 3 via the general minors -/

/-- The rank of a `3×3` integer matrix (a similarity invariant) via the general minors: `3` when the
full determinant is nonzero, else `2` when some `2×2` minor is nonzero, else `1` when some entry is
nonzero, else `0`.  The nine `2×2` minors range over the row/column pairs `{0,1} {0,2} {1,2}`.
Written in the `if (Prop)` idiom (decidable `Int` equalities, no `List` ops) so it stays propext-free. -/
def endomorphismRank3 (matrix : SetoidMatrix Int) : Nat :=
  if intCofactorDet 3 matrix = 0 then
    (if intMinorDet matrix 2 selectPairLow selectPairLow = 0
          ∧ intMinorDet matrix 2 selectPairLow selectPairOuter = 0
          ∧ intMinorDet matrix 2 selectPairLow selectPairHigh = 0
          ∧ intMinorDet matrix 2 selectPairOuter selectPairLow = 0
          ∧ intMinorDet matrix 2 selectPairOuter selectPairOuter = 0
          ∧ intMinorDet matrix 2 selectPairOuter selectPairHigh = 0
          ∧ intMinorDet matrix 2 selectPairHigh selectPairLow = 0
          ∧ intMinorDet matrix 2 selectPairHigh selectPairOuter = 0
          ∧ intMinorDet matrix 2 selectPairHigh selectPairHigh = 0 then
      (if matrix.entry 0 0 = 0 ∧ matrix.entry 0 1 = 0 ∧ matrix.entry 0 2 = 0
            ∧ matrix.entry 1 0 = 0 ∧ matrix.entry 1 1 = 0 ∧ matrix.entry 1 2 = 0
            ∧ matrix.entry 2 0 = 0 ∧ matrix.entry 2 1 = 0 ∧ matrix.entry 2 2 = 0
        then 0 else 1)
     else 2)
  else 3

/-- `source` and `target` are dissimilar because their dimension-`3` ranks differ. -/
@[reducible] def EndomorphismDissimilarByRank3 (source target : SetoidMatrix Int) : Prop :=
  endomorphismRank3 source ≠ endomorphismRank3 target

/-! ## Groundings -/

/-- Rank `0`: the zero `3×3`. -/
theorem endomorphismRank3ZeroExample :
    endomorphismRank3 (setoidMatrixOfRows [[0, 0, 0], [0, 0, 0], [0, 0, 0]]) = 0 := rfl

/-- Rank `1`: a single nonzero strand (`det = 0`, all `2×2` minors `0`, one entry nonzero). -/
theorem endomorphismRank3OneExample :
    endomorphismRank3 (setoidMatrixOfRows [[1, 0, 0], [0, 0, 0], [0, 0, 0]]) = 1 := rfl

/-- Rank `2` on a `3×3`: `det = 0` but the top-left `2×2` minor is `1 ≠ 0` — the value the `2×2`
engine could not compute, now reached by the general minor selector. -/
theorem endomorphismRank3TwoExample :
    endomorphismRank3 (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 0]]) = 2 := rfl

/-- Rank `3`: the `3×3` identity (`det = 1 ≠ 0`). -/
theorem endomorphismRank3ThreeExample :
    endomorphismRank3 (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 1]]) = 3 := rfl

/-- A dimension-`3` dissimilarity certificate: a rank-`2` `3×3` and a rank-`1` `3×3` are dissimilar,
decided by the general-minor rank (both have all-zero trace and determinant, so lower separators are
blind — only the `2×2` minors tell them apart).  `2 ≠ 1` by `Nat.noConfusion`. -/
theorem endomorphismRank3SeparatesRankTwoFromRankOne :
    EndomorphismDissimilarByRank3
      (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 0]])
      (setoidMatrixOfRows [[1, 0, 0], [0, 0, 0], [0, 0, 0]]) :=
  fun rankEquation => Nat.noConfusion rankEquation (fun oneEqZero => Nat.noConfusion oneEqZero)

end FX1Poly.ComputerAlgebra
