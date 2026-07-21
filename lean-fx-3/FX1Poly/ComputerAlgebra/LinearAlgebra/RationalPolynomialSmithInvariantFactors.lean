import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # RationalPolynomialSmithInvariantFactors — the ℚ[x] Smith submatrix descent and invariant-factor chain

Building on the re-pivot driver of `RationalPolynomialSmithDriver`
(`rseRepivotDriverReachesAllZeroCross`: from a nonzero pivot the driver reaches an all-zero cross about its
final pivot position), this module builds the submatrix descent. `rsiDiagonalize` is a total fuel-structural
driver: at each stage it finds a minimum-degree nonzero pivot (`rsmPivotSearch`), runs the re-pivot driver to
an all-zero cross (`rsiStage`), records the final pivot entry as the next diagonal entry, and recurses on the
`(r-1)×(c-1)` submatrix (`rsfSubmatrix`). It ships the per-stage all-zero-cross correctness
(`rsiStageAllZeroCross`, `rsiDiagonalizeHeadAllZeroCross`) and the abstract invariant-factor chain assembly
(`rsiHeadDividesAllOfConsecutive`: a consecutively-divisible diagonal closes to "the head divides every
entry", via `rbzDividesTrans` and `rpeDividesRefl`). It also constructs the `xI − A` characteristic matrix
(`rsiCharMatrix`).

`rsmCrossClear` reduces each off-pivot cross entry modulo the pivot independently rather than performing a
full row/column elementary operation, so the descent leaves the trailing submatrix untouched and does not
preserve the determinant ideal. Hence the produced diagonal is the all-zero-cross descent diagonal, not the
true Smith normal form: on `[[x², x²+x], [x²+x, x²]]` (determinant degree 3) it yields two degree-1 factors,
whereas the true invariant factors have degrees `[1, 2]`. The true Smith normal form and the rational
canonical form corollary remain walled (`rsiHasSmithNormalForm`).

Every definition is structural on the `Nat` fuel or list; case analyses are full-constructor Option/Prod/List
splits. No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or
`WellFounded.fix`. Per-declaration audit twin in the matching `FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Descent driver -/

/-- One descent stage: run the re-pivot driver at fuel `rsePivotDegree` about the pivot position, reaching a
matrix with an all-zero cross about its final pivot position `(finalMatrix, finalRow, finalCol)`. -/
def rsiStage (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) :
    List (List (List QnfRat)) × Nat × Nat :=
  rseRepivotDriver (rsePivotDegree matrix pivotRow pivotCol) matrix pivotRow pivotCol

/-- The submatrix descent driver, structural on `Nat` fuel. At each stage: find a minimum-degree nonzero
pivot (`rsmPivotSearch`); `none` ends the diagonal; on `some`, run the re-pivot driver to an all-zero cross
(`rsiStage`), record the final pivot entry, and recurse on the `(r-1)×(c-1)` submatrix (`rsfSubmatrix`). -/
def rsiDiagonalize : Nat → List (List (List QnfRat)) → List (List QnfRat)
  | 0, _matrix => []
  | fuel + 1, matrix =>
      match rsmPivotSearch matrix with
      | none => []
      | some pivotPosition =>
          let driven := rsiStage matrix pivotPosition.1 pivotPosition.2
          rbzMatrixEntry driven.1 driven.2.1 driven.2.2
            :: rsiDiagonalize fuel (rsfSubmatrix driven.1 driven.2.1 driven.2.2)

/-- The descent at a successor fuel with an all-zero matrix returns the empty diagonal. -/
theorem rsiDiagonalizeSuccNone (fuel : Nat) (matrix : List (List (List QnfRat)))
    (hNone : rsmPivotSearch matrix = none) : rsiDiagonalize (fuel + 1) matrix = [] := by
  dsimp only [rsiDiagonalize]; rw [hNone]

/-- The descent at a successor fuel with a pivot prepends the stage's final pivot entry, then recurses. -/
theorem rsiDiagonalizeSuccSome (fuel : Nat) (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat) (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    rsiDiagonalize (fuel + 1) matrix
      = rbzMatrixEntry (rsiStage matrix pivotRow pivotCol).1 (rsiStage matrix pivotRow pivotCol).2.1
          (rsiStage matrix pivotRow pivotCol).2.2
        :: rsiDiagonalize fuel (rsfSubmatrix (rsiStage matrix pivotRow pivotCol).1
            (rsiStage matrix pivotRow pivotCol).2.1 (rsiStage matrix pivotRow pivotCol).2.2) := by
  dsimp only [rsiDiagonalize]; rw [hPivot]

/-! ## Per-stage all-zero-cross correctness -/

/-- Each stage reaches an all-zero cross: from a found (nonzero) pivot the stage's re-pivot driver reaches a
matrix whose cross about the final pivot position is entirely zero, via `rseRepivotDriverReachesAllZeroCross`
at fuel `rsePivotDegree`. -/
theorem rsiStageAllZeroCross (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat)
    (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    rseCrossIsAllZero (rsiStage matrix pivotRow pivotCol).1 (rsiStage matrix pivotRow pivotCol).2.1
      (rsiStage matrix pivotRow pivotCol).2.2 := by
  dsimp only [rsiStage]
  exact rseRepivotDriverReachesAllZeroCross (rsePivotDegree matrix pivotRow pivotCol) matrix
    pivotRow pivotCol (rsmPivotSearchNonzero matrix pivotRow pivotCol hPivot) (Nat.le_refl _)

/-- The produced diagonal's head is an all-zero-cross pivot entry: for a nonzero matrix the descent output is
`finalPivotEntry :: restDiagonal` with `finalPivotEntry` read at a position whose cross is entirely zero. -/
theorem rsiDiagonalizeHeadAllZeroCross (fuel : Nat) (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat) (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    ∃ (finalMatrix : List (List (List QnfRat))) (finalRow finalCol : Nat)
      (restDiagonal : List (List QnfRat)),
      rsiDiagonalize (fuel + 1) matrix = rbzMatrixEntry finalMatrix finalRow finalCol :: restDiagonal
        ∧ rseCrossIsAllZero finalMatrix finalRow finalCol :=
  ⟨(rsiStage matrix pivotRow pivotCol).1, (rsiStage matrix pivotRow pivotCol).2.1,
   (rsiStage matrix pivotRow pivotCol).2.2,
   rsiDiagonalize fuel (rsfSubmatrix (rsiStage matrix pivotRow pivotCol).1
      (rsiStage matrix pivotRow pivotCol).2.1 (rsiStage matrix pivotRow pivotCol).2.2),
   rsiDiagonalizeSuccSome fuel matrix pivotRow pivotCol hPivot,
   rsiStageAllZeroCross matrix pivotRow pivotCol hPivot⟩

/-! ## Invariant-factor chain assembly -/

/-- Consecutive divisibility: each entry divides the next (`d₁ | d₂ | ⋯`), the invariant-factor chain shape. -/
def rsiConsecutiveDivides : List (List QnfRat) → Prop
  | [] => True
  | [_single] => True
  | first :: second :: rest => rpeDivides first second ∧ rsiConsecutiveDivides (second :: rest)

/-- An anchor divides every entry of a list. -/
def rsiHeadDividesAll (anchor : List QnfRat) : List (List QnfRat) → Prop
  | [] => True
  | entry :: rest => rpeDivides anchor entry ∧ rsiHeadDividesAll anchor rest

/-- The chain assembly: if `anchor` divides the list's head and the list is consecutively divisible, then
`anchor` divides every entry — transitive closure via `rbzDividesTrans`, structural on the three-case list
split matching `rsiConsecutiveDivides`. -/
theorem rsiAnchorDividesAllOfConsecutive :
    ∀ (anchor : List QnfRat) (diagonal : List (List QnfRat)),
      (∀ firstEntry restEntries, diagonal = firstEntry :: restEntries → rpeDivides anchor firstEntry) →
      rsiConsecutiveDivides diagonal →
      rsiHeadDividesAll anchor diagonal
  | _anchor, [], _headDivides, _chain => True.intro
  | anchor, [single], headDivides, _chain => ⟨headDivides single [] rfl, True.intro⟩
  | anchor, first :: second :: rest, headDivides, chain => by
      refine ⟨headDivides first (second :: rest) rfl, ?_⟩
      have anchorDivFirst : rpeDivides anchor first := headDivides first (second :: rest) rfl
      have firstDivSecond : rpeDivides first second := chain.1
      have anchorDivSecond : rpeDivides anchor second :=
        rbzDividesTrans anchor first second anchorDivFirst firstDivSecond
      exact rsiAnchorDividesAllOfConsecutive anchor (second :: rest)
        (fun firstEntry _restEntries heq => by
          injection heq with headEq _tailEq; rw [← headEq]; exact anchorDivSecond)
        chain.2

/-- The head of a consecutively-divisible diagonal divides every entry (`d₁ | dⱼ` for all `j`), assembled from
the consecutive chain by `rsiAnchorDividesAllOfConsecutive` with the head dividing itself (`rpeDividesRefl`). -/
theorem rsiHeadDividesAllOfConsecutive (headEntry : List QnfRat) (restEntries : List (List QnfRat))
    (chain : rsiConsecutiveDivides (headEntry :: restEntries)) :
    rsiHeadDividesAll headEntry (headEntry :: restEntries) :=
  rsiAnchorDividesAllOfConsecutive headEntry (headEntry :: restEntries)
    (fun firstEntry _restEntries heq => by
      injection heq with headEq _tailEq; rw [headEq]; exact rpeDividesRefl firstEntry)
    chain

/-! ## The `xI − A` characteristic matrix -/

/-- A characteristic-matrix cell `x·δ − a`: on the diagonal it is `x − a`, off the diagonal `−a`. -/
def rsiCharCell (rowIndex colIndex : Nat) (coeff : QnfRat) : List QnfRat :=
  match Nat.decEq rowIndex colIndex with
  | isTrue _ => rpxSub [qnfOfInt 0, qnfOfInt 1] [coeff]
  | isFalse _ => rpxSub [] [coeff]

/-- Build one characteristic-matrix row from a base-matrix row, tracking the column index. -/
def rsiCharRowBuild (rowIndex : Nat) : Nat → List QnfRat → List (List QnfRat)
  | _colIndex, [] => []
  | colIndex, coeff :: rest =>
      rsiCharCell rowIndex colIndex coeff :: rsiCharRowBuild rowIndex (colIndex + 1) rest

/-- Build the characteristic matrix from a base matrix, tracking the row index. -/
def rsiCharMatrixBuild : Nat → List (List QnfRat) → List (List (List QnfRat))
  | _rowIndex, [] => []
  | rowIndex, row :: rest =>
      rsiCharRowBuild rowIndex 0 row :: rsiCharMatrixBuild (rowIndex + 1) rest

/-- The `xI − A` characteristic matrix: from a rational base matrix `A`, the polynomial matrix whose `(i, j)`
entry is `x·δᵢⱼ − aᵢⱼ`, whose Smith invariant factors classify `A` up to similarity (that classification is
walled — see `rsiHasSmithNormalForm`). -/
def rsiCharMatrix (baseMatrix : List (List QnfRat)) : List (List (List QnfRat)) :=
  rsiCharMatrixBuild 0 baseMatrix

/-! ## Groundings (fires) -/

set_option maxRecDepth 16384

/-- The already-Smith fire matrix `diag(x − 1, (x − 1)(x − 2))`. -/
def rsiFireDiagMatrix : List (List (List QnfRat)) :=
  [[[qnfOfInt (-1), qnfOfInt 1], []],
   [[], [qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]]]

/-- Fire: the descent on the already-Smith `diag(x − 1, (x − 1)(x − 2))` returns the diagonal unchanged. -/
theorem rsiFireDiagAlreadySmith :
    rsiDiagonalize 2 rsiFireDiagMatrix
      = [[qnfOfInt (-1), qnfOfInt 1], [qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]] := rfl

/-- Fire (genuine descent, length): the non-diagonal matrix `[[x², x² + x], [x² + x, x²]]` descends to a
two-entry diagonal. -/
theorem rsiFireDescentLength : (rsiDiagonalize 2 rseFireMatrix).length = 2 := rfl

/-- Fire (genuine descent, degrees): both produced diagonal entries have degree `1`, witnessing that this is
the all-zero-cross descent diagonal, not the true Smith form (whose factors have degrees `[1, 2]`; see the
`rsiHasSmithNormalForm` wall). -/
theorem rsiFireDescentDegrees : (rsiDiagonalize 2 rseFireMatrix).map rpxDegree = [1, 1] := rfl

/-- Fire (false control): the descent diagonal of the fire matrix is not the single-entry list `[x]`. -/
theorem rsiFireWrongDiagonalRefuted :
    rsiDiagonalize 2 rseFireMatrix ≠ [[qnfOfInt 0, qnfOfInt 1]] := by
  intro hEq
  nomatch congrArg List.tail hEq

/-- Fire: stage 0 of the fire matrix reaches an all-zero cross about its final pivot position. -/
theorem rsiFireStageAllZeroCross :
    rseCrossIsAllZero (rsiStage rseFireMatrix 0 0).1 (rsiStage rseFireMatrix 0 0).2.1
      (rsiStage rseFireMatrix 0 0).2.2 :=
  rsiStageAllZeroCross rseFireMatrix 0 0 rfl

/-- Fire: the already-Smith diagonal is consecutively divisible (`x − 1 | (x − 1)(x − 2)`). -/
theorem rsiFireDiagConsecutiveDivides :
    rsiConsecutiveDivides (rsiDiagonalize 2 rsiFireDiagMatrix) := by
  rw [rsiFireDiagAlreadySmith]
  exact ⟨⟨[qnfOfInt (-2), qnfOfInt 1], rfl⟩, True.intro⟩

/-- Fire: from the consecutive chain the head `x − 1` divides every diagonal entry. -/
theorem rsiFireDiagHeadDividesAll :
    rsiHeadDividesAll [qnfOfInt (-1), qnfOfInt 1]
      ([qnfOfInt (-1), qnfOfInt 1] :: [[qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]]) :=
  rsiHeadDividesAllOfConsecutive [qnfOfInt (-1), qnfOfInt 1] [[qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]]
    (by
      have hDiag : rsiDiagonalize 2 rsiFireDiagMatrix
          = [qnfOfInt (-1), qnfOfInt 1] :: [[qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]] := rfl
      rw [← hDiag]; exact rsiFireDiagConsecutiveDivides)

/-- Fire: `xI − A` for the companion matrix `[[0,1],[1,0]]` of `x² − 1` is `[[x, −1], [−1, x]]`. -/
theorem rsiFireCharMatrix :
    rsiCharMatrix [[qnfOfInt 0, qnfOfInt 1], [qnfOfInt 1, qnfOfInt 0]]
      = [[[qnfOfInt 0, qnfOfInt 1], [qnfOfInt (-1)]], [[qnfOfInt (-1)], [qnfOfInt 0, qnfOfInt 1]]] := rfl

/-! ## Content markers -/

/-- The ℚ[x] Smith submatrix descent is decided: `rsiDiagonalize`, a total fuel-structural driver running
pivot-search → re-pivot driver to an all-zero cross (`rsiStage`, `rsiStageAllZeroCross`,
`rsiDiagonalizeHeadAllZeroCross`) → submatrix extraction → recurse. The abstract invariant-factor chain
assembly is also decided: a consecutively-divisible diagonal closes to "the head divides every entry"
(`rsiHeadDividesAllOfConsecutive`, on `rbzDividesTrans`/`rpeDividesRefl`), fired on the already-Smith diagonal
`diag(x−1, (x−1)(x−2))`. The consecutive-divisibility facts are hypotheses; deriving them from the algorithm
requires the walled true Smith form. -/
def rsiHasDescentDriver : Bool := true

/-- The true Smith normal form over ℚ[x] — the diagonal whose invariant factors satisfy `d₁ | d₂ | ⋯` — and
the rational canonical form corollary remain walled. `rsmCrossClear` reduces each off-pivot cross entry modulo
the pivot independently rather than by a full row/column elementary operation, so `rsiDiagonalize` reaches an
all-zero cross about each pivot but leaves the trailing submatrix untouched and does not preserve the
determinant ideal (witness `rsiFireDescentDegrees`: `[[x²,x²+x],[x²+x,x²]]` descends to two degree-1 factors,
not the true `[1,2]`). Closing it needs the full row/column elementary operation plus the
pivot-divides-submatrix second descent, after which `rpeGcdDividesBoth` composed with
`rsiHeadDividesAllOfConsecutive` delivers the chain. The `xI − A` constructor `rsiCharMatrix` ships and fires,
but the similarity classification behind the rational canonical form also rests on this walled Smith form. -/
def rsiHasSmithNormalForm : Bool := false

end FX1Poly.ComputerAlgebra
