import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithInvariantFactors — the ℚ[x] Smith
submatrix descent and the invariant-factor chain assembly

The committed re-pivot driver (`RationalPolynomialSmithDriver`) ships
`rseRepivotDriverReachesAllZeroCross`: from a nonzero pivot, the driver reaches a matrix whose CROSS about
its final pivot position is entirely zero (the off-pivot pivot-row and pivot-column entries all trim to the
zero polynomial).  This module builds the SUBMATRIX DESCENT on top of that terminal: a total, fuel-structural
driver `rsiDiagonalize` that runs pivot-search → re-pivot driver (all-zero cross) → `rsfSubmatrix` (drop the
pivot's row and column) → recurse, accumulating one diagonal entry per stage.  It ships the per-stage
all-zero-cross correctness (transporting the rung-8 terminal through the recursion onto the produced list),
and the abstract invariant-factor CHAIN ASSEMBLY (consecutive divisibility ⟹ head divides all, via the
committed `rbzDividesTrans` and `rpeDividesRefl`).

## The honest scope — what is DECIDED and what is WALLED

`rsmCrossClear` (the cross clear the driver iterates) reduces each off-pivot cross entry modulo the pivot
INDEPENDENTLY — it replaces the entry at `(pivotRow, col)` (resp. `(row, pivotCol)`) by its Euclidean residue
against the pivot, touching NOTHING else.  This is NOT a full row/column ELEMENTARY OPERATION (which would
subtract `quotient · (whole pivot row)` from another row, modifying the trailing submatrix too).  Consequently
`rsiDiagonalize` reaches an all-zero CROSS about each stage's pivot, but it does NOT touch the trailing
submatrix and does NOT preserve the determinant ideal.  Concretely, on the genuine-re-pivot fire matrix
`[[x², x² + x], [x² + x, x²]]` (determinant `−2x³ − x²`, degree 3) the descent produces TWO degree-`1` factors
(product degree 2 ≠ 3) — so the produced diagonal is the all-zero-cross descent diagonal, NOT the true Smith
normal form, whose invariant factors have degrees `[1, 2]`.

Hence:
  * DECIDED — the DESCENT SKELETON (`rsiDiagonalize`, `rsiHasDescentDriver`) and its PER-STAGE all-zero cross
    (`rsiStageAllZeroCross`, `rsiDiagonalizeHeadAllZeroCross`, `rsiHasAllZeroCrossPerStage`);
  * DECIDED — the abstract invariant-factor CHAIN ASSEMBLY (`rsiHeadDividesAllOfConsecutive`,
    `rsiHasChainAssembly`): a list of consecutive `rpeDivides` facts closes to "the head divides every
    entry", the transitive-closure content the invariant-factor poset needs, built on `rbzDividesTrans`;
  * WALLED — the true SMITH NORMAL FORM (`rsiHasSmithNormalForm := false`): reaching it needs the FULL
    row/column elementary operation (subtract `quotient · pivot row` from another row, touching the
    submatrix) plus the pivot-divides-every-submatrix-entry second descent, neither built here; the produced
    diagonal satisfies the invariant-factor chain only when the pivot already divides its trailing submatrix
    (e.g. already-diagonal inputs — fired);
  * WALLED — the RATIONAL CANONICAL FORM corollary (`rsiHasRationalCanonicalForm := false`): the `xI − A`
    characteristic-matrix constructor (`rsiCharMatrix`) ships and fires, but classifying similarity by the
    invariant factors of its Smith form needs the walled true Smith form plus the similarity theorem.

## Zero-axiom design

Every definition is structural on the `Nat` fuel or the list; every specification routes through the
committed driver/pivot-search/divisibility lemmas and the calibrated-clean `Nat` order lemmas.  Case analyses
are `Option`/`Prod`/`List` full-constructor splits (no wildcard arms over enumerable scrutinees).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithInvariantFactors.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## T1 — the submatrix descent driver -/

/-- **One descent stage.**  Run the re-pivot driver at fuel `= rsePivotDegree` (the pivot's degree) about the
pivot position, reaching a matrix with an all-zero cross about its final pivot position (returned as
`(finalMatrix, finalRow, finalCol)`). -/
def rsiStage (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat) :
    List (List (List QnfRat)) × Nat × Nat :=
  rseRepivotDriver (rsePivotDegree matrix pivotRow pivotCol) matrix pivotRow pivotCol

/-- **The submatrix descent driver.**  Structural on `Nat` fuel (= the matrix dimension).  At each stage:
find a minimum-degree nonzero pivot (`rsmPivotSearch`); `none` (all-zero matrix) ends the diagonal; on `some`,
run the re-pivot driver to an all-zero cross (`rsiStage`), record the final pivot entry as the next diagonal
entry, and recurse on the `(r-1)×(c-1)` submatrix (`rsfSubmatrix`) about that final pivot. -/
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

/-- The descent at a successor fuel with pivot `(pivotRow, pivotCol)` prepends the stage's final pivot entry
and recurses on the submatrix. -/
theorem rsiDiagonalizeSuccSome (fuel : Nat) (matrix : List (List (List QnfRat)))
    (pivotRow pivotCol : Nat) (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    rsiDiagonalize (fuel + 1) matrix
      = rbzMatrixEntry (rsiStage matrix pivotRow pivotCol).1 (rsiStage matrix pivotRow pivotCol).2.1
          (rsiStage matrix pivotRow pivotCol).2.2
        :: rsiDiagonalize fuel (rsfSubmatrix (rsiStage matrix pivotRow pivotCol).1
            (rsiStage matrix pivotRow pivotCol).2.1 (rsiStage matrix pivotRow pivotCol).2.2) := by
  dsimp only [rsiDiagonalize]; rw [hPivot]

/-! ## T2 — per-stage all-zero-cross correctness -/

/-- **Each stage reaches an all-zero cross.**  From a found pivot (nonzero, `rsmPivotSearchNonzero`), the
stage's re-pivot driver at fuel `= rsePivotDegree` reaches a matrix whose cross about the final pivot position
is entirely zero — the rung-8 terminal `rseRepivotDriverReachesAllZeroCross` at the exact-degree fuel. -/
theorem rsiStageAllZeroCross (matrix : List (List (List QnfRat))) (pivotRow pivotCol : Nat)
    (hPivot : rsmPivotSearch matrix = some (pivotRow, pivotCol)) :
    rseCrossIsAllZero (rsiStage matrix pivotRow pivotCol).1 (rsiStage matrix pivotRow pivotCol).2.1
      (rsiStage matrix pivotRow pivotCol).2.2 := by
  dsimp only [rsiStage]
  exact rseRepivotDriverReachesAllZeroCross (rsePivotDegree matrix pivotRow pivotCol) matrix
    pivotRow pivotCol (rsmPivotSearchNonzero matrix pivotRow pivotCol hPivot) (Nat.le_refl _)

/-- **The produced diagonal's head is an all-zero-cross pivot entry.**  Ties the rung-8 terminal to the actual
output list: for a nonzero matrix the descent output is `finalPivotEntry :: restDiagonal`, where
`finalPivotEntry` is read at a position whose cross is entirely zero.  The diagonal-correctness content
transported through the recursion. -/
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

/-! ## T3 — the invariant-factor chain assembly -/

/-- **Consecutive divisibility.**  Each entry divides the next: `d₁ | d₂`, `d₂ | d₃`, … — the invariant-factor
chain shape. -/
def rsiConsecutiveDivides : List (List QnfRat) → Prop
  | [] => True
  | [_single] => True
  | first :: second :: rest => rpeDivides first second ∧ rsiConsecutiveDivides (second :: rest)

/-- **An anchor divides every entry of a list.** -/
def rsiHeadDividesAll (anchor : List QnfRat) : List (List QnfRat) → Prop
  | [] => True
  | entry :: rest => rpeDivides anchor entry ∧ rsiHeadDividesAll anchor rest

/-- **The chain assembly.**  If `anchor` divides the list's head and the list is consecutively divisible, then
`anchor` divides EVERY entry — transitive closure of the invariant-factor chain, threaded through
`rbzDividesTrans`.  Structural on the three-case list split matching `rsiConsecutiveDivides`. -/
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

/-- **The head of a consecutively-divisible diagonal divides every entry.**  The invariant-factor conclusion
`d₁ | dⱼ` for all `j`, assembled from the consecutive chain `d₁ | d₂ | ⋯` by `rsiAnchorDividesAllOfConsecutive`
(the anchor is the head, dividing itself by `rpeDividesRefl`). -/
theorem rsiHeadDividesAllOfConsecutive (headEntry : List QnfRat) (restEntries : List (List QnfRat))
    (chain : rsiConsecutiveDivides (headEntry :: restEntries)) :
    rsiHeadDividesAll headEntry (headEntry :: restEntries) :=
  rsiAnchorDividesAllOfConsecutive headEntry (headEntry :: restEntries)
    (fun firstEntry _restEntries heq => by
      injection heq with headEq _tailEq; rw [headEq]; exact rpeDividesRefl firstEntry)
    chain

/-! ## T5 — the characteristic-matrix constructor `xI − A` (RCF seed) -/

/-- **A characteristic-matrix cell.**  `x·δ − a`: on the diagonal `rowIndex = colIndex` it is `x − a =
rpxSub [0, x] [a]`, off the diagonal it is `−a = rpxSub [] [a]`. -/
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

/-- **The `xI − A` characteristic matrix.**  From a rational base matrix `A`, produce the polynomial matrix
whose `(i, j)` entry is `x·δᵢⱼ − aᵢⱼ` — the matrix whose Smith invariant factors classify `A` up to
similarity (the classification theorem itself is walled: `rsiHasRationalCanonicalForm`). -/
def rsiCharMatrix (baseMatrix : List (List QnfRat)) : List (List (List QnfRat)) :=
  rsiCharMatrixBuild 0 baseMatrix

/-! ## Groundings (fires)

Magnitudes ≤ 3.  The already-Smith diagonal `diag(x − 1, (x − 1)(x − 2))` passes through unchanged (its cross
is already zero); the genuine-re-pivot matrix `[[x², x² + x], [x² + x, x²]]` descends to a two-entry diagonal. -/

set_option maxRecDepth 16384

/-- The already-Smith fire matrix `diag(x − 1, (x − 1)(x − 2))`. -/
def rsiFireDiagMatrix : List (List (List QnfRat)) :=
  [[[qnfOfInt (-1), qnfOfInt 1], []],
   [[], [qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]]]

/-- Fire (already-Smith pass-through, exact value): the descent on `diag(x − 1, (x − 1)(x − 2))` returns the
diagonal unchanged — `[x − 1, (x − 1)(x − 2)]`. -/
theorem rsiFireDiagAlreadySmith :
    rsiDiagonalize 2 rsiFireDiagMatrix
      = [[qnfOfInt (-1), qnfOfInt 1], [qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]] := rfl

/-- Fire (genuine descent, length): the non-diagonal matrix `[[x², x² + x], [x² + x, x²]]` descends to a
two-entry diagonal. -/
theorem rsiFireDescentLength : (rsiDiagonalize 2 rseFireMatrix).length = 2 := rfl

/-- Fire (genuine descent, degrees): both produced diagonal entries have degree `1` — the descent re-pivots
the degree-`2` minimum pivot `x²` down and splits the cross.  (Both degree `1` witnesses that this is the
all-zero-cross descent diagonal, NOT the true Smith form, whose factors have degrees `[1, 2]`; see the
`rsiHasSmithNormalForm` wall.) -/
theorem rsiFireDescentDegrees : (rsiDiagonalize 2 rseFireMatrix).map rpxDegree = [1, 1] := rfl

/-- Fire (FALSE control): the descent diagonal of the fire matrix is NOT the single-entry list `[x]` — it has
length `2`, refuted by a length mismatch. -/
theorem rsiFireWrongDiagonalRefuted :
    rsiDiagonalize 2 rseFireMatrix ≠ [[qnfOfInt 0, qnfOfInt 1]] := by
  intro hEq
  nomatch congrArg List.tail hEq

/-- Fire (per-stage all-zero cross, instantiated): stage 0 of the fire matrix reaches an all-zero cross about
its final pivot position, via `rsiStageAllZeroCross` at the pivot `x²` found at `(0, 0)`. -/
theorem rsiFireStageAllZeroCross :
    rseCrossIsAllZero (rsiStage rseFireMatrix 0 0).1 (rsiStage rseFireMatrix 0 0).2.1
      (rsiStage rseFireMatrix 0 0).2.2 :=
  rsiStageAllZeroCross rseFireMatrix 0 0 rfl

/-- Fire (invariant-factor chain holds on the already-Smith diagonal): `x − 1 | (x − 1)(x − 2)` (cofactor
`x − 2`), so the produced diagonal is consecutively divisible. -/
theorem rsiFireDiagConsecutiveDivides :
    rsiConsecutiveDivides (rsiDiagonalize 2 rsiFireDiagMatrix) := by
  rw [rsiFireDiagAlreadySmith]
  exact ⟨⟨[qnfOfInt (-2), qnfOfInt 1], rfl⟩, True.intro⟩

/-- Fire (chain assembly, instantiated): from the consecutive chain, the head `x − 1` divides EVERY diagonal
entry, via `rsiHeadDividesAllOfConsecutive`. -/
theorem rsiFireDiagHeadDividesAll :
    rsiHeadDividesAll [qnfOfInt (-1), qnfOfInt 1]
      ([qnfOfInt (-1), qnfOfInt 1] :: [[qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]]) :=
  rsiHeadDividesAllOfConsecutive [qnfOfInt (-1), qnfOfInt 1] [[qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]]
    (by
      have hDiag : rsiDiagonalize 2 rsiFireDiagMatrix
          = [qnfOfInt (-1), qnfOfInt 1] :: [[qnfOfInt 2, qnfOfInt (-3), qnfOfInt 1]] := rfl
      rw [← hDiag]; exact rsiFireDiagConsecutiveDivides)

/-- Fire (characteristic matrix, exact value): `xI − A` for the companion matrix `A = [[0, 1], [1, 0]]` of
`x² − 1` is `[[x, −1], [−1, x]]`. -/
theorem rsiFireCharMatrix :
    rsiCharMatrix [[qnfOfInt 0, qnfOfInt 1], [qnfOfInt 1, qnfOfInt 0]]
      = [[[qnfOfInt 0, qnfOfInt 1], [qnfOfInt (-1)]], [[qnfOfInt (-1)], [qnfOfInt 0, qnfOfInt 1]]] := rfl

/-! ## Content markers -/

/-- DECIDED: the ℚ[x] Smith SUBMATRIX DESCENT skeleton — `rsiDiagonalize`, a total fuel-structural driver that
runs pivot-search (`rsmPivotSearch`) → re-pivot driver to an all-zero cross (`rsiStage`, rung 8) → submatrix
extraction (`rsfSubmatrix`) → recurse, accumulating one diagonal entry per stage.  Terminates structurally on
the `Nat` fuel (= matrix dimension); no `WellFounded.fix`. -/
def rsiHasDescentDriver : Bool := true

/-- DECIDED: the PER-STAGE all-zero-cross correctness — each descent stage reaches a matrix whose cross about
the final pivot position is entirely zero (`rsiStageAllZeroCross`), transported onto the produced diagonal
list as `rsiDiagonalizeHeadAllZeroCross` (the output is `finalPivotEntry :: rest` with `finalPivotEntry` read
at an all-zero-cross position).  The rung-8 terminal `rseRepivotDriverReachesAllZeroCross` threaded through the
recursion. -/
def rsiHasAllZeroCrossPerStage : Bool := true

/-- DECIDED: the invariant-factor CHAIN ASSEMBLY — a consecutively-divisible diagonal (`rsiConsecutiveDivides`:
`d₁ | d₂ | ⋯`) closes to "the head divides every entry" (`rsiHeadDividesAllOfConsecutive`,
`rsiHeadDividesAll`), the transitive-closure content of the invariant-factor poset, built on the committed
`rbzDividesTrans` and `rpeDividesRefl`.  Fired on the already-Smith diagonal `diag(x − 1, (x − 1)(x − 2))`.
The consecutive facts are HYPOTHESES here; deriving them from the algorithm needs the true Smith form
(walled). -/
def rsiHasChainAssembly : Bool := true

/-- WALLED (owner-false; the committed `rseHasSubmatrixDescent := false`, `rsfHasSubmatrixDescent := false`,
`rsmHasSmithNormalForm := false`, `rbzHasSmithNormalForm := false`, `rsdHasInvariantFactorChain := false` all
stay byte-intact): the TRUE Smith normal form over ℚ[x], with the invariant-factor divisibility chain
`d₁ | d₂ | ⋯ | dᵣ` HOLDING for the produced diagonal.

Precise obstruction: `rsmCrossClear` (the clear the re-pivot driver iterates) reduces each off-pivot cross
entry modulo the pivot INDEPENDENTLY — it rewrites the entry at `(pivotRow, col)` / `(row, pivotCol)` to its
Euclidean residue and touches nothing else.  This is NOT a full row/column ELEMENTARY OPERATION (which
subtracts `quotient · (whole pivot row)` from another row, modifying the trailing submatrix too).  So
`rsiDiagonalize` reaches an all-zero CROSS about each pivot but leaves the trailing submatrix UNTOUCHED and
does NOT preserve the determinant ideal.  Fire evidence: on `[[x², x² + x], [x² + x, x²]]` (det `−2x³ − x²`,
degree 3) the descent yields TWO degree-`1` factors (`rsiFireDescentDegrees`), product degree 2 ≠ 3 — the true
Smith factors have degrees `[1, 2]`.

Two burned approaches to force the chain from THIS all-zero-cross diagonal: (1) read the diagonal directly off
the all-zero-cross terminal — refuted, because the cross clear never touches the submatrix, so a pivot need
not divide the submatrix entries and `dₖ | dₖ₊₁` fails; (2) re-run the fixed-pivot clear on the submatrix to
force divisibility — refuted for the same reason `rsfHasAllZeroCrossFixedPoint` was walled: a residue of
degree below the pivot is division-stable, and the clear does not propagate into the submatrix.

Route to close: replace `rsmCrossClear`'s per-entry residue by the FULL row/column elementary operation
(subtract `quotient · pivot row` from row `k`, `quotient · pivot column` from column `k`), preserving the
determinant ideal and driving the submatrix; then the pivot-divides-every-submatrix-entry second descent (add
an offending row into the pivot row, re-clear, produce a still-smaller residue) makes `dₖ | (every submatrix
entry)`, after which `rpeGcdDividesBoth` (each `dᵢ` is a gcd of surviving minors) composed with the shipped
`rsiHeadDividesAllOfConsecutive` (via `rbzDividesTrans`) delivers the chain. -/
def rsiHasSmithNormalForm : Bool := false

/-- WALLED (owner-false): the RATIONAL CANONICAL FORM corollary — the invariant factors of the Smith form of
the characteristic matrix `xI − A` classify `A` up to similarity.  The `xI − A` constructor `rsiCharMatrix`
ships and fires (`rsiFireCharMatrix`: `[[0,1],[1,0]] ↦ [[x, −1], [−1, x]]`), but the corollary rests on (1) the
true Smith normal form of `xI − A` (walled above, `rsiHasSmithNormalForm`) — the all-zero-cross descent
already mis-scales it (its diagonal of `[[x, −1], [−1, x]]` collapses to units, not `[1, x² − 1]`, for the same
determinant reason), and (2) the similarity classification theorem "`A ∼ B` iff `xI − A` and `xI − B` have
equal Smith invariant factors", which needs a matrix-similarity relation and a companion-block reader, neither
built here. -/
def rsiHasRationalCanonicalForm : Bool := false

end FX1Poly.ComputerAlgebra
