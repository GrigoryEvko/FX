import FX1Poly.ComputerAlgebra.IntMatrix
import FX1Poly.ComputerAlgebra.Number.IntGreatestCommonDivisor
import FX1Poly.ComputerAlgebra.Number.IntExactDivision
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithNormalForm — the ZZ Smith driver + certificates
    (H2-SMITH r1)

`IntMatrix` (the `ComputerAlgebra/` substrate) already ships the CARRIER, the unimodular operation
ALPHABET (swap / negate / transvection, row and column), the `applyOperations` applier, and the
`IsSmithNormalFormWithin` PREDICATE + `SmithReductionCertificate` type.  This module adds the four
missing pieces for exact integral homology with torsion (frontiers.md Domain XI):

  * **The certified-gcd interface** (`CertifiedGcd`) with the three defining gcd properties (divides
    both, greatest) over an abstract carrier — laws over the parameter, sized for ZZ now and
    ratPoly / F2 later — instantiated for `Int` by `intCertifiedGcd` from the shipped signed-gcd
    kit (`Number/IntGreatestCommonDivisor`).
  * **The operation-inverse kit** (`inverseOperation`, `reverseOperationWord`): every alphabet
    letter has a definitional inverse letter, so a checked reduction word witnesses genuine ZZ
    EQUIVALENCE (each op is undoable) with no matrix multiplication at all.  The negate letter is
    unconditionally involutive at the matrix level (`negateRowInvolutive`); the transvection letter
    cancels at the row level (`addScaledEntriesCancel`, under the equal-length hypothesis that
    rectangularity supplies).
  * **The elimination driver** (`smithReduceSweep` / `smithReduce`): a structural-fuel pivot sweep
    that emits a `SmithReductionCertificate` — the untrusted producer.  Coefficients come from the
    magnitude quotient (`intMagnitudeQuotient`); each pivot clears its column-below and row-right by
    Euclidean transvection.
  * **Non-vacuity**: SNF verified on concrete inputs — the driver's output on the upper-triangular
    and dense `2 x 2` inputs is proved `IsSmithNormalFormWithin` (the driver produces a
    kernel-checked certificate), plus a torsion diagonal, a `3 x 3` invariant-factor chain
    `2 | 2 | 4`, and the `[[2]]` boundary map whose SNF is the `Z/2` homology-with-torsion seed the
    H2-WALKERS lane consumes.

Honest r2 residual (named, with exact goals, in the module footer): the Bezout coefficient identity
over ZZ; a general Int `divmod` with reconstruction + shrink for the abstract Euclidean interface;
the SWAP letter's self-inverse and the full matrix-level transvection round-trip under
`IsRectangular`; and the driver's TOTAL correctness `∀ matrix, (smithReduce matrix ..).reducesToSmithForm ..`
(r1 proves concrete-input non-vacuity, the honest floor).

## Zero-axiom

Structural fuel in the driver (no `WellFounded.fix`), `congrArg`/`Eq.trans` witness arithmetic over
the propext-clean `Int` kit, `decide` on the LITERAL reduced matrices (never on the driver
computation, which taints `decide` through `Nat.min`/`Nat.sub`), and the clean peel refutation
`Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc ..))` for past-diagonal positions (bare
`nomatch` on `k + 2 < 2` leaks propext).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithNormalForm.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The certified-gcd interface (B1)

Laws over the parameter (OMEGA-5 discipline): the three properties that PIN the gcd — divides both
arguments, and is divisible by every common divisor — plus the Euclidean size measure the driver's
fuel rides.  The ZZ instance is built from the shipped signed-gcd kit; ratPoly / F2 instances reuse
the same interface in later rounds. -/

/-- A certified greatest-common-divisor structure over `carrier`: the gcd together with its
divisibility relation and the three defining properties, plus the Euclidean size measure. -/
structure CertifiedGcd (carrier : Type) where
  /-- The Euclidean size (well-founded measure): ZZ uses `Int.natAbs`. -/
  euclideanSize : carrier → Nat
  /-- The greatest common divisor. -/
  gcd : carrier → carrier → carrier
  /-- The divisibility relation (`∃ cofactor, value = divisor * cofactor`). -/
  Divides : carrier → carrier → Prop
  /-- The gcd divides its left argument. -/
  gcdDividesLeft : ∀ leftValue rightValue, Divides (gcd leftValue rightValue) leftValue
  /-- The gcd divides its right argument. -/
  gcdDividesRight : ∀ leftValue rightValue, Divides (gcd leftValue rightValue) rightValue
  /-- Every common divisor divides the gcd (greatest-ness). -/
  gcdGreatest : ∀ commonDivisor leftValue rightValue,
    Divides commonDivisor leftValue → Divides commonDivisor rightValue →
    Divides commonDivisor (gcd leftValue rightValue)

/-- The integer instance: `Int.natAbs` measure, the signed `intGcd`, `IntDivides`, and the three
certificates from `Number/IntGreatestCommonDivisor`. -/
def intCertifiedGcd : CertifiedGcd Int where
  euclideanSize := Int.natAbs
  gcd := intGcd
  Divides := IntDivides
  gcdDividesLeft := intGcdDividesLeft
  gcdDividesRight := intGcdDividesRight
  gcdGreatest := fun _ _ _ dividesLeft dividesRight => intGcdGreatest dividesLeft dividesRight

/-! ## The operation-inverse kit (B2)

Each alphabet letter is undoable by a definitional inverse letter, so `applyOperations word matrix`
is ZZ-EQUIVALENT to `matrix` — an explicit invertible trail, no `U * D * V` re-multiplication.  The
per-letter cancel certificates below realise the two letters whose inverse is a clean matrix-level
(negate) or row-level (transvection) identity; the swap letter's self-inverse and the full
matrix-level transvection round-trip under `IsRectangular` are the r2 residual. -/

/-- The inverse row letter: swap and negate are self-inverse; a transvection negates its
coefficient. -/
def inverseRowOperation : ElementaryRowOperation → ElementaryRowOperation
  | .swapRows firstIndex secondIndex => .swapRows firstIndex secondIndex
  | .negateRow rowIndex => .negateRow rowIndex
  | .addRowMultiple sourceIndex targetIndex coefficient =>
      .addRowMultiple sourceIndex targetIndex (-coefficient)

/-- The inverse column letter (mirror of `inverseRowOperation`). -/
def inverseColumnOperation : ElementaryColumnOperation → ElementaryColumnOperation
  | .swapColumns firstIndex secondIndex => .swapColumns firstIndex secondIndex
  | .negateColumn colIndex => .negateColumn colIndex
  | .addColumnMultiple sourceIndex targetIndex coefficient =>
      .addColumnMultiple sourceIndex targetIndex (-coefficient)

/-- The inverse of one certificate step. -/
def inverseOperation : ElementaryOperation → ElementaryOperation
  | .rowOperation operation => .rowOperation (inverseRowOperation operation)
  | .columnOperation operation => .columnOperation (inverseColumnOperation operation)

/-- Reverse a certificate word into its undo word: invert each letter and reverse the order (the
inverse of `applyOperations`, letter-wise). -/
def reverseOperationWord : List ElementaryOperation → List ElementaryOperation
  | [] => []
  | operation :: remainingOperations =>
      reverseOperationWord remainingOperations ++ [inverseOperation operation]

/-- Negating a row's entries twice is the identity — `intNegNeg` on each entry. -/
theorem listMapNegNeg : ∀ row : IntRow,
    (row.map (fun entry => -entry)).map (fun entry => -entry) = row
  | [] => rfl
  | head :: tail =>
      (congrArg (· :: (tail.map (fun entry => -entry)).map (fun entry => -entry))
          (intNegNeg head)).trans
        (congrArg (head :: ·) (listMapNegNeg tail))

/-- Negating one row's entries twice, in place, is the identity. -/
theorem listModifyAtNegNeg : ∀ (rows : List IntRow) (rowIndex : Nat),
    listModifyAt (fun row => row.map (fun entry => -entry))
      (listModifyAt (fun row => row.map (fun entry => -entry)) rows rowIndex) rowIndex = rows
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | row :: remainingRows, 0 => congrArg (· :: remainingRows) (listMapNegNeg row)
  | row :: remainingRows, rowIndex + 1 =>
      congrArg (row :: ·) (listModifyAtNegNeg remainingRows rowIndex)

/-- **The negate letter is unconditionally involutive** — `negateRow` composed with itself is the
identity, at the matrix level, for any index. -/
theorem negateRowInvolutive (matrix : IntMatrix) (rowIndex : Nat) :
    (matrix.negateRow rowIndex).negateRow rowIndex = matrix :=
  match matrix with
  | { rows := underlyingRows } =>
      congrArg IntMatrix.mk (listModifyAtNegNeg underlyingRows rowIndex)

/-- **The transvection letter cancels** — adding `coefficient` then `-coefficient` times a source
row leaves the target unchanged, for equal-length rows (rectangularity supplies the length
hypothesis).  The head step is `(target + coefficient * source) + (-coefficient) * source =
target`. -/
theorem addScaledEntriesCancel : ∀ (coefficient : Int) (sourceRow targetRow : IntRow),
    sourceRow.length = targetRow.length →
    addScaledEntries (-coefficient) sourceRow (addScaledEntries coefficient sourceRow targetRow)
      = targetRow
  | _, [], [], _ => rfl
  | _, [], _ :: _, lengthsAgree => nomatch lengthsAgree
  | _, _ :: _, [], lengthsAgree => nomatch lengthsAgree
  | coefficient, sourceEntry :: sourceRemaining, targetEntry :: targetRemaining, lengthsAgree =>
      have headCancels :
          (targetEntry + coefficient * sourceEntry) + -coefficient * sourceEntry = targetEntry :=
        (intAddAssoc targetEntry (coefficient * sourceEntry) (-coefficient * sourceEntry)).trans
          ((congrArg (targetEntry + ·)
              ((intRightDistrib coefficient (-coefficient) sourceEntry).symm.trans
                ((congrArg (· * sourceEntry) (intAddRightNeg coefficient)).trans
                  (intZeroMul sourceEntry)))).trans
            (intAddZero targetEntry))
      (congrArg
          (· :: addScaledEntries (-coefficient) sourceRemaining
                  (addScaledEntries coefficient sourceRemaining targetRemaining))
          headCancels).trans
        (congrArg (targetEntry :: ·)
          (addScaledEntriesCancel coefficient sourceRemaining targetRemaining
            (Nat.succ.inj lengthsAgree)))

/-! ## The elimination driver (B3)

The untrusted producer: a structural-fuel pivot sweep emitting a `SmithReductionCertificate`.  Each
pivot clears its column-below and row-right by a Euclidean transvection whose coefficient is the
magnitude quotient (correct sign when the pivot is nonnegative — the diagonal invariant the driver
maintains).  Coefficients within one clear read the CURRENT matrix, so column and row clears are
threaded through `applyOperations`.  Correctness is NOT claimed here (r2) — it is checked per-input
in the non-vacuity section. -/

/-- The transvection coefficient zeroing `entry` against a nonnegative `pivot`: `entry / pivot` with
sign, via the magnitude quotient. -/
def intPivotQuotient (pivot entry : Int) : Int :=
  intMagnitudeQuotient pivot.natAbs entry

/-- Column ops clearing the pivot row to the right: for each of `stepCount` columns from `colIndex`
onward, subtract `(entry / pivot)` times the pivot column (all coefficients read `matrix`). -/
def smithClearRowRightSteps (matrix : IntMatrix) (pivotIndex : Nat) :
    Nat → Nat → List ElementaryColumnOperation
  | 0, _ => []
  | stepCount + 1, colIndex =>
      ElementaryColumnOperation.addColumnMultiple pivotIndex colIndex
          (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
              (matrix.entryAt pivotIndex colIndex)))
        :: smithClearRowRightSteps matrix pivotIndex stepCount (colIndex + 1)

/-- Row ops clearing the pivot column below: for each of `stepCount` rows from `rowIndex` onward,
subtract `(entry / pivot)` times the pivot row (all coefficients read `matrix`). -/
def smithClearColumnBelowSteps (matrix : IntMatrix) (pivotIndex : Nat) :
    Nat → Nat → List ElementaryRowOperation
  | 0, _ => []
  | stepCount + 1, rowIndex =>
      ElementaryRowOperation.addRowMultiple pivotIndex rowIndex
          (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
              (matrix.entryAt rowIndex pivotIndex)))
        :: smithClearColumnBelowSteps matrix pivotIndex stepCount (rowIndex + 1)

/-- One structural-fuel pivot sweep: at each pivot within the `height x width` window, clear the
column below then the row to the right, threading the partially-reduced matrix so later coefficients
are exact, and recurse on the next pivot. -/
def smithReduceSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | fuel + 1, matrix, pivotIndex, height, width =>
      if pivotIndex + 1 ≤ Nat.min height width then
        let columnOps :=
          (smithClearColumnBelowSteps matrix pivotIndex (height - (pivotIndex + 1))
              (pivotIndex + 1)).map ElementaryOperation.rowOperation
        let afterColumnClear := matrix.applyOperations columnOps
        let rowOps :=
          (smithClearRowRightSteps afterColumnClear pivotIndex (width - (pivotIndex + 1))
              (pivotIndex + 1)).map ElementaryOperation.columnOperation
        let afterRowClear := afterColumnClear.applyOperations rowOps
        columnOps ++ rowOps ++ smithReduceSweep fuel afterRowClear (pivotIndex + 1) height width
      else []

/-- The Smith reduction certificate produced for `matrix` in the `height x width` window — fuel is
`Nat.min height width` (one sweep per pivot). -/
def smithReduce (matrix : IntMatrix) (height width : Nat) : SmithReductionCertificate :=
  { operations := smithReduceSweep (Nat.min height width) matrix 0 height width }

/-! ## The total driver (H2-SMITH r3, B1) — search + sign + Euclid cascade wired

The r1 `smithReduce` clears a pivot's cross by ONE magnitude-quotient transvection, so it stalls
whenever the pivot does not already divide a cross entry (`[[6, 4], [0, 0]]`: `6 ∤ 4`, coefficient
`0`, the `4` survives).  `smithReduceTotal` ADDS the three missing passes AROUND the reused r1 clear
helpers, keeping `smithReduce` byte-identical (the two driver-riding defeq theorems
`smithReducedUpperTriangular` / `smithReducedDenseTwo` stay green):

  * **Search** (`smithFindMinAbsInMinor`): the minimal-magnitude nonzero entry of the pivot minor —
    the Euclidean pivot choice (reducing a larger entry by a smaller one is what makes the quotient
    nonzero).
  * **Move + sign** (`smithMoveToPivotOps` / `smithSignNormalizeOps`): swap that entry to the pivot
    slot, then `negateRow` a negative pivot so the exact clear (whose divisor is `pivot.natAbs`)
    always sees a nonnegative pivot.
  * **Euclid cascade** (`smithCascadeSweep`, structural on `innerFuel`): move-sign-clear, then if the
    cross is not yet zero, LOOP — the freshly parked remainders are strictly smaller than the pivot,
    so the next minimal-magnitude search finds a strictly smaller pivot; the rotation count is
    bounded by the pivot magnitude, over-approximated by the whole-minor magnitude sum
    (`smithMinorAbsSum`) as the structural fuel.

STRUCTURAL fuel throughout (no `WellFounded.fix`); the decision branches (`Nat`/`Int` `<`/`==`, the
`if`/`match` on `Bool`) are all axiom-free `Decidable` instances.  Correctness is the untrusted
producer's — CHECKED per input by the r1-battery `#eval` regression (every r1 hand-word certificate
input now reduces BY THE DRIVER to the same Smith normal form).  The whole-minor
divisibility-repair phase that would force the full invariant-factor chain `d_p | d_{p+1}` on
arbitrary inputs is the honest r4 residual (see the totality footer). -/

/-- Scan `colCount` entries of row `rowIndex` from `colStart`, keeping the running minimal-magnitude
nonzero position (`best`).  Structural on the column count. -/
def smithScanRowMinAbs (matrix : IntMatrix) (rowIndex : Nat) :
    Nat → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, _, best => best
  | colCount + 1, colStart, best =>
      let entry := matrix.entryAt rowIndex colStart
      let updatedBest :=
        match best with
        | none => if entry.natAbs == 0 then none else some (rowIndex, colStart)
        | some (bestRow, bestCol) =>
            if entry.natAbs == 0 then some (bestRow, bestCol)
            else if entry.natAbs < (matrix.entryAt bestRow bestCol).natAbs then
              some (rowIndex, colStart)
            else some (bestRow, bestCol)
      smithScanRowMinAbs matrix rowIndex colCount (colStart + 1) updatedBest

/-- Scan `rowCount` rows from `rowStart`, each over `colCount` columns from `colStart`, folding the
minimal-magnitude nonzero position.  Structural on the row count. -/
def smithScanMinorMinAbs (matrix : IntMatrix) (colStart colCount : Nat) :
    Nat → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, _, best => best
  | rowCount + 1, rowStart, best =>
      smithScanMinorMinAbs matrix colStart colCount rowCount (rowStart + 1)
        (smithScanRowMinAbs matrix rowStart colCount colStart best)

/-- The minimal-magnitude nonzero position of the pivot minor (rows/cols `≥ pivotIndex`), or `none`
when the minor is all zero — the Euclidean pivot search. -/
def smithFindMinAbsInMinor (matrix : IntMatrix) (pivotIndex height width : Nat) :
    Option (Nat × Nat) :=
  smithScanMinorMinAbs matrix pivotIndex (width - pivotIndex)
    (height - pivotIndex) pivotIndex none

/-- Bring the found entry to the pivot slot: swap its row and its column into `pivotIndex` (both
swaps are identities when the found index already equals the pivot). -/
def smithMoveToPivotOps (pivotIndex foundRow foundCol : Nat) : List ElementaryOperation :=
  [ ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows pivotIndex foundRow)
  , ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns pivotIndex foundCol) ]

/-- Normalise the pivot's sign: `negateRow` the pivot row when the pivot entry is negative, so the
exact clear (divisor `pivot.natAbs`) sees a nonnegative pivot; the empty word otherwise. -/
def smithSignNormalizeOps (matrix : IntMatrix) (pivotIndex : Nat) : List ElementaryOperation :=
  if matrix.entryAt pivotIndex pivotIndex < 0 then
    [ ElementaryOperation.rowOperation (ElementaryRowOperation.negateRow pivotIndex) ]
  else []

/-- Are all `colCount` entries of row `rowIndex` from `colStart` zero?  Structural on the count. -/
def smithRowSegmentAllZero (matrix : IntMatrix) (rowIndex : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | colCount + 1, colStart =>
      (matrix.entryAt rowIndex colStart).natAbs == 0 &&
        smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1)

/-- Are all `rowCount` entries of column `colIndex` from `rowStart` zero?  Structural on the count. -/
def smithColSegmentAllZero (matrix : IntMatrix) (colIndex : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | rowCount + 1, rowStart =>
      (matrix.entryAt rowStart colIndex).natAbs == 0 &&
        smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1)

/-- Is the pivot's cross cleared — every entry of row `pivotIndex` right of the pivot and every entry
of column `pivotIndex` below the pivot is zero?  The cascade's loop-termination flag. -/
def smithCrossIsClear (matrix : IntMatrix) (pivotIndex height width : Nat) : Bool :=
  smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) &&
    smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)

/-- Sum the magnitudes of `colCount` entries of row `rowIndex` from `colStart`. -/
def smithRowAbsSum (matrix : IntMatrix) (rowIndex : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | colCount + 1, colStart =>
      (matrix.entryAt rowIndex colStart).natAbs + smithRowAbsSum matrix rowIndex colCount (colStart + 1)

/-- Sum the magnitudes over `rowCount` rows from `rowStart`, each `colCount` columns from `colStart`. -/
def smithMinorAbsSumRows (matrix : IntMatrix) (colStart colCount : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | rowCount + 1, rowStart =>
      smithRowAbsSum matrix rowStart colCount colStart +
        smithMinorAbsSumRows matrix colStart colCount rowCount (rowStart + 1)

/-- The whole-minor magnitude sum — the over-approximated Euclid-cascade fuel (at least the minimal
pivot magnitude, which bounds the rotation count). -/
def smithMinorAbsSum (matrix : IntMatrix) (pivotIndex height width : Nat) : Nat :=
  smithMinorAbsSumRows matrix pivotIndex (width - pivotIndex) (height - pivotIndex) pivotIndex

/-- One pivot's Euclid cascade: search the minor, move + sign-normalise the minimal-magnitude entry
into the pivot slot, clear the cross by magnitude-quotient transvections (the reused r1 helpers),
and — if the cross is not yet zero — LOOP on the reduced matrix with one less fuel.  Structural on
`innerFuel`. -/
def smithCascadeSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | innerFuel + 1, matrix, pivotIndex, height, width =>
      match smithFindMinAbsInMinor matrix pivotIndex height width with
      | none => []
      | some (foundRow, foundCol) =>
          let moveOps := smithMoveToPivotOps pivotIndex foundRow foundCol
          let afterMove := matrix.applyOperations moveOps
          let signOps := smithSignNormalizeOps afterMove pivotIndex
          let afterSign := afterMove.applyOperations signOps
          let columnClearOps :=
            (smithClearColumnBelowSteps afterSign pivotIndex (height - (pivotIndex + 1))
                (pivotIndex + 1)).map ElementaryOperation.rowOperation
          let afterColumnClear := afterSign.applyOperations columnClearOps
          let rowClearOps :=
            (smithClearRowRightSteps afterColumnClear pivotIndex (width - (pivotIndex + 1))
                (pivotIndex + 1)).map ElementaryOperation.columnOperation
          let afterRowClear := afterColumnClear.applyOperations rowClearOps
          let settledOps := moveOps ++ signOps ++ columnClearOps ++ rowClearOps
          match smithCrossIsClear afterRowClear pivotIndex height width with
          | true => settledOps
          | false =>
              settledOps ++ smithCascadeSweep innerFuel afterRowClear pivotIndex height width

/-- The total pivot sweep: at each pivot run the Euclid cascade (fuelled by the minor's magnitude
sum), thread the reduced matrix, and recurse on the next pivot.  Structural on `outerFuel` (the pivot
budget `Nat.min height width`). -/
def smithReduceTotalSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | outerFuel + 1, matrix, pivotIndex, height, width =>
      if pivotIndex + 1 ≤ Nat.min height width then
        let pivotOps :=
          smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width
        let afterPivot := matrix.applyOperations pivotOps
        pivotOps ++ smithReduceTotalSweep outerFuel afterPivot (pivotIndex + 1) height width
      else []

/-- The total Smith reduction certificate for `matrix` in the `height × width` window — search + sign
+ Euclid cascade per pivot, one sweep per pivot (`Nat.min height width` outer fuel). -/
def smithReduceTotal (matrix : IntMatrix) (height width : Nat) : SmithReductionCertificate :=
  { operations := smithReduceTotalSweep (Nat.min height width) matrix 0 height width }

/-! ## Non-vacuity (B4)

Concrete SNF certificates, produced-then-checked.  The `diagonalDividesSuccessor` witnesses are
built by hand (the `∃`-divisibility field is not `decide`-able); the decidable off-diagonal and
nonnegativity fields are discharged by `decide` on the LITERAL reduced matrix (deciding on the
driver expression taints `decide` with propext through `Nat.min`/`Nat.sub`), then the driver-typed
statements are closed by defeq (the driver computes to the literal). -/

/-- The torsion diagonal `diag(2, 4)` — already Smith-normal, the `Z/2 ⊕ Z/4` reading.  The chain
`2 | 4` is the hand-built witness `(4 : Int) = 2 * 2`. -/
theorem smithExampleTorsionDiagonal :
    ({ rows := [[2, 0], [0, 4]] } : IntMatrix).IsSmithNormalFormWithin 2 2 where
  offDiagonalVanishes := by
    have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
        rowIndex ≠ colIndex →
        ({ rows := [[2, 0], [0, 4]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
    exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
      offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
  diagonalIsNonnegative := by decide
  diagonalDividesSuccessor := fun position isPositionBelow =>
    match position, isPositionBelow with
    | 0, _ => ⟨2, rfl⟩
    | _ + 1, isBeyondDiagonal =>
        Nat.noConfusion
          (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))

/-- The upper-triangular input `[[1,1],[0,2]]`, reduced by the DRIVER to `diag(1, 2)` — the
`SmithReductionCertificate` `smithReduce` emits is kernel-checked to land in Smith normal form.  The
proof is the literal-matrix SNF, closed against the driver goal by defeq. -/
theorem smithReducedUpperTriangular :
    (({ rows := [[1, 1], [0, 2]] } : IntMatrix).applyOperations
        (smithReduce { rows := [[1, 1], [0, 2]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[1, 0], [0, 2]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0], [0, 2]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨2, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- The dense input `[[2,2],[2,4]]`, reduced by the DRIVER to `diag(2, 2)` (gcd of the entries is 2,
determinant is 4, so both invariant factors are 2).  The chain `2 | 2` is `(2 : Int) = 2 * 1`. -/
theorem smithReducedDenseTwo :
    (({ rows := [[2, 2], [2, 4]] } : IntMatrix).applyOperations
        (smithReduce { rows := [[2, 2], [2, 4]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 2]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 2]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- A `3 x 3` invariant-factor chain `2 | 2 | 4` (the `Z/2 ⊕ Z/2 ⊕ Z/4` reading) — already
Smith-normal, showing a genuine three-length divisibility chain with hand-built witnesses at
positions 0 (`2 = 2 * 1`) and 1 (`4 = 2 * 2`). -/
theorem smithExampleChainThree :
    ({ rows := [[2, 0, 0], [0, 2, 0], [0, 0, 4]] } : IntMatrix).IsSmithNormalFormWithin 3 3 where
  offDiagonalVanishes := by
    have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
        rowIndex ≠ colIndex →
        ({ rows := [[2, 0, 0], [0, 2, 0], [0, 0, 4]] } : IntMatrix).entryAt rowIndex colIndex = 0 :=
      by decide
    exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
      offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
  diagonalIsNonnegative := by decide
  diagonalDividesSuccessor := fun position isPositionBelow =>
    match position, isPositionBelow with
    | 0, _ => ⟨1, rfl⟩
    | 1, _ => ⟨2, rfl⟩
    | _ + 2, isBeyondDiagonal =>
        Nat.noConfusion
          (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))))

/-- The `1 x 1` boundary map `[[2]]` — its Smith normal form is itself, the `Z/2` torsion the
homology-with-torsion computation reads off (the H2-WALKERS degree-2 seed).  A single nonnegative
diagonal entry, no off-diagonal, no successor to divide. -/
theorem smithExampleCyclicTwo :
    ({ rows := [[2]] } : IntMatrix).IsSmithNormalFormWithin 1 1 where
  offDiagonalVanishes := fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
    match rowIndex, colIndex, isRowInRange, isColInRange with
    | 0, 0, _, _ => absurd rfl isOffDiagonal
    | _ + 1, _, isRowInRange, _ =>
        Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isRowInRange))
    | 0, _ + 1, _, isColInRange =>
        Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isColInRange))
  diagonalIsNonnegative := by decide
  diagonalDividesSuccessor := fun position isPositionBelow =>
    Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow))

/-- A genuinely NON-SQUARE `2 x 3` Smith normal form `diag(1, 2)` with a free zero column — the
`H = ℤ` free-summand read-off (no torsion: the unit `1` gives `1 | 2`).  `Nat.min 2 3 = 2` gates the
diagonal at two positions while column 2 stays free.  The r1/r2 battery's missing rectangular member
(H2-SMITH r3, B3). -/
theorem smithExampleWideTwoByThree :
    ({ rows := [[1, 0, 0], [0, 2, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 3 where
  offDiagonalVanishes := by
    have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 3 →
        rowIndex ≠ colIndex →
        ({ rows := [[1, 0, 0], [0, 2, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
    exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
      offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
  diagonalIsNonnegative := by decide
  diagonalDividesSuccessor := fun position isPositionBelow =>
    match position, isPositionBelow with
    | 0, _ => ⟨2, rfl⟩
    | _ + 1, isBeyondDiagonal =>
        Nat.noConfusion
          (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))

/-! ## The Euclid cascade + sign/swap pass (H2-SMITH r2, B1/B2)

The r1 driver clears a pivot's row and column by ONE magnitude-quotient transvection, which only
zeroes an entry the pivot already divides.  When it does not (e.g. `[[6, 4], [0, 0]]`: pivot `6`,
row entry `4`, `6 ∤ 4`), the coefficient `intPivotQuotient 6 4 = 0` and the `4` survives — not
Smith-normal.  The gcd cascade replaces the one-shot clear with a Euclidean ROTATION loop: park the
remainder `r = entry − (entry / pivot) · pivot` at the pivot by a transvection, swap it into the
pivot slot, and repeat.  The measure the loop rides is the pivot's `euclideanSize` (`Int.natAbs`):
one rotation drops it to the counting remainder, and

  `smithRotationDecreasesPivotSize` : `intMagnitudeRemainder pivot.natAbs entry < pivot.natAbs`

is the STRICT, SUBTRACTION-FREE descent (the remainder bound `natDivModCountingRemainderIsBounded`
read through `intMagnitudeRemainderAsCounting`; no `Nat.sub` in the measure).  The pass structure
(Job 2) is INTERLEAVED per pivot — pivot search + swap, sign-normalise (`negateRow` on a negative
pivot), Euclid cascade, exact clear, divisibility-repair — so the exact clear always sees a
nonnegative pivot (`intMagnitudeDivisionExact` reconstructs against `Int.ofNat pivot.natAbs`).

The three r1 failures below are closed AS KERNEL-CHECKED CERTIFICATES: each ships the explicit
unimodular reduction word and its produced-then-checked Smith normal form, closed against the
literal by defeq (the `applyOperations` word computes to the literal, checked propext-cleanly by
`decide` on the literal with hand-built divisibility witnesses).  Totalising the DRIVER to emit
these words for every input is the named residual `SmithReduceTotalStatement` (r3). -/

/-- **The Euclidean rotation's strict descent** — the parked remainder's magnitude sits strictly
below the pivot's, subtraction-free: the counting-divider remainder bound
(`natDivModCountingRemainderIsBounded`) read at the magnitude remainder through
`intMagnitudeRemainderAsCounting`.  This is the well-founded measure the cascade's fuel rides. -/
theorem smithRotationDecreasesPivotSize (pivot entry : Int)
    (isPivotPositive : 0 < pivot.natAbs) :
    intMagnitudeRemainder pivot.natAbs entry < pivot.natAbs :=
  Eq.mp
    (congrArg (· < pivot.natAbs)
        (intMagnitudeRemainderAsCounting pivot.natAbs entry)).symm
    (natDivModCountingRemainderIsBounded entry.natAbs pivot.natAbs isPivotPositive)

/-- **The Euclidean-row failure closed** — `[[6, 4], [0, 0]]` (pivot `6` does not divide the row
entry `4`) reduces to `diag(2, 0)` by two column transvections realising Euclid on `(6, 4)`
(`gcd = 2`).  The r1 one-shot clear left the `4`; the cascade word lands in Smith normal form. -/
theorem smithReducedEuclideanRow :
    (({ rows := [[6, 4], [0, 0]] } : IntMatrix).applyOperations
        [ ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple 1 0 (-1))
        , ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple 0 1 (-2)) ]).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **The signed-diagonal failure closed** — `diag(-2, -6)` (already off-diagonal-clear but with
NEGATIVE pivots, so `diagonalIsNonnegative` fails) normalises to `diag(2, 6)` by one `negateRow` per
row.  The chain `2 | 6` is the hand-built witness `(6 : Int) = 2 * 3`.  The sign pass makes the
nonnegative-diagonal invariant HOLD. -/
theorem smithReducedSignedDiagonal :
    (({ rows := [[-2, 0], [0, -6]] } : IntMatrix).applyOperations
        [ ElementaryOperation.rowOperation (ElementaryRowOperation.negateRow 0)
        , ElementaryOperation.rowOperation (ElementaryRowOperation.negateRow 1) ]).IsSmithNormalFormWithin
      2 2 :=
  show ({ rows := [[2, 0], [0, 6]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 6]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨3, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **The rank-deficient pivot-search failure closed** — `[[2, 4, 6], [1, 2, 3], [3, 6, 9]]` (rank
one: rows `2·`, `1·`, `3·` the vector `[1, 2, 3]`) reduces to `diag(1, 0, 0)`.  The r1 driver, with
no pivot search, kept the non-dividing `2` at the pivot and mangled the column; the pass swaps the
unit entry `1` into the pivot, clears, and lands in Smith normal form.  Chains `1 | 0` and `0 | 0`
are the witnesses `⟨0, rfl⟩`. -/
theorem smithReducedRankDeficient :
    (({ rows := [[2, 4, 6], [1, 2, 3], [3, 6, 9]] } : IntMatrix).applyOperations
        [ ElementaryOperation.rowOperation (ElementaryRowOperation.swapRows 0 1)
        , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 (-2))
        , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 2 (-3))
        , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 1 (-2))
        , ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple 0 2 (-3)) ]).IsSmithNormalFormWithin 3 3 :=
  show ({ rows := [[1, 0, 0], [0, 0, 0], [0, 0, 0]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0], [0, 0, 0], [0, 0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by
        decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | 1, _ => ⟨0, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

/-! ## Rectangularity preservation + the totality statement (H2-SMITH r2, B3)

`IsRectangular` (equal-length rows) is load-bearing for the totalisation: the exact-clear arithmetic
(`addScaledEntriesCancel`) and the transvection round-trip need the source and target rows to share a
length, which rectangularity supplies.  `applyOperationsPreservesRectangular` discharges the
prerequisite the recon flags "build FIRST": every alphabet letter is length-preserving on the outer
row list AND on each row, so a whole certificate word carries `height x width` rectangularity from
the input to the output.  The proof is structural — a stack of length lemmas
(`listReplaceAt`/`listModifyAt`/`mapAllRows`/`addScaledEntries`/`swapEntriesWithinRow` preserve
lengths) plus width-preservation lemmas over `rowsAllHaveWidth`, then per-letter guard navigation.

`SmithReduceTotalStatement` NAMES the driver's total-correctness goal as a first-class `Prop` — that
`smithReduce` emits a Smith-reducing word for EVERY rectangular integer matrix.  It is the honest r3
RESIDUAL: r2 ships the cascade certificates (the three r1 failures reduce), the strict-descent
measure, and this rectangularity prerequisite; the full two-level induction (outer pivot budget,
inner Euclid fuel) that inhabits `SmithReduceTotalStatement` is the next round's pole (the recon's
Risk 1 — a full verified elimination theorem). -/

/-- `listReplaceAt` preserves the outer length — it never grows or shrinks the list. -/
theorem listReplaceAtPreservesLength {Entry : Type} :
    ∀ (entries : List Entry) (position : Nat) (newEntry : Entry),
      (listReplaceAt entries position newEntry).length = entries.length
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: remainingEntries, position + 1, newEntry =>
      congrArg (· + 1) (listReplaceAtPreservesLength remainingEntries position newEntry)

/-- `listModifyAt` preserves the outer length — it transforms in place. -/
theorem listModifyAtPreservesLength {Entry : Type} (transform : Entry → Entry) :
    ∀ (entries : List Entry) (position : Nat),
      (listModifyAt transform entries position).length = entries.length
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: remainingEntries, position + 1 =>
      congrArg (· + 1) (listModifyAtPreservesLength transform remainingEntries position)

/-- `mapAllRows` preserves the row count. -/
theorem mapAllRowsPreservesLength (transform : IntRow → IntRow) :
    ∀ rows : List IntRow, (mapAllRows transform rows).length = rows.length
  | [] => rfl
  | _ :: remainingRows => congrArg (· + 1) (mapAllRowsPreservesLength transform remainingRows)

/-- `List.map` preserves length (self-contained, for the `negateRow` width step). -/
theorem listMapPreservesLength {Source Target : Type} (transform : Source → Target) :
    ∀ entries : List Source, (entries.map transform).length = entries.length
  | [] => rfl
  | _ :: remainingEntries => congrArg (· + 1) (listMapPreservesLength transform remainingEntries)

/-- `addScaledEntries` preserves the target row's length when the rows agree in length. -/
theorem addScaledEntriesPreservesLength (coefficient : Int) :
    ∀ sourceRow targetRow : IntRow, sourceRow.length = targetRow.length →
      (addScaledEntries coefficient sourceRow targetRow).length = targetRow.length
  | [], [], _ => rfl
  | [], _ :: _, lengthsAgree => nomatch lengthsAgree
  | _ :: _, [], lengthsAgree => nomatch lengthsAgree
  | _ :: sourceRemaining, _ :: targetRemaining, lengthsAgree =>
      congrArg (· + 1)
        (addScaledEntriesPreservesLength coefficient sourceRemaining targetRemaining
          (Nat.succ.inj lengthsAgree))

/-- A within-row column swap preserves the row's length. -/
theorem swapEntriesWithinRowPreservesLength (row : IntRow) (firstIndex secondIndex : Nat) :
    (swapEntriesWithinRow row firstIndex secondIndex).length = row.length := by
  unfold swapEntriesWithinRow
  split
  · split
    · exact (listReplaceAtPreservesLength _ _ _).trans (listReplaceAtPreservesLength _ _ _)
    · rfl
  · rfl

/-- A within-row column transvection preserves the row's length. -/
theorem addScaledEntryWithinRowPreservesLength (row : IntRow)
    (sourceIndex targetIndex : Nat) (coefficient : Int) :
    (addScaledEntryWithinRow row sourceIndex targetIndex coefficient).length = row.length := by
  unfold addScaledEntryWithinRow
  split
  · exact listModifyAtPreservesLength _ _ _
  · rfl

/-- `listModifyAt` preserves `rowsAllHaveWidth` when the transform keeps a width-`width` row's
width. -/
theorem listModifyAtPreservesRowsWidth {width : Nat} (transform : IntRow → IntRow)
    (transformKeepsWidth : ∀ row : IntRow, row.length = width → (transform row).length = width) :
    ∀ (rows : List IntRow) (position : Nat),
      rowsAllHaveWidth width rows → rowsAllHaveWidth width (listModifyAt transform rows position)
  | [], 0, allHaveWidth => allHaveWidth
  | [], _ + 1, allHaveWidth => allHaveWidth
  | row :: _, 0, ⟨rowHasWidth, restHaveWidth⟩ => ⟨transformKeepsWidth row rowHasWidth, restHaveWidth⟩
  | _ :: remainingRows, position + 1, ⟨rowHasWidth, restHaveWidth⟩ =>
      ⟨rowHasWidth,
        listModifyAtPreservesRowsWidth transform transformKeepsWidth remainingRows position
          restHaveWidth⟩

/-- `listReplaceAt` preserves `rowsAllHaveWidth` when the replacement row has the right width. -/
theorem listReplaceAtPreservesRowsWidth {width : Nat} {newRow : IntRow}
    (newRowHasWidth : newRow.length = width) :
    ∀ (rows : List IntRow) (position : Nat),
      rowsAllHaveWidth width rows → rowsAllHaveWidth width (listReplaceAt rows position newRow)
  | [], 0, allHaveWidth => allHaveWidth
  | [], _ + 1, allHaveWidth => allHaveWidth
  | _ :: _, 0, ⟨_, restHaveWidth⟩ => ⟨newRowHasWidth, restHaveWidth⟩
  | _ :: remainingRows, position + 1, ⟨rowHasWidth, restHaveWidth⟩ =>
      ⟨rowHasWidth, listReplaceAtPreservesRowsWidth newRowHasWidth remainingRows position restHaveWidth⟩

/-- `mapAllRows` preserves `rowsAllHaveWidth` when the transform keeps a width-`width` row's width. -/
theorem mapAllRowsPreservesRowsWidth {width : Nat} (transform : IntRow → IntRow)
    (transformKeepsWidth : ∀ row : IntRow, row.length = width → (transform row).length = width) :
    ∀ rows : List IntRow,
      rowsAllHaveWidth width rows → rowsAllHaveWidth width (mapAllRows transform rows)
  | [], allHaveWidth => allHaveWidth
  | _ :: remainingRows, ⟨rowHasWidth, restHaveWidth⟩ =>
      ⟨transformKeepsWidth _ rowHasWidth,
        mapAllRowsPreservesRowsWidth transform transformKeepsWidth remainingRows restHaveWidth⟩

/-- An in-range row read has the declared width (the swap letter's swapped-in rows). -/
theorem listGetWithDefaultHasWidth {width : Nat} :
    ∀ (rows : List IntRow) (position : Nat),
      rowsAllHaveWidth width rows → position < rows.length →
      (listGetWithDefault [] rows position).length = width
  | [], _, _, isInRange => Nat.noConfusion (natEqZeroOfLeZero isInRange)
  | _ :: _, 0, ⟨rowHasWidth, _⟩, _ => rowHasWidth
  | _ :: remainingRows, position + 1, ⟨_, restHaveWidth⟩, isInRange =>
      listGetWithDefaultHasWidth remainingRows position restHaveWidth (natLeOfSuccLeSucc isInRange)

/-- Every row letter preserves rectangularity. -/
theorem applyRowOperationPreservesRectangular {height width : Nat}
    (operation : ElementaryRowOperation) (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width) :
    (matrix.applyRowOperation operation).IsRectangular height width := by
  obtain ⟨rowCount, rowWidths⟩ := isRect
  cases operation with
  | swapRows firstIndex secondIndex =>
      show (matrix.swapRows firstIndex secondIndex).IsRectangular height width
      unfold IntMatrix.swapRows
      split
      · rename_i isFirstInRange
        split
        · rename_i isSecondInRange
          exact ⟨(listReplaceAtPreservesLength _ _ _).trans
              ((listReplaceAtPreservesLength _ _ _).trans rowCount),
            listReplaceAtPreservesRowsWidth
              (listGetWithDefaultHasWidth matrix.rows firstIndex rowWidths isFirstInRange) _ _
              (listReplaceAtPreservesRowsWidth
                (listGetWithDefaultHasWidth matrix.rows secondIndex rowWidths isSecondInRange) _ _
                rowWidths)⟩
        · exact ⟨rowCount, rowWidths⟩
      · exact ⟨rowCount, rowWidths⟩
  | negateRow rowIndex =>
      show (matrix.negateRow rowIndex).IsRectangular height width
      exact ⟨(listModifyAtPreservesLength _ _ _).trans rowCount,
        listModifyAtPreservesRowsWidth _ (fun row rowHasWidth => (listMapPreservesLength _ row).trans rowHasWidth)
          matrix.rows rowIndex rowWidths⟩
  | addRowMultiple sourceIndex targetIndex coefficient =>
      show (matrix.addRowMultiple sourceIndex targetIndex coefficient).IsRectangular height width
      unfold IntMatrix.addRowMultiple
      split
      · exact ⟨rowCount, rowWidths⟩
      · split
        · rename_i isSourceInRange
          split
          · exact ⟨(listModifyAtPreservesLength _ _ _).trans rowCount,
              listModifyAtPreservesRowsWidth _
                (fun row rowHasWidth =>
                  (addScaledEntriesPreservesLength coefficient _ row
                    ((listGetWithDefaultHasWidth matrix.rows sourceIndex rowWidths isSourceInRange).trans
                      rowHasWidth.symm)).trans rowHasWidth)
                matrix.rows targetIndex rowWidths⟩
          · exact ⟨rowCount, rowWidths⟩
        · exact ⟨rowCount, rowWidths⟩

/-- Every column letter preserves rectangularity. -/
theorem applyColumnOperationPreservesRectangular {height width : Nat}
    (operation : ElementaryColumnOperation) (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width) :
    (matrix.applyColumnOperation operation).IsRectangular height width := by
  obtain ⟨rowCount, rowWidths⟩ := isRect
  cases operation with
  | swapColumns firstIndex secondIndex =>
      show (matrix.swapColumns firstIndex secondIndex).IsRectangular height width
      exact ⟨(mapAllRowsPreservesLength _ _).trans rowCount,
        mapAllRowsPreservesRowsWidth _
          (fun row rowHasWidth => (swapEntriesWithinRowPreservesLength row firstIndex secondIndex).trans rowHasWidth)
          matrix.rows rowWidths⟩
  | negateColumn colIndex =>
      show (matrix.negateColumn colIndex).IsRectangular height width
      exact ⟨(mapAllRowsPreservesLength _ _).trans rowCount,
        mapAllRowsPreservesRowsWidth _
          (fun row rowHasWidth => (listModifyAtPreservesLength _ row colIndex).trans rowHasWidth)
          matrix.rows rowWidths⟩
  | addColumnMultiple sourceIndex targetIndex coefficient =>
      show (matrix.addColumnMultiple sourceIndex targetIndex coefficient).IsRectangular height width
      unfold IntMatrix.addColumnMultiple
      split
      · exact ⟨rowCount, rowWidths⟩
      · exact ⟨(mapAllRowsPreservesLength _ _).trans rowCount,
          mapAllRowsPreservesRowsWidth _
            (fun row rowHasWidth =>
              (addScaledEntryWithinRowPreservesLength row sourceIndex targetIndex coefficient).trans
                rowHasWidth)
            matrix.rows rowWidths⟩

/-- One certificate step preserves rectangularity — dispatch to the row/column half. -/
theorem applyOperationPreservesRectangular {height width : Nat} (operation : ElementaryOperation)
    (matrix : IntMatrix) (isRect : matrix.IsRectangular height width) :
    (matrix.applyOperation operation).IsRectangular height width := by
  cases operation with
  | rowOperation operation => exact applyRowOperationPreservesRectangular operation matrix isRect
  | columnOperation operation => exact applyColumnOperationPreservesRectangular operation matrix isRect

/-- **Rectangularity is preserved by a whole certificate word** — the r3 totalisation
prerequisite: `applyOperations` carries `height x width` shape from input to output, so the
exact-clear arithmetic and transvection round-trips always see equal-length rows. -/
theorem applyOperationsPreservesRectangular {height width : Nat} :
    ∀ (word : List ElementaryOperation) (matrix : IntMatrix),
      matrix.IsRectangular height width →
      (matrix.applyOperations word).IsRectangular height width
  | [], _, isRect => isRect
  | operation :: remainingOperations, matrix, isRect =>
      applyOperationsPreservesRectangular remainingOperations (matrix.applyOperation operation)
        (applyOperationPreservesRectangular operation matrix isRect)

/-- **The total-correctness goal named over the r1 driver** — that `smithReduce` emits a
Smith-reducing word for every rectangular integer matrix.  As stated (over the ONE-SHOT `smithReduce`)
this `Prop` is REFUTABLE: the r1 driver stalls on `[[6, 4], [0, 0]]` — see `smithReduceIsNotTotal`
below, which inhabits its negation.  The r3 correction re-points the goal at the total driver as
`SmithReduceTotalDriverStatement`; this def is kept (name and meaning unchanged) so the refutation has
a subject.  r2 ships the strict-descent measure (`smithRotationDecreasesPivotSize`), the cascade
certificates, and the rectangularity prerequisite (`applyOperationsPreservesRectangular`). -/
def SmithReduceTotalStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    (smithReduce matrix height width).reducesToSmithForm matrix height width

/-! ## The walker teaser: a degree-2 boundary map's torsion + free read-off (H2-SMITH r2, B4)

The H2-CHAIN framing (H2-SMITH's sibling #2136, frontiers.md Domain XI) reads a polygraphic degree-2
boundary `∂₂ : C₂ → C₁` as an integer matrix; its Smith normal form's diagonal `d₁ | d₂ | ...` reads
off the integral homology at that degree — `im ∂₂ ≅ ⨁ dᵢ·ℤ`, so the cokernel `C₁ / im ∂₂` is
`(⨁_{dᵢ > 1} ℤ / dᵢ·ℤ) ⊕ ℤ^(rankC₁ − #nonzero dᵢ)`: TORSION from each invariant factor above one, a
FREE summand from each zero column.  ℤ-coefficients see the torsion that the shipped 𝔽₂
`F2ChainComplex` cannot.

The r1 seed `smithExampleCyclicTwo` (`[[2]] ↝ [[2]]`) is the pure-`ℤ/2` torsion reading (the walking
involution's degree-2 seed).  This teaser is one rung richer: a representative degree-2 boundary
matrix whose SNF exhibits BOTH a torsion coefficient AND a free summand. -/

/-- **The torsion-plus-free boundary read-off** — the degree-2 boundary `[[2, 2], [2, 2]]` (rank one,
gcd `2`, determinant `0`) reduces to `diag(2, 0)`.  The homology read-off: `im ∂₂ ≅ 2·ℤ`, so
`H = ℤ/2 ⊕ ℤ` — a `ℤ/2` TORSION summand from the invariant factor `2`, plus one FREE `ℤ` from the
zero column.  The kernel-checked SNF the H2-WALKERS integral-homology lane consumes, one rung beyond
the `[[2]]` pure-`ℤ/2` seed. -/
theorem smithExampleBoundaryMap :
    (({ rows := [[2, 2], [2, 2]] } : IntMatrix).applyOperations
        [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 (-1))
        , ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple 0 1 (-1)) ]).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-! ## The r3 driver-produced battery + the corrected totality target (H2-SMITH r3, B1/B2/B4)

`smithReduceTotal` reduces the FULL r1/r2 battery BY THE DRIVER: every input the r1 one-shot
`smithReduce` could only diagonalise by a HAND-WRITTEN word now reduces by the driver's emitted
certificate, closed against the literal Smith normal form by defeq (the driver computes to the
literal; corroborated live by the r1-battery `#eval` regression).  The five theorems below re-close
the three r2 failures, the walker boundary map, and the B3 non-square member as DRIVER-produced
certificates, superseding the hand-word `smithReducedEuclideanRow` / `smithReducedSignedDiagonal` /
`smithReducedRankDeficient` / `smithExampleBoundaryMap` (kept, name and meaning unchanged, for
history).

**B2 (totality).**  `SmithReduceTotalStatement` names the goal over the WRONG driver — the one-shot
`smithReduce` is not total.  `smithReduceIsNotTotal` proves that Prop FALSE by the `[[6, 4], [0, 0]]`
witness (`smithReduce` leaves the `4`; the reduced `entryAt 0 1` computes to `4 ≠ 0`).
`SmithReduceTotalDriverStatement` re-points the goal at `smithReduceTotal`; its inhabitant is the
two-level induction (outer pivot budget structural on `Nat.min height width`, inner Euclid cascade
structural on the minor magnitude sum), riding the shipped `applyOperationsPreservesRectangular` and
`smithRotationDecreasesPivotSize`.  That inhabitant is NOT shipped this round — the honest r4 pole.

**B4 (divisibility chain), honest deferral.**  The cascade clears each pivot's CROSS (its own row and
column), so the driver reaches a DIAGONAL with each pivot dividing its cross and nonnegative — but NOT
in general the full invariant-factor chain `d_p | d_{p+1}` that `IsSmithNormalFormWithin` demands: a
coprime diagonal like `[[2, 0], [0, 3]]` is left as `diag(2, 3)` (the driver's own `#eval` exhibits
this), which is off-diagonal-clear and nonnegative but is NOT Smith-normal.  Forcing the chain needs
the whole-minor divisibility-repair pass (add a non-multiple's row into the pivot row, re-Euclid) —
the named r4 residual.  Every r1/r2/B3 battery member is rank ≤ 1 or an already-divisible diagonal, so
the cross-only driver lands each in genuine Smith normal form (the driver-produced theorems below are
the kernel-checked witnesses); the chain gap is invisible to the battery, visible only to a coprime
multi-invariant input. -/

/-- **The Euclidean-row failure, driver-produced** — `smithReduceTotal` reduces `[[6, 4], [0, 0]]`
(`6 ∤ 4`, the r1 one-shot stall) to `diag(2, 0)`; the emitted certificate is kernel-checked into Smith
normal form, closed against the literal by defeq.  Supersedes the hand-word `smithReducedEuclideanRow`. -/
theorem smithReducedEuclideanRowByDriver :
    (({ rows := [[6, 4], [0, 0]] } : IntMatrix).applyOperations
        (smithReduceTotal { rows := [[6, 4], [0, 0]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **The rank-deficient pivot-search failure, driver-produced** — `smithReduceTotal` reduces the
rank-one `[[2, 4, 6], [1, 2, 3], [3, 6, 9]]` to `diag(1, 0, 0)`; the search swaps the unit `1` into
the pivot the r1 driver could not find.  Supersedes the hand-word `smithReducedRankDeficient`. -/
theorem smithReducedRankDeficientByDriver :
    (({ rows := [[2, 4, 6], [1, 2, 3], [3, 6, 9]] } : IntMatrix).applyOperations
        (smithReduceTotal { rows := [[2, 4, 6], [1, 2, 3], [3, 6, 9]] } 3 3).operations).IsSmithNormalFormWithin
      3 3 :=
  show ({ rows := [[1, 0, 0], [0, 0, 0], [0, 0, 0]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0], [0, 0, 0], [0, 0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by
        decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | 1, _ => ⟨0, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

/-- **The signed-diagonal failure, driver-produced** — `smithReduceTotal` normalises `diag(-2, -6)` to
`diag(2, 6)` by the sign pass (`negateRow` on each negative pivot); the chain `2 | 6` is `(6 : Int) =
2 * 3`.  Supersedes the hand-word `smithReducedSignedDiagonal`. -/
theorem smithReducedSignedDiagonalByDriver :
    (({ rows := [[-2, 0], [0, -6]] } : IntMatrix).applyOperations
        (smithReduceTotal { rows := [[-2, 0], [0, -6]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 6]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 6]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨3, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **The torsion-plus-free boundary map, driver-produced** — `smithReduceTotal` reduces the degree-2
boundary `[[2, 2], [2, 2]]` (rank one, gcd `2`) to `diag(2, 0)`: `im ∂₂ ≅ 2·ℤ`, so `H = ℤ/2 ⊕ ℤ`.
Supersedes the hand-word `smithExampleBoundaryMap`; the integral-homology read-off now rides the
driver. -/
theorem smithReducedBoundaryMapByDriver :
    (({ rows := [[2, 2], [2, 2]] } : IntMatrix).applyOperations
        (smithReduceTotal { rows := [[2, 2], [2, 2]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **The non-square member, driver-produced** — `smithReduceTotal` leaves the already-Smith-normal
`2 x 3` `diag(1, 2)`-with-free-column in place (the rectangular B3 member reduced BY THE DRIVER). -/
theorem smithReducedWideTwoByThreeByDriver :
    (({ rows := [[1, 0, 0], [0, 2, 0]] } : IntMatrix).applyOperations
        (smithReduceTotal { rows := [[1, 0, 0], [0, 2, 0]] } 2 3).operations).IsSmithNormalFormWithin 2 3 :=
  show ({ rows := [[1, 0, 0], [0, 2, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0], [0, 2, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨2, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **The r1 driver is not total** — `SmithReduceTotalStatement` (which names the one-shot
`smithReduce`) is FALSE: `[[6, 4], [0, 0]]` is rectangular yet `smithReduce` leaves the off-diagonal
`4` (the one-shot magnitude quotient `intPivotQuotient 6 4 = 0`), so the reduced `entryAt 0 1`
computes to `4`, contradicting `offDiagonalVanishes`.  This is why the corrected B2 target names the
total driver (`SmithReduceTotalDriverStatement`). -/
theorem smithReduceIsNotTotal : ¬ SmithReduceTotalStatement := fun isTotal =>
  have reducesToSmith :=
    isTotal { rows := [[6, 4], [0, 0]] } 2 2 ⟨rfl, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩
  absurd
    (((reducesToSmith.offDiagonalVanishes 0 1 (by decide) (by decide) (by decide)).symm).trans
      (rfl : (({ rows := [[6, 4], [0, 0]] } : IntMatrix).applyOperations
          (smithReduce { rows := [[6, 4], [0, 0]] } 2 2).operations).entryAt 0 1 = 4))
    (by decide)

/-- **The corrected totality target** — that the TOTAL driver `smithReduceTotal` emits a
Smith-reducing word for every rectangular integer matrix.  Its inhabitant is the two-level induction
(outer pivot budget structural on `Nat.min height width`; inner Euclid cascade structural on the minor
magnitude sum), riding `applyOperationsPreservesRectangular` (shipped) and
`smithRotationDecreasesPivotSize` (shipped).  NOT inhabited this round — the honest r4 pole; the exact
remaining obligations are (i) the outer-step LOCALITY lemma (minor ops at indices `> pivotIndex` leave
the settled pivot row/column fixed), and (ii) the whole-minor divisibility repair that forces the
`d_p | d_{p+1}` chain (B4), without which even the total driver falls short on coprime diagonals. -/
def SmithReduceTotalDriverStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    (smithReduceTotal matrix height width).reducesToSmithForm matrix height width

end FX1Poly.ComputerAlgebra
