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

/-! ## The divisibility-repair pass + the augmented driver (H2-SMITH r4, B1)

`smithReduceTotal` clears each pivot's CROSS, reaching a nonnegative DIAGONAL — but not the
invariant-factor CHAIN `d_p | d_q` that Smith normal form demands: a coprime diagonal like
`diag(2, 3)` is left in place (off-diagonal-clear, nonnegative, yet `2 ∤ 3`), so
`SmithReduceTotalDriverStatement` is REFUTABLE (`smithReduceTotalIsNotFullyReducing`, footer).  This
pass runs a SEPARATE TOP-DOWN full-settle sweep on the already-diagonal output: at each position `p`,
while some later diagonal entry `d_q` (`q > p`) is not divisible by `d_p`, FOLD row `q` into pivot row
`p` (one row transvection, so the coprime pair `(d_p, d_q)` now shares the pivot row) and re-fire the
shipped `smithCascadeSweep` at `p` — landing `gcd(d_p, d_q)` at the pivot and pushing `lcm` down.  A
final diagonal sign sweep repairs the transient negatives the Euclid clears leave behind.

TOP-DOWN (settle `d_p` against EVERY later entry before advancing), not bottom-up: once `d_p` divides
all later entries it stays so (later settles only combine those entries by gcd/lcm, both divisible by
`d_p`).  SEPARATE post-pass, not interleaved: `smithReduceTotal` stays byte-identical, so its five
driver-produced battery theorems stay green by defeq.  The entire repair REUSES `smithCascadeSweep`
verbatim — NO new elimination arm.  STRUCTURAL fuel throughout (no `WellFounded.fix`): the outer
sweeps ride the pivot budget `Nat.min height width`, the per-position fold loop rides the minor
magnitude sum `smithMinorAbsSum` recomputed at position entry (each genuine fold strictly drops the
pivot magnitude — `gcd(d_p, d_q) < d_p` when `d_p ∤ d_q` — so the fold count is bounded by that
per-position pivot, NOT by the whole-matrix sum, which the pushed-down `lcm` can exceed).  Correctness
is the untrusted producer's — CHECKED per input by the B4 driver-produced battery. -/

/-- Does the pivot diagonal entry `pivotEntry` divide the later diagonal entry `laterEntry` over ZZ?
`0` divides only `0`; otherwise the magnitude remainder of `laterEntry` by `|pivotEntry|` vanishes. -/
def smithPivotDividesEntry (pivotEntry laterEntry : Int) : Bool :=
  if pivotEntry.natAbs == 0 then laterEntry.natAbs == 0
  else intMagnitudeRemainder pivotEntry.natAbs laterEntry == 0

/-- Scan the `scanCount` later diagonal positions from `scanStart` for the first whose entry the pivot
does not divide (the target of the next fold), or `none` when the pivot already divides all of them.
Structural on the count. -/
def smithFindNonDividingLaterDiagonal (matrix : IntMatrix) (pivotIndex : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | scanCount + 1, scanStart =>
      if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.diagonalEntryAt scanStart) then
        smithFindNonDividingLaterDiagonal matrix pivotIndex scanCount (scanStart + 1)
      else some scanStart

/-- One position's divisibility repair: while a later diagonal entry is not divided by the pivot, fold
that entry's row into the pivot row (`addRowMultiple foundPos pivotIndex 1`) and re-fire the shipped
Euclid cascade at the pivot, then loop on the reduced matrix with one less fuel.  Structural on
`fuel`. -/
def smithRepairPositionSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | fuel + 1, matrix, pivotIndex, height, width =>
      match smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) with
      | none => []
      | some foundPos =>
          let foldOps :=
            [ ElementaryOperation.rowOperation
                (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ]
          let afterFold := matrix.applyOperations foldOps
          let clearOps :=
            smithCascadeSweep (smithMinorAbsSum afterFold pivotIndex height width)
              afterFold pivotIndex height width
          let afterClear := afterFold.applyOperations clearOps
          foldOps ++ clearOps ++ smithRepairPositionSweep fuel afterClear pivotIndex height width

/-- The top-down divisibility-repair sweep: at each pivot run the position repair (fuelled by the minor
magnitude sum), thread the reduced matrix, and recurse on the next pivot.  Structural on `outerFuel`
(the pivot budget). -/
def smithDivisibilityRepairSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | outerFuel + 1, matrix, pivotIndex, height, width =>
      if pivotIndex + 1 ≤ Nat.min height width then
        let positionOps :=
          smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width
        let afterPosition := matrix.applyOperations positionOps
        positionOps ++
          smithDivisibilityRepairSweep outerFuel afterPosition (pivotIndex + 1) height width
      else []

/-- The final diagonal sign sweep: negate each negative diagonal pivot so the repaired diagonal is
nonnegative (the Euclid clears leave transient negatives).  Structural on `fuel` (the pivot budget). -/
def smithDiagonalSignSweep : Nat → IntMatrix → Nat → Nat → Nat → List ElementaryOperation
  | 0, _, _, _, _ => []
  | fuel + 1, matrix, pivotIndex, height, width =>
      if pivotIndex + 1 ≤ Nat.min height width then
        let signOps := smithSignNormalizeOps matrix pivotIndex
        signOps ++
          smithDiagonalSignSweep fuel (matrix.applyOperations signOps) (pivotIndex + 1) height width
      else []

/-- The augmented total driver: the cross-clearing `smithReduceTotal`, then the top-down
divisibility-repair sweep, then the final sign sweep — the full classical Smith reduction.  Each phase
is fuelled by the pivot budget `Nat.min height width` (the repair's per-position inner fuel is the
minor magnitude sum, recomputed at position entry).  The r4 driver whose B4 battery lands the coprime
diagonals `smithReduceTotal` stalls on. -/
def smithReduceFull (matrix : IntMatrix) (height width : Nat) : SmithReductionCertificate :=
  let diagOps := (smithReduceTotal matrix height width).operations
  let afterDiag := matrix.applyOperations diagOps
  let repairOps := smithDivisibilityRepairSweep (Nat.min height width) afterDiag 0 height width
  let afterRepair := afterDiag.applyOperations repairOps
  let signOps := smithDiagonalSignSweep (Nat.min height width) afterRepair 0 height width
  { operations := diagOps ++ repairOps ++ signOps }

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

/-! ## The crosses-stay-zero locality core (H2-SMITH r4, B2)

The augmented driver's totality induction (B3) needs to know that repairing position `p` — the fold
`addRowMultiple foundPos pivotIndex 1` (`foundPos > pivotIndex`) plus the re-fired cascade — leaves
every ALREADY-SETTLED pivot `settled < p` fixed.  The fold is a ROW transvection whose TARGET is the
pivot row `p`; it modifies only that row.  So every settled pivot's WHOLE ROW (index `settled ≠ p`) —
its diagonal entry `d_settled` and its cross's row-part — is untouched.  That is the load-bearing new
lemma below (`addRowMultiplePreservesEntryOffTargetRow`), resting on the atomic list locality
`listGetWithDefaultModifyAtNe` (reading at an index the modify skipped is unchanged).

This closes the fold's ROW half of crosses-stay-zero UNCONDITIONALLY (no diagonal hypothesis).  The
remaining half — that the fold leaves the settled COLUMN entry `(p, settled)` zero — is semantic: it
holds because `(foundPos, settled) = 0` in the diagonal the repair runs on (`foundPos > p > settled`),
so it rides the INV-DIAG invariant of the induction, named in the B3 residual footer. -/

/-- Atomic list locality: reading at an index the modify did not touch returns the original entry —
`listModifyAt` only rewrites `position`, so a read at any `index ≠ position` is unchanged.  Structural
on the list. -/
theorem listGetWithDefaultModifyAtNe {Entry : Type} (defaultEntry : Entry)
    (transform : Entry → Entry) :
    ∀ (entries : List Entry) (position index : Nat), index ≠ position →
      listGetWithDefault defaultEntry (listModifyAt transform entries position) index
        = listGetWithDefault defaultEntry entries index
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, 0, indexIsNotPosition => absurd rfl indexIsNotPosition
  | _ :: _, 0, _ + 1, _ => rfl
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: remainingEntries, position + 1, index + 1, indexIsNotPosition =>
      listGetWithDefaultModifyAtNe defaultEntry transform remainingEntries position index
        (fun successorsAgree => indexIsNotPosition (congrArg (· + 1) successorsAgree))

/-- **The repair transvection's row locality (the crosses-stay-zero core)** — the fold
`addRowMultiple sourceIndex targetIndex coefficient` modifies ONLY the target row, so every entry in a
row other than the target is untouched.  With `targetIndex := pivotIndex` and a settled pivot
`rowIndex := settled < pivotIndex` (`settled ≠ pivotIndex`), this says the repair fold leaves every
settled pivot's whole row — its diagonal entry and its cross's row-part — fixed.  The proof navigates
`addRowMultiple`'s three guards; the live branch rewrites the read row by `listGetWithDefaultModifyAtNe`
at the off-target index. -/
theorem addRowMultiplePreservesEntryOffTargetRow (matrix : IntMatrix)
    (sourceIndex targetIndex : Nat) (coefficient : Int) (rowIndex colIndex : Nat)
    (isOffTarget : rowIndex ≠ targetIndex) :
    (matrix.addRowMultiple sourceIndex targetIndex coefficient).entryAt rowIndex colIndex
      = matrix.entryAt rowIndex colIndex := by
  unfold IntMatrix.addRowMultiple
  split
  · rfl
  · split
    · split
      · show listGetWithDefault 0
            (listGetWithDefault [] (listModifyAt _ matrix.rows targetIndex) rowIndex) colIndex = _
        exact congrArg (fun readRow => listGetWithDefault 0 readRow colIndex)
          (listGetWithDefaultModifyAtNe [] _ matrix.rows targetIndex rowIndex isOffTarget)
      · rfl
    · rfl

/-! ## The r4 refutation + driver-produced battery + the augmented totality target (B4/B3)

`smithReduceTotalIsNotFullyReducing` proves `SmithReduceTotalDriverStatement` FALSE — the cross-only
total driver leaves the coprime diagonal `diag(2, 3)` unrepaired, so its `diagonalDividesSuccessor 0`
would need `dividesExactly 2 3`, refuted by pushing the `∃`-witness through `natAbs`
(`intNatAbsMul`) to `NatDivides 2 3` and collapsing the counting remainder
(`natDividesRemainderIsZero`, which computes to `1 ≠ 0`).  This mirrors the r1→r3 honesty move
(`smithReduceIsNotTotal` refuted the one-shot driver) one rung up: r3's cross-only driver is not
CHAIN-total.

The battery reduces the three MANDATED coprime probes plus a multi-invariant `3 × 3` BY THE AUGMENTED
DRIVER `smithReduceFull`, each closed against its literal Smith normal form by defeq (`smithReduceFull`
computes to the literal; corroborated live by the prototype `#eval` regression), with hand-built
divisibility witnesses and `decide` on the LITERAL.  The full-driver regression members re-close the
already-Smith / rank-deficient inputs against `smithReduceFull` (the repair + sign passes are no-ops on
them), and every r1/r2/r3 battery theorem stays green untouched (`smithReduceTotal` is byte-identical).

`SmithReduceFullDriverStatement` names the augmented driver's total-correctness goal — the honest B3
node whose inhabitant is the r5 pole (footer). -/

/-- **The cross-only total driver is not CHAIN-reducing** — `SmithReduceTotalDriverStatement` is FALSE:
`[[2, 0], [0, 3]]` is rectangular and `smithReduceTotal` leaves it as `diag(2, 3)` (off-diagonal-clear,
nonnegative — the cross is already zero, so the driver is a no-op), but Smith normal form needs
`2 | 3`.  The refutation reads off `diagonalDividesSuccessor 0`'s witness `⟨factor, (3 : Int) = 2 *
factor⟩`, pushes it through `natAbs` (`intNatAbsMul`) to `NatDivides 2 3`, and collapses the counting
remainder (`natDividesRemainderIsZero`, computing to `1 ≠ 0`).  This is why the corrected B3 target
names the AUGMENTED driver (`SmithReduceFullDriverStatement`). -/
theorem smithReduceTotalIsNotFullyReducing : ¬ SmithReduceTotalDriverStatement := fun isTotal =>
  match (isTotal { rows := [[2, 0], [0, 3]] } 2 2
      ⟨rfl, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩).diagonalDividesSuccessor 0 (by decide) with
  | ⟨factor, threeEqTwoFactor⟩ =>
      have dividesNat : NatDivides 2 3 :=
        ⟨factor.natAbs, (congrArg Int.natAbs threeEqTwoFactor).trans (intNatAbsMul 2 factor)⟩
      absurd (natDividesRemainderIsZero (by decide) dividesNat) (by decide)

/-- **Coprime `diag(2, 3)`, augmented-driver-produced** — `smithReduceFull` repairs `diag(2, 3)` (which
the cross-only driver leaves untouched) to `diag(1, 6)`: the fold injects `3` into the pivot row, the
re-fired cascade Euclid-clears `(2, 3)` to `gcd = 1` and pushes `lcm = 6` down.  Chain `1 | 6` is
`(6 : Int) = 1 * 6`. -/
theorem smithReducedCoprimeTwoThreeByDriver :
    (({ rows := [[2, 0], [0, 3]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[2, 0], [0, 3]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[1, 0], [0, 6]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0], [0, 6]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨6, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **Coprime `diag(6, 10)`, augmented-driver-produced** — reduces to `diag(2, 30)` (`gcd(6, 10) = 2`,
`lcm = 30`).  Chain `2 | 30` is `(30 : Int) = 2 * 15`. -/
theorem smithReducedCoprimeSixTenByDriver :
    (({ rows := [[6, 0], [0, 10]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[6, 0], [0, 10]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 30]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 30]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨15, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **Coprime `diag(4, 6)`, augmented-driver-produced** — reduces to `diag(2, 12)` (`gcd(4, 6) = 2`,
`lcm = 12`).  Chain `2 | 12` is `(12 : Int) = 2 * 6`. -/
theorem smithReducedCoprimeFourSixByDriver :
    (({ rows := [[4, 0], [0, 6]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[4, 0], [0, 6]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 12]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0], [0, 12]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨6, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **Multi-invariant `diag(4, 6, 9)`, augmented-driver-produced** — the `3 × 3` stress case exercising
a MULTI-FOLD settle and sub-block re-diagonalization: settling position 0 folds BOTH `d_1 = 6` and
`d_2 = 9` into the pivot (`4 ∤ 9`), landing `gcd(4, 6, 9) = 1` at the pivot and re-diagonalizing the
sub-block to `diag(6, 36)`.  Result `diag(1, 6, 36)`; chains `1 | 6` (`6 = 1 * 6`) and `6 | 36`
(`36 = 6 * 6`). -/
theorem smithReducedCoprimeChainByFullDriver :
    (({ rows := [[4, 0, 0], [0, 6, 0], [0, 0, 9]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[4, 0, 0], [0, 6, 0], [0, 0, 9]] } 3 3).operations).IsSmithNormalFormWithin
      3 3 :=
  show ({ rows := [[1, 0, 0], [0, 6, 0], [0, 0, 36]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0], [0, 6, 0], [0, 0, 36]] } : IntMatrix).entryAt rowIndex colIndex = 0 :=
        by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨6, rfl⟩
      | 1, _ => ⟨6, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

/-- **Regression: already-divisible `diag(2, 4)`, augmented-driver-produced** — `smithReduceFull` is a
no-op on an already-Smith diagonal (the repair finds no non-dividing later entry, the sign sweep no-ops
on nonnegatives), leaving `diag(2, 4)`.  Chain `2 | 4` is `(4 : Int) = 2 * 2`. -/
theorem smithReducedAlreadyDivisibleByFullDriver :
    (({ rows := [[2, 0], [0, 4]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[2, 0], [0, 4]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  show ({ rows := [[2, 0], [0, 4]] } : IntMatrix).IsSmithNormalFormWithin 2 2 from
  { offDiagonalVanishes := by
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
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-- **Regression: Euclidean-row `[[6, 4], [0, 0]]`, augmented-driver-produced** — `smithReduceFull`
reduces it to `diag(2, 0)` (the cross-clear phase already lands it; repair and sign no-op).  Chain
`2 | 0` is `(0 : Int) = 2 * 0`. -/
theorem smithReducedEuclideanRowByFullDriver :
    (({ rows := [[6, 4], [0, 0]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[6, 4], [0, 0]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
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

/-- **Regression: non-square `[[1, 0, 0], [0, 2, 0]]`, augmented-driver-produced** — `smithReduceFull`
leaves the already-Smith `2 × 3` `diag(1, 2)`-with-free-column in place. -/
theorem smithReducedWideByFullDriver :
    (({ rows := [[1, 0, 0], [0, 2, 0]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[1, 0, 0], [0, 2, 0]] } 2 3).operations).IsSmithNormalFormWithin 2 3 :=
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

/-- **Regression: signed `diag(-2, -6)`, augmented-driver-produced** — `smithReduceFull` normalises the
negative pivots to `diag(2, 6)` (the sign phase negates each negative diagonal; the already-divisible
chain needs no repair).  Chain `2 | 6` is `(6 : Int) = 2 * 3`. -/
theorem smithReducedSignedByFullDriver :
    (({ rows := [[-2, 0], [0, -6]] } : IntMatrix).applyOperations
        (smithReduceFull { rows := [[-2, 0], [0, -6]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
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

/-- **The augmented totality target (H2-SMITH r4, B3)** — that the augmented driver `smithReduceFull`
emits a Smith-reducing word for every rectangular integer matrix.  This is the honest B3 NODE; its
inhabitant is the THREE-LEVEL structural induction

  * OUTER `smithDivisibilityRepairSweep`, structural on the pivot budget `Nat.min height width`;
  * MIDDLE `smithRepairPositionSweep`, structural on the per-position minor magnitude sum (each genuine
    fold strictly drops the pivot magnitude, `gcd(d_p, d_q).natAbs < d_p.natAbs` when `d_p ∤ d_q`, via
    the shipped `intGcdDividesLeft` + `Nat.le.intro` pattern — the r5 lemma
    `smithRepairDecreasesPivotSize`);
  * INNER `smithCascadeSweep` (SHIPPED), structural on `smithMinorAbsSum`, riding
    `smithRotationDecreasesPivotSize`,

carried by the invariants INV-DIAG (window stays diagonal), INV-CHAIN-PREFIX (`d_i | d_q` for all
`i < p`, `q > i`), and INV-RECT (`applyOperationsPreservesRectangular`, shipped).  It is NOT inhabited
this round — the honest r5 pole.  The EXACT remaining obligations are:

  (a) [HIGH, shared with the r3 pole] `smithCascadeSweep` RE-DIAGONALIZES after a fold — clearing the
      pivot cross AND leaving the sub-block `≥ p+1` diagonal with `gcd` at the pivot (empirically true
      on every probe incl. `3 × 3`, but a general proof is the deep elimination-correctness lemma r3
      also deferred);
  (b) [the semantic COLUMN half of crosses-stay-zero] the fold leaves the settled column entry
      `(p, settled) = 0` — it does because `(foundPos, settled) = 0` in the diagonal INV-DIAG supplies
      (`foundPos > p > settled`); its ROW half is the shipped B2 lemma
      `addRowMultiplePreservesEntryOffTargetRow`;
  (c) [MIDDLE-level top-down monotonicity] once `d_p` divides every later entry it stays so under later
      settles (later gcd/lcm combinations of multiples of `d_p` remain multiples of `d_p`) — the
      single-pass-soundness fact.

The B4 battery sidesteps all three by defeq on the literal reductions; B2 discharges (b)'s row half and
the descent measure of (a)/(middle) is the shipped `smithRotationDecreasesPivotSize`. -/
def SmithReduceFullDriverStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    (smithReduceFull matrix height width).reducesToSmithForm matrix height width

/-! ## The r5 totality decomposition — substrate append + the middle-level descent measure (B1/B2)

The recon's build-FIRST substrate prerequisite and the one clean, self-contained descent lemma the
three-level induction rides.  `smithReduceFull` composes its three phases as `diagOps ++ repairOps ++
signOps` (and each phase composes its own sub-words), so every phase-boundary step needs to split
`applyOperations` across a `++` — the missing `applyOperationsAppend` below (only
`applyOperationsPreservesRectangular` previously spoke about `applyOperations`).  The MIDDLE-level
fold loop (`smithRepairPositionSweep`) rides `smithRepairDecreasesPivotSize`: each genuine fold lands
`gcd(d_p, d_q)` at the pivot, whose magnitude drops strictly below `d_p`'s exactly when `d_p ∤ d_q`
(if `d_p | d_q` the gcd IS `|d_p|` and no fold fires).  Pure Number-layer over the shipped
`natGcdDividesLeft` / `natGcdDividesRight` and the `Int`/`Nat` `natAbs` divisibility bridges — no
matrix machinery, no propext traps. -/

/-- **`applyOperations` distributes over word concatenation** — firing `leadingWord ++ trailingWord`
equals firing `leadingWord` then `trailingWord`.  The build-FIRST composition substrate every phase
boundary of `smithReduceFull` consumes; a 2-arm structural induction on `leadingWord` over the
`applyOperations` cons equation. -/
theorem applyOperationsAppend :
    ∀ (leadingWord trailingWord : List ElementaryOperation) (matrix : IntMatrix),
      matrix.applyOperations (leadingWord ++ trailingWord)
        = (matrix.applyOperations leadingWord).applyOperations trailingWord
  | [], _, _ => rfl
  | operation :: remainingOperations, trailingWord, matrix =>
      applyOperationsAppend remainingOperations trailingWord (matrix.applyOperation operation)

/-- **The Nat gcd sits strictly below a non-dividing left argument** — when `leftValue > 0` and
`leftValue ∤ rightValue`, `natGcd leftValue rightValue < leftValue`.  The gcd divides `leftValue`
(`natGcdDividesLeft`, cofactor `≥ 1` since `leftValue > 0`) giving `gcd ≤ leftValue`; equality would
make `leftValue = gcd` divide `rightValue` (`natGcdDividesRight`), contradicting the hypothesis, so
`gcd ≠ leftValue`.  `Nat.lt_of_le_of_ne` closes. -/
theorem natGcdLtLeftOfNotDivides (leftValue rightValue : Nat)
    (isLeftPositive : 0 < leftValue)
    (leftDoesNotDivide : ¬ NatDivides leftValue rightValue) :
    natGcd leftValue rightValue < leftValue :=
  match natGcdDividesLeft leftValue rightValue with
  | ⟨cofactor, leftEquation⟩ =>
      match cofactor, leftEquation with
      | 0, leftEquation =>
          have leftIsZero : leftValue = 0 :=
            leftEquation.trans (Nat.mul_zero (natGcd leftValue rightValue))
          absurd (Eq.mp (congrArg (0 < ·) leftIsZero) isLeftPositive) (Nat.lt_irrefl 0)
      | cofactorPredecessor + 1, leftEquation =>
          have gcdPlusReaches :
              natGcd leftValue rightValue
                + natGcd leftValue rightValue * cofactorPredecessor = leftValue :=
            (Nat.add_comm (natGcd leftValue rightValue)
                (natGcd leftValue rightValue * cofactorPredecessor)).trans
              ((Nat.mul_succ (natGcd leftValue rightValue) cofactorPredecessor).symm.trans
                leftEquation.symm)
          have gcdLeLeft : natGcd leftValue rightValue ≤ leftValue :=
            Nat.le.intro gcdPlusReaches
          have gcdNeLeft : natGcd leftValue rightValue ≠ leftValue := fun gcdEqLeft =>
            leftDoesNotDivide
              (Eq.mp (congrArg (fun divisor => NatDivides divisor rightValue) gcdEqLeft)
                (natGcdDividesRight leftValue rightValue))
          Nat.lt_of_le_of_ne gcdLeLeft gcdNeLeft

/-- **The middle-level fold descent measure** — when the nonzero pivot `pivotEntry` does not divide a
later diagonal entry `laterEntry`, the fold's landed `gcd(pivotEntry, laterEntry)` has strictly
smaller magnitude than the pivot.  This is the strict measure the `smithRepairPositionSweep` fold
loop rides (the sibling of the shipped inner `smithRotationDecreasesPivotSize`), lifting
`natGcdLtLeftOfNotDivides` through the `natAbs`/`intGcd` bridges (`(intGcd a b).natAbs =
natGcd a.natAbs b.natAbs` definitionally; `IntDivides` descends to `NatDivides` of the magnitudes via
`intDividesOfNatDividesNatAbs`/`intDividesOfNatAbsDivides`). -/
theorem smithRepairDecreasesPivotSize (pivotEntry laterEntry : Int)
    (isPivotPositive : 0 < pivotEntry.natAbs)
    (pivotDoesNotDivide : ¬ IntDivides pivotEntry laterEntry) :
    (intGcd pivotEntry laterEntry).natAbs < pivotEntry.natAbs :=
  natGcdLtLeftOfNotDivides pivotEntry.natAbs laterEntry.natAbs isPivotPositive
    (fun natDivides =>
      pivotDoesNotDivide
        (intDividesOfNatAbsDivides (intDividesOfNatDividesNatAbs natDivides)))

/-! ## The invariant bundle + the column half of crosses-stay-zero (B1)

The three-level induction carries two invariants the recon pins as load-bearing (INV-RECT is the
shipped `applyOperationsPreservesRectangular`; INV-NONNEG-PREFIX is established by the final sign
sweep, not carried):

  * **INV-DIAG** `IsWindowDiagonal matrix windowStart height width` — the window `≥ windowStart` is
    off-diagonal-zero.  Held only at PHASE BOUNDARIES (mid-cascade transvections break it), never
    per-cascade-step.
  * **INV-CHAIN-PREFIX** `SmithChainPrefix matrix pivotIndex height width` — every settled prefix
    entry `d_i` (`i < pivotIndex`) divides every later diagonal `d_q` (`i ≤ q`).  The TRUE (c)
    invariant: the naive "settled values frozen" reading is false (the working position drops), but
    the settled PREFIX chain is genuinely preserved.

`foldPreservesSettledColumnZero` discharges the COLUMN half of crosses-stay-zero the r4 footer left
semantic (its ROW half is the shipped `addRowMultiplePreservesEntryOffTargetRow`): the repair fold
`addRowMultiple foundPos pivotIndex 1` leaves the settled column entry `(pivotIndex, settled) = 0`
because it reads `old(pivotIndex, settled) + 1 * old(foundPos, settled)`, and INV-DIAG zeroes both
off-diagonal summands (`pivotIndex ≠ settled`, `foundPos ≠ settled`, both in the window).  It rides
the new ON-target-row entry formula `addRowMultipleEntryOnTargetRow` (the sibling of the shipped
OFF-target lemma) over the pointwise scaled-add read `listGetWithDefaultAddScaledEntries` and the
at-modify-index read `listGetWithDefaultModifyAtEq`. -/

/-- **INV-DIAG as a Lean Prop** — the window of rows/columns at or beyond `windowStart` (and below
`height`/`width`) is off-diagonal-zero.  A PHASE-BOUNDARY invariant of the repair induction (not a
per-cascade-step one). -/
def IsWindowDiagonal (matrix : IntMatrix) (windowStart height width : Nat) : Prop :=
  ∀ rowIndex colIndex, windowStart ≤ rowIndex → rowIndex < height →
    windowStart ≤ colIndex → colIndex < width → rowIndex ≠ colIndex →
    matrix.entryAt rowIndex colIndex = 0

/-- **INV-CHAIN-PREFIX as a Lean Prop** — every settled prefix diagonal `d_earlier`
(`earlier < pivotIndex`) divides every later diagonal `d_later` (`earlier ≤ later`) in the window.
The true top-down monotonicity invariant (the settled prefix's divisibility chain, not the raw
values, is what survives later settles). -/
def SmithChainPrefix (matrix : IntMatrix) (pivotIndex height width : Nat) : Prop :=
  ∀ earlierIndex, earlierIndex < pivotIndex →
    ∀ laterIndex, earlierIndex ≤ laterIndex → laterIndex < Nat.min height width →
      dividesExactly (matrix.diagonalEntryAt earlierIndex) (matrix.diagonalEntryAt laterIndex)

/-- Atomic list locality (AT the modified index) — reading `position` of a `listModifyAt transform`
returns the transformed original entry, when `position` is in range.  The at-index sibling of
`listGetWithDefaultModifyAtNe`.  Structural on the list. -/
theorem listGetWithDefaultModifyAtEq {Entry : Type} (defaultEntry : Entry)
    (transform : Entry → Entry) :
    ∀ (entries : List Entry) (position : Nat), position < entries.length →
      listGetWithDefault defaultEntry (listModifyAt transform entries position) position
        = transform (listGetWithDefault defaultEntry entries position)
  | [], _, isInRange => Nat.noConfusion (natEqZeroOfLeZero isInRange)
  | _ :: _, 0, _ => rfl
  | _ :: remainingEntries, position + 1, isInRange =>
      listGetWithDefaultModifyAtEq defaultEntry transform remainingEntries position
        (natLeOfSuccLeSucc isInRange)

/-- Pointwise read of a scaled-add row — reading `index` of `addScaledEntries coefficient sourceRow
targetRow` is `targetRow[index] + coefficient * sourceRow[index]`, when the rows agree in length and
`index` is in range (rectangularity supplies the length equality).  Structural on both rows with the
index. -/
theorem listGetWithDefaultAddScaledEntries (coefficient : Int) :
    ∀ (sourceRow targetRow : IntRow) (index : Nat),
      sourceRow.length = targetRow.length → index < targetRow.length →
      listGetWithDefault 0 (addScaledEntries coefficient sourceRow targetRow) index
        = listGetWithDefault 0 targetRow index
            + coefficient * listGetWithDefault 0 sourceRow index
  | [], [], _, _, isInRange => Nat.noConfusion (natEqZeroOfLeZero isInRange)
  | [], _ :: _, _, lengthsAgree, _ => nomatch lengthsAgree
  | _ :: _, [], _, lengthsAgree, _ => nomatch lengthsAgree
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: sourceRemaining, _ :: targetRemaining, index + 1, lengthsAgree, isInRange =>
      listGetWithDefaultAddScaledEntries coefficient sourceRemaining targetRemaining index
        (Nat.succ.inj lengthsAgree) (natLeOfSuccLeSucc isInRange)

/-- **The ON-target-row entry formula** — the sibling of the shipped
`addRowMultiplePreservesEntryOffTargetRow`: reading the TARGET row after `addRowMultiple sourceIndex
targetIndex coefficient` gives `old(target, col) + coefficient * old(source, col)`, for distinct
in-range rows and an in-range column (rectangularity supplies the equal row lengths).  Navigates
`addRowMultiple`'s three guards, reads the modified target row by `listGetWithDefaultModifyAtEq`, then
pointwise by `listGetWithDefaultAddScaledEntries`. -/
theorem addRowMultipleEntryOnTargetRow {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (sourceIndex targetIndex colIndex : Nat) (coefficient : Int)
    (isDistinct : sourceIndex ≠ targetIndex)
    (isSourceInRange : sourceIndex < height) (isTargetInRange : targetIndex < height)
    (isColInRange : colIndex < width) :
    (matrix.addRowMultiple sourceIndex targetIndex coefficient).entryAt targetIndex colIndex
      = matrix.entryAt targetIndex colIndex
          + coefficient * matrix.entryAt sourceIndex colIndex := by
  obtain ⟨rowCount, rowWidths⟩ := isRect
  have targetInRows : targetIndex < matrix.rows.length :=
    Eq.mp (congrArg (targetIndex < ·) rowCount.symm) isTargetInRange
  have sourceInRows : sourceIndex < matrix.rows.length :=
    Eq.mp (congrArg (sourceIndex < ·) rowCount.symm) isSourceInRange
  have sourceHasWidth :
      (listGetWithDefault [] matrix.rows sourceIndex).length = width :=
    listGetWithDefaultHasWidth matrix.rows sourceIndex rowWidths sourceInRows
  have targetHasWidth :
      (listGetWithDefault [] matrix.rows targetIndex).length = width :=
    listGetWithDefaultHasWidth matrix.rows targetIndex rowWidths targetInRows
  unfold IntMatrix.addRowMultiple
  rw [if_neg isDistinct, if_pos sourceInRows, if_pos targetInRows]
  show listGetWithDefault 0
      (listGetWithDefault []
        (listModifyAt
          (fun targetRow =>
            addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
          matrix.rows targetIndex) targetIndex) colIndex = _
  rw [listGetWithDefaultModifyAtEq [] _ matrix.rows targetIndex targetInRows]
  exact listGetWithDefaultAddScaledEntries coefficient
    (listGetWithDefault [] matrix.rows sourceIndex)
    (listGetWithDefault [] matrix.rows targetIndex) colIndex
    (sourceHasWidth.trans targetHasWidth.symm)
    (Eq.mp (congrArg (colIndex < ·) targetHasWidth.symm) isColInRange)

/-- **The COLUMN half of crosses-stay-zero** — the repair fold `addRowMultiple foundPos pivotIndex 1`
leaves the settled column entry `(pivotIndex, settled) = 0`.  The new target-row entry reads
`old(pivotIndex, settled) + 1 * old(foundPos, settled)`, and INV-DIAG zeroes both off-diagonal
summands (`pivotIndex ≠ settled` since `settled < pivotIndex`; `foundPos ≠ settled` since
`settled < pivotIndex < foundPos`).  Discharges the r4 footer's semantic (b)-column obligation; its
ROW half is the shipped `addRowMultiplePreservesEntryOffTargetRow`. -/
theorem foldPreservesSettledColumnZero {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex foundPos settled : Nat)
    (isDiag : IsWindowDiagonal matrix 0 height width)
    (settledBelowPivot : settled < pivotIndex) (pivotBelowFound : pivotIndex < foundPos)
    (foundInWindow : foundPos < height) (pivotInWindow : pivotIndex < height)
    (settledInWidth : settled < width) :
    (matrix.addRowMultiple foundPos pivotIndex 1).entryAt pivotIndex settled = 0 :=
  have foundNePivot : foundPos ≠ pivotIndex := fun foundEqPivot =>
    Nat.lt_irrefl pivotIndex (Eq.mp (congrArg (pivotIndex < ·) foundEqPivot) pivotBelowFound)
  have pivotEntryIsZero : matrix.entryAt pivotIndex settled = 0 :=
    isDiag pivotIndex settled (Nat.zero_le pivotIndex) pivotInWindow (Nat.zero_le settled)
      settledInWidth (fun pivotEqSettled =>
        Nat.lt_irrefl settled (Eq.mp (congrArg (settled < ·) pivotEqSettled) settledBelowPivot))
  have settledBelowFound : settled < foundPos := Nat.lt_trans settledBelowPivot pivotBelowFound
  have foundEntryIsZero : matrix.entryAt foundPos settled = 0 :=
    isDiag foundPos settled (Nat.zero_le foundPos) foundInWindow (Nat.zero_le settled)
      settledInWidth (fun foundEqSettled =>
        Nat.lt_irrefl settled (Eq.mp (congrArg (settled < ·) foundEqSettled) settledBelowFound))
  (addRowMultipleEntryOnTargetRow matrix isRect foundPos pivotIndex settled 1 foundNePivot
    foundInWindow pivotInWindow settledInWidth).trans
    ((congrArg (· + 1 * matrix.entryAt foundPos settled) pivotEntryIsZero).trans
      ((congrArg (fun laterEntry => (0 : Int) + 1 * laterEntry) foundEntryIsZero).trans
        ((intZeroAdd (1 * 0)).trans (intOneMul 0))))

/-! ## The totality first step: phase decomposition + outer fuel-lockstep base (B3)

The recon's totality skeleton opens by splitting the applied full-driver output across its three
phase words `diagOps ++ repairOps ++ signOps`.  `smithReduceFullApplied` performs exactly that split
via the shipped `applyOperationsAppend` (twice), expressing the reduced matrix as the composed phase
outputs `((afterDiag).applyOperations repairOps).applyOperations signOps` — the shape the three-level
induction then attacks phase by phase.

The three `*PastWindow` lemmas are the outer fuel-lockstep base: each outer sweep returns the EMPTY
word once `pivotIndex` has passed the window (`¬ (pivotIndex + 1 ≤ Nat.min height width)`), for ANY
fuel.  This is the guard-exhaustion base case of the fuel-adequacy coupling the recon flags "tight and
trivially adequate" — the guard falsifies before fuel runs out, so no fuel measure is needed for the
outer sweeps. -/

/-- **The applied full-driver output, phase-decomposed** — `matrix.applyOperations (smithReduceFull
matrix height width).operations` equals the three phase words fired in sequence: cross-clear
(`smithReduceTotal`), then the top-down divisibility repair, then the diagonal sign sweep.  The first
structural step of any `smithReduceFull` totality proof, riding the shipped `applyOperationsAppend`
twice over the `diagOps ++ repairOps ++ signOps` composition. -/
theorem smithReduceFullApplied (matrix : IntMatrix) (height width : Nat) :
    matrix.applyOperations (smithReduceFull matrix height width).operations
      = (((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
            (smithDivisibilityRepairSweep (Nat.min height width)
              (matrix.applyOperations (smithReduceTotal matrix height width).operations)
              0 height width)).applyOperations
          (smithDiagonalSignSweep (Nat.min height width)
            ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
              (smithDivisibilityRepairSweep (Nat.min height width)
                (matrix.applyOperations (smithReduceTotal matrix height width).operations)
                0 height width))
            0 height width)) := by
  show matrix.applyOperations
      ((smithReduceTotal matrix height width).operations
        ++ smithDivisibilityRepairSweep (Nat.min height width)
              (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width
        ++ smithDiagonalSignSweep (Nat.min height width)
              ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
                (smithDivisibilityRepairSweep (Nat.min height width)
                  (matrix.applyOperations (smithReduceTotal matrix height width).operations)
                  0 height width))
              0 height width) = _
  rw [applyOperationsAppend, applyOperationsAppend]

/-- **Outer sign sweep, past the window** — once `pivotIndex` is beyond the pivot budget the sign
sweep emits no operations, for any fuel.  The guard-exhaustion base of the outer fuel lockstep. -/
theorem smithDiagonalSignSweepPastWindow :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      ¬ (pivotIndex + 1 ≤ Nat.min height width) →
      smithDiagonalSignSweep fuel matrix pivotIndex height width = []
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, pastWindow => if_neg pastWindow

/-- **Outer cross-clear sweep, past the window** — the total sweep emits no operations once the pivot
budget is exhausted, for any fuel. -/
theorem smithReduceTotalSweepPastWindow :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      ¬ (pivotIndex + 1 ≤ Nat.min height width) →
      smithReduceTotalSweep fuel matrix pivotIndex height width = []
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, pastWindow => if_neg pastWindow

/-- **Outer repair sweep, past the window** — the divisibility-repair sweep emits no operations once
the pivot budget is exhausted, for any fuel. -/
theorem smithDivisibilityRepairSweepPastWindow :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      ¬ (pivotIndex + 1 ≤ Nat.min height width) →
      smithDivisibilityRepairSweep fuel matrix pivotIndex height width = []
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, pastWindow => if_neg pastWindow

/-! ## The sign-phase kernel toward INV-NONNEG (B1)

The final `smithDiagonalSignSweep` establishes INV-NONNEG-PREFIX (the Euclid clears leave transient
negatives; the sign phase repairs them).  Its two atomic facts, completing the entry-under-operation
formula family (`addRowMultiplePreservesEntryOffTargetRow` OFF-target row, `addRowMultipleEntryOnTargetRow`
ON-target row, and now `negateRowEntry` for the sign letter):

  * `negateRowEntry` — the sign letter negates every entry of its (in-range) row, so a negative
    diagonal pivot flips to its positive magnitude; rides `listGetWithDefaultMapNeg` (pointwise read of
    a negated row) and the shipped `listGetWithDefaultModifyAtEq`.
  * `smithSignNormalizeOpsNonneg` — the sign-normalization emits no operation on an
    already-nonnegative pivot, so the sign phase is a no-op wherever the diagonal is already
    nonnegative (the regression battery's already-nonnegative inputs). -/

/-- Pointwise read of a negated row — reading `index` of `row.map (fun entry => -entry)` is the
negation of `row[index]` (the out-of-range default `0` negates to `0` through `intNegZero`).  Structural
on the row with the index. -/
theorem listGetWithDefaultMapNeg : ∀ (row : IntRow) (index : Nat),
    listGetWithDefault 0 (row.map (fun entry => -entry)) index
      = -(listGetWithDefault 0 row index)
  | [], 0 => intNegZero.symm
  | [], _ + 1 => intNegZero.symm
  | _ :: _, 0 => rfl
  | _ :: remainingEntries, index + 1 => listGetWithDefaultMapNeg remainingEntries index

/-- **The sign letter negates its row's entries** — `(matrix.negateRow rowIndex).entryAt rowIndex
colIndex = -(matrix.entryAt rowIndex colIndex)` for an in-range row.  The sign-phase analog of the
transvection entry formulas: a negative diagonal pivot flips to its positive magnitude, the mechanism
by which the sign sweep establishes INV-NONNEG. -/
theorem negateRowEntry (matrix : IntMatrix) (rowIndex colIndex : Nat)
    (isInRange : rowIndex < matrix.rows.length) :
    (matrix.negateRow rowIndex).entryAt rowIndex colIndex
      = -(matrix.entryAt rowIndex colIndex) := by
  show listGetWithDefault 0
      (listGetWithDefault []
        (listModifyAt (fun row => row.map (fun entry => -entry)) matrix.rows rowIndex) rowIndex)
      colIndex = _
  rw [listGetWithDefaultModifyAtEq [] _ matrix.rows rowIndex isInRange]
  exact listGetWithDefaultMapNeg (listGetWithDefault [] matrix.rows rowIndex) colIndex

/-- **The sign normalization is a no-op on a nonnegative pivot** — `smithSignNormalizeOps` emits no
operation when `matrix.entryAt pivotIndex pivotIndex` is not negative, so the sign phase adds nothing
wherever the diagonal is already nonnegative. -/
theorem smithSignNormalizeOpsNonneg (matrix : IntMatrix) (pivotIndex : Nat)
    (isNonneg : ¬ (matrix.entryAt pivotIndex pivotIndex < 0)) :
    smithSignNormalizeOps matrix pivotIndex = [] :=
  if_neg isNonneg

/-! ## The named wall: cascade re-diagonalization = the r6 elimination-correctness pole (B3)

`SmithReduceFullDriverStatement` stays UNINHABITED this round.  The r5 decomposition ships every
independently-closeable sub-lemma of the recon's three-level induction — the composition substrate
(`applyOperationsAppend`), the applied-output phase split (`smithReduceFullApplied`), the middle-level
fold descent measure (`smithRepairDecreasesPivotSize`), the invariant Props
(`IsWindowDiagonal` / `SmithChainPrefix`), the column half of crosses-stay-zero
(`foldPreservesSettledColumnZero`, resting on `addRowMultipleEntryOnTargetRow`), the outer fuel-lockstep
base (`smith*SweepPastWindow`), and the sign-phase kernel (`negateRowEntry`).  What remains is the ONE
deep obligation the recon flags `[HIGH, shared with the r3 pole]`: obligation (a), that the Euclid
cascade `smithCascadeSweep` RE-DIAGONALIZES a folded window — a full verified Gaussian-elimination
correctness proof over the extrinsic-shape substrate, not a one-round deliverable.

`SmithCascadeReDiagonalizesStatement` NAMED that obligation as a first-class `Prop`, but the r5
adversarial verification REFUTED the statement as written: its conclusion fires only the cross-clear
cascade `smithCascadeSweep`, while the gcd/divisibility landing is performed by the SEPARATE
`smithDivisibilityRepairSweep` (fold-then-recascade).  The hypothesis `IsWindowDiagonal` admits
already-diagonal-but-non-divisible inputs (`diag(2, 3)` at pivot 0 — a member of this round's own
battery) on which the cascade is a NO-OP, so clause (c) demands `2 ∣ 3` — FALSE.  The r4 refutation
`smithReduceTotalIsNotFullyReducing` makes the same point from the driver side.  The Prop is retained
below EXACTLY as shipped (a false `Prop` definition is harmless and nothing is proved from it) as the
honest record; the CORRECTED r6 pole must be stated over the POST-FOLD shape — the window after
`addRowMultiple foundPos pivotIndex 1` has the non-dividing entry IN the pivot cross, and THERE the
cascade genuinely lands the gcd — or equivalently over `smithDivisibilityRepairSweep` end-to-end.
Stating and inhabiting that corrected Prop assembles `SmithReduceFullDriverStatement` phase by phase
over the shipped decomposition. -/

/-- **REFUTED as the r6 pole (r5 adversarial verification)** — retained verbatim as the honest record;
see the section header above.  As written this `Prop` is FALSE: on `diag(2, 3)` at pivot 0 the
hypotheses hold, the cascade is a no-op (the window is already diagonal, the cross already clear), and
clause (c) demands `2 ∣ 3`.  The defect: the conclusion uses only the cross-clear `smithCascadeSweep`;
the divisibility landing lives in `smithDivisibilityRepairSweep` (fold-then-recascade), so the correct
pole must quantify over the POST-FOLD window shape.  Do NOT attempt to inhabit this; the r6 round
states the corrected pole. -/
def SmithCascadeReDiagonalizesStatement : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width →
    IsWindowDiagonal matrix pivotIndex height width →
    smithCrossIsClear
        (matrix.applyOperations
          (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width = true
      ∧ IsWindowDiagonal
          (matrix.applyOperations
            (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
              matrix pivotIndex height width))
          (pivotIndex + 1) height width
      ∧ (∀ laterIndex, pivotIndex < laterIndex → laterIndex < Nat.min height width →
          dividesExactly
            ((matrix.applyOperations
              (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width)).diagonalEntryAt pivotIndex)
            ((matrix.applyOperations
              (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
                matrix pivotIndex height width)).diagonalEntryAt laterIndex))

/-! ## The CORRECTED r6 poles + their truth probes (H2-SMITH r6, B1)

The r5 refutation of `SmithCascadeReDiagonalizesStatement` (above) demanded the corrected pole be
stated over the POST-FOLD window shape, and it warned of the R1 trap: a naive "the pivot gcd divides
ALL later diagonal entries" clause REPEATS the r5 mistake.  On `diag(6, 10, 15)` one fold + cascade at
pivot 0 lands `gcd(6, 10) = 2` at the pivot and pushes `lcm = 30` down, leaving `diag(2, 30, 15)` — and
`2 ∤ 15`.  So the atomic per-fold guarantee CANNOT say "divides all later"; it says "divides the two
folded operands `d_p`, `d_q`" only.  The two corrected poles, stated at two granularities:

  * **POLE-A** `SmithCascadeReDiagonalizesPostFoldStatement` — the DIRECT correction of the refuted
    cascade decl: after folding the non-dividing `foundPos` row into the pivot row and re-firing
    `smithCascadeSweep`, the pivot cross is clear, the sub-block `≥ pivotIndex + 1` is window-diagonal,
    and the landed pivot divides BOTH folded operands (the WEAKENED clause — never "all later").
  * **POLE-B** `SmithRepairChainDiagonalizesStatement` — the ASSEMBLY-facing end-to-end pole: the whole
    `smithDivisibilityRepairSweep` takes a window-diagonal input to a window-diagonal output whose
    FULL prefix chain divides (`SmithChainPrefix`).  Sign-blind (`dividesExactly` survives the transient
    negatives the Euclid clears leave; nonnegativity is the sign phase's exclusive job — POLE-B does NOT
    claim it, the r5 R4 caution).

Neither is inhabited this round (their inhabitant is the deep Gaussian-elimination correctness pole,
still the named r7 wall).  What ships here is the r6 forward-statement discipline: BEFORE any proof
work, each pole is machine-checked to HOLD on both adversarial inputs — `diag(2, 3)` (the r5 refutation
input) and `diag(6, 10, 15)` (the R1-trap input) — as kernel-checked, zero-axiom truth probes.  The
statements HELD on every probe; had any probe failed, the pole would be re-stated, not proved.  The
`smithCascadePostFoldDividesAllFailsOnSixTenFifteen` probe kernel-checks the R1 trap itself (`2 ∤ 15`),
so the reason the clause is WEAKENED is a machine-checked fact, not a claim. -/

/-- **POLE-A — the corrected post-fold cascade re-diagonalization (WEAKENED divides clause)** — the
direct correction of the refuted `SmithCascadeReDiagonalizesStatement`: on a window-diagonal `matrix`
with a later diagonal `foundPos` the pivot does NOT divide, folding row `foundPos` into the pivot row
(`addRowMultiple foundPos pivotIndex 1`) and re-firing the Euclid cascade at the pivot (a) clears the
pivot cross, (b) leaves the sub-block `≥ pivotIndex + 1` window-diagonal, and (c) lands a pivot that
divides the two folded operands `d_p` and `d_q` — and ONLY those two (the R1-trap-safe clause; the
cascade need NOT make the pivot divide entries beyond `foundPos`, as `diag(6, 10, 15)` witnesses).
Truth-probed on `diag(2, 3)` and `diag(6, 10, 15)` below; NOT inhabited (the r7 elimination pole). -/
def SmithCascadeReDiagonalizesPostFoldStatement : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex foundPos height width : Nat),
    matrix.IsRectangular height width →
    IsWindowDiagonal matrix pivotIndex height width →
    pivotIndex < foundPos → foundPos < Nat.min height width →
    ¬ dividesExactly (matrix.diagonalEntryAt pivotIndex) (matrix.diagonalEntryAt foundPos) →
    let folded := matrix.addRowMultiple foundPos pivotIndex 1
    let cascaded := folded.applyOperations
        (smithCascadeSweep (smithMinorAbsSum folded pivotIndex height width)
          folded pivotIndex height width)
    smithCrossIsClear cascaded pivotIndex height width = true
      ∧ IsWindowDiagonal cascaded (pivotIndex + 1) height width
      ∧ dividesExactly (cascaded.diagonalEntryAt pivotIndex) (matrix.diagonalEntryAt pivotIndex)
      ∧ dividesExactly (cascaded.diagonalEntryAt pivotIndex) (matrix.diagonalEntryAt foundPos)

/-- **POLE-B — the end-to-end repair-sweep chain diagonalization (sign-blind)** — the assembly-facing
corrected pole: the whole top-down `smithDivisibilityRepairSweep` takes a window-diagonal `matrix` to a
window-diagonal `repaired` whose FULL settled prefix chain divides (`SmithChainPrefix` — every earlier
diagonal divides every later one across the whole `Nat.min height width` window).  This is the clean
"divides all" chain POLE-A cannot state per fold: it holds only END-TO-END, after the fold loop has
settled every position.  Deliberately sign-BLIND — the repair output carries transient negatives
(`diag(1, 30, -30)` on `diag(6, 10, 15)`), so `dividesExactly` (which ignores sign) is used, NOT
nonnegativity (the sign phase's exclusive job).  POLE-B composes with `smithReduceFullApplied` toward
`SmithReduceFullDriverStatement`.  Truth-probed on `diag(2, 3)` and `diag(6, 10, 15)` below; NOT
inhabited (rides the same r7 cascade pole as POLE-A). -/
def SmithRepairChainDiagonalizesStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat),
    matrix.IsRectangular height width →
    IsWindowDiagonal matrix 0 height width →
    let repaired := matrix.applyOperations
        (smithDivisibilityRepairSweep (Nat.min height width) matrix 0 height width)
    IsWindowDiagonal repaired 0 height width
      ∧ SmithChainPrefix repaired (Nat.min height width) height width

/-- **Truth probe A1 — POLE-A holds on `diag(2, 3)` (the r5 refutation input)** — folding row 1 into the
pivot row gives `[[2, 3], [0, 3]]`; the re-fired cascade Euclid-clears `(2, 3)` to `gcd = 1` at the
pivot and pushes `lcm = 6` down, reaching `[[1, 0], [0, -6]]`.  The pivot cross is clear, the `1 × 1`
sub-block is (vacuously) window-diagonal, and `gcd = 1` divides both `d_p = 2` and `d_q = 3`.  Each
clause closes on the LITERAL cascade output by defeq (`decide` on the Bool, the decidable-window map on
the sub-block, hand-built witnesses `⟨2, rfl⟩` / `⟨3, rfl⟩` for the divisibilities). -/
theorem smithCascadePostFoldHoldsOnCoprimeTwoThree :
    let folded := ({ rows := [[2, 0], [0, 3]] } : IntMatrix).addRowMultiple 1 0 1
    let cascaded := folded.applyOperations
        (smithCascadeSweep (smithMinorAbsSum folded 0 2 2) folded 0 2 2)
    smithCrossIsClear cascaded 0 2 2 = true
      ∧ IsWindowDiagonal cascaded 1 2 2
      ∧ dividesExactly (cascaded.diagonalEntryAt 0)
          (({ rows := [[2, 0], [0, 3]] } : IntMatrix).diagonalEntryAt 0)
      ∧ dividesExactly (cascaded.diagonalEntryAt 0)
          (({ rows := [[2, 0], [0, 3]] } : IntMatrix).diagonalEntryAt 1) :=
  ⟨by decide,
   show IsWindowDiagonal ({ rows := [[1, 0], [0, -6]] } : IntMatrix) 1 2 2 from
     fun rowIndex colIndex oneLeRow rowLt2 oneLeCol colLt2 rowNeCol =>
       (by decide : ∀ rr, rr < 2 → ∀ cc, cc < 2 → 1 ≤ rr → 1 ≤ cc → rr ≠ cc →
           ({ rows := [[1, 0], [0, -6]] } : IntMatrix).entryAt rr cc = 0)
         rowIndex rowLt2 colIndex colLt2 oneLeRow oneLeCol rowNeCol,
   ⟨2, rfl⟩,
   ⟨3, rfl⟩⟩

/-- **Truth probe A2 — POLE-A holds on `diag(6, 10, 15)` (the R1-trap input)** — folding row 1 into the
pivot row gives `[[6, 10, 0], [0, 10, 0], [0, 0, 15]]`; one cascade lands `gcd(6, 10) = 2` at the pivot
and pushes `lcm = 30` down, reaching `[[2, 0, 0], [0, 30, 0], [0, 0, 15]]`.  The pivot cross is clear,
the `2 × 2` sub-block is window-diagonal, and the landed `2` divides both folded operands `d_p = 6`
(`⟨3, rfl⟩`) and `d_q = 10` (`⟨5, rfl⟩`).  Crucially `2 ∤ 15` here (the untouched `d_2`), which is why
POLE-A's clause is WEAKENED to the two folded operands — see
`smithCascadePostFoldDividesAllFailsOnSixTenFifteen`. -/
theorem smithCascadePostFoldHoldsOnSixTenFifteen :
    let folded := ({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 15]] } : IntMatrix).addRowMultiple 1 0 1
    let cascaded := folded.applyOperations
        (smithCascadeSweep (smithMinorAbsSum folded 0 3 3) folded 0 3 3)
    smithCrossIsClear cascaded 0 3 3 = true
      ∧ IsWindowDiagonal cascaded 1 3 3
      ∧ dividesExactly (cascaded.diagonalEntryAt 0)
          (({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 15]] } : IntMatrix).diagonalEntryAt 0)
      ∧ dividesExactly (cascaded.diagonalEntryAt 0)
          (({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 15]] } : IntMatrix).diagonalEntryAt 1) :=
  ⟨by decide,
   show IsWindowDiagonal ({ rows := [[2, 0, 0], [0, 30, 0], [0, 0, 15]] } : IntMatrix) 1 3 3 from
     fun rowIndex colIndex oneLeRow rowLt3 oneLeCol colLt3 rowNeCol =>
       (by decide : ∀ rr, rr < 3 → ∀ cc, cc < 3 → 1 ≤ rr → 1 ≤ cc → rr ≠ cc →
           ({ rows := [[2, 0, 0], [0, 30, 0], [0, 0, 15]] } : IntMatrix).entryAt rr cc = 0)
         rowIndex rowLt3 colIndex colLt3 oneLeRow oneLeCol rowNeCol,
   ⟨3, rfl⟩,
   ⟨5, rfl⟩⟩

/-- **The R1 guard — "divides ALL later" is FALSE on `diag(6, 10, 15)`** — the post-fold cascade's
landed pivot `2` does NOT divide the untouched third diagonal `15`.  This kernel-checks the exact trap
the r5 caution names: had POLE-A demanded the pivot divide every later entry, it would be REFUTED here.
Refutes `dividesExactly 2 15` by pushing the `∃`-witness through `natAbs` (`intNatAbsMul`) to
`NatDivides 2 15` and collapsing the counting remainder (`natDividesRemainderIsZero`, computing to
`1 ≠ 0`) — the same shape as the r4 refutation `smithReduceTotalIsNotFullyReducing`. -/
theorem smithCascadePostFoldDividesAllFailsOnSixTenFifteen :
    let folded := ({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 15]] } : IntMatrix).addRowMultiple 1 0 1
    let cascaded := folded.applyOperations
        (smithCascadeSweep (smithMinorAbsSum folded 0 3 3) folded 0 3 3)
    ¬ dividesExactly (cascaded.diagonalEntryAt 0) (cascaded.diagonalEntryAt 2) :=
  fun ⟨factor, fifteenEqTwoFactor⟩ =>
    have dividesNat : NatDivides 2 15 :=
      ⟨factor.natAbs,
        (congrArg Int.natAbs fifteenEqTwoFactor).trans (intNatAbsMul 2 factor)⟩
    absurd (natDividesRemainderIsZero (by decide) dividesNat) (by decide)

/-- **Truth probe B1 — POLE-B holds on `diag(2, 3)`** — the end-to-end repair sweep reduces `diag(2, 3)`
to `[[1, 0], [0, -6]]` (diagonal, transient negative, full chain `1 | -6`).  The window stays diagonal
(decidable-window map), and the full prefix chain divides: `1 | 1`, `1 | -6`, `-6 | -6` (hand-built
witnesses over the 2-position interval, impossible index pairs discharged by the shipped Nat peel
`natLeOfSuccLeSucc` / `natEqZeroOfLeZero` idiom). -/
theorem smithRepairChainHoldsOnCoprimeTwoThree :
    let repaired := ({ rows := [[2, 0], [0, 3]] } : IntMatrix).applyOperations
        (smithDivisibilityRepairSweep (Nat.min 2 2) { rows := [[2, 0], [0, 3]] } 0 2 2)
    IsWindowDiagonal repaired 0 2 2
      ∧ SmithChainPrefix repaired (Nat.min 2 2) 2 2 :=
  ⟨show IsWindowDiagonal ({ rows := [[1, 0], [0, -6]] } : IntMatrix) 0 2 2 from
     fun rowIndex colIndex _zeroLeRow rowLt2 _zeroLeCol colLt2 rowNeCol =>
       (by decide : ∀ rr, rr < 2 → ∀ cc, cc < 2 → rr ≠ cc →
           ({ rows := [[1, 0], [0, -6]] } : IntMatrix).entryAt rr cc = 0)
         rowIndex rowLt2 colIndex colLt2 rowNeCol,
   show SmithChainPrefix ({ rows := [[1, 0], [0, -6]] } : IntMatrix) 2 2 2 from
     fun earlierIndex earlierLt laterIndex earlierLe laterLt =>
       match earlierIndex, laterIndex, earlierLt, earlierLe, laterLt with
       | 0, 0, _, _, _ => ⟨1, rfl⟩
       | 0, 1, _, _, _ => ⟨-6, rfl⟩
       | 0, _ + 2, _, _, laterLt =>
           Nat.noConfusion
             (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc laterLt)))
       | 1, 0, _, earlierLe, _ => Nat.noConfusion (natEqZeroOfLeZero earlierLe)
       | 1, 1, _, _, _ => ⟨1, rfl⟩
       | 1, _ + 2, _, _, laterLt =>
           Nat.noConfusion
             (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc laterLt)))
       | _ + 2, _, earlierLt, _, _ =>
           Nat.noConfusion
             (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc earlierLt)))⟩

/-- **Truth probe B2 — POLE-B holds on `diag(6, 10, 15)` (the R1-trap input, end-to-end)** — the
end-to-end repair sweep reduces `diag(6, 10, 15)` to `[[1, 0, 0], [0, 30, 0], [0, 0, -30]]` (diagonal,
transient negative, full chain `1 | 30 | -30`).  Where POLE-A's single fold could only land the two
folded operands (`2 ∤ 15`), the FULL sweep settles every position: `gcd(6, 10, 15) = 1` at the pivot,
then `diag(30, -30)` in the sub-block, giving the clean "divides all" chain POLE-B demands (`1` divides
`30` and `-30`; `30 | -30`).  Sign-blind: the transient `-30` survives; nonnegativity is the sign
phase's job, not POLE-B's.  The 3-position prefix chain is discharged by hand-built witnesses with the
shipped Nat peel idiom for the impossible index pairs. -/
theorem smithRepairChainHoldsOnSixTenFifteen :
    let repaired := ({ rows := [[6, 0, 0], [0, 10, 0], [0, 0, 15]] } : IntMatrix).applyOperations
        (smithDivisibilityRepairSweep (Nat.min 3 3)
          { rows := [[6, 0, 0], [0, 10, 0], [0, 0, 15]] } 0 3 3)
    IsWindowDiagonal repaired 0 3 3
      ∧ SmithChainPrefix repaired (Nat.min 3 3) 3 3 :=
  ⟨show IsWindowDiagonal ({ rows := [[1, 0, 0], [0, 30, 0], [0, 0, -30]] } : IntMatrix) 0 3 3 from
     fun rowIndex colIndex _zeroLeRow rowLt3 _zeroLeCol colLt3 rowNeCol =>
       (by decide : ∀ rr, rr < 3 → ∀ cc, cc < 3 → rr ≠ cc →
           ({ rows := [[1, 0, 0], [0, 30, 0], [0, 0, -30]] } : IntMatrix).entryAt rr cc = 0)
         rowIndex rowLt3 colIndex colLt3 rowNeCol,
   show SmithChainPrefix ({ rows := [[1, 0, 0], [0, 30, 0], [0, 0, -30]] } : IntMatrix) 3 3 3 from
     fun earlierIndex earlierLt laterIndex earlierLe laterLt =>
       match earlierIndex, laterIndex, earlierLt, earlierLe, laterLt with
       | 0, 0, _, _, _ => ⟨1, rfl⟩
       | 0, 1, _, _, _ => ⟨30, rfl⟩
       | 0, 2, _, _, _ => ⟨-30, rfl⟩
       | 0, _ + 3, _, _, laterLt =>
           Nat.noConfusion
             (natEqZeroOfLeZero
               (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc laterLt))))
       | 1, 0, _, earlierLe, _ => Nat.noConfusion (natEqZeroOfLeZero earlierLe)
       | 1, 1, _, _, _ => ⟨1, rfl⟩
       | 1, 2, _, _, _ => ⟨-1, rfl⟩
       | 1, _ + 3, _, _, laterLt =>
           Nat.noConfusion
             (natEqZeroOfLeZero
               (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc laterLt))))
       | 2, 0, _, earlierLe, _ => Nat.noConfusion (natEqZeroOfLeZero earlierLe)
       | 2, 1, _, earlierLe, _ =>
           Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc earlierLe))
       | 2, 2, _, _, _ => ⟨1, rfl⟩
       | 2, _ + 3, _, _, laterLt =>
           Nat.noConfusion
             (natEqZeroOfLeZero
               (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc laterLt))))
       | _ + 3, _, earlierLt, _, _ =>
           Nat.noConfusion
             (natEqZeroOfLeZero
               (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc earlierLt))))⟩

/-! ## The Euclid invariant made a machine-checked fact (H2-SMITH r6, B2)

The termination side of the middle repair loop is already SHIPPED: `smithRepairDecreasesPivotSize`
(the strict measure `gcd(d_p, d_q).natAbs < d_p.natAbs` when `d_p ∤ d_q`, resting on
`natGcdLtLeftOfNotDivides`) and the inner-cascade descent `smithRotationDecreasesPivotSize`.  What
was only INFORMALLY described (§3 of the r6 recon: "gcd(pivotEntry, later) is INVARIANT while the
pivot magnitude drops") is now a proven lemma: `intGcdInvariantUnderAddScaledLeft` — the gcd is
unchanged by folding any multiple of the left argument into the right.  This is the exact arithmetic
core of the Euclid rotation: the fold + cascade replaces `(d_p, d_q)` by `(gcd, lcm)` WITHOUT changing
the pivot's gcd with the folded entry, so the classical invariant that made termination meaningful is
no longer a claim.  Pure Number-layer over the shipped signed-gcd certificates (`intGcdGreatest`,
`intGcdDividesLeft/Right`, the sign bridges) plus four small `IntDivides` combinators; no matrix
machinery, no propext traps. -/

/-- `divisor` divides `value`  ==>  `divisor` divides `value * multiplier` (the cofactor scales;
`intMulAssoc` reassociates). -/
theorem intDividesScaled {divisor value : Int} (divides : IntDivides divisor value)
    (multiplier : Int) : IntDivides divisor (value * multiplier) :=
  match divides with
  | ⟨factor, valueEquation⟩ =>
      ⟨factor * multiplier,
        (congrArg (· * multiplier) valueEquation).trans (intMulAssoc divisor factor multiplier)⟩

/-- `divisor` divides both summands  ==>  `divisor` divides their sum (the cofactors add;
`intLeftDistrib` refactors). -/
theorem intDividesSum {divisor leftValue rightValue : Int}
    (dividesLeft : IntDivides divisor leftValue) (dividesRight : IntDivides divisor rightValue) :
    IntDivides divisor (leftValue + rightValue) :=
  match dividesLeft, dividesRight with
  | ⟨leftFactor, leftEquation⟩, ⟨rightFactor, rightEquation⟩ =>
      ⟨leftFactor + rightFactor,
        ((congrArg (· + rightValue) leftEquation).trans
          (congrArg (divisor * leftFactor + ·) rightEquation)).trans
          (intLeftDistrib divisor leftFactor rightFactor).symm⟩

/-- `divisor` divides `value`  ==>  `divisor` divides `-value` (the cofactor negates; `intMulNeg`
pulls the sign out). -/
theorem intDividesNegated {divisor value : Int} (divides : IntDivides divisor value) :
    IntDivides divisor (-value) :=
  match divides with
  | ⟨factor, valueEquation⟩ =>
      ⟨-factor,
        (congrArg (fun entry => -entry) valueEquation).trans (intMulNeg divisor factor).symm⟩

/-- The residue direction — `divisor` divides `leftValue` and divides the fold `rightValue +
leftValue * multiplier`  ==>  `divisor` divides the base `rightValue`: subtract the folded multiple
back off (`(rightValue + leftValue * multiplier) + -(leftValue * multiplier) = rightValue` by
`intAddAssoc` / `intAddRightNeg` / `intAddZero`) and transport the sum-divisibility across the
cancellation. -/
theorem intDividesRightOfDividesFold {divisor leftValue rightValue multiplier : Int}
    (dividesLeft : IntDivides divisor leftValue)
    (dividesFold : IntDivides divisor (rightValue + leftValue * multiplier)) :
    IntDivides divisor rightValue :=
  have dividesSum :
      IntDivides divisor ((rightValue + leftValue * multiplier) + -(leftValue * multiplier)) :=
    intDividesSum dividesFold (intDividesNegated (intDividesScaled dividesLeft multiplier))
  have foldCancels :
      (rightValue + leftValue * multiplier) + -(leftValue * multiplier) = rightValue :=
    (intAddAssoc rightValue (leftValue * multiplier) (-(leftValue * multiplier))).trans
      ((congrArg (rightValue + ·) (intAddRightNeg (leftValue * multiplier))).trans
        (intAddZero rightValue))
  foldCancels ▸ dividesSum

/-- **gcd-invariance per rotation** — folding any integer multiple of `leftValue` into `rightValue`
leaves the gcd unchanged: `intGcd leftValue rightValue = intGcd leftValue (rightValue + leftValue *
multiplier)`.  The classical Euclid-rotation invariant the middle repair loop rides (the pivot's gcd
with a later entry is fixed while the pivot magnitude strictly drops — the counterpart of the shipped
descent `smithRepairDecreasesPivotSize`).  Each gcd is a common divisor of the OTHER's operand pair
(`intGcdGreatest` fed by the `IntDivides` combinators — forward via `intDividesSum`/`intDividesScaled`,
backward via `intDividesRightOfDividesFold`), so they divide each other; `natDividesAntisymm` on the
nonnegative magnitudes collapses the two divisibilities to equality. -/
theorem intGcdInvariantUnderAddScaledLeft (leftValue rightValue multiplier : Int) :
    intGcd leftValue rightValue = intGcd leftValue (rightValue + leftValue * multiplier) :=
  have forwardDivides :
      IntDivides (intGcd leftValue rightValue)
        (intGcd leftValue (rightValue + leftValue * multiplier)) :=
    intGcdGreatest (intGcdDividesLeft leftValue rightValue)
      (intDividesSum (intGcdDividesRight leftValue rightValue)
        (intDividesScaled (intGcdDividesLeft leftValue rightValue) multiplier))
  have backwardDivides :
      IntDivides (intGcd leftValue (rightValue + leftValue * multiplier))
        (intGcd leftValue rightValue) :=
    intGcdGreatest (intGcdDividesLeft leftValue (rightValue + leftValue * multiplier))
      (intDividesRightOfDividesFold
        (intGcdDividesLeft leftValue (rightValue + leftValue * multiplier))
        (intGcdDividesRight leftValue (rightValue + leftValue * multiplier)))
  congrArg Int.ofNat
    (natDividesAntisymm
      (natDividesNatAbsOfIntDivides forwardDivides)
      (natDividesNatAbsOfIntDivides backwardDivides))

end FX1Poly.ComputerAlgebra
