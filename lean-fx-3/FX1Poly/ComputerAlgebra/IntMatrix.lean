/-! # FX1Poly/ComputerAlgebra/IntMatrix — exact integer matrices + the unimodular operation alphabet
    (the `ComputerAlgebra/` substrate, brick 1)

`ComputerAlgebra/` is the Init-only certificate-first computational-algebra layer of the dependency
spine (`Init -> ComputerAlgebra/ -> Polygraph/ -> ...`, frontiers.md Domain XI): one library, three
payoffs —
Steiner/ADC homology via Smith normal form over ZZ (computable H1/H2 + torsion), the
Goreinov-Tyrtyshnikov-Zamarashkin ("Moscow") certificate ladder, and matroid-Hodge certificates.

This brick ships the CARRIER and the CERTIFICATE ALPHABET, certificate-first: the kernel never
trusts a solver — it CHECKS a reduction certificate (a list of elementary operations) against the
Smith-normal-form predicates.  The alphabet is exactly the UNIMODULAR (determinant +-1) row/column
operations — swap, negate, transvection — so a checked reduction witnesses genuine ZZ-equivalence
`A = U * D * V` with `U`, `V` invertible over ZZ (the U/V bookkeeping and the equivalence theorem
are later bricks; this file is data + predicates).

## Zero-axiom design decisions
  * Shape is EXTRINSIC: a matrix is a plain `List` of rows plus a separate `IsRectangular`
    proposition — every match below is on non-indexed inductives, so none of the indexed-match
    propext traps apply, and equality stays structural (no funext).
  * All list accessors are self-defined with fully enumerated match arms (no catch-all arms) so
    later proofs can `dsimp only` against controlled equations.
  * Indexing is by `Nat` with total out-of-range behaviour (reads default, writes no-op) — no
    `Fin` elimination anywhere.
  * Divisibility is the explicit-witness `dividesExactly` (no typeclass dependence).
  * Out-of-range elementary operations are IDENTITIES — an ill-formed certificate can never
    fabricate or destroy entries, only waste steps.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/IntMatrix.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-- One matrix row: the integer entries, left to right. -/
abbrev IntRow := List Int

/-- Read the entry at `position`, or `defaultEntry` past the end — total lookup, `Nat`-indexed. -/
def listGetWithDefault {Entry : Type} (defaultEntry : Entry) : List Entry → Nat → Entry
  | [], 0 => defaultEntry
  | [], _ + 1 => defaultEntry
  | entry :: _, 0 => entry
  | _ :: remainingEntries, position + 1 =>
      listGetWithDefault defaultEntry remainingEntries position

/-- Replace the entry at `position` (no-op past the end — writes can never grow a list). -/
def listReplaceAt {Entry : Type} : List Entry → Nat → Entry → List Entry
  | [], 0, _ => []
  | [], _ + 1, _ => []
  | _ :: remainingEntries, 0, newEntry => newEntry :: remainingEntries
  | entry :: remainingEntries, position + 1, newEntry =>
      entry :: listReplaceAt remainingEntries position newEntry

/-- Transform the entry at `position` in place (no-op past the end). -/
def listModifyAt {Entry : Type} (transform : Entry → Entry) : List Entry → Nat → List Entry
  | [], 0 => []
  | [], _ + 1 => []
  | entry :: remainingEntries, 0 => transform entry :: remainingEntries
  | entry :: remainingEntries, position + 1 =>
      entry :: listModifyAt transform remainingEntries position

/-- Map a transform over every row of a row list (self-defined for controlled equations). -/
def mapAllRows (transform : IntRow → IntRow) : List IntRow → List IntRow
  | [] => []
  | row :: remainingRows => transform row :: mapAllRows transform remainingRows

/-- `left` divides `right` over the integers — explicit-witness form, no typeclass dependence. -/
def dividesExactly (left right : Int) : Prop :=
  ∃ factor, right = left * factor

/-- An exact integer matrix: a list of rows.  Shape is carried extrinsically by
`IsRectangular`. -/
structure IntMatrix where
  rows : List IntRow

namespace IntMatrix

/-- Does every row in the list have exactly `expectedWidth` entries? -/
def rowsAllHaveWidth (expectedWidth : Nat) : List IntRow → Prop
  | [] => True
  | row :: remainingRows =>
      row.length = expectedWidth ∧ rowsAllHaveWidth expectedWidth remainingRows

/-- The matrix has exactly `height` rows, each of width `width`. -/
def IsRectangular (matrix : IntMatrix) (height width : Nat) : Prop :=
  matrix.rows.length = height ∧ rowsAllHaveWidth width matrix.rows

/-- The entry at `(rowIndex, colIndex)` — total, `0` outside the matrix. -/
def entryAt (matrix : IntMatrix) (rowIndex colIndex : Nat) : Int :=
  listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) colIndex

/-- The diagonal entry at `position` — total, `0` outside the matrix. -/
def diagonalEntryAt (matrix : IntMatrix) (position : Nat) : Int :=
  matrix.entryAt position position

/-! ## The unimodular row operations -/

/-- Swap two rows (identity unless BOTH indices are in range — an ill-formed certificate can
never fabricate a row). -/
def swapRows (matrix : IntMatrix) (firstIndex secondIndex : Nat) : IntMatrix :=
  if firstIndex < matrix.rows.length then
    if secondIndex < matrix.rows.length then
      let firstRow := listGetWithDefault [] matrix.rows firstIndex
      let secondRow := listGetWithDefault [] matrix.rows secondIndex
      { rows :=
          listReplaceAt (listReplaceAt matrix.rows firstIndex secondRow) secondIndex firstRow }
    else matrix
  else matrix

/-- Negate one row (determinant `-1` — unimodular; identity past the end). -/
def negateRow (matrix : IntMatrix) (rowIndex : Nat) : IntMatrix :=
  { rows :=
      listModifyAt (fun row => row.map (fun entry => -entry)) matrix.rows rowIndex }

/-- Add `coefficient` times the entries of `sourceRow` to `targetRow`, pointwise; ragged or
short rows truncate to the shorter length (rectangularity keeps this exact). -/
def addScaledEntries (coefficient : Int) : IntRow → IntRow → IntRow
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | sourceEntry :: sourceRemaining, targetEntry :: targetRemaining =>
      (targetEntry + coefficient * sourceEntry)
        :: addScaledEntries coefficient sourceRemaining targetRemaining

/-- The transvection: `targetRow += coefficient * sourceRow` (determinant `1`; identity unless
both indices are in range and distinct — a self-transvection is NOT unimodular for
`coefficient = -1`, so it is excluded at the operation level, not left to certificates). -/
def addRowMultiple (matrix : IntMatrix) (sourceIndex targetIndex : Nat)
    (coefficient : Int) : IntMatrix :=
  if sourceIndex = targetIndex then matrix
  else
    if sourceIndex < matrix.rows.length then
      if targetIndex < matrix.rows.length then
        let sourceRow := listGetWithDefault [] matrix.rows sourceIndex
        { rows :=
            listModifyAt (fun targetRow => addScaledEntries coefficient sourceRow targetRow)
              matrix.rows targetIndex }
      else matrix
    else matrix

/-! ## The unimodular column operations (implemented row-locally — no transpose needed) -/

/-- Swap the entries at two column positions within one row (identity unless both in range). -/
def swapEntriesWithinRow (row : IntRow) (firstIndex secondIndex : Nat) : IntRow :=
  if firstIndex < row.length then
    if secondIndex < row.length then
      let firstEntry := listGetWithDefault 0 row firstIndex
      let secondEntry := listGetWithDefault 0 row secondIndex
      listReplaceAt (listReplaceAt row firstIndex secondEntry) secondIndex firstEntry
    else row
  else row

/-- Swap two columns. -/
def swapColumns (matrix : IntMatrix) (firstIndex secondIndex : Nat) : IntMatrix :=
  { rows := mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex) matrix.rows }

/-- Negate one column. -/
def negateColumn (matrix : IntMatrix) (colIndex : Nat) : IntMatrix :=
  { rows :=
      mapAllRows (fun row => listModifyAt (fun entry => -entry) row colIndex) matrix.rows }

/-- Column transvection within one row: `entry(target) += coefficient * entry(source)`. -/
def addScaledEntryWithinRow (row : IntRow) (sourceIndex targetIndex : Nat)
    (coefficient : Int) : IntRow :=
  if sourceIndex < row.length then
    let sourceEntry := listGetWithDefault 0 row sourceIndex
    listModifyAt (fun targetEntry => targetEntry + coefficient * sourceEntry) row targetIndex
  else row

/-- The column transvection: `column(target) += coefficient * column(source)` (identity on a
self-transvection, mirroring `addRowMultiple`). -/
def addColumnMultiple (matrix : IntMatrix) (sourceIndex targetIndex : Nat)
    (coefficient : Int) : IntMatrix :=
  if sourceIndex = targetIndex then matrix
  else
    { rows :=
        mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          matrix.rows }

end IntMatrix

/-! ## The certificate alphabet -/

/-- A unimodular row operation — one letter of the reduction-certificate alphabet. -/
inductive ElementaryRowOperation
  | swapRows (firstIndex secondIndex : Nat)
  | negateRow (rowIndex : Nat)
  | addRowMultiple (sourceIndex targetIndex : Nat) (coefficient : Int)

/-- A unimodular column operation. -/
inductive ElementaryColumnOperation
  | swapColumns (firstIndex secondIndex : Nat)
  | negateColumn (colIndex : Nat)
  | addColumnMultiple (sourceIndex targetIndex : Nat) (coefficient : Int)

/-- One certificate step: a row- or column-side unimodular operation. -/
inductive ElementaryOperation
  | rowOperation (operation : ElementaryRowOperation)
  | columnOperation (operation : ElementaryColumnOperation)

namespace IntMatrix

/-- Fire one row operation. -/
def applyRowOperation (matrix : IntMatrix) : ElementaryRowOperation → IntMatrix
  | .swapRows firstIndex secondIndex => matrix.swapRows firstIndex secondIndex
  | .negateRow rowIndex => matrix.negateRow rowIndex
  | .addRowMultiple sourceIndex targetIndex coefficient =>
      matrix.addRowMultiple sourceIndex targetIndex coefficient

/-- Fire one column operation. -/
def applyColumnOperation (matrix : IntMatrix) : ElementaryColumnOperation → IntMatrix
  | .swapColumns firstIndex secondIndex => matrix.swapColumns firstIndex secondIndex
  | .negateColumn colIndex => matrix.negateColumn colIndex
  | .addColumnMultiple sourceIndex targetIndex coefficient =>
      matrix.addColumnMultiple sourceIndex targetIndex coefficient

/-- Fire one certificate step. -/
def applyOperation (matrix : IntMatrix) : ElementaryOperation → IntMatrix
  | .rowOperation operation => matrix.applyRowOperation operation
  | .columnOperation operation => matrix.applyColumnOperation operation

/-- Fire a whole certificate, left to right. -/
def applyOperations (matrix : IntMatrix) : List ElementaryOperation → IntMatrix
  | [] => matrix
  | operation :: remainingOperations =>
      (matrix.applyOperation operation).applyOperations remainingOperations

/-! ## The Smith-normal-form predicates -/

/-- Smith normal form within the `height × width` window: off-diagonal entries vanish, the
diagonal is nonnegative, and each diagonal entry divides its successor (so zero diagonal
entries come last — `dividesExactly 0 d` forces `d = 0`). -/
structure IsSmithNormalFormWithin (matrix : IntMatrix) (height width : Nat) : Prop where
  offDiagonalVanishes :
    ∀ rowIndex colIndex, rowIndex < height → colIndex < width →
      rowIndex ≠ colIndex → matrix.entryAt rowIndex colIndex = 0
  diagonalIsNonnegative :
    ∀ position, position < Nat.min height width → 0 ≤ matrix.diagonalEntryAt position
  diagonalDividesSuccessor :
    ∀ position, position + 1 < Nat.min height width →
      dividesExactly (matrix.diagonalEntryAt position) (matrix.diagonalEntryAt (position + 1))

/-- A reduction certificate: the operation word taking the matrix to Smith normal form.  The
checker consumes this; no solver is ever trusted. -/
structure SmithReductionCertificate where
  operations : List ElementaryOperation

/-- The certificate `certificate` reduces `matrix` to Smith normal form within the
`height × width` window. -/
def SmithReductionCertificate.reducesToSmithForm (certificate : SmithReductionCertificate)
    (matrix : IntMatrix) (height width : Nat) : Prop :=
  (matrix.applyOperations certificate.operations).IsSmithNormalFormWithin height width

end IntMatrix

end FX1Poly.ComputerAlgebra
