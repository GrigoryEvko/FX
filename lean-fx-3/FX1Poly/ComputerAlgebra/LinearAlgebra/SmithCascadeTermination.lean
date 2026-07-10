import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithNormalForm

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithCascadeTermination — the Euclid-cascade
    descent-measure infrastructure (H2-SMITH r8)

`SmithNormalForm` ships the total driver (`smithReduceTotal` / `smithReduceFull`), the Euclid
cascade (`smithCascadeSweep`), the minimal-magnitude search (`smithFindMinAbsInMinor`), the
exact clears, and the *shipped* strict rotation-descent
`smithRotationDecreasesPivotSize : intMagnitudeRemainder pivot.natAbs entry < pivot.natAbs`.
What that descent still needs, to become the fuel-adequacy heart of the cascade recursion, is a
bridge from the abstract remainder to the *actual matrix entry the clear op lands*, plus the
search-correctness lower bound.  This module ships that infrastructure as FUNCTION-CORRECTNESS
lemmas — each a statement about one operation or one scan, never a sweep over arbitrary
window-diagonal inputs — so they are immune to the r5/r6 refutation shape (the driver is correct
only along its own min-abs-presorted path; POLE-A/POLE-B died stating correctness over arbitrary
diagonals, see `SmithNormalForm`'s refuted `SmithCascadeReDiagonalizesStatement` cluster).

  * **Signed-residue reconstruction** (`intMagnitudeReconstructs`): the counting divider's `Int`
    factorization `mantissa = quotient * ofNat d + signedResidue`, carrying the sign
    (`signedResidue.natAbs = intMagnitudeRemainder d mantissa`).  The `ofNat` arm mirrors the
    shipped `intMagnitudeDivisionExact`; the `negSucc` arm distributes the negation through
    `intNegAdd` / `intNegMul`.
  * **Column ON-target entry formula** (`addColumnMultipleEntryOnTargetCol`): the column mirror of
    the shipped row formula `addRowMultipleEntryOnTargetRow`, reading the target column after a
    `addColumnMultiple` through the new `listGetWithDefaultMapAllRows` row-read and the shipped
    `listGetWithDefaultModifyAtEq`.
  * **Single-clear residue landing** (`smithSingleClearResidueLands`): one row-right clear column
    op at a NONNEGATIVE pivot lands the cross entry with `natAbs = intMagnitudeRemainder`.
    Composes the two above with the reconstruction; combined with the shipped
    `smithRotationDecreasesPivotSize` this is the single-step strict descent the cascade rides.

  * **Minimal-magnitude search lower bound** (`smithFindMinAbsInMinorBoundsWitness` and the row/minor
    scan lemmas beneath it): `smithFindMinAbsInMinor` returns a `some` position whose magnitude is
    `≤` that of any nonzero entry in the pivot minor.  Feeding the parked residue as the witness gives
    the cascade's next-pivot bound `found ≤ residue < pivot`.  Structural over the scans, with the
    update-step guards navigated propext-cleanly (`natBeqZeroFalseOfNe`, `Nat.decLt`).

The cascade-recursion ASSEMBLY that consumes this — the fuel-adequacy induction threading min-abs
through `smithCascadeSweep` — is the r9 wall (the shared r3/r6 elimination-correctness node
`SmithReduceFullDriverStatement`, uninhabited).

## Zero-axiom

`congrArg`/`Eq.trans` witness arithmetic over the propext-clean `Int` kit
(`intNegMul` / `intNegAdd` / `intAddAssoc` / `intAddRightNeg`), structural list recursion, and the
shipped `if_pos`/`if_neg` navigation of the operation guards (`decide` never touches a driver
expression).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithCascadeTermination.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The signed-residue reconstruction (the descent's arithmetic core)

`intMagnitudeQuotient` / `intMagnitudeRemainder` divide an `Int`'s magnitude by a `Nat`, quotient
sign-reattached.  The clear op needs the SIGNED residue `mantissa - quotient * divisor`, the entry
that actually lands in the matrix, and the fact that its magnitude is the (unsigned) counting
remainder the shipped bound `smithRotationDecreasesPivotSize` reasons about. -/

/-- The signed residue `mantissa - intMagnitudeQuotient d mantissa * d` — the mirror of
`intMagnitudeQuotient`: an `ofNat` residue on nonnegative mantissas, a negated one on `negSucc`. -/
def intMagnitudeSignedRemainder (divisor : Nat) : Int → Int
  | .ofNat magnitude => Int.ofNat (natDivModCounting magnitude divisor).snd
  | .negSucc magnitudePredecessor =>
      -(Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).snd)

/-- The signed residue's magnitude IS the unsigned magnitude remainder — the `ofNat` arm is `rfl`,
the `negSucc` arm strips the sign through `intNegOfNatNatAbs`.  This is what bridges the signed
entry the clear op lands to the shipped bound `smithRotationDecreasesPivotSize`. -/
theorem intMagnitudeSignedRemainderNatAbs (divisor : Nat) : ∀ mantissa : Int,
    (intMagnitudeSignedRemainder divisor mantissa).natAbs
      = intMagnitudeRemainder divisor mantissa
  | .ofNat _ => rfl
  | .negSucc magnitudePredecessor =>
      intNegOfNatNatAbs (natDivModCounting (magnitudePredecessor + 1) divisor).snd

/-- **Signed-residue reconstruction** — `mantissa = quotient * ofNat divisor + signedResidue` in
`Int`, carrying the sign.  The `ofNat` arm is the counting reconstruction under `congrArg Int.ofNat`
(with `Nat.mul_comm` to flip the factor order, exactly as the shipped `intMagnitudeDivisionExact`);
the `negSucc` arm proves the positive shadow, negates it, and distributes the negation over the sum
(`intNegAdd`) and the product (`intNegMul`). -/
theorem intMagnitudeReconstructs (divisor : Nat) : ∀ mantissa : Int,
    mantissa = intMagnitudeQuotient divisor mantissa * Int.ofNat divisor
      + intMagnitudeSignedRemainder divisor mantissa
  | .ofNat magnitude =>
      congrArg Int.ofNat
        ((natDivModCountingReconstructs magnitude divisor).trans
          (congrArg (· + (natDivModCounting magnitude divisor).snd)
            (Nat.mul_comm divisor (natDivModCounting magnitude divisor).fst)))
  | .negSucc magnitudePredecessor =>
      (congrArg (fun value => -value)
          (congrArg Int.ofNat
            ((natDivModCountingReconstructs (magnitudePredecessor + 1) divisor).trans
              (congrArg (· + (natDivModCounting (magnitudePredecessor + 1) divisor).snd)
                (Nat.mul_comm divisor
                  (natDivModCounting (magnitudePredecessor + 1) divisor).fst))))).trans
        ((intNegAdd
            (Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).fst
              * Int.ofNat divisor)
            (Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).snd)).trans
          (congrArg
            (· + -(Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).snd))
            (intNegMul
              (Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).fst)
              (Int.ofNat divisor)).symm))

/-- A nonnegative `Int` is its own magnitude as an `ofNat` — the `natAbs` sibling of the shipped
`intOfNatToNatOfNonNeg`, riding the `intZeroLeDest` destruction.  This is what lets the clear's
divisor `pivot.natAbs` reattach to the nonnegative pivot the sign pass guarantees. -/
theorem intOfNatNatAbsOfNonNeg {value : Int} (isNonNegative : (0 : Int) ≤ value) :
    Int.ofNat value.natAbs = value :=
  match intZeroLeDest isNonNegative with
  | ⟨_, valueEquation⟩ =>
      (congrArg (fun sameValue => Int.ofNat sameValue.natAbs) valueEquation).trans
        valueEquation.symm

/-! ## The column ON-target entry formula (the row formula's column mirror)

`smithClearRowRightSteps` clears the pivot row by `addColumnMultiple` column transvections; the
shipped entry formulas cover only the ROW transvection (`addRowMultiple`).  This section supplies
the column mirror: a `mapAllRows` row-read (`listGetWithDefaultMapAllRows`) feeding the shipped
at-index read `listGetWithDefaultModifyAtEq` through `addScaledEntryWithinRow`. -/

/-- Reading an in-range row after `mapAllRows` returns the transformed original row — the row-list
locality of a per-row map.  Structural on the row list. -/
theorem listGetWithDefaultMapAllRows (transform : IntRow → IntRow) :
    ∀ (rows : List IntRow) (position : Nat), position < rows.length →
      listGetWithDefault [] (mapAllRows transform rows) position
        = transform (listGetWithDefault [] rows position)
  | [], _, isInRange => Nat.noConfusion (natEqZeroOfLeZero isInRange)
  | _ :: _, 0, _ => rfl
  | _ :: remainingRows, position + 1, isInRange =>
      listGetWithDefaultMapAllRows transform remainingRows position (natLeOfSuccLeSucc isInRange)

/-- **The column ON-target entry formula** — the column mirror of the shipped
`addRowMultipleEntryOnTargetRow`: reading the TARGET column after `addColumnMultiple sourceIndex
targetIndex coefficient` gives `old(row, target) + coefficient * old(row, source)`, for distinct
in-range columns and an in-range row (rectangularity supplies the row width).  Navigates the
`addColumnMultiple` distinctness guard and the `addScaledEntryWithinRow` source-in-range guard,
reads the mapped row by `listGetWithDefaultMapAllRows`, then the modified entry by
`listGetWithDefaultModifyAtEq`. -/
theorem addColumnMultipleEntryOnTargetCol {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (sourceIndex targetIndex rowIndex : Nat) (coefficient : Int)
    (isDistinct : sourceIndex ≠ targetIndex)
    (isRowInRange : rowIndex < height)
    (isSourceInRange : sourceIndex < width) (isTargetInRange : targetIndex < width) :
    (matrix.addColumnMultiple sourceIndex targetIndex coefficient).entryAt rowIndex targetIndex
      = matrix.entryAt rowIndex targetIndex
          + coefficient * matrix.entryAt rowIndex sourceIndex := by
  obtain ⟨rowCount, rowWidths⟩ := isRect
  have rowInRows : rowIndex < matrix.rows.length :=
    Eq.mp (congrArg (rowIndex < ·) rowCount.symm) isRowInRange
  have rowHasWidth : (listGetWithDefault [] matrix.rows rowIndex).length = width :=
    listGetWithDefaultHasWidth matrix.rows rowIndex rowWidths rowInRows
  unfold IntMatrix.addColumnMultiple
  rw [if_neg isDistinct]
  show listGetWithDefault 0
      (listGetWithDefault []
        (mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          matrix.rows) rowIndex) targetIndex = _
  rw [listGetWithDefaultMapAllRows _ matrix.rows rowIndex rowInRows]
  unfold IntMatrix.addScaledEntryWithinRow
  rw [if_pos (Eq.mp (congrArg (sourceIndex < ·) rowHasWidth.symm) isSourceInRange)]
  rw [listGetWithDefaultModifyAtEq 0 _ (listGetWithDefault [] matrix.rows rowIndex) targetIndex
      (Eq.mp (congrArg (targetIndex < ·) rowHasWidth.symm) isTargetInRange)]
  rfl

/-! ## The single-clear residue landing (the single-step strict descent)

Composing the column entry formula, the signed-residue reconstruction, and the nonnegative-pivot
bridge: one row-right clear column op at a NONNEGATIVE pivot lands the cross entry exactly on the
signed residue, whose magnitude is `intMagnitudeRemainder pivot.natAbs old` — the value the shipped
`smithRotationDecreasesPivotSize` proves strictly below `pivot.natAbs`.  This is the r8 form of the
cascade's per-rotation strict descent; the RECURSION over it (fuel adequacy) is r9. -/

/-- **The single-clear residue landing** — firing the row-right clear column op
`addColumnMultiple pivotIndex colIndex (-(intPivotQuotient pivot old))` at a nonnegative pivot lands
the cross entry `(pivotIndex, colIndex)` with magnitude exactly `intMagnitudeRemainder pivot.natAbs
old`.  The entry formula gives `old + (-(quotient)) * pivot`; `intNegMul` and the nonnegative-pivot
bridge rewrite `pivot` to `ofNat pivot.natAbs`, the signed-residue reconstruction folds the sum to
`signedResidue`, and `intMagnitudeSignedRemainderNatAbs` reads off the magnitude.  Combined with the
shipped `smithRotationDecreasesPivotSize`, `(landed entry).natAbs < pivot.natAbs` when the pivot is
positive — the cascade's strict per-rotation descent. -/
theorem smithSingleClearResidueLands {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex colIndex : Nat)
    (isDistinct : pivotIndex ≠ colIndex)
    (isPivotRowInRange : pivotIndex < height)
    (isPivotColInRange : pivotIndex < width)
    (isTargetColInRange : colIndex < width)
    (isPivotNonneg : (0 : Int) ≤ matrix.entryAt pivotIndex pivotIndex) :
    ((matrix.addColumnMultiple pivotIndex colIndex
        (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
            (matrix.entryAt pivotIndex colIndex)))).entryAt pivotIndex colIndex).natAbs
      = intMagnitudeRemainder (matrix.entryAt pivotIndex pivotIndex).natAbs
          (matrix.entryAt pivotIndex colIndex) :=
  let pivot := matrix.entryAt pivotIndex pivotIndex
  let old := matrix.entryAt pivotIndex colIndex
  let productTerm := intMagnitudeQuotient pivot.natAbs old * Int.ofNat pivot.natAbs
  let signedResidue := intMagnitudeSignedRemainder pivot.natAbs old
  have entryFormula :
      (matrix.addColumnMultiple pivotIndex colIndex (-(intPivotQuotient pivot old))).entryAt
          pivotIndex colIndex
        = old + (-(intPivotQuotient pivot old)) * pivot :=
    addColumnMultipleEntryOnTargetCol matrix isRect pivotIndex colIndex pivotIndex
      (-(intPivotQuotient pivot old)) isDistinct isPivotRowInRange isPivotColInRange
      isTargetColInRange
  have pivotIsOfNat : pivot = Int.ofNat pivot.natAbs :=
    (intOfNatNatAbsOfNonNeg isPivotNonneg).symm
  have reconstruction : old = productTerm + signedResidue :=
    intMagnitudeReconstructs pivot.natAbs old
  have landsOnResidue : old + (-(intPivotQuotient pivot old)) * pivot = signedResidue :=
    (congrArg (old + ·) (intNegMul (intPivotQuotient pivot old) pivot)).trans
      ((congrArg (fun scale => old + -(intMagnitudeQuotient pivot.natAbs old * scale))
            pivotIsOfNat).trans
        ((congrArg (· + -productTerm) reconstruction).trans
          ((intAddAssoc productTerm signedResidue (-productTerm)).trans
            ((congrArg (productTerm + ·) (intAddComm signedResidue (-productTerm))).trans
              ((intAddAssoc productTerm (-productTerm) signedResidue).symm.trans
                ((congrArg (· + signedResidue) (intAddRightNeg productTerm)).trans
                  (intZeroAdd signedResidue)))))))
  (congrArg Int.natAbs (entryFormula.trans landsOnResidue)).trans
    (intMagnitudeSignedRemainderNatAbs pivot.natAbs old)

/-- **The single-rotation strict descent** — for a POSITIVE pivot, one row-right clear column op
lands the cross entry with magnitude STRICTLY below the pivot's.  The composition the cascade's fuel
adequacy rides: the residue landing (`smithSingleClearResidueLands`, magnitude `=`
`intMagnitudeRemainder`) rewritten into the shipped remainder bound
(`smithRotationDecreasesPivotSize`, `<` the pivot).  This is the r8 endpoint of the per-rotation
measure decrease; the RECURSION over it (that the cascade halts at a cross-clear state within its
min-abs fuel) is the r9 assembly. -/
theorem smithSingleClearStrictlyDecreasesPivot {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex colIndex : Nat)
    (isDistinct : pivotIndex ≠ colIndex)
    (isPivotRowInRange : pivotIndex < height)
    (isPivotColInRange : pivotIndex < width)
    (isTargetColInRange : colIndex < width)
    (isPivotNonneg : (0 : Int) ≤ matrix.entryAt pivotIndex pivotIndex)
    (isPivotPositive : 0 < (matrix.entryAt pivotIndex pivotIndex).natAbs) :
    ((matrix.addColumnMultiple pivotIndex colIndex
        (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
            (matrix.entryAt pivotIndex colIndex)))).entryAt pivotIndex colIndex).natAbs
      < (matrix.entryAt pivotIndex pivotIndex).natAbs :=
  Eq.mpr
    (congrArg (· < (matrix.entryAt pivotIndex pivotIndex).natAbs)
      (smithSingleClearResidueLands matrix isRect pivotIndex colIndex isDistinct isPivotRowInRange
        isPivotColInRange isTargetColInRange isPivotNonneg))
    (smithRotationDecreasesPivotSize (matrix.entryAt pivotIndex pivotIndex)
      (matrix.entryAt pivotIndex colIndex) isPivotPositive)

/-! ## The minimal-magnitude search lower bound (the search-correctness sibling)

The strict descent above shows the parked cross entry is a residue below the pivot; the cascade's
next rotation searches the minor for a strictly smaller pivot.  For that search to make progress the
selected minimal-magnitude entry must be a genuine LOWER BOUND — no larger than any particular
nonzero entry present in the minor.  These lemmas discharge exactly that, at scan granularity: given
a nonzero entry anywhere in the scanned region, `smithFindMinAbsInMinor` returns `some` position
whose magnitude is `≤` the witness's.  Combined with the residue landing (witness := the parked
residue) this is the r9 assembly's "found ≤ residue < pivot" step; here the search correctness stands
alone as a function-correctness fact, refutation-immune.

Each update step is characterized about the reduced `if`/`if`-chain a CONSTRUCTOR `best` produces
(so the scan step is definitionally that same expression — a freshly written `match best with` would
compile to a distinct match-auxiliary that is not defeq to the scan's internal one).  The `== 0`
guard is navigated by the structural `natBeqZeroFalseOfNe` (no `LawfulBEq` reflection, which drags in
`propext`), the `<` guard by `Nat.decLt` + `if_pos`/`if_neg`. -/

/-- `magnitude == 0` is `false` for a positive `magnitude` — structural on `magnitude`, dodging the
`propext`-tainted `LawfulBEq`-instance reflection route to `eq_of_beq`. -/
theorem natBeqZeroFalseOfNe : ∀ magnitude : Nat, magnitude ≠ 0 → (magnitude == 0) = false
  | 0, isNonzero => absurd rfl isNonzero
  | _ + 1, _ => rfl

/-- The row-scan update keeps a `some` best and never grows its magnitude (regardless of the current
entry): the `== 0` branch keeps the best, the `<` branches take the strictly smaller or keep the
best. -/
theorem smithScanRowUpdateSomeBound (matrix : IntMatrix) (rowIndex colStart bestRow bestCol : Nat) :
    ∃ foundRow foundCol,
      (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
       else if (matrix.entryAt rowIndex colStart).natAbs
              < (matrix.entryAt bestRow bestCol).natAbs then some (rowIndex, colStart)
       else some (bestRow, bestCol)) = some (foundRow, foundCol)
      ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt bestRow bestCol).natAbs :=
  match (matrix.entryAt rowIndex colStart).natAbs == 0 with
  | true => ⟨bestRow, bestCol, rfl, Nat.le_refl _⟩
  | false =>
      match Nat.decLt (matrix.entryAt rowIndex colStart).natAbs
          (matrix.entryAt bestRow bestCol).natAbs with
      | isTrue hLt =>
          ⟨rowIndex, colStart,
            (if_neg (fun isTrueEq => Bool.noConfusion isTrueEq)).trans (if_pos hLt),
            Nat.le_of_lt hLt⟩
      | isFalse hNlt =>
          ⟨bestRow, bestCol,
            (if_neg (fun isTrueEq => Bool.noConfusion isTrueEq)).trans (if_neg hNlt),
            Nat.le_refl _⟩

/-- The row-scan update at a nonzero entry with an empty best selects that entry — magnitude equal to
this entry (the `== 0` branch is impossible, closed by `natBeqZeroFalseOfNe`). -/
theorem smithScanRowUpdateNoneBound (matrix : IntMatrix) (rowIndex colStart : Nat)
    (entryNonzero : (matrix.entryAt rowIndex colStart).natAbs ≠ 0) :
    ∃ foundRow foundCol,
      (if (matrix.entryAt rowIndex colStart).natAbs == 0 then none else some (rowIndex, colStart))
        = some (foundRow, foundCol)
      ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt rowIndex colStart).natAbs :=
  ⟨rowIndex, colStart,
    if_neg (fun isEqZero =>
      Bool.noConfusion (isEqZero.symm.trans (natBeqZeroFalseOfNe _ entryNonzero))),
    Nat.le_refl _⟩

/-- The row-scan update at a nonzero entry with a `some` best keeps `some` with magnitude never
exceeding THIS entry: the `<` branch takes the entry, the `≥` branch keeps a best already `≤` the
entry. -/
theorem smithScanRowUpdateSomeEntryBound (matrix : IntMatrix)
    (rowIndex colStart bestRow bestCol : Nat)
    (entryNonzero : (matrix.entryAt rowIndex colStart).natAbs ≠ 0) :
    ∃ foundRow foundCol,
      (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
       else if (matrix.entryAt rowIndex colStart).natAbs
              < (matrix.entryAt bestRow bestCol).natAbs then some (rowIndex, colStart)
       else some (bestRow, bestCol)) = some (foundRow, foundCol)
      ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt rowIndex colStart).natAbs :=
  match Nat.decLt (matrix.entryAt rowIndex colStart).natAbs
      (matrix.entryAt bestRow bestCol).natAbs with
  | isTrue hLt =>
      ⟨rowIndex, colStart,
        (if_neg (fun isEqZero =>
          Bool.noConfusion (isEqZero.symm.trans (natBeqZeroFalseOfNe _ entryNonzero)))).trans
          (if_pos hLt),
        Nat.le_refl _⟩
  | isFalse hNlt =>
      ⟨bestRow, bestCol,
        (if_neg (fun isEqZero =>
          Bool.noConfusion (isEqZero.symm.trans (natBeqZeroFalseOfNe _ entryNonzero)))).trans
          (if_neg hNlt),
        (Nat.lt_or_ge (matrix.entryAt rowIndex colStart).natAbs
            (matrix.entryAt bestRow bestCol).natAbs).elim (fun hLt => absurd hLt hNlt) id⟩

/-- **Row scan preserves a `some` bound** — scanning any column window from a `some` best returns a
`some` position whose magnitude is `≤` the incoming best's.  Structural on the column count, threading
`smithScanRowUpdateSomeBound` through the recursion. -/
theorem smithScanRowMinAbsPreservesSomeBound (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart bestRow bestCol : Nat),
      ∃ foundRow foundCol,
        smithScanRowMinAbs matrix rowIndex colCount colStart (some (bestRow, bestCol))
          = some (foundRow, foundCol)
        ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt bestRow bestCol).natAbs
  | 0, _, bestRow, bestCol => ⟨bestRow, bestCol, rfl, Nat.le_refl _⟩
  | colCount + 1, colStart, bestRow, bestCol =>
      match smithScanRowUpdateSomeBound matrix rowIndex colStart bestRow bestCol with
      | ⟨updRow, updCol, updEq, updLe⟩ =>
          match smithScanRowMinAbsPreservesSomeBound matrix rowIndex colCount (colStart + 1)
              updRow updCol with
          | ⟨foundRow, foundCol, foundEq, foundLe⟩ =>
              ⟨foundRow, foundCol,
                (congrArg (smithScanRowMinAbs matrix rowIndex colCount (colStart + 1)) updEq).trans
                  foundEq,
                Nat.le_trans foundLe updLe⟩

/-- **Row scan lower bound at a witness** — if a nonzero entry sits at `witnessCol` within the scanned
window, the scan returns `some` position whose magnitude is `≤` the witness's.  Structural on the
column count; at the witness column (`Nat.le.dest` diff `0`) the update selects a magnitude `≤` the
witness and `PreservesSomeBound` carries it to the end; past it (diff `+1`) the recursion advances one
column with the guaranteed-`some` updated best. -/
theorem smithScanRowMinAbsBoundsWitness (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart witnessCol : Nat) (best : Option (Nat × Nat)),
      colStart ≤ witnessCol → witnessCol < colStart + colCount →
      (matrix.entryAt rowIndex witnessCol).natAbs ≠ 0 →
      ∃ foundRow foundCol,
        smithScanRowMinAbs matrix rowIndex colCount colStart best = some (foundRow, foundCol)
        ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt rowIndex witnessCol).natAbs
  | 0, colStart, witnessCol, _, witColGe, witColLt, _ =>
      absurd (Nat.lt_of_lt_of_le witColLt witColGe) (Nat.lt_irrefl witnessCol)
  | colCount + 1, colStart, witnessCol, none, witColGe, witColLt, witNonzero =>
      match Nat.le.dest witColGe with
      | ⟨0, colEq⟩ =>
          have entryNonzeroHere : (matrix.entryAt rowIndex colStart).natAbs ≠ 0 :=
            fun isZero => witNonzero
              ((congrArg (fun col => (matrix.entryAt rowIndex col).natAbs) colEq).symm.trans isZero)
          match smithScanRowUpdateNoneBound matrix rowIndex colStart entryNonzeroHere with
          | ⟨updRow, updCol, updEq, updLe⟩ =>
              match smithScanRowMinAbsPreservesSomeBound matrix rowIndex colCount (colStart + 1)
                  updRow updCol with
              | ⟨foundRow, foundCol, foundEq, foundLe⟩ =>
                  ⟨foundRow, foundCol,
                    (congrArg (smithScanRowMinAbs matrix rowIndex colCount (colStart + 1))
                        updEq).trans foundEq,
                    Nat.le_trans (Nat.le_trans foundLe updLe)
                      (Nat.le_of_eq
                        (congrArg (fun col => (matrix.entryAt rowIndex col).natAbs) colEq))⟩
      | ⟨diff + 1, colEq⟩ =>
          smithScanRowMinAbsBoundsWitness matrix rowIndex colCount (colStart + 1) witnessCol
            (if (matrix.entryAt rowIndex colStart).natAbs == 0 then none
             else some (rowIndex, colStart))
            (Nat.le.intro ((Nat.succ_add colStart diff).trans colEq))
            (Eq.mp (congrArg (witnessCol < ·) (Nat.succ_add colStart colCount).symm) witColLt)
            witNonzero
  | colCount + 1, colStart, witnessCol, some (bestRow, bestCol),
      witColGe, witColLt, witNonzero =>
      match Nat.le.dest witColGe with
      | ⟨0, colEq⟩ =>
          have entryNonzeroHere : (matrix.entryAt rowIndex colStart).natAbs ≠ 0 :=
            fun isZero => witNonzero
              ((congrArg (fun col => (matrix.entryAt rowIndex col).natAbs) colEq).symm.trans isZero)
          match smithScanRowUpdateSomeEntryBound matrix rowIndex colStart bestRow bestCol
              entryNonzeroHere with
          | ⟨updRow, updCol, updEq, updLe⟩ =>
              match smithScanRowMinAbsPreservesSomeBound matrix rowIndex colCount (colStart + 1)
                  updRow updCol with
              | ⟨foundRow, foundCol, foundEq, foundLe⟩ =>
                  ⟨foundRow, foundCol,
                    (congrArg (smithScanRowMinAbs matrix rowIndex colCount (colStart + 1))
                        updEq).trans foundEq,
                    Nat.le_trans (Nat.le_trans foundLe updLe)
                      (Nat.le_of_eq
                        (congrArg (fun col => (matrix.entryAt rowIndex col).natAbs) colEq))⟩
      | ⟨diff + 1, colEq⟩ =>
          smithScanRowMinAbsBoundsWitness matrix rowIndex colCount (colStart + 1) witnessCol
            (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
             else if (matrix.entryAt rowIndex colStart).natAbs
                    < (matrix.entryAt bestRow bestCol).natAbs then some (rowIndex, colStart)
             else some (bestRow, bestCol))
            (Nat.le.intro ((Nat.succ_add colStart diff).trans colEq))
            (Eq.mp (congrArg (witnessCol < ·) (Nat.succ_add colStart colCount).symm) witColLt)
            witNonzero

/-- **Minor scan preserves a `some` bound** — the row-folded minor scan keeps a `some` best and never
grows its magnitude.  Structural on the row count, lifting the row-scan `PreservesSomeBound` through
each folded row. -/
theorem smithScanMinorMinAbsPreservesSomeBound (matrix : IntMatrix) (colStart colCount : Nat) :
    ∀ (rowCount rowStart bestRow bestCol : Nat),
      ∃ foundRow foundCol,
        smithScanMinorMinAbs matrix colStart colCount rowCount rowStart (some (bestRow, bestCol))
          = some (foundRow, foundCol)
        ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt bestRow bestCol).natAbs
  | 0, _, bestRow, bestCol => ⟨bestRow, bestCol, rfl, Nat.le_refl _⟩
  | rowCount + 1, rowStart, bestRow, bestCol =>
      match smithScanRowMinAbsPreservesSomeBound matrix rowStart colCount colStart bestRow
          bestCol with
      | ⟨innerRow, innerCol, innerEq, innerLe⟩ =>
          match smithScanMinorMinAbsPreservesSomeBound matrix colStart colCount rowCount
              (rowStart + 1) innerRow innerCol with
          | ⟨foundRow, foundCol, foundEq, foundLe⟩ =>
              ⟨foundRow, foundCol,
                (congrArg (smithScanMinorMinAbs matrix colStart colCount rowCount (rowStart + 1))
                    innerEq).trans foundEq,
                Nat.le_trans foundLe innerLe⟩

/-- **Minor scan lower bound at a witness** — if a nonzero entry sits at `(witnessRow, witnessCol)`
within the scanned rectangle, the minor scan returns `some` position whose magnitude is `≤` the
witness's.  Structural on the row count; at the witness row the inner row-scan bounds by the witness
(row `BoundsWitness`) and `PreservesSomeBound` carries it; past it the recursion advances one row with
the folded-through best. -/
theorem smithScanMinorMinAbsBoundsWitness (matrix : IntMatrix) (colStart colCount : Nat) :
    ∀ (rowCount rowStart witnessRow witnessCol : Nat) (best : Option (Nat × Nat)),
      rowStart ≤ witnessRow → witnessRow < rowStart + rowCount →
      colStart ≤ witnessCol → witnessCol < colStart + colCount →
      (matrix.entryAt witnessRow witnessCol).natAbs ≠ 0 →
      ∃ foundRow foundCol,
        smithScanMinorMinAbs matrix colStart colCount rowCount rowStart best
          = some (foundRow, foundCol)
        ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt witnessRow witnessCol).natAbs
  | 0, rowStart, witnessRow, _, _, witRowGe, witRowLt, _, _, _ =>
      absurd (Nat.lt_of_lt_of_le witRowLt witRowGe) (Nat.lt_irrefl witnessRow)
  | rowCount + 1, rowStart, witnessRow, witnessCol, best,
      witRowGe, witRowLt, witColGe, witColLt, witNonzero =>
      match Nat.le.dest witRowGe with
      | ⟨0, rowEq⟩ =>
          have witnessNonzeroAtRowStart : (matrix.entryAt rowStart witnessCol).natAbs ≠ 0 :=
            fun isZero => witNonzero
              ((congrArg (fun row => (matrix.entryAt row witnessCol).natAbs) rowEq).symm.trans
                isZero)
          match smithScanRowMinAbsBoundsWitness matrix rowStart colCount colStart witnessCol best
              witColGe witColLt witnessNonzeroAtRowStart with
          | ⟨innerRow, innerCol, innerEq, innerLe⟩ =>
              match smithScanMinorMinAbsPreservesSomeBound matrix colStart colCount rowCount
                  (rowStart + 1) innerRow innerCol with
              | ⟨foundRow, foundCol, foundEq, foundLe⟩ =>
                  ⟨foundRow, foundCol,
                    (congrArg
                        (smithScanMinorMinAbs matrix colStart colCount rowCount (rowStart + 1))
                        innerEq).trans foundEq,
                    Nat.le_trans (Nat.le_trans foundLe innerLe)
                      (Nat.le_of_eq
                        (congrArg (fun row => (matrix.entryAt row witnessCol).natAbs) rowEq))⟩
      | ⟨diff + 1, rowEq⟩ =>
          smithScanMinorMinAbsBoundsWitness matrix colStart colCount rowCount (rowStart + 1)
            witnessRow witnessCol
            (smithScanRowMinAbs matrix rowStart colCount colStart best)
            (Nat.le.intro ((Nat.succ_add rowStart diff).trans rowEq))
            (Eq.mp (congrArg (witnessRow < ·) (Nat.succ_add rowStart rowCount).symm) witRowLt)
            witColGe witColLt witNonzero

/-- **The search lower bound** — `smithFindMinAbsInMinor` returns `some` position whose magnitude is
`≤` that of any nonzero entry in the pivot minor.  The pivot-minor wrapper of the minor scan bound;
the window ranges are stated as the literal scan parameters (`pivotIndex + (dim - pivotIndex)`) so this
is a pure specialization — the r9 cascade supplies the residue as the witness and reads off
`found ≤ residue`, which the shipped `smithRotationDecreasesPivotSize` places strictly below the
pivot. -/
theorem smithFindMinAbsInMinorBoundsWitness (matrix : IntMatrix)
    (pivotIndex height width witnessRow witnessCol : Nat)
    (witRowGe : pivotIndex ≤ witnessRow)
    (witRowLt : witnessRow < pivotIndex + (height - pivotIndex))
    (witColGe : pivotIndex ≤ witnessCol)
    (witColLt : witnessCol < pivotIndex + (width - pivotIndex))
    (witNonzero : (matrix.entryAt witnessRow witnessCol).natAbs ≠ 0) :
    ∃ foundRow foundCol,
      smithFindMinAbsInMinor matrix pivotIndex height width = some (foundRow, foundCol)
      ∧ (matrix.entryAt foundRow foundCol).natAbs ≤ (matrix.entryAt witnessRow witnessCol).natAbs :=
  smithScanMinorMinAbsBoundsWitness matrix pivotIndex (width - pivotIndex)
    (height - pivotIndex) pivotIndex witnessRow witnessCol none
    witRowGe witRowLt witColGe witColLt witNonzero

/-! ## The clear-word lift (H2-SMITH r9) — the ops-list decoupling the coefficient source from the
    threaded work matrix

`smithClearRowRightSteps coeffMatrix pivotIndex stepCount startCol` bakes every coefficient off a
FIXED `coeffMatrix` (the recursion advances only the column, never the matrix), yet `applyOperations`
fires the emitted column word SEQUENTIALLY over a THREADED work matrix.  The lift below decouples the
two: reading the pivot row at any target column after the whole row-right word equals the single-op
landing value on the work matrix, with the coefficient read off `coeffMatrix`.  Its column mirror
(`smithClearColumnBelowSteps`, row ops) rides the SHIPPED row atoms.  Each is a statement about the
DEFINITE word one matrix produces — no sweep over arbitrary window-diagonal inputs — so the whole
family is immune to the r5/r6 refutation shape. -/

/-- **The column OFF-target entry formula** — the column mirror of the shipped
`addRowMultiplePreservesEntryOffTargetRow`: reading a column OTHER than the target after
`addColumnMultiple sourceIndex targetIndex coefficient` is unchanged (the op maps every row but
rewrites only the target column within each).  Cases the `addColumnMultiple` distinctness guard
(identity when `sourceIndex = targetIndex`), reads the mapped in-range row by
`listGetWithDefaultMapAllRows`, then navigates the `addScaledEntryWithinRow` source-in-range guard —
the live branch reads the off-target column via `listGetWithDefaultModifyAtNe`, the dead branch leaves
the row untouched. -/
theorem addColumnMultipleEntryOffTargetCol {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (sourceIndex targetIndex rowIndex colIndex : Nat) (coefficient : Int)
    (isOffTarget : colIndex ≠ targetIndex)
    (isRowInRange : rowIndex < height) :
    (matrix.addColumnMultiple sourceIndex targetIndex coefficient).entryAt rowIndex colIndex
      = matrix.entryAt rowIndex colIndex := by
  obtain ⟨rowCount, _⟩ := isRect
  have rowInRows : rowIndex < matrix.rows.length :=
    Eq.mp (congrArg (rowIndex < ·) rowCount.symm) isRowInRange
  unfold IntMatrix.addColumnMultiple
  split
  · rfl
  · show listGetWithDefault 0
        (listGetWithDefault []
          (mapAllRows (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
            matrix.rows) rowIndex) colIndex = _
    rw [listGetWithDefaultMapAllRows _ matrix.rows rowIndex rowInRows]
    unfold IntMatrix.addScaledEntryWithinRow
    split
    · exact listGetWithDefaultModifyAtNe 0 _ (listGetWithDefault [] matrix.rows rowIndex)
        targetIndex colIndex isOffTarget
    · rfl

/-- **Row-right word preserves a left column** — every op in `smithClearRowRightSteps coeffMatrix
pivotIndex stepCount startCol` targets a column in `[startCol, startCol + stepCount)`, so reading any
column `readCol < startCol` after the whole mapped word is unchanged.  Structural on `stepCount`,
threading `addColumnMultipleEntryOffTargetCol` (the head op's target `startCol` is `> readCol`) through
`applyOperations`; `applyOperationPreservesRectangular` carries the shape to the recursion. -/
theorem smithClearRowRightStepsPreservesColumn (coeffMatrix : IntMatrix)
    (pivotIndex height width readRow readCol : Nat)
    (isReadRowInRange : readRow < height) :
    ∀ (stepCount startCol : Nat) (workMatrix : IntMatrix),
      workMatrix.IsRectangular height width →
      readCol < startCol →
      (workMatrix.applyOperations
          ((smithClearRowRightSteps coeffMatrix pivotIndex stepCount startCol).map
            ElementaryOperation.columnOperation)).entryAt readRow readCol
        = workMatrix.entryAt readRow readCol
  | 0, _, _, _, _ => rfl
  | stepCount + 1, startCol, workMatrix, isRect, readColLtStart =>
      have headOffTarget :
          (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol)))).entryAt readRow readCol
            = workMatrix.entryAt readRow readCol :=
        addColumnMultipleEntryOffTargetCol workMatrix isRect pivotIndex startCol readRow readCol
          (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
              (coeffMatrix.entryAt pivotIndex startCol)))
          (Nat.ne_of_lt readColLtStart) isReadRowInRange
      have nextRect :
          (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol)))).IsRectangular height width :=
        applyOperationPreservesRectangular
          (ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol))))) workMatrix isRect
      (smithClearRowRightStepsPreservesColumn coeffMatrix pivotIndex height width readRow readCol
        isReadRowInRange stepCount (startCol + 1)
        (workMatrix.addColumnMultiple pivotIndex startCol
          (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
              (coeffMatrix.entryAt pivotIndex startCol))))
        nextRect (Nat.lt_trans readColLtStart (Nat.lt_succ_self startCol))).trans headOffTarget

/-- **The row-right clear-word lift** — reading the pivot row at any target column `targetCol` in the
cleared window after the whole `smithClearRowRightSteps coeffMatrix pivotIndex stepCount startCol` word
lands `old + (coeff) * pivot`, with `old`/`pivot` read off the THREADED `workMatrix` and the
`coeff = -(intPivotQuotient …)` read off the FIXED `coeffMatrix`.  This is the decoupling the cascade
recursion needs: the coefficient source and the transformed matrix are independent arguments.
Induction on `stepCount`; the head op targets `startCol`, split on `targetCol = startCol` (on-target
landing frozen through the rest by `smithClearRowRightStepsPreservesColumn`) versus `startCol <
targetCol` (head leaves both `(pivotIndex, targetCol)` and the source `(pivotIndex, pivotIndex)` fixed —
`addColumnMultipleEntryOffTargetCol` twice — then recurse; `coeffMatrix` reads are identical literals
across the recursion). -/
theorem smithClearRowRightStepsLandsAt (coeffMatrix : IntMatrix) (pivotIndex height width : Nat) :
    ∀ (stepCount startCol targetCol : Nat) (workMatrix : IntMatrix),
      workMatrix.IsRectangular height width →
      pivotIndex < startCol →
      startCol ≤ targetCol → targetCol < startCol + stepCount →
      pivotIndex < height → startCol + stepCount ≤ width →
      (workMatrix.applyOperations
          ((smithClearRowRightSteps coeffMatrix pivotIndex stepCount startCol).map
            ElementaryOperation.columnOperation)).entryAt pivotIndex targetCol
        = workMatrix.entryAt pivotIndex targetCol
            + (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex targetCol)))
                * workMatrix.entryAt pivotIndex pivotIndex := by
  intro stepCount
  induction stepCount with
  | zero =>
      intro startCol targetCol _ _ _ targetGe targetLt _ _
      exact absurd (Nat.lt_of_le_of_lt targetGe targetLt) (Nat.lt_irrefl startCol)
  | succ m ih =>
      intro startCol targetCol workMatrix isRect pivotBelowStart targetGe targetLt
        pivotRowInRange allColsInRange
      have pivotNeStart : pivotIndex ≠ startCol := Nat.ne_of_lt pivotBelowStart
      have nextRect :
          (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol)))).IsRectangular height width :=
        applyOperationPreservesRectangular
          (ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol))))) workMatrix isRect
      show ((workMatrix.addColumnMultiple pivotIndex startCol
                (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                    (coeffMatrix.entryAt pivotIndex startCol)))).applyOperations
              ((smithClearRowRightSteps coeffMatrix pivotIndex m (startCol + 1)).map
                ElementaryOperation.columnOperation)).entryAt pivotIndex targetCol
            = workMatrix.entryAt pivotIndex targetCol
                + (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt pivotIndex targetCol)))
                    * workMatrix.entryAt pivotIndex pivotIndex
      cases Nat.eq_or_lt_of_le targetGe with
      | inl startEqTarget =>
          have startColLtWidth : startCol < width :=
            Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt (Nat.le_add_right startCol m) (Nat.lt_succ_self (startCol + m)))
              allColsInRange
          have pivotColLtWidth : pivotIndex < width := Nat.lt_trans pivotBelowStart startColLtWidth
          rw [← startEqTarget]
          rw [smithClearRowRightStepsPreservesColumn coeffMatrix pivotIndex height width pivotIndex
                startCol pivotRowInRange m (startCol + 1)
                (workMatrix.addColumnMultiple pivotIndex startCol
                  (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt pivotIndex startCol))))
                nextRect (Nat.lt_succ_self startCol)]
          exact addColumnMultipleEntryOnTargetCol workMatrix isRect pivotIndex startCol pivotIndex
            (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                (coeffMatrix.entryAt pivotIndex startCol)))
            pivotNeStart pivotRowInRange pivotColLtWidth startColLtWidth
      | inr startLtTarget =>
          have addSwap : startCol + (m + 1) = startCol + 1 + m :=
            (Nat.add_succ startCol m).trans (Nat.succ_add startCol m).symm
          have targetLt' : targetCol < startCol + 1 + m :=
            Eq.mp (congrArg (targetCol < ·) addSwap) targetLt
          have allColsInRange' : startCol + 1 + m ≤ width :=
            Eq.mp (congrArg (· ≤ width) addSwap) allColsInRange
          have ihResult := ih (startCol + 1) targetCol
            (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol))))
            nextRect (Nat.lt_succ_of_lt pivotBelowStart) startLtTarget targetLt'
            pivotRowInRange allColsInRange'
          have entryTargetEq :
              (workMatrix.addColumnMultiple pivotIndex startCol
                  (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt pivotIndex startCol)))).entryAt pivotIndex targetCol
                = workMatrix.entryAt pivotIndex targetCol :=
            addColumnMultipleEntryOffTargetCol workMatrix isRect pivotIndex startCol pivotIndex
              targetCol _ (Nat.ne_of_lt startLtTarget).symm pivotRowInRange
          have entryPivotEq :
              (workMatrix.addColumnMultiple pivotIndex startCol
                  (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt pivotIndex startCol)))).entryAt pivotIndex pivotIndex
                = workMatrix.entryAt pivotIndex pivotIndex :=
            addColumnMultipleEntryOffTargetCol workMatrix isRect pivotIndex startCol pivotIndex
              pivotIndex _ pivotNeStart pivotRowInRange
          rw [ihResult, entryTargetEq, entryPivotEq]

/-- **Column-below word preserves a top row** — the row mirror of `smithClearRowRightStepsPreservesColumn`:
every op in `smithClearColumnBelowSteps coeffMatrix pivotIndex stepCount startRow` targets a row in
`[startRow, startRow + stepCount)`, so reading any row `readRow < startRow` after the whole mapped word
is unchanged.  Structural on `stepCount`, threading the SHIPPED off-target-row atom
`addRowMultiplePreservesEntryOffTargetRow` (which needs no rectangularity) through `applyOperations`. -/
theorem smithClearColumnBelowStepsPreservesRow (coeffMatrix : IntMatrix)
    (pivotIndex readRow readCol : Nat) :
    ∀ (stepCount startRow : Nat) (workMatrix : IntMatrix),
      readRow < startRow →
      (workMatrix.applyOperations
          ((smithClearColumnBelowSteps coeffMatrix pivotIndex stepCount startRow).map
            ElementaryOperation.rowOperation)).entryAt readRow readCol
        = workMatrix.entryAt readRow readCol
  | 0, _, _, _ => rfl
  | stepCount + 1, startRow, workMatrix, readRowLtStart =>
      have headOffTarget :
          (workMatrix.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))).entryAt readRow readCol
            = workMatrix.entryAt readRow readCol :=
        addRowMultiplePreservesEntryOffTargetRow workMatrix pivotIndex startRow
          (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
              (coeffMatrix.entryAt startRow pivotIndex)))
          readRow readCol (Nat.ne_of_lt readRowLtStart)
      (smithClearColumnBelowStepsPreservesRow coeffMatrix pivotIndex readRow readCol
        stepCount (startRow + 1)
        (workMatrix.addRowMultiple pivotIndex startRow
          (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
              (coeffMatrix.entryAt startRow pivotIndex))))
        (Nat.lt_trans readRowLtStart (Nat.lt_succ_self startRow))).trans headOffTarget

/-- **The column-below clear-word lift** — the row mirror of `smithClearRowRightStepsLandsAt`: reading
the pivot column at any target row `targetRow` in the cleared window after the whole
`smithClearColumnBelowSteps coeffMatrix pivotIndex stepCount startRow` word lands `old + (coeff) *
pivot`, with `old`/`pivot` read off the THREADED `workMatrix` and `coeff = -(intPivotQuotient …)` read
off the FIXED `coeffMatrix`.  Induction on `stepCount`; the on-target landing rides the shipped
`addRowMultipleEntryOnTargetRow`, the frozen-through-rest and source-preservation ride the shipped
`addRowMultiplePreservesEntryOffTargetRow` and `smithClearColumnBelowStepsPreservesRow` — no new atom. -/
theorem smithClearColumnBelowStepsLandsAt (coeffMatrix : IntMatrix) (pivotIndex height width : Nat) :
    ∀ (stepCount startRow targetRow : Nat) (workMatrix : IntMatrix),
      workMatrix.IsRectangular height width →
      pivotIndex < startRow →
      startRow ≤ targetRow → targetRow < startRow + stepCount →
      pivotIndex < width → startRow + stepCount ≤ height →
      (workMatrix.applyOperations
          ((smithClearColumnBelowSteps coeffMatrix pivotIndex stepCount startRow).map
            ElementaryOperation.rowOperation)).entryAt targetRow pivotIndex
        = workMatrix.entryAt targetRow pivotIndex
            + (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt targetRow pivotIndex)))
                * workMatrix.entryAt pivotIndex pivotIndex := by
  intro stepCount
  induction stepCount with
  | zero =>
      intro startRow targetRow _ _ _ targetGe targetLt _ _
      exact absurd (Nat.lt_of_le_of_lt targetGe targetLt) (Nat.lt_irrefl startRow)
  | succ m ih =>
      intro startRow targetRow workMatrix isRect pivotBelowStart targetGe targetLt
        pivotColInRange allRowsInRange
      have pivotNeStart : pivotIndex ≠ startRow := Nat.ne_of_lt pivotBelowStart
      have nextRect :
          (workMatrix.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))).IsRectangular height width :=
        applyOperationPreservesRectangular
          (ElementaryOperation.rowOperation
            (ElementaryRowOperation.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex))))) workMatrix isRect
      show ((workMatrix.addRowMultiple pivotIndex startRow
                (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                    (coeffMatrix.entryAt startRow pivotIndex)))).applyOperations
              ((smithClearColumnBelowSteps coeffMatrix pivotIndex m (startRow + 1)).map
                ElementaryOperation.rowOperation)).entryAt targetRow pivotIndex
            = workMatrix.entryAt targetRow pivotIndex
                + (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt targetRow pivotIndex)))
                    * workMatrix.entryAt pivotIndex pivotIndex
      cases Nat.eq_or_lt_of_le targetGe with
      | inl startEqTarget =>
          have startRowLtHeight : startRow < height :=
            Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt (Nat.le_add_right startRow m) (Nat.lt_succ_self (startRow + m)))
              allRowsInRange
          have pivotRowLtHeight : pivotIndex < height := Nat.lt_trans pivotBelowStart startRowLtHeight
          rw [← startEqTarget]
          rw [smithClearColumnBelowStepsPreservesRow coeffMatrix pivotIndex startRow pivotIndex m
                (startRow + 1)
                (workMatrix.addRowMultiple pivotIndex startRow
                  (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt startRow pivotIndex))))
                (Nat.lt_succ_self startRow)]
          exact addRowMultipleEntryOnTargetRow workMatrix isRect pivotIndex startRow pivotIndex
            (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                (coeffMatrix.entryAt startRow pivotIndex)))
            pivotNeStart pivotRowLtHeight startRowLtHeight pivotColInRange
      | inr startLtTarget =>
          have addSwap : startRow + (m + 1) = startRow + 1 + m :=
            (Nat.add_succ startRow m).trans (Nat.succ_add startRow m).symm
          have targetLt' : targetRow < startRow + 1 + m :=
            Eq.mp (congrArg (targetRow < ·) addSwap) targetLt
          have allRowsInRange' : startRow + 1 + m ≤ height :=
            Eq.mp (congrArg (· ≤ height) addSwap) allRowsInRange
          have ihResult := ih (startRow + 1) targetRow
            (workMatrix.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex))))
            nextRect (Nat.lt_succ_of_lt pivotBelowStart) startLtTarget targetLt'
            pivotColInRange allRowsInRange'
          have entryTargetEq :
              (workMatrix.addRowMultiple pivotIndex startRow
                  (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt startRow pivotIndex)))).entryAt targetRow pivotIndex
                = workMatrix.entryAt targetRow pivotIndex :=
            addRowMultiplePreservesEntryOffTargetRow workMatrix pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))
              targetRow pivotIndex (Nat.ne_of_lt startLtTarget).symm
          have entryPivotEq :
              (workMatrix.addRowMultiple pivotIndex startRow
                  (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                      (coeffMatrix.entryAt startRow pivotIndex)))).entryAt pivotIndex pivotIndex
                = workMatrix.entryAt pivotIndex pivotIndex :=
            addRowMultiplePreservesEntryOffTargetRow workMatrix pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))
              pivotIndex pivotIndex pivotNeStart
          rw [ihResult, entryTargetEq, entryPivotEq]

/-! ## Concrete truth probes for the clear-word lift

Machine-checked on literal matrices (`decide` clean — no `Nat.min`/`Nat.sub` in the applied
expressions), confirming the LIFT lemmas describe the ACTUAL threaded computation, including a case
with TRANSIENT GROWTH in a non-pivot row (r8's shape).  Anonymous, so they carry no axiom footprint of
their own. -/

/-- Row-right clear of pivot row `0` (pivot `3`), columns `1..2`, over `[[3, 7, 5], [6, 2, 9]]`.  Row
`1` column `1` grows `2 -> -10` MID-WORD, yet the pivot-row landings `(0, 1) = 1`, `(0, 2) = 2` match
the per-column single-op residues — `smithClearRowRightStepsLandsAt`'s prediction on the real word. -/
example :
    (({ rows := [[3, 7, 5], [6, 2, 9]] } : IntMatrix).applyOperations
        ((smithClearRowRightSteps { rows := [[3, 7, 5], [6, 2, 9]] } 0 2 1).map
          ElementaryOperation.columnOperation)).rows
      = [[3, 1, 2], [6, -10, 3]] := by decide

/-- Column-below clear of pivot column `0` (pivot `3`), rows `1..2`, over
`[[3, 0, 0], [7, 5, 0], [5, 0, 9]]`.  The pivot-column landings `(1, 0) = 1`, `(2, 0) = 2` match the
per-row single-op residues — `smithClearColumnBelowStepsLandsAt`'s prediction on the real word. -/
example :
    (({ rows := [[3, 0, 0], [7, 5, 0], [5, 0, 9]] } : IntMatrix).applyOperations
        ((smithClearColumnBelowSteps { rows := [[3, 0, 0], [7, 5, 0], [5, 0, 9]] } 0 2 1).map
          ElementaryOperation.rowOperation)).rows
      = [[3, 0, 0], [1, 5, 0], [2, 0, 9]] := by decide

/-! ## The whole-word-equals-single-op bridge (the strict descent for the whole cross clear)

Instantiating the lift with `coeffMatrix := workMatrix := matrix` collapses the whole clear word's
landed cross entry onto the SINGLE-op landed value at the same position (both are `old + coeff *
pivot` with the coefficient read off `matrix` itself).  That reuses the shipped single-op residue and
strict-descent theorems VERBATIM — no re-derivation of the `intMagnitudeReconstructs` arithmetic — to
place the whole-word cross residue strictly below a positive pivot's magnitude.  This is the per-clear
strict descent the fuel-adequacy recursion rides. -/

/-- **Row-right whole word = single op, at a cross column** — with the coefficient source and work
matrix both `matrix`, the whole `smithClearRowRightSteps` word lands the pivot-row cross entry exactly
where the ONE `addColumnMultiple` at that column lands it.  `smithClearRowRightStepsLandsAt` (self
coefficients) trans the shipped `addColumnMultipleEntryOnTargetCol`. -/
theorem smithClearRowRightStepsCrossEntryEqSingle {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex stepCount startCol targetCol : Nat)
    (pivotBelowStart : pivotIndex < startCol)
    (targetGe : startCol ≤ targetCol) (targetLt : targetCol < startCol + stepCount)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (allColsInRange : startCol + stepCount ≤ width) :
    (matrix.applyOperations
        ((smithClearRowRightSteps matrix pivotIndex stepCount startCol).map
          ElementaryOperation.columnOperation)).entryAt pivotIndex targetCol
      = (matrix.addColumnMultiple pivotIndex targetCol
          (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
              (matrix.entryAt pivotIndex targetCol)))).entryAt pivotIndex targetCol :=
  (smithClearRowRightStepsLandsAt matrix pivotIndex height width stepCount startCol targetCol matrix
      isRect pivotBelowStart targetGe targetLt pivotRowInRange allColsInRange).trans
    (addColumnMultipleEntryOnTargetCol matrix isRect pivotIndex targetCol pivotIndex
      (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
          (matrix.entryAt pivotIndex targetCol)))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le pivotBelowStart targetGe)) pivotRowInRange pivotColInRange
      (Nat.lt_of_lt_of_le targetLt allColsInRange)).symm

/-- **Column-below whole word = single op, at a cross row** — the row mirror of the above, over the
shipped `addRowMultipleEntryOnTargetRow`. -/
theorem smithClearColumnBelowStepsCrossEntryEqSingle {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex stepCount startRow targetRow : Nat)
    (pivotBelowStart : pivotIndex < startRow)
    (targetGe : startRow ≤ targetRow) (targetLt : targetRow < startRow + stepCount)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (allRowsInRange : startRow + stepCount ≤ height) :
    (matrix.applyOperations
        ((smithClearColumnBelowSteps matrix pivotIndex stepCount startRow).map
          ElementaryOperation.rowOperation)).entryAt targetRow pivotIndex
      = (matrix.addRowMultiple pivotIndex targetRow
          (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
              (matrix.entryAt targetRow pivotIndex)))).entryAt targetRow pivotIndex :=
  (smithClearColumnBelowStepsLandsAt matrix pivotIndex height width stepCount startRow targetRow
      matrix isRect pivotBelowStart targetGe targetLt pivotColInRange allRowsInRange).trans
    (addRowMultipleEntryOnTargetRow matrix isRect pivotIndex targetRow pivotIndex
      (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
          (matrix.entryAt targetRow pivotIndex)))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le pivotBelowStart targetGe)) pivotRowInRange
      (Nat.lt_of_lt_of_le targetLt allRowsInRange) pivotColInRange).symm

/-- **The single COLUMN-BELOW clear residue landing** — the ROW-op mirror of the shipped
`smithSingleClearResidueLands`: firing `addRowMultiple pivotIndex rowIndex (-(intPivotQuotient pivot
old))` at a nonnegative pivot lands the pivot-column cross entry `(rowIndex, pivotIndex)` with magnitude
exactly `intMagnitudeRemainder pivot.natAbs old`.  The entry formula is the shipped
`addRowMultipleEntryOnTargetRow` (giving `old + coeff * pivot`); the signed-residue arithmetic
(`intNegMul`, the nonnegative-pivot bridge, `intMagnitudeReconstructs`, `intMagnitudeSignedRemainderNatAbs`)
is byte-identical to the shipped column-op residue landing (it operates on `old`/`pivot` abstractly). -/
theorem smithSingleColumnBelowClearResidueLands {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex rowIndex : Nat)
    (isDistinct : pivotIndex ≠ rowIndex)
    (isPivotRowInRange : pivotIndex < height)
    (isTargetRowInRange : rowIndex < height)
    (isPivotColInRange : pivotIndex < width)
    (isPivotNonneg : (0 : Int) ≤ matrix.entryAt pivotIndex pivotIndex) :
    ((matrix.addRowMultiple pivotIndex rowIndex
        (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
            (matrix.entryAt rowIndex pivotIndex)))).entryAt rowIndex pivotIndex).natAbs
      = intMagnitudeRemainder (matrix.entryAt pivotIndex pivotIndex).natAbs
          (matrix.entryAt rowIndex pivotIndex) :=
  let pivot := matrix.entryAt pivotIndex pivotIndex
  let old := matrix.entryAt rowIndex pivotIndex
  let productTerm := intMagnitudeQuotient pivot.natAbs old * Int.ofNat pivot.natAbs
  let signedResidue := intMagnitudeSignedRemainder pivot.natAbs old
  have entryFormula :
      (matrix.addRowMultiple pivotIndex rowIndex (-(intPivotQuotient pivot old))).entryAt
          rowIndex pivotIndex
        = old + (-(intPivotQuotient pivot old)) * pivot :=
    addRowMultipleEntryOnTargetRow matrix isRect pivotIndex rowIndex pivotIndex
      (-(intPivotQuotient pivot old)) isDistinct isPivotRowInRange isTargetRowInRange isPivotColInRange
  have pivotIsOfNat : pivot = Int.ofNat pivot.natAbs :=
    (intOfNatNatAbsOfNonNeg isPivotNonneg).symm
  have reconstruction : old = productTerm + signedResidue :=
    intMagnitudeReconstructs pivot.natAbs old
  have landsOnResidue : old + (-(intPivotQuotient pivot old)) * pivot = signedResidue :=
    (congrArg (old + ·) (intNegMul (intPivotQuotient pivot old) pivot)).trans
      ((congrArg (fun scale => old + -(intMagnitudeQuotient pivot.natAbs old * scale))
            pivotIsOfNat).trans
        ((congrArg (· + -productTerm) reconstruction).trans
          ((intAddAssoc productTerm signedResidue (-productTerm)).trans
            ((congrArg (productTerm + ·) (intAddComm signedResidue (-productTerm))).trans
              ((intAddAssoc productTerm (-productTerm) signedResidue).symm.trans
                ((congrArg (· + signedResidue) (intAddRightNeg productTerm)).trans
                  (intZeroAdd signedResidue)))))))
  (congrArg Int.natAbs (entryFormula.trans landsOnResidue)).trans
    (intMagnitudeSignedRemainderNatAbs pivot.natAbs old)

/-- **The single COLUMN-BELOW rotation strict descent** — the ROW-op mirror of the shipped
`smithSingleClearStrictlyDecreasesPivot`: for a positive nonnegative pivot, one column-below clear row
op lands the pivot-column cross entry with magnitude STRICTLY below the pivot's.  The residue landing
rewritten into the shipped remainder bound `smithRotationDecreasesPivotSize`. -/
theorem smithSingleColumnBelowClearStrictlyDecreasesPivot {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex rowIndex : Nat)
    (isDistinct : pivotIndex ≠ rowIndex)
    (isPivotRowInRange : pivotIndex < height)
    (isTargetRowInRange : rowIndex < height)
    (isPivotColInRange : pivotIndex < width)
    (isPivotNonneg : (0 : Int) ≤ matrix.entryAt pivotIndex pivotIndex)
    (isPivotPositive : 0 < (matrix.entryAt pivotIndex pivotIndex).natAbs) :
    ((matrix.addRowMultiple pivotIndex rowIndex
        (-(intPivotQuotient (matrix.entryAt pivotIndex pivotIndex)
            (matrix.entryAt rowIndex pivotIndex)))).entryAt rowIndex pivotIndex).natAbs
      < (matrix.entryAt pivotIndex pivotIndex).natAbs :=
  Eq.mpr
    (congrArg (· < (matrix.entryAt pivotIndex pivotIndex).natAbs)
      (smithSingleColumnBelowClearResidueLands matrix isRect pivotIndex rowIndex isDistinct
        isPivotRowInRange isTargetRowInRange isPivotColInRange isPivotNonneg))
    (smithRotationDecreasesPivotSize (matrix.entryAt pivotIndex pivotIndex)
      (matrix.entryAt rowIndex pivotIndex) isPivotPositive)

/-- **Row-right cross residue strictly below a positive pivot** — reading any cleared pivot-row cross
column after the whole word lands a magnitude STRICTLY below the (nonnegative, positive) pivot's.  The
whole-word=single-op bridge rewritten into the shipped single-op strict descent
`smithSingleClearStrictlyDecreasesPivot`.  The per-clear strict descent the cascade fuel adequacy
rides. -/
theorem smithClearRowRightStepsCrossEntryStrictlyDecreases {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex stepCount startCol targetCol : Nat)
    (pivotBelowStart : pivotIndex < startCol)
    (targetGe : startCol ≤ targetCol) (targetLt : targetCol < startCol + stepCount)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (allColsInRange : startCol + stepCount ≤ width)
    (isPivotNonneg : (0 : Int) ≤ matrix.entryAt pivotIndex pivotIndex)
    (isPivotPositive : 0 < (matrix.entryAt pivotIndex pivotIndex).natAbs) :
    ((matrix.applyOperations
        ((smithClearRowRightSteps matrix pivotIndex stepCount startCol).map
          ElementaryOperation.columnOperation)).entryAt pivotIndex targetCol).natAbs
      < (matrix.entryAt pivotIndex pivotIndex).natAbs :=
  Eq.mpr
    (congrArg (fun value => value.natAbs < (matrix.entryAt pivotIndex pivotIndex).natAbs)
      (smithClearRowRightStepsCrossEntryEqSingle matrix isRect pivotIndex stepCount startCol targetCol
        pivotBelowStart targetGe targetLt pivotRowInRange pivotColInRange allColsInRange))
    (smithSingleClearStrictlyDecreasesPivot matrix isRect pivotIndex targetCol
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le pivotBelowStart targetGe)) pivotRowInRange pivotColInRange
      (Nat.lt_of_lt_of_le targetLt allColsInRange) isPivotNonneg isPivotPositive)

/-- **Column-below cross residue strictly below a positive pivot** — the row mirror. -/
theorem smithClearColumnBelowStepsCrossEntryStrictlyDecreases {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex stepCount startRow targetRow : Nat)
    (pivotBelowStart : pivotIndex < startRow)
    (targetGe : startRow ≤ targetRow) (targetLt : targetRow < startRow + stepCount)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (allRowsInRange : startRow + stepCount ≤ height)
    (isPivotNonneg : (0 : Int) ≤ matrix.entryAt pivotIndex pivotIndex)
    (isPivotPositive : 0 < (matrix.entryAt pivotIndex pivotIndex).natAbs) :
    ((matrix.applyOperations
        ((smithClearColumnBelowSteps matrix pivotIndex stepCount startRow).map
          ElementaryOperation.rowOperation)).entryAt targetRow pivotIndex).natAbs
      < (matrix.entryAt pivotIndex pivotIndex).natAbs :=
  Eq.mpr
    (congrArg (fun value => value.natAbs < (matrix.entryAt pivotIndex pivotIndex).natAbs)
      (smithClearColumnBelowStepsCrossEntryEqSingle matrix isRect pivotIndex stepCount startRow
        targetRow pivotBelowStart targetGe targetLt pivotRowInRange pivotColInRange allRowsInRange))
    (smithSingleColumnBelowClearStrictlyDecreasesPivot matrix isRect pivotIndex targetRow
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le pivotBelowStart targetGe)) pivotRowInRange
      (Nat.lt_of_lt_of_le targetLt allRowsInRange) pivotColInRange isPivotNonneg isPivotPositive)

end FX1Poly.ComputerAlgebra
