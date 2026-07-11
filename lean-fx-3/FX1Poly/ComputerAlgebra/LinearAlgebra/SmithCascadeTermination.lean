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

**H2-SMITH r9 ships the clear-word LIFT + the search COMPANIONS** — the infrastructure the
fuel-adequacy induction threads, every one a FUNCTION-CORRECTNESS fact about a definite word on ONE
matrix (never a sweep over arbitrary window-diagonal inputs, so immune to the r5/r6 refutation shape):

  * **The ops-list lift** (`smithClearRowRightStepsLandsAt` / `smithClearColumnBelowStepsLandsAt`, over
    the `PreservesColumn`/`PreservesRow` word locality and the new `addColumnMultipleEntryOffTargetCol`
    atom): reading a cross entry after the WHOLE clear word equals the SINGLE-op landing, DECOUPLING the
    FIXED coefficient source from the THREADED work matrix (the r8 counterexample's transient growth
    elsewhere leaves the pivot-row/column landings intact — machine-checked in the truth probes).
  * **The whole-word strict descent**
    (`smithClear{RowRight,ColumnBelow}StepsCrossEntryStrictlyDecreases`, over the ROW-op single-clear
    mirror `smithSingleColumnBelowClearResidueLands`): each cross residue lands STRICTLY below a
    positive nonnegative pivot's magnitude — the per-clear descent the fuel recursion rides.
  * **The search companions** — `smithMinorEntryLeAbsSum` (the fixed fuel seed `measure ≤ smithMinorAbsSum`),
    `smithFindMinAbsInMinorFoundNonzero` (the moved pivot is positive), `smithFindMinAbsInMinorNoneAllZero`
    (a `none` search means the minor is all zero — the cross-clear base case).
  * **The cross-clear segment characterization** (`smithCrossIsClearOfFindNone` +
    `smithCrossNotClearWitness`, over the segment pointwise/`false`-witness Bool-fold lemmas and the
    propext-clean window bridge `smithNatAddSubOfLe` / `natLtAddSubOfLt`): a `none` search means the cross is
    ALREADY clear (the fuel-adequacy base case), and a `false` cross exhibits a nonzero cross residue in
    one of the two segments (the loop step's next-pivot witness).  This is r9's discharge of joint (b).
  * **The move swap-entry bridge** (`smithMoveToPivotEntryOnPivot`, over the new `listReplaceAt` read
    atoms `listGetWithDefaultReplaceAt{Eq,Ne}` and the swap-entry formulas `swap{Rows,Columns}EntryAtFirst`
    / `swapEntriesWithinRowAtFirst`): after `smithMoveToPivotOps` the pivot slot `(pivotIndex, pivotIndex)`
    holds exactly `matrix.entryAt foundRow foundCol` — the swap-entry formula that was joint (a)'s backbone
    (needs the found position in range, supplied by the caller).

**H2-SMITH r10 SHIPS the fuel-adequacy induction `smithCascadeReachesCrossClear`** — a strong
induction on `smithCascadeSweep`'s inner fuel threading the PIVOT MAGNITUDE (measure = the found
min-abs pivot's `natAbs`; NEVER the abs-sum — the fuel is the STATIC budget `smithMinorAbsSum`, read
ONCE at cascade entry, so the r8 transient abs-sum growth is IRRELEVANT).  Its three glue joints,
all now shipped: (i) `smithFindMinAbsInMinorFoundInRange` (the found position sits in
`[pivotIndex, height) × [pivotIndex, width)`, feeding `smithMoveToPivotEntryOnPivot`'s in-range
hypotheses — the generic-predicate scan companion `smithScan{Row,Minor}MinAbsResultInRange`); (ii) the
sign-phase magnitude bridge `smithSignNormalizeOpsPreservesPivotMagnitude`
(`|afterSign pivot| = |afterMove pivot|` from `signNormalizeOpsEntryOnPivotIsSignedInput` +
`intNegNatAbs`, carried through the column clear by `smithClearColumnBelowStepsPreservesRow`, nonneg by
`signNormalizeOpsEntryOnPivotNonneg`) so that `pivotMag = (matrix.entryAt foundRow foundCol).natAbs`
`≤ f + 1` and is positive; and (iii) the induction body — the `false`-branch bound via
`smithCrossNotClearWitness` → `smithClear{RowRight,ColumnBelow}StepsCrossEntryStrictlyDecreases`
(+ `smithClearRowRightStepsPreservesColumn` for the column segment) →
`smithFindMinAbsInMinorBoundsWitness`, placing the residue witness strictly below `pivotMag ≤ f + 1`,
hence `≤ f`, feeding the IH via the `smithCascadeSweepSucc` succ-unfolding.  The driver-path corollary
`smithCascadeSweepSeedReachesCrossClear` discharges it at the ACTUAL seed fuel `smithMinorAbsSum` (via
`smithMinorEntryLeAbsSum`).  **Honest scope caveat (DESIGN-LOCKED):** `smithCascadeReachesCrossClear`
delivers ONLY the cross-clear conjunct of obligation (a); the sub-block-stays-diagonal +
gcd-divides-folded-operands + chain conjuncts feeding `SmithNormalForm`'s `repairWindowDiagHolds` /
`repairChainHolds` remain the r11+ wall — so those two surviving repair hypotheses stay UNCLOSED (no
flip; `SmithReduceFullDriverStatement` uninhabited).

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

/-! ## The search companions (H2-SMITH r9) — the fuel seeding and the measure/`none` bridges

Three refutation-immune scan-correctness facts the fuel-adequacy recursion consumes: a minor entry's
magnitude is `≤` the whole-minor abs-sum (the fixed seed `measure ≤ smithMinorAbsSum`), the search
returns a NONZERO position (the measure is `0 ⟺ none`, and the moved pivot is positive), and a `none`
search means every minor entry is zero (the cross-clear base case).  Each is structural over the same
scan/sum definitions the shipped `BoundsWitness` family rides, with the update guards navigated
propext-cleanly. -/

/-- **Row entry `≤` row abs-sum** — a witness column's magnitude in the scanned row window is `≤` the
row's magnitude sum.  Structural on the column count; the sum mirror of `smithScanRowMinAbsBoundsWitness`
(`Nat.le_add_right`/`Nat.le_add_left` in place of the min-selection bound). -/
theorem smithRowEntryLeAbsSum (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart witnessCol : Nat),
      colStart ≤ witnessCol → witnessCol < colStart + colCount →
      (matrix.entryAt rowIndex witnessCol).natAbs ≤ smithRowAbsSum matrix rowIndex colCount colStart
  | 0, _, witnessCol, witColGe, witColLt =>
      absurd (Nat.lt_of_lt_of_le witColLt witColGe) (Nat.lt_irrefl witnessCol)
  | colCount + 1, colStart, witnessCol, witColGe, witColLt =>
      match Nat.le.dest witColGe with
      | ⟨0, colEq⟩ =>
          Nat.le_trans
            (Nat.le_of_eq (congrArg (fun col => (matrix.entryAt rowIndex col).natAbs) colEq.symm))
            (Nat.le_add_right (matrix.entryAt rowIndex colStart).natAbs
              (smithRowAbsSum matrix rowIndex colCount (colStart + 1)))
      | ⟨diff + 1, colEq⟩ =>
          Nat.le_trans
            (smithRowEntryLeAbsSum matrix rowIndex colCount (colStart + 1) witnessCol
              (Nat.le.intro ((Nat.succ_add colStart diff).trans colEq))
              (Eq.mp (congrArg (witnessCol < ·) (Nat.succ_add colStart colCount).symm) witColLt))
            (Nat.le_add_left (smithRowAbsSum matrix rowIndex colCount (colStart + 1))
              (matrix.entryAt rowIndex colStart).natAbs)

/-- **Minor entry `≤` minor abs-sum (row-folded form)** — a witness position's magnitude in the scanned
rectangle is `≤` the folded magnitude sum.  Structural on the row count; the witness row bounds by its
row sum (`smithRowEntryLeAbsSum`), the rest folds through `Nat.le_add_right`/`Nat.le_add_left`. -/
theorem smithMinorEntryLeAbsSumRows (matrix : IntMatrix) (colStart colCount : Nat) :
    ∀ (rowCount rowStart witnessRow witnessCol : Nat),
      rowStart ≤ witnessRow → witnessRow < rowStart + rowCount →
      colStart ≤ witnessCol → witnessCol < colStart + colCount →
      (matrix.entryAt witnessRow witnessCol).natAbs
        ≤ smithMinorAbsSumRows matrix colStart colCount rowCount rowStart
  | 0, _, witnessRow, _, witRowGe, witRowLt, _, _ =>
      absurd (Nat.lt_of_lt_of_le witRowLt witRowGe) (Nat.lt_irrefl witnessRow)
  | rowCount + 1, rowStart, witnessRow, witnessCol, witRowGe, witRowLt, witColGe, witColLt =>
      match Nat.le.dest witRowGe with
      | ⟨0, rowEq⟩ =>
          Nat.le_trans
            (Nat.le_trans
              (Nat.le_of_eq
                (congrArg (fun row => (matrix.entryAt row witnessCol).natAbs) rowEq.symm))
              (smithRowEntryLeAbsSum matrix rowStart colCount colStart witnessCol witColGe witColLt))
            (Nat.le_add_right (smithRowAbsSum matrix rowStart colCount colStart)
              (smithMinorAbsSumRows matrix colStart colCount rowCount (rowStart + 1)))
      | ⟨diff + 1, rowEq⟩ =>
          Nat.le_trans
            (smithMinorEntryLeAbsSumRows matrix colStart colCount rowCount (rowStart + 1)
              witnessRow witnessCol
              (Nat.le.intro ((Nat.succ_add rowStart diff).trans rowEq))
              (Eq.mp (congrArg (witnessRow < ·) (Nat.succ_add rowStart rowCount).symm) witRowLt)
              witColGe witColLt)
            (Nat.le_add_left (smithMinorAbsSumRows matrix colStart colCount rowCount (rowStart + 1))
              (smithRowAbsSum matrix rowStart colCount colStart))

/-- **The fixed fuel seed** — any nonzero-or-not entry of the pivot minor has magnitude `≤` the minor
abs-sum `smithMinorAbsSum`, the structural fuel the cascade is seeded with.  The pivot-minor wrapper of
`smithMinorEntryLeAbsSumRows`; feeding the found min-abs entry as the witness discharges
`cascadeMeasure ≤ smithMinorAbsSum` at cascade entry (the ONLY place the abs-sum enters — never as a
per-iteration decreasing quantity). -/
theorem smithMinorEntryLeAbsSum (matrix : IntMatrix)
    (pivotIndex height width witnessRow witnessCol : Nat)
    (witRowGe : pivotIndex ≤ witnessRow)
    (witRowLt : witnessRow < pivotIndex + (height - pivotIndex))
    (witColGe : pivotIndex ≤ witnessCol)
    (witColLt : witnessCol < pivotIndex + (width - pivotIndex)) :
    (matrix.entryAt witnessRow witnessCol).natAbs ≤ smithMinorAbsSum matrix pivotIndex height width :=
  smithMinorEntryLeAbsSumRows matrix pivotIndex (width - pivotIndex) (height - pivotIndex) pivotIndex
    witnessRow witnessCol witRowGe witRowLt witColGe witColLt

/-- `magnitude ≠ 0` from a `false` `== 0` beq — the structural converse of `natBeqZeroFalseOfNe`
(zero decides `true`, positives are `Nat.noConfusion`-distinct from zero), dodging `LawfulBEq`. -/
theorem natNeZeroOfBeqZeroFalse : ∀ magnitude : Nat, (magnitude == 0) = false → magnitude ≠ 0
  | 0, hFalse => Bool.noConfusion hFalse
  | _ + 1, _ => fun succEqZero => Nat.noConfusion succEqZero

/-- **Row scan result is nonzero** — if the incoming `best` (when `some`) points to a nonzero entry,
so does the row-scan result.  Structural on the column count; the update either keeps `best` (invariant
carried), takes a nonzero current entry (`natNeZeroOfBeqZeroFalse` off the `== 0` guard), or drops to
`none` (no `some` result to worry about). -/
theorem smithScanRowMinAbsResultNonzero (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart : Nat) (best : Option (Nat × Nat)) (foundRow foundCol : Nat),
      (∀ bestRow bestCol, best = some (bestRow, bestCol) →
        (matrix.entryAt bestRow bestCol).natAbs ≠ 0) →
      smithScanRowMinAbs matrix rowIndex colCount colStart best = some (foundRow, foundCol) →
      (matrix.entryAt foundRow foundCol).natAbs ≠ 0 := by
  intro colCount
  induction colCount with
  | zero =>
      intro colStart best foundRow foundCol bestNonzero scanEq
      exact bestNonzero foundRow foundCol scanEq
  | succ colCount ih =>
      intro colStart best foundRow foundCol bestNonzero scanEq
      cases best with
      | none =>
          refine ih (colStart + 1)
            (if (matrix.entryAt rowIndex colStart).natAbs == 0 then none
             else some (rowIndex, colStart)) foundRow foundCol ?_ scanEq
          intro updRow updCol updEq
          cases hGuard : (matrix.entryAt rowIndex colStart).natAbs == 0 with
          | true =>
              rw [if_pos hGuard] at updEq
              contradiction
          | false =>
              rw [if_neg (fun isTrue => Bool.noConfusion (isTrue.symm.trans hGuard))] at updEq
              injection updEq with pairEq
              injection pairEq with rowEq colEq
              subst rowEq; subst colEq
              exact natNeZeroOfBeqZeroFalse _ hGuard
      | some bestPair =>
          obtain ⟨bestRow, bestCol⟩ := bestPair
          have bestPairNonzero : (matrix.entryAt bestRow bestCol).natAbs ≠ 0 :=
            bestNonzero bestRow bestCol rfl
          refine ih (colStart + 1)
            (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
             else if (matrix.entryAt rowIndex colStart).natAbs < (matrix.entryAt bestRow bestCol).natAbs
                  then some (rowIndex, colStart) else some (bestRow, bestCol))
            foundRow foundCol ?_ scanEq
          intro updRow updCol updEq
          cases hGuard : (matrix.entryAt rowIndex colStart).natAbs == 0 with
          | true =>
              rw [if_pos hGuard] at updEq
              injection updEq with pairEq
              injection pairEq with rowEq colEq
              subst rowEq; subst colEq
              exact bestPairNonzero
          | false =>
              rw [if_neg (fun isTrue => Bool.noConfusion (isTrue.symm.trans hGuard))] at updEq
              cases Nat.decLt (matrix.entryAt rowIndex colStart).natAbs
                  (matrix.entryAt bestRow bestCol).natAbs with
              | isTrue takesCurrent =>
                  rw [if_pos takesCurrent] at updEq
                  injection updEq with pairEq
                  injection pairEq with rowEq colEq
                  subst rowEq; subst colEq
                  exact natNeZeroOfBeqZeroFalse _ hGuard
              | isFalse keepsBest =>
                  rw [if_neg keepsBest] at updEq
                  injection updEq with pairEq
                  injection pairEq with rowEq colEq
                  subst rowEq; subst colEq
                  exact bestPairNonzero

/-- **Minor scan result is nonzero** — the row-folded minor scan returns a `some` position at a nonzero
entry whenever the incoming best does.  Structural on the row count, lifting the row-scan
`ResultNonzero` through each folded row. -/
theorem smithScanMinorMinAbsResultNonzero (matrix : IntMatrix) (colStart colCount : Nat) :
    ∀ (rowCount rowStart : Nat) (best : Option (Nat × Nat)) (foundRow foundCol : Nat),
      (∀ bestRow bestCol, best = some (bestRow, bestCol) →
        (matrix.entryAt bestRow bestCol).natAbs ≠ 0) →
      smithScanMinorMinAbs matrix colStart colCount rowCount rowStart best = some (foundRow, foundCol) →
      (matrix.entryAt foundRow foundCol).natAbs ≠ 0 := by
  intro rowCount
  induction rowCount with
  | zero =>
      intro rowStart best foundRow foundCol bestNonzero scanEq
      exact bestNonzero foundRow foundCol scanEq
  | succ rowCount ih =>
      intro rowStart best foundRow foundCol bestNonzero scanEq
      refine ih (rowStart + 1) (smithScanRowMinAbs matrix rowStart colCount colStart best)
        foundRow foundCol ?_ scanEq
      intro innerRow innerCol innerEq
      exact smithScanRowMinAbsResultNonzero matrix rowStart colCount colStart best innerRow innerCol
        bestNonzero innerEq

/-- **The search returns a nonzero position** — `smithFindMinAbsInMinor` never reports a `some` at a
zero entry (the scan records only nonzero magnitudes).  So the found pivot magnitude is `> 0` — the
positivity the strict per-clear descent (`smithSingleClearStrictlyDecreasesPivot`) requires.  The
pivot-minor wrapper of `smithScanMinorMinAbsResultNonzero`, seeded from the vacuous `none`
invariant. -/
theorem smithFindMinAbsInMinorFoundNonzero (matrix : IntMatrix)
    (pivotIndex height width foundRow foundCol : Nat)
    (findEq : smithFindMinAbsInMinor matrix pivotIndex height width = some (foundRow, foundCol)) :
    (matrix.entryAt foundRow foundCol).natAbs ≠ 0 :=
  smithScanMinorMinAbsResultNonzero matrix pivotIndex (width - pivotIndex) (height - pivotIndex)
    pivotIndex none foundRow foundCol (fun _ _ noneEq => nomatch noneEq) findEq

/-- **A `none` search means the minor is all zero** — the completeness converse of the shipped
`smithFindMinAbsInMinorBoundsWitness`: if `smithFindMinAbsInMinor` returns `none`, every entry of the
pivot minor has magnitude zero (a nonzero one would force a `some` via the witness bound,
contradicting `none`).  Restricted to the cross this is the cross-clear base case of the fuel-adequacy
recursion. -/
theorem smithFindMinAbsInMinorNoneAllZero (matrix : IntMatrix)
    (pivotIndex height width witnessRow witnessCol : Nat)
    (findNone : smithFindMinAbsInMinor matrix pivotIndex height width = none)
    (witRowGe : pivotIndex ≤ witnessRow) (witRowLt : witnessRow < pivotIndex + (height - pivotIndex))
    (witColGe : pivotIndex ≤ witnessCol) (witColLt : witnessCol < pivotIndex + (width - pivotIndex)) :
    (matrix.entryAt witnessRow witnessCol).natAbs = 0 :=
  match Nat.eq_zero_or_pos (matrix.entryAt witnessRow witnessCol).natAbs with
  | .inl isZero => isZero
  | .inr isPositive =>
      match smithFindMinAbsInMinorBoundsWitness matrix pivotIndex height width witnessRow witnessCol
          witRowGe witRowLt witColGe witColLt
          (fun isZero => absurd (isZero ▸ isPositive) (Nat.lt_irrefl 0)) with
      | ⟨_, _, findSome, _⟩ => nomatch (findNone.symm.trans findSome)

/-! ## The cross-clear segment characterization (H2-SMITH r9) — the fuel-adequacy base/loop bridge

The fuel-adequacy recursion's base case (`fuel = 0`, and the `none` search) needs `smithCrossIsClear
= true` from "the pivot minor is all zero" (the shipped `smithFindMinAbsInMinorNoneAllZero`); its loop
step needs the converse — a `false` cross exhibits a nonzero cross residue to feed as the next-pivot
witness.  Both are structural Bool-fold facts over `smithRowSegmentAllZero` / `smithColSegmentAllZero`,
refutation-immune (a statement about ONE matrix's cross, never a sweep over arbitrary window-diagonal
inputs).  The window-range bridge is the propext-clean hand-proved `smithNatAddSubOfLe` (Init's
`Nat.add_sub_cancel'` is propext-dirty), so the whole family stays zero-axiom. -/

/-- **`k + (n - k) = n` for `k ≤ n`** — the hand-proved, propext-clean replacement for Init's
`Nat.add_sub_cancel'` (which drags `propext`).  Structural on `k`: the `succ`/`succ` arm reduces the
subtraction with `Nat.succ_sub_succ` (`succ - succ` is NOT definitionally `sub`), then rides
`Nat.succ_add` and the recursion. -/
theorem smithNatAddSubOfLe : ∀ (offset upper : Nat), offset ≤ upper → offset + (upper - offset) = upper
  | 0, upper, _ => Nat.zero_add upper
  | offset + 1, 0, isLe => absurd isLe (Nat.not_succ_le_zero offset)
  | offset + 1, upperPredecessor + 1, isLe =>
      (congrArg (fun difference => (offset + 1) + difference)
          (Nat.succ_sub_succ upperPredecessor offset)).trans
        ((Nat.succ_add offset (upperPredecessor - offset)).trans
          (congrArg Nat.succ
            (smithNatAddSubOfLe offset upperPredecessor (Nat.le_of_succ_le_succ isLe))))

/-- **A position below `upper` sits inside the `[offset, offset + (upper - offset))` window** — the
window-membership bridge: from `offset ≤ target` and `target < upper`, `target < offset + (upper -
offset)`, propext-clean through `smithNatAddSubOfLe`.  Feeds the shipped scan lemmas whose ranges are the
literal `pivotIndex + (dim - pivotIndex)` window bounds. -/
theorem natLtAddSubOfLt (offset target upper : Nat)
    (isGe : offset ≤ target) (isLt : target < upper) :
    target < offset + (upper - offset) :=
  Eq.mp (congrArg (target < ·)
      (smithNatAddSubOfLe offset upper (Nat.le_trans isGe (Nat.le_of_lt isLt))).symm) isLt

/-- **Row segment all-zero from pointwise zero** — if every entry of the scanned row window has
magnitude zero, the segment-all-zero flag is `true`.  Structural on the column count; the head entry
rewrites the `== 0` guard to `true` (`congrArg`), the tail rides the recursion. -/
theorem smithRowSegmentAllZeroOfPointwiseZero (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart : Nat),
      (∀ col, colStart ≤ col → col < colStart + colCount →
        (matrix.entryAt rowIndex col).natAbs = 0) →
      smithRowSegmentAllZero matrix rowIndex colCount colStart = true
  | 0, _, _ => rfl
  | colCount + 1, colStart, allZero =>
      have headZero : (matrix.entryAt rowIndex colStart).natAbs = 0 :=
        allZero colStart (Nat.le_refl colStart)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self colStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le colCount)) colStart))
      have restTrue : smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1) = true :=
        smithRowSegmentAllZeroOfPointwiseZero matrix rowIndex colCount (colStart + 1)
          (fun col colGe colLt =>
            allZero col (Nat.le_of_succ_le colGe)
              (Eq.mp (congrArg (col < ·) (Nat.succ_add colStart colCount)) colLt))
      (congrArg
          (fun headEntry =>
            (headEntry == 0) && smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1))
          headZero).trans restTrue

/-- **Column segment all-zero from pointwise zero** — the row mirror of the above, over
`smithColSegmentAllZero`. -/
theorem smithColSegmentAllZeroOfPointwiseZero (matrix : IntMatrix) (colIndex : Nat) :
    ∀ (rowCount rowStart : Nat),
      (∀ row, rowStart ≤ row → row < rowStart + rowCount →
        (matrix.entryAt row colIndex).natAbs = 0) →
      smithColSegmentAllZero matrix colIndex rowCount rowStart = true
  | 0, _, _ => rfl
  | rowCount + 1, rowStart, allZero =>
      have headZero : (matrix.entryAt rowStart colIndex).natAbs = 0 :=
        allZero rowStart (Nat.le_refl rowStart)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self rowStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rowCount)) rowStart))
      have restTrue : smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1) = true :=
        smithColSegmentAllZeroOfPointwiseZero matrix colIndex rowCount (rowStart + 1)
          (fun row rowGe rowLt =>
            allZero row (Nat.le_of_succ_le rowGe)
              (Eq.mp (congrArg (row < ·) (Nat.succ_add rowStart rowCount)) rowLt))
      (congrArg
          (fun headEntry =>
            (headEntry == 0) && smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1))
          headZero).trans restTrue

/-- **A `none` search means the cross is clear** — the base case of the fuel-adequacy recursion:
when `smithFindMinAbsInMinor` returns `none` the whole pivot minor is zero
(`smithFindMinAbsInMinorNoneAllZero`), so in particular each cross segment is pointwise zero and
`smithCrossIsClear = true`.  The window bridge `natLtAddSubOfLt` lands each segment position inside
the minor's scan window. -/
theorem smithCrossIsClearOfFindNone (matrix : IntMatrix) (pivotIndex height width : Nat)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (findNone : smithFindMinAbsInMinor matrix pivotIndex height width = none) :
    smithCrossIsClear matrix pivotIndex height width = true := by
  have rowTrue :
      smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) = true :=
    smithRowSegmentAllZeroOfPointwiseZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1)
      (fun col colGe colLt =>
        have colLtWidth : col < width :=
          Eq.mp (congrArg (col < ·) (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange)) colLt
        smithFindMinAbsInMinorNoneAllZero matrix pivotIndex height width pivotIndex col findNone
          (Nat.le_refl pivotIndex)
          (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pivotRowInRange)
          (Nat.le_of_succ_le colGe)
          (natLtAddSubOfLt pivotIndex col width (Nat.le_of_succ_le colGe) colLtWidth))
  have colTrue :
      smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1) = true :=
    smithColSegmentAllZeroOfPointwiseZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)
      (fun row rowGe rowLt =>
        have rowLtHeight : row < height :=
          Eq.mp (congrArg (row < ·) (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange)) rowLt
        smithFindMinAbsInMinorNoneAllZero matrix pivotIndex height width row pivotIndex findNone
          (Nat.le_of_succ_le rowGe)
          (natLtAddSubOfLt pivotIndex row height (Nat.le_of_succ_le rowGe) rowLtHeight)
          (Nat.le_refl pivotIndex)
          (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pivotColInRange))
  show (smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) &&
      smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)) = true
  rw [rowTrue, colTrue]
  rfl

/-- **A `false` row segment exhibits a nonzero column** — the converse of
`smithRowSegmentAllZeroOfPointwiseZero`: a `false` flag means some scanned position is nonzero.
Structural on the column count; the head `== 0` guard splits into "this column is the witness"
(`natNeZeroOfBeqZeroFalse`) or "recurse on the tail". -/
theorem smithRowSegmentNotAllZeroWitness (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart : Nat),
      smithRowSegmentAllZero matrix rowIndex colCount colStart = false →
      ∃ col, colStart ≤ col ∧ col < colStart + colCount ∧ (matrix.entryAt rowIndex col).natAbs ≠ 0 := by
  intro colCount
  induction colCount with
  | zero => intro colStart segFalse; exact Bool.noConfusion segFalse
  | succ colCount ih =>
      intro colStart segFalse
      have segUnfold :
          (((matrix.entryAt rowIndex colStart).natAbs == 0) &&
            smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1)) = false := segFalse
      cases hGuard : (matrix.entryAt rowIndex colStart).natAbs == 0 with
      | false =>
          exact ⟨colStart, Nat.le_refl colStart,
            Nat.lt_of_lt_of_le (Nat.lt_succ_self colStart)
              (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le colCount)) colStart),
            natNeZeroOfBeqZeroFalse _ hGuard⟩
      | true =>
          rw [hGuard] at segUnfold
          have restFalse : smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1) = false :=
            segUnfold
          match ih (colStart + 1) restFalse with
          | ⟨col, colGe, colLt, nonzero⟩ =>
              exact ⟨col, Nat.le_of_succ_le colGe,
                Eq.mp (congrArg (col < ·) (Nat.succ_add colStart colCount)) colLt, nonzero⟩

/-- **A `false` column segment exhibits a nonzero row** — the row mirror of the above. -/
theorem smithColSegmentNotAllZeroWitness (matrix : IntMatrix) (colIndex : Nat) :
    ∀ (rowCount rowStart : Nat),
      smithColSegmentAllZero matrix colIndex rowCount rowStart = false →
      ∃ row, rowStart ≤ row ∧ row < rowStart + rowCount ∧ (matrix.entryAt row colIndex).natAbs ≠ 0 := by
  intro rowCount
  induction rowCount with
  | zero => intro rowStart segFalse; exact Bool.noConfusion segFalse
  | succ rowCount ih =>
      intro rowStart segFalse
      have segUnfold :
          (((matrix.entryAt rowStart colIndex).natAbs == 0) &&
            smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1)) = false := segFalse
      cases hGuard : (matrix.entryAt rowStart colIndex).natAbs == 0 with
      | false =>
          exact ⟨rowStart, Nat.le_refl rowStart,
            Nat.lt_of_lt_of_le (Nat.lt_succ_self rowStart)
              (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rowCount)) rowStart),
            natNeZeroOfBeqZeroFalse _ hGuard⟩
      | true =>
          rw [hGuard] at segUnfold
          have restFalse : smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1) = false :=
            segUnfold
          match ih (rowStart + 1) restFalse with
          | ⟨row, rowGe, rowLt, nonzero⟩ =>
              exact ⟨row, Nat.le_of_succ_le rowGe,
                Eq.mp (congrArg (row < ·) (Nat.succ_add rowStart rowCount)) rowLt, nonzero⟩

/-- **A `false` cross exhibits a nonzero cross residue** — the loop step's witness source: when
`smithCrossIsClear = false`, either the pivot's row segment or its column segment carries a nonzero
entry (the segment `false` decomposed off the `&&`).  The disjunct positions are the literal segment
windows; the fuel-adequacy recursion lands them in the minor via `natLtAddSubOfLt` and bounds the
next measure through `smithFindMinAbsInMinorBoundsWitness`. -/
theorem smithCrossNotClearWitness (matrix : IntMatrix) (pivotIndex height width : Nat)
    (crossFalse : smithCrossIsClear matrix pivotIndex height width = false) :
    (∃ col, pivotIndex + 1 ≤ col ∧ col < (pivotIndex + 1) + (width - (pivotIndex + 1)) ∧
        (matrix.entryAt pivotIndex col).natAbs ≠ 0)
      ∨ (∃ row, pivotIndex + 1 ≤ row ∧ row < (pivotIndex + 1) + (height - (pivotIndex + 1)) ∧
        (matrix.entryAt row pivotIndex).natAbs ≠ 0) := by
  have crossUnfold :
      (smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) &&
        smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1))
          = false := crossFalse
  cases hRow :
      smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) with
  | false =>
      exact Or.inl (smithRowSegmentNotAllZeroWitness matrix pivotIndex (width - (pivotIndex + 1))
        (pivotIndex + 1) hRow)
  | true =>
      rw [hRow] at crossUnfold
      have colFalse :
          smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)
            = false := crossUnfold
      exact Or.inr (smithColSegmentNotAllZeroWitness matrix pivotIndex (height - (pivotIndex + 1))
        (pivotIndex + 1) colFalse)

/-! ## The move swap-entry bridge (H2-SMITH r9) — joint (a)'s backbone

`smithMoveToPivotOps` swaps the found min-abs entry into the pivot slot by one `swapRows` then one
`swapColumns`.  The fuel-adequacy recursion needs the resulting pivot slot's value read off: after the
move it holds exactly `matrix.entryAt foundRow foundCol` (the found min-abs entry).  This section ships
the two `listReplaceAt` read atoms (the `listModifyAt` sibling was already shipped) and the swap-entry
formulas built on them, then the move composition.  Each is a FUNCTION-CORRECTNESS fact about one
definite operation on one matrix — refutation-immune, like the B1–B5 clear atoms. -/

/-- **Reading the replaced position returns the new entry** — the `listReplaceAt` sibling of the shipped
`listGetWithDefaultModifyAtEq`.  Structural on the entry list and position (in range). -/
theorem listGetWithDefaultReplaceAtEq {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (position : Nat) (newEntry : Entry), position < entries.length →
      listGetWithDefault defaultEntry (listReplaceAt entries position newEntry) position = newEntry
  | [], _, _, isInRange => Nat.noConfusion (natEqZeroOfLeZero isInRange)
  | _ :: _, 0, _, _ => rfl
  | _ :: remainingEntries, position + 1, newEntry, isInRange =>
      listGetWithDefaultReplaceAtEq defaultEntry remainingEntries position newEntry
        (natLeOfSuccLeSucc isInRange)

/-- **Reading a different position is unchanged after a replace** — the `listReplaceAt` sibling of the
shipped `listGetWithDefaultModifyAtNe`.  Fully enumerated on list/position/read-position. -/
theorem listGetWithDefaultReplaceAtNe {Entry : Type} (defaultEntry : Entry) :
    ∀ (entries : List Entry) (position index : Nat) (newEntry : Entry), index ≠ position →
      listGetWithDefault defaultEntry (listReplaceAt entries position newEntry) index
        = listGetWithDefault defaultEntry entries index
  | [], 0, _, _, _ => rfl
  | [], _ + 1, _, _, _ => rfl
  | _ :: _, 0, 0, _, indexIsNotPosition => absurd rfl indexIsNotPosition
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: remainingEntries, position + 1, index + 1, newEntry, indexIsNotPosition =>
      listGetWithDefaultReplaceAtNe defaultEntry remainingEntries position index newEntry
        (fun successorsAgree => indexIsNotPosition (congrArg (· + 1) successorsAgree))

/-- **Swap reads the other row at the first index** — reading row `firstIndex` after `swapRows
firstIndex secondIndex` returns the whole `secondIndex` row (so its entry at `colIndex` is
`matrix.entryAt secondIndex colIndex`), both indices in range.  Cases the index equality (the
identity-on-equal-indices swap is uniform), then reads through the two `listReplaceAt` atoms. -/
theorem swapRowsEntryAtFirst (matrix : IntMatrix) (firstIndex secondIndex colIndex : Nat)
    (isFirstInRange : firstIndex < matrix.rows.length)
    (isSecondInRange : secondIndex < matrix.rows.length) :
    (matrix.swapRows firstIndex secondIndex).entryAt firstIndex colIndex
      = matrix.entryAt secondIndex colIndex := by
  have rowEq :
      listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows firstIndex
        = listGetWithDefault [] matrix.rows secondIndex := by
    unfold IntMatrix.swapRows
    rw [if_pos isFirstInRange, if_pos isSecondInRange]
    show listGetWithDefault []
        (listReplaceAt (listReplaceAt matrix.rows firstIndex
            (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
          (listGetWithDefault [] matrix.rows firstIndex)) firstIndex
      = listGetWithDefault [] matrix.rows secondIndex
    cases Nat.decEq firstIndex secondIndex with
    | isTrue firstEqSecond =>
        subst firstEqSecond
        rw [listGetWithDefaultReplaceAtEq [] _ firstIndex
            (listGetWithDefault [] matrix.rows firstIndex)
            (Eq.mp (congrArg (firstIndex < ·)
              (listReplaceAtPreservesLength matrix.rows firstIndex
                (listGetWithDefault [] matrix.rows firstIndex)).symm) isFirstInRange)]
    | isFalse firstNeSecond =>
        rw [listGetWithDefaultReplaceAtNe [] _ secondIndex firstIndex _ firstNeSecond,
            listGetWithDefaultReplaceAtEq [] matrix.rows firstIndex _ isFirstInRange]
  show listGetWithDefault 0
      (listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows firstIndex) colIndex
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows secondIndex) colIndex
  rw [rowEq]

/-- **Within-row swap reads the other entry at the first index** — the entry-level mirror of
`swapRowsEntryAtFirst`: reading position `firstIndex` after `swapEntriesWithinRow row firstIndex
secondIndex` returns `listGetWithDefault 0 row secondIndex`, both positions in range. -/
theorem swapEntriesWithinRowAtFirst (row : IntRow) (firstIndex secondIndex : Nat)
    (isFirstInRange : firstIndex < row.length) (isSecondInRange : secondIndex < row.length) :
    listGetWithDefault 0 (swapEntriesWithinRow row firstIndex secondIndex) firstIndex
      = listGetWithDefault 0 row secondIndex := by
  unfold IntMatrix.swapEntriesWithinRow
  rw [if_pos isFirstInRange, if_pos isSecondInRange]
  show listGetWithDefault 0
      (listReplaceAt (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
        (listGetWithDefault 0 row firstIndex)) firstIndex
    = listGetWithDefault 0 row secondIndex
  cases Nat.decEq firstIndex secondIndex with
  | isTrue firstEqSecond =>
      subst firstEqSecond
      rw [listGetWithDefaultReplaceAtEq 0 _ firstIndex (listGetWithDefault 0 row firstIndex)
          (Eq.mp (congrArg (firstIndex < ·)
            (listReplaceAtPreservesLength row firstIndex
              (listGetWithDefault 0 row firstIndex)).symm) isFirstInRange)]
  | isFalse firstNeSecond =>
      rw [listGetWithDefaultReplaceAtNe 0 _ secondIndex firstIndex _ firstNeSecond,
          listGetWithDefaultReplaceAtEq 0 row firstIndex _ isFirstInRange]

/-- **Swap reads the other column at the first index** — the column mirror of `swapRowsEntryAtFirst`:
reading column `firstIndex` of row `rowIndex` after `swapColumns firstIndex secondIndex` returns
`matrix.entryAt rowIndex secondIndex`, all indices in range (rectangularity supplies the row width).
Reads the mapped row by the shipped `listGetWithDefaultMapAllRows`, then rides
`swapEntriesWithinRowAtFirst`. -/
theorem swapColumnsEntryAtFirst {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (firstIndex secondIndex rowIndex : Nat)
    (isRowInRange : rowIndex < height)
    (isFirstInRange : firstIndex < width) (isSecondInRange : secondIndex < width) :
    (matrix.swapColumns firstIndex secondIndex).entryAt rowIndex firstIndex
      = matrix.entryAt rowIndex secondIndex := by
  obtain ⟨rowCount, rowWidths⟩ := isRect
  have rowInRows : rowIndex < matrix.rows.length :=
    Eq.mp (congrArg (rowIndex < ·) rowCount.symm) isRowInRange
  have rowHasWidth : (listGetWithDefault [] matrix.rows rowIndex).length = width :=
    listGetWithDefaultHasWidth matrix.rows rowIndex rowWidths rowInRows
  show listGetWithDefault 0 (listGetWithDefault []
      (mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex) matrix.rows) rowIndex)
      firstIndex
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) secondIndex
  rw [listGetWithDefaultMapAllRows _ matrix.rows rowIndex rowInRows]
  exact swapEntriesWithinRowAtFirst (listGetWithDefault [] matrix.rows rowIndex) firstIndex secondIndex
    (Eq.mp (congrArg (firstIndex < ·) rowHasWidth.symm) isFirstInRange)
    (Eq.mp (congrArg (secondIndex < ·) rowHasWidth.symm) isSecondInRange)

/-- **The move lands the found entry on the pivot slot** — after `smithMoveToPivotOps pivotIndex
foundRow foundCol` (swap the found row into the pivot row, then the found column into the pivot column)
the pivot slot `(pivotIndex, pivotIndex)` holds exactly `matrix.entryAt foundRow foundCol`.  The
column swap reads column `pivotIndex` back to column `foundCol` (`swapColumnsEntryAtFirst`), the row
swap reads row `pivotIndex` back to row `foundRow` (`swapRowsEntryAtFirst`).  This is joint (a)'s
backbone: with the found position nonzero and sign-normalised nonnegative, the pivot magnitude the
strict per-clear descent needs equals `(matrix.entryAt foundRow foundCol).natAbs`. -/
theorem smithMoveToPivotEntryOnPivot {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex foundRow foundCol : Nat)
    (isPivotRowInRange : pivotIndex < height) (isFoundRowInRange : foundRow < height)
    (isPivotColInRange : pivotIndex < width) (isFoundColInRange : foundCol < width) :
    (matrix.applyOperations (smithMoveToPivotOps pivotIndex foundRow foundCol)).entryAt
        pivotIndex pivotIndex
      = matrix.entryAt foundRow foundCol := by
  have rowCount : matrix.rows.length = height := isRect.1
  have pivotInRows : pivotIndex < matrix.rows.length :=
    Eq.mp (congrArg (pivotIndex < ·) rowCount.symm) isPivotRowInRange
  have foundInRows : foundRow < matrix.rows.length :=
    Eq.mp (congrArg (foundRow < ·) rowCount.symm) isFoundRowInRange
  have swapRowRect : (matrix.swapRows pivotIndex foundRow).IsRectangular height width :=
    applyRowOperationPreservesRectangular (ElementaryRowOperation.swapRows pivotIndex foundRow) matrix
      isRect
  show ((matrix.swapRows pivotIndex foundRow).swapColumns pivotIndex foundCol).entryAt
      pivotIndex pivotIndex
    = matrix.entryAt foundRow foundCol
  rw [swapColumnsEntryAtFirst (matrix.swapRows pivotIndex foundRow) swapRowRect pivotIndex foundCol
      pivotIndex isPivotRowInRange isPivotColInRange isFoundColInRange]
  exact swapRowsEntryAtFirst matrix pivotIndex foundRow foundCol pivotInRows foundInRows

/-! ## The found-in-range scan companion (H2-SMITH r10, B1) — joint (i)

The fuel-adequacy recursion moves the found min-abs entry into the pivot slot via
`smithMoveToPivotEntryOnPivot`, whose in-range hypotheses (`foundRow < height`, `foundCol < width`)
demand a scan companion certifying the found position sits in the pivot window.  This section threads
a GENERIC position predicate through the row/minor scans — a structural mirror of the shipped
`smithScanMinorMinAbsResultNonzero` — then instantiates it at the window-membership predicate.  Each
is a FUNCTION-CORRECTNESS fact about the definite scan on ONE matrix, refutation-immune. -/

/-- **Concrete truth probe for the found-in-range companion** — on `[[0, 6], [4, 0]]` at pivot `0`
the whole-minor min-abs search lands the intervening `4` at `(1, 0)` (NOT the pivot `(0, 0) = 0`),
a position genuinely inside `[0, 2) × [0, 2)`.  Anonymous, so it carries no axiom footprint. -/
example :
    smithFindMinAbsInMinor ({ rows := [[0, 6], [4, 0]] } : IntMatrix) 0 2 2 = some (1, 0) := by decide

/-- **Row scan keeps a window predicate** — if every scanned column position `(rowIndex, col)` in
`[colStart, colStart + colCount)` satisfies `property`, and an incoming `some` best does too, then the
row-scan result (when `some`) satisfies `property`.  Structural on the column count; the update either
keeps `best` (invariant carried) or takes the current position (in the scanned window).  The generic
mirror of `smithScanRowMinAbsResultNonzero`. -/
theorem smithScanRowMinAbsResultInRange (matrix : IntMatrix) (rowIndex : Nat)
    (property : Nat → Nat → Prop) :
    ∀ (colCount colStart : Nat) (best : Option (Nat × Nat)) (foundRow foundCol : Nat),
      (∀ col, colStart ≤ col → col < colStart + colCount → property rowIndex col) →
      (∀ bestRow bestCol, best = some (bestRow, bestCol) → property bestRow bestCol) →
      smithScanRowMinAbs matrix rowIndex colCount colStart best = some (foundRow, foundCol) →
      property foundRow foundCol := by
  intro colCount
  induction colCount with
  | zero =>
      intro colStart best foundRow foundCol _ bestInRange scanEq
      exact bestInRange foundRow foundCol scanEq
  | succ colCount ih =>
      intro colStart best foundRow foundCol colInRange bestInRange scanEq
      have headProperty : property rowIndex colStart :=
        colInRange colStart (Nat.le_refl colStart)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self colStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le colCount)) colStart))
      have tailInRange : ∀ col, colStart + 1 ≤ col → col < (colStart + 1) + colCount →
          property rowIndex col :=
        fun col colGe colLt =>
          colInRange col (Nat.le_of_succ_le colGe)
            (Eq.mp (congrArg (col < ·) (Nat.succ_add colStart colCount)) colLt)
      cases best with
      | none =>
          refine ih (colStart + 1)
            (if (matrix.entryAt rowIndex colStart).natAbs == 0 then none
             else some (rowIndex, colStart)) foundRow foundCol tailInRange ?_ scanEq
          intro updRow updCol updEq
          cases hGuard : (matrix.entryAt rowIndex colStart).natAbs == 0 with
          | true =>
              rw [if_pos hGuard] at updEq
              contradiction
          | false =>
              rw [if_neg (fun isTrue => Bool.noConfusion (isTrue.symm.trans hGuard))] at updEq
              injection updEq with pairEq
              injection pairEq with rowEq colEq
              subst rowEq; subst colEq
              exact headProperty
      | some bestPair =>
          obtain ⟨bestRow, bestCol⟩ := bestPair
          have bestPairInRange : property bestRow bestCol := bestInRange bestRow bestCol rfl
          refine ih (colStart + 1)
            (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
             else if (matrix.entryAt rowIndex colStart).natAbs < (matrix.entryAt bestRow bestCol).natAbs
                  then some (rowIndex, colStart) else some (bestRow, bestCol))
            foundRow foundCol tailInRange ?_ scanEq
          intro updRow updCol updEq
          cases hGuard : (matrix.entryAt rowIndex colStart).natAbs == 0 with
          | true =>
              rw [if_pos hGuard] at updEq
              injection updEq with pairEq
              injection pairEq with rowEq colEq
              subst rowEq; subst colEq
              exact bestPairInRange
          | false =>
              rw [if_neg (fun isTrue => Bool.noConfusion (isTrue.symm.trans hGuard))] at updEq
              cases Nat.decLt (matrix.entryAt rowIndex colStart).natAbs
                  (matrix.entryAt bestRow bestCol).natAbs with
              | isTrue takesCurrent =>
                  rw [if_pos takesCurrent] at updEq
                  injection updEq with pairEq
                  injection pairEq with rowEq colEq
                  subst rowEq; subst colEq
                  exact headProperty
              | isFalse keepsBest =>
                  rw [if_neg keepsBest] at updEq
                  injection updEq with pairEq
                  injection pairEq with rowEq colEq
                  subst rowEq; subst colEq
                  exact bestPairInRange

/-- **Minor scan keeps a window predicate** — if every scanned position `(row, col)` in the rectangle
`[rowStart, rowStart + rowCount) × [colStart, colStart + colCount)` satisfies `property`, and an
incoming `some` best does too, then the folded minor scan result (when `some`) satisfies `property`.
Structural on the row count, lifting the row-scan companion through each folded row.  The generic
mirror of `smithScanMinorMinAbsResultNonzero`. -/
theorem smithScanMinorMinAbsResultInRange (matrix : IntMatrix) (colStart colCount : Nat)
    (property : Nat → Nat → Prop) :
    ∀ (rowCount rowStart : Nat) (best : Option (Nat × Nat)) (foundRow foundCol : Nat),
      (∀ row col, rowStart ≤ row → row < rowStart + rowCount →
        colStart ≤ col → col < colStart + colCount → property row col) →
      (∀ bestRow bestCol, best = some (bestRow, bestCol) → property bestRow bestCol) →
      smithScanMinorMinAbs matrix colStart colCount rowCount rowStart best = some (foundRow, foundCol) →
      property foundRow foundCol := by
  intro rowCount
  induction rowCount with
  | zero =>
      intro rowStart best foundRow foundCol _ bestInRange scanEq
      exact bestInRange foundRow foundCol scanEq
  | succ rowCount ih =>
      intro rowStart best foundRow foundCol cellInRange bestInRange scanEq
      refine ih (rowStart + 1) (smithScanRowMinAbs matrix rowStart colCount colStart best)
        foundRow foundCol ?_ ?_ scanEq
      · intro row col rowGe rowLt colGe colLt
        exact cellInRange row col (Nat.le_of_succ_le rowGe)
          (Eq.mp (congrArg (row < ·) (Nat.succ_add rowStart rowCount)) rowLt) colGe colLt
      · intro innerRow innerCol innerEq
        exact smithScanRowMinAbsResultInRange matrix rowStart property colCount colStart best
          innerRow innerCol
          (fun col colGe colLt =>
            cellInRange rowStart col (Nat.le_refl rowStart)
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self rowStart)
                (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rowCount)) rowStart))
              colGe colLt)
          bestInRange innerEq

/-- **The search returns an in-range position** — `smithFindMinAbsInMinor` reports a `some` position
inside the pivot window `[pivotIndex, height) × [pivotIndex, width)`.  The window-membership
instantiation of `smithScanMinorMinAbsResultInRange`, converting the raw scan bounds
`pivotIndex + (dim - pivotIndex)` to `< dim` via the propext-clean `smithNatAddSubOfLe`
(`pivotIndex ≤ dim` from the pivot-in-range hypotheses).  This feeds `smithMoveToPivotEntryOnPivot`'s
in-range hypotheses in the fuel-adequacy recursion — joint (i). -/
theorem smithFindMinAbsInMinorFoundInRange (matrix : IntMatrix)
    (pivotIndex height width foundRow foundCol : Nat)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (findEq : smithFindMinAbsInMinor matrix pivotIndex height width = some (foundRow, foundCol)) :
    pivotIndex ≤ foundRow ∧ foundRow < height ∧ pivotIndex ≤ foundCol ∧ foundCol < width :=
  smithScanMinorMinAbsResultInRange matrix pivotIndex (width - pivotIndex)
    (fun row col => pivotIndex ≤ row ∧ row < height ∧ pivotIndex ≤ col ∧ col < width)
    (height - pivotIndex) pivotIndex none foundRow foundCol
    (fun row col rowGe rowLt colGe colLt =>
      ⟨rowGe,
        Eq.mp (congrArg (row < ·)
          (smithNatAddSubOfLe pivotIndex height (Nat.le_of_lt pivotRowInRange))) rowLt,
        colGe,
        Eq.mp (congrArg (col < ·)
          (smithNatAddSubOfLe pivotIndex width (Nat.le_of_lt pivotColInRange))) colLt⟩)
    (fun _ _ noneEq => nomatch noneEq)
    findEq

/-- **Negation preserves magnitude** — `(-value).natAbs = value.natAbs` for any `Int`.  The `ofNat`
arm rides the shipped `intNegOfNatNatAbs`; the `negSucc` arm is `rfl` (`-(negSucc m) = ofNat (m+1)`).
The micro-atom the sign-phase magnitude bridge needs (`|-x| = |x|`). -/
theorem intNegNatAbs : ∀ value : Int, (-value).natAbs = value.natAbs
  | .ofNat magnitude => intNegOfNatNatAbs magnitude
  | .negSucc _ => rfl

/-! ## The fuel-adequacy induction (H2-SMITH r10, B2) — `smithCascadeReachesCrossClear`

The cascade recursion moves the min-abs entry to the pivot, sign-normalises it, clears the cross, and
LOOPS if the cross is not yet zero.  The measure is the moved pivot's magnitude
`(matrix.entryAt foundRow foundCol).natAbs`, read at cascade entry and bounded by the STATIC fuel; each
loop iteration re-searches a strictly smaller minor (the parked cross residues land strictly below the
old pivot).  This section ships the strong (structural) induction on the inner fuel that, seeded with
`measure ≤ fuel`, reaches a cross-clear state.

The pivot-magnitude PACKAGING (`smithSignNormalizeOpsPreservesPivotMagnitude`) and the sweep
succ-unfolding equation (`smithCascadeSweepSucc`) are the two glue atoms; the induction body dispatches
the shipped `smithCrossNotClearWitness` into the two strict-descent lemmas
(`smithClear{RowRight,ColumnBelow}StepsCrossEntryStrictlyDecreases`, threading the pivot-column locality
`smithClearRowRightStepsPreservesColumn` for the column segment) and bounds the next measure through
`smithFindMinAbsInMinorBoundsWitness`.  Every joint is a NAMED shipped lemma; the whole family is
function-correctness about the definite cascade word on ONE threaded matrix, refutation-immune.

**Scope caveat (honest, DESIGN-LOCKED):** `smithCascadeReachesCrossClear` delivers ONLY the cross-clear
conjunct of obligation (a).  The sub-block-stays-diagonal + gcd-divides-folded-operands + chain
conjuncts feeding `SmithNormalForm`'s `repairWindowDiagHolds` / `repairChainHolds` remain the r10+ wall
— those two surviving repair hypotheses stay UNCLOSED, `SmithReduceFullDriverStatement` uninhabited (no
flip). -/

/-- **The per-pivot sign word preserves the pivot magnitude** — `|afterSign pivot| = |afterMove pivot|`:
the sign word either leaves the pivot untouched (`signNormalizeOpsEntryOnPivotIsSignedInput` left arm,
`natAbs` unchanged) or negates it (right arm, `intNegNatAbs` strips the flip).  The magnitude bridge the
cascade recursion rides to carry the moved pivot's magnitude through the sign phase. -/
theorem smithSignNormalizeOpsPreservesPivotMagnitude (matrix : IntMatrix) (pivotIndex : Nat)
    (isInRange : pivotIndex < matrix.rows.length) :
    ((matrix.applyOperations (smithSignNormalizeOps matrix pivotIndex)).entryAt
        pivotIndex pivotIndex).natAbs
      = (matrix.entryAt pivotIndex pivotIndex).natAbs :=
  match signNormalizeOpsEntryOnPivotIsSignedInput matrix pivotIndex isInRange with
  | Or.inl unchanged => congrArg Int.natAbs unchanged
  | Or.inr negated =>
      (congrArg Int.natAbs negated).trans (intNegNatAbs (matrix.entryAt pivotIndex pivotIndex))

/-- **`smithCascadeSweep` at successor fuel unfolds to its match body** — the definitional unfolding of
the structural recursion at `innerFuel + 1`, exposed as a rewrite target (`rfl`).  Lets the fuel-adequacy
induction reduce the sweep by rewriting the search result (`hFind`) and the cross-clear branch. -/
theorem smithCascadeSweepSucc (innerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat) :
    smithCascadeSweep (innerFuel + 1) matrix pivotIndex height width
      = (match smithFindMinAbsInMinor matrix pivotIndex height width with
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
                 settledOps ++ smithCascadeSweep innerFuel afterRowClear pivotIndex height width) :=
  rfl

/-- **The cascade reaches a cross-clear state within its fuel** — for a rectangular matrix with the
pivot in range, if the fuel bounds the moved pivot's magnitude (`measure ≤ fuel`, seeded at cascade
entry by `smithMinorEntryLeAbsSum`), then after `smithCascadeSweep fuel` the pivot's cross is clear.
Strong (structural) induction on the inner `fuel`.

  * **Base (`fuel = 0`)**: the sweep is empty; the search must be `none` (a `some` would carry a
    nonzero magnitude `≤ 0`, impossible by `smithFindMinAbsInMinorFoundNonzero`), so
    `smithCrossIsClearOfFindNone` closes.
  * **Step, `none`**: same — the empty sweep leaves the already-clear cross.
  * **Step, `some (foundRow, foundCol)`, cross already clear after the settle**: the settle word applied
    lands `afterRowClear`, whose cross-clear flag is the taken branch.
  * **Step, `some`, cross NOT clear**: the sweep loops on `afterRowClear` with fuel `fuel`; the IH
    closes, once the fuel bound descends.  The descent: the moved+sign-normalised pivot has magnitude
    `= (matrix.entryAt foundRow foundCol).natAbs ≤ fuel + 1` (the packaging bridges), positive and
    nonnegative; `smithCrossNotClearWitness` exhibits a nonzero cross residue whose magnitude is
    STRICTLY below that pivot (the two strict-descent lemmas, the column segment carried through the
    row clear by `smithClearRowRightStepsPreservesColumn`), and `smithFindMinAbsInMinorBoundsWitness`
    bounds the next search result by that residue — strictly below `fuel + 1`, hence `≤ fuel`. -/
theorem smithCascadeReachesCrossClear :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      (∀ foundRow foundCol,
        smithFindMinAbsInMinor matrix pivotIndex height width = some (foundRow, foundCol) →
        (matrix.entryAt foundRow foundCol).natAbs ≤ fuel) →
      smithCrossIsClear
          (matrix.applyOperations (smithCascadeSweep fuel matrix pivotIndex height width))
          pivotIndex height width = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width _ pivotRowInRange pivotColInRange fuelBound
      show smithCrossIsClear matrix pivotIndex height width = true
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          exact smithCrossIsClearOfFindNone matrix pivotIndex height width pivotRowInRange
            pivotColInRange hFind
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
          exact absurd
            (Nat.le_antisymm (fuelBound foundRow foundCol hFind) (Nat.zero_le _))
            (smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width foundRow foundCol hFind)
  | succ fuel ih =>
      intro matrix pivotIndex height width isRect pivotRowInRange pivotColInRange fuelBound
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          exact smithCrossIsClearOfFindNone matrix pivotIndex height width pivotRowInRange
            pivotColInRange hFind
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
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
          have afterMoveRect : afterMove.IsRectangular height width :=
            applyOperationsPreservesRectangular moveOps matrix isRect
          have afterSignRect : afterSign.IsRectangular height width :=
            applyOperationsPreservesRectangular signOps afterMove afterMoveRect
          have afterColumnClearRect : afterColumnClear.IsRectangular height width :=
            applyOperationsPreservesRectangular columnClearOps afterSign afterSignRect
          have afterRowClearRect : afterRowClear.IsRectangular height width :=
            applyOperationsPreservesRectangular rowClearOps afterColumnClear afterColumnClearRect
          have afterMoveInRows : pivotIndex < afterMove.rows.length :=
            Eq.mp (congrArg (pivotIndex < ·) afterMoveRect.1.symm) pivotRowInRange
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pivotRowInRange pivotColInRange hFind
          have foundNonzero : (matrix.entryAt foundRow foundCol).natAbs ≠ 0 :=
            smithFindMinAbsInMinorFoundNonzero matrix pivotIndex height width foundRow foundCol hFind
          have pivotPositive : 0 < (matrix.entryAt foundRow foundCol).natAbs :=
            match Nat.eq_zero_or_pos (matrix.entryAt foundRow foundCol).natAbs with
            | Or.inl isZero => absurd isZero foundNonzero
            | Or.inr isPositive => isPositive
          have pivotMagLe : (matrix.entryAt foundRow foundCol).natAbs ≤ fuel + 1 :=
            fuelBound foundRow foundCol hFind
          have moveEntry : afterMove.entryAt pivotIndex pivotIndex = matrix.entryAt foundRow foundCol :=
            smithMoveToPivotEntryOnPivot matrix isRect pivotIndex foundRow foundCol pivotRowInRange
              foundInRange.2.1 pivotColInRange foundInRange.2.2.2
          have signMagFound :
              (afterSign.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (smithSignNormalizeOpsPreservesPivotMagnitude afterMove pivotIndex afterMoveInRows).trans
              (congrArg Int.natAbs moveEntry)
          have signNonneg : 0 ≤ afterSign.entryAt pivotIndex pivotIndex :=
            signNormalizeOpsEntryOnPivotNonneg afterMove pivotIndex afterMoveInRows
          have colClearPreservesPivot :
              afterColumnClear.entryAt pivotIndex pivotIndex = afterSign.entryAt pivotIndex pivotIndex :=
            smithClearColumnBelowStepsPreservesRow afterSign pivotIndex pivotIndex pivotIndex
              (height - (pivotIndex + 1)) (pivotIndex + 1) afterSign (Nat.lt_succ_self pivotIndex)
          have colClearPivotMag :
              (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs = (matrix.entryAt foundRow foundCol).natAbs :=
            (congrArg Int.natAbs colClearPreservesPivot).trans signMagFound
          have colClearPivotNonneg : 0 ≤ afterColumnClear.entryAt pivotIndex pivotIndex :=
            Eq.mp (congrArg (0 ≤ ·) colClearPreservesPivot.symm) signNonneg
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          have hSweep : smithCascadeSweep (fuel + 1) matrix pivotIndex height width
              = (match smithCrossIsClear afterRowClear pivotIndex height width with
                 | true => settledOps
                 | false => settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width) := by
            rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          rw [hSweep]
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true =>
              rw [hApplySettled]
              exact hCross
          | false =>
              rw [applyOperationsAppend, hApplySettled]
              refine ih afterRowClear pivotIndex height width afterRowClearRect pivotRowInRange
                pivotColInRange ?_
              intro nextRow nextCol hFind'
              have boundFromWitness : ∀ witnessRow witnessCol,
                  pivotIndex ≤ witnessRow → witnessRow < pivotIndex + (height - pivotIndex) →
                  pivotIndex ≤ witnessCol → witnessCol < pivotIndex + (width - pivotIndex) →
                  (afterRowClear.entryAt witnessRow witnessCol).natAbs ≠ 0 →
                  (afterRowClear.entryAt witnessRow witnessCol).natAbs
                    < (matrix.entryAt foundRow foundCol).natAbs →
                  (afterRowClear.entryAt nextRow nextCol).natAbs ≤ fuel := by
                intro witnessRow witnessCol wRGe wRLt wCGe wCLt witNonzero witLtPivot
                match smithFindMinAbsInMinorBoundsWitness afterRowClear pivotIndex height width
                    witnessRow witnessCol wRGe wRLt wCGe wCLt witNonzero with
                | ⟨boundRow, boundCol, boundFindEq, boundLe⟩ =>
                    have someEq : some (boundRow, boundCol) = some (nextRow, nextCol) :=
                      boundFindEq.symm.trans hFind'
                    injection someEq with pairEq
                    injection pairEq with rowEq colEq
                    subst rowEq
                    subst colEq
                    exact Nat.le_trans boundLe
                      (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le witLtPivot pivotMagLe))
              cases smithCrossNotClearWitness afterRowClear pivotIndex height width hCross with
              | inl rowWitness =>
                  obtain ⟨col, colGe, colLt, colNonzero⟩ := rowWitness
                  have colLtWidth : col < width :=
                    Eq.mp (congrArg (col < ·)
                      (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange)) colLt
                  have colClearPivotPositive : 0 < (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs :=
                    Nat.lt_of_lt_of_le pivotPositive (Nat.le_of_eq colClearPivotMag.symm)
                  have rowStrict :
                      (afterRowClear.entryAt pivotIndex col).natAbs
                        < (afterColumnClear.entryAt pivotIndex pivotIndex).natAbs :=
                    smithClearRowRightStepsCrossEntryStrictlyDecreases afterColumnClear
                      afterColumnClearRect pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) col
                      (Nat.lt_succ_self pivotIndex) colGe colLt pivotRowInRange pivotColInRange
                      (Nat.le_of_eq (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange))
                      colClearPivotNonneg colClearPivotPositive
                  have witLtPivot :
                      (afterRowClear.entryAt pivotIndex col).natAbs
                        < (matrix.entryAt foundRow foundCol).natAbs :=
                    Nat.lt_of_lt_of_le rowStrict (Nat.le_of_eq colClearPivotMag)
                  exact boundFromWitness pivotIndex col (Nat.le_refl pivotIndex)
                    (natLtAddSubOfLt pivotIndex pivotIndex height (Nat.le_refl pivotIndex) pivotRowInRange)
                    (Nat.le_of_succ_le colGe)
                    (natLtAddSubOfLt pivotIndex col width (Nat.le_of_succ_le colGe) colLtWidth)
                    colNonzero witLtPivot
              | inr colWitness =>
                  obtain ⟨row, rowGe, rowLt, rowNonzero⟩ := colWitness
                  have rowLtHeight : row < height :=
                    Eq.mp (congrArg (row < ·)
                      (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange)) rowLt
                  have signPositive : 0 < (afterSign.entryAt pivotIndex pivotIndex).natAbs :=
                    Nat.lt_of_lt_of_le pivotPositive (Nat.le_of_eq signMagFound.symm)
                  have rowClearPreservesCol :
                      afterRowClear.entryAt row pivotIndex = afterColumnClear.entryAt row pivotIndex :=
                    smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width
                      row pivotIndex rowLtHeight (width - (pivotIndex + 1)) (pivotIndex + 1)
                      afterColumnClear afterColumnClearRect (Nat.lt_succ_self pivotIndex)
                  have colStrict :
                      (afterColumnClear.entryAt row pivotIndex).natAbs
                        < (afterSign.entryAt pivotIndex pivotIndex).natAbs :=
                    smithClearColumnBelowStepsCrossEntryStrictlyDecreases afterSign afterSignRect
                      pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1) row
                      (Nat.lt_succ_self pivotIndex) rowGe rowLt pivotRowInRange pivotColInRange
                      (Nat.le_of_eq (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange))
                      signNonneg signPositive
                  have witLtPivot :
                      (afterRowClear.entryAt row pivotIndex).natAbs
                        < (matrix.entryAt foundRow foundCol).natAbs :=
                    Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg Int.natAbs rowClearPreservesCol))
                      (Nat.lt_of_lt_of_le colStrict (Nat.le_of_eq signMagFound))
                  exact boundFromWitness row pivotIndex (Nat.le_of_succ_le rowGe)
                    (natLtAddSubOfLt pivotIndex row height (Nat.le_of_succ_le rowGe) rowLtHeight)
                    (Nat.le_refl pivotIndex)
                    (natLtAddSubOfLt pivotIndex pivotIndex width (Nat.le_refl pivotIndex) pivotColInRange)
                    rowNonzero witLtPivot

/-- **The cascade at its ACTUAL seed fuel reaches cross-clear** (H2-SMITH r10, B3, driver-path) —
`smithCascadeReachesCrossClear` discharged at `smithMinorAbsSum matrix pivotIndex height width`, the
STATIC fuel the total driver (`smithReduceTotalSweep`) and the repair (`smithRepairPositionSweep`)
actually seed the cascade with.  The fuel-adequacy precondition is met because any found min-abs entry
sits in the pivot window (`smithFindMinAbsInMinorFoundInRange`) and every window entry's magnitude is
`≤ smithMinorAbsSum` (`smithMinorEntryLeAbsSum`).  This is the driver-path postcondition — a
function-correctness fact about the definite cascade word on ONE threaded matrix, under the delivered
`IsRectangular` + pivot-in-range preconditions — NOT a free-standing sweep pole over arbitrary
window-diagonal inputs (the r5/r6 refuted shape).  It delivers ONLY the cross-clear conjunct of
obligation (a); the sub-block-diagonal + gcd-chain conjuncts feeding `SmithNormalForm`'s
`repairWindowDiagHolds` / `repairChainHolds` stay UNCLOSED this round. -/
theorem smithCascadeSweepSeedReachesCrossClear (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width) :
    smithCrossIsClear
        (matrix.applyOperations
          (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width))
        pivotIndex height width = true :=
  smithCascadeReachesCrossClear (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
    height width isRect pivotRowInRange pivotColInRange
    (fun foundRow foundCol findEq =>
      let foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width foundRow
        foundCol pivotRowInRange pivotColInRange findEq
      smithMinorEntryLeAbsSum matrix pivotIndex height width foundRow foundCol
        foundInRange.1
        (natLtAddSubOfLt pivotIndex foundRow height foundInRange.1 foundInRange.2.1)
        foundInRange.2.2.1
        (natLtAddSubOfLt pivotIndex foundCol width foundInRange.2.2.1 foundInRange.2.2.2))

/-! ## The sub-block (low-low) locality round (H2-SMITH r11, B1) — the settled-prefix monotonicity

The cascade word at pivot `pivotIndex` modifies only rows `≥ pivotIndex` (move swap, sign, column
clears) and only columns `≥ pivotIndex` (move swap, row clears).  Consequently a LOW-LOW entry
`(readRow, readCol)` with `readRow < pivotIndex ∧ readCol < pivotIndex` — a settled-prefix cell — is
left UNCHANGED by the whole cascade.  This is the sharpest predicate that folds cleanly across the
heterogeneous move/sign/clear word: a row op defeats reads with `readRow < pivotIndex` (all columns),
a column op defeats reads with `readCol < pivotIndex` (all rows), and only the low-low corner defeats
BOTH.

Every atom below is a FUNCTION-CORRECTNESS fact about the definite word on ONE threaded matrix, under
the delivered `IsRectangular` + pivot-in-range preconditions — refutation-immune, like the r9/r10 clear
and cross-clear atoms.  The two swaps are the only letters that lacked an "off-both" preserver; the sign
phase (`signNormalizeOpsPreserveEntryOffPivot`) and both clears (`smithClearColumnBelowStepsPreservesRow`
/ `smithClearRowRightStepsPreservesColumn`) are already shipped and reused verbatim.  The move swap is
local ONLY because the r10 `smithFindMinAbsInMinorFoundInRange` pins `pivotIndex ≤ foundRow` and
`pivotIndex ≤ foundCol` — without it the swapped-in row/column could sit BELOW the pivot and drag a low
cell.

SCOPE (per the recon gap audit): this delivers the PREFIX conjunct of `SmithNormalForm`'s window-diagonal
predicate ONLY (`readRow < pivotIndex ∧ readCol < pivotIndex`).  The below-left / above-right bands and
the sub-block re-diagonalization are NOT locality — they need the invariant-fed "reads-only-zeros"
argument (POLE-A), so `repairWindowDiagHolds` / `repairChainHolds` stay UNCLOSED this round; no flip. -/

/-- **Concrete truth probe for low-low locality** — on `[[7, 2, 3], [4, 5, 6], [1, 2, 4]]` at pivot `1`
the cascade FIRES a genuine 8-letter move+sign+clear word (its sub-minor `[[5, 6], [2, 4]]` is nonzero, so
the search moves the `2` at `(2, 1)` in, sign-normalises, and Euclid-clears the pivot's cross), yet the
marked low-low entry `(0, 0) = 7` — a settled-prefix cell strictly above and left of the pivot — is left
untouched.  Anonymous, so it carries no axiom footprint. -/
example :
    (({ rows := [[7, 2, 3], [4, 5, 6], [1, 2, 4]] } : IntMatrix).applyOperations
        (smithCascadeSweep 6 ({ rows := [[7, 2, 3], [4, 5, 6], [1, 2, 4]] } : IntMatrix) 1 3 3)).entryAt 0 0
      = 7 := by decide

/-- **Swap preserves an entry off BOTH swapped rows** — reading row `readRow` after `swapRows firstIndex
secondIndex` is unchanged when `readRow` is neither swapped index.  No rectangularity: the two range
`if`-guards make the op an identity when out of range, and the in-range branch reads through the two
`listReplaceAt` atoms at the off-position (`listGetWithDefaultReplaceAtNe` twice).  The off-both mirror of
`swapRowsEntryAtFirst`; covers the move's row swap at a low read row. -/
theorem swapRowsPreservesEntryOffBothRows (matrix : IntMatrix)
    (firstIndex secondIndex readRow colIndex : Nat)
    (isOffFirst : readRow ≠ firstIndex) (isOffSecond : readRow ≠ secondIndex) :
    (matrix.swapRows firstIndex secondIndex).entryAt readRow colIndex
      = matrix.entryAt readRow colIndex := by
  have rowEq :
      listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows readRow
        = listGetWithDefault [] matrix.rows readRow := by
    unfold IntMatrix.swapRows
    split
    · split
      · show listGetWithDefault []
            (listReplaceAt (listReplaceAt matrix.rows firstIndex
                (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
              (listGetWithDefault [] matrix.rows firstIndex)) readRow
          = listGetWithDefault [] matrix.rows readRow
        rw [listGetWithDefaultReplaceAtNe [] _ secondIndex readRow _ isOffSecond,
            listGetWithDefaultReplaceAtNe [] matrix.rows firstIndex readRow _ isOffFirst]
      · rfl
    · rfl
  show listGetWithDefault 0
      (listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows readRow) colIndex
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows readRow) colIndex
  rw [rowEq]

/-- **Within-row swap preserves an entry off BOTH swapped positions** — the entry-level off-both mirror of
`swapEntriesWithinRowAtFirst`: reading position `readCol` after `swapEntriesWithinRow row firstIndex
secondIndex` is unchanged when `readCol` is neither swapped index.  Two `listGetWithDefaultReplaceAtNe`
through the range guards. -/
theorem swapEntriesWithinRowPreservesEntryOffBoth (row : IntRow)
    (firstIndex secondIndex readCol : Nat)
    (isOffFirst : readCol ≠ firstIndex) (isOffSecond : readCol ≠ secondIndex) :
    listGetWithDefault 0 (swapEntriesWithinRow row firstIndex secondIndex) readCol
      = listGetWithDefault 0 row readCol := by
  unfold IntMatrix.swapEntriesWithinRow
  split
  · split
    · show listGetWithDefault 0
          (listReplaceAt (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
            (listGetWithDefault 0 row firstIndex)) readCol
        = listGetWithDefault 0 row readCol
      rw [listGetWithDefaultReplaceAtNe 0 _ secondIndex readCol _ isOffSecond,
          listGetWithDefaultReplaceAtNe 0 row firstIndex readCol _ isOffFirst]
    · rfl
  · rfl

/-- **Swap preserves an entry off BOTH swapped columns** — the column off-both mirror of
`swapColumnsEntryAtFirst`: reading column `readCol` of an in-range row `rowIndex` after `swapColumns
firstIndex secondIndex` is unchanged when `readCol` is neither swapped index.  Needs rectangularity only
for the mapped-row read (`listGetWithDefaultMapAllRows`); the within-row off-both preserver needs no
column-in-range (identity past the end).  Covers the move's column swap at a low read column. -/
theorem swapColumnsPreservesEntryOffBothCols {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (firstIndex secondIndex rowIndex readCol : Nat)
    (isRowInRange : rowIndex < height)
    (isOffFirst : readCol ≠ firstIndex) (isOffSecond : readCol ≠ secondIndex) :
    (matrix.swapColumns firstIndex secondIndex).entryAt rowIndex readCol
      = matrix.entryAt rowIndex readCol := by
  obtain ⟨rowCount, _⟩ := isRect
  have rowInRows : rowIndex < matrix.rows.length :=
    Eq.mp (congrArg (rowIndex < ·) rowCount.symm) isRowInRange
  show listGetWithDefault 0 (listGetWithDefault []
      (mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex) matrix.rows) rowIndex)
      readCol
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) readCol
  rw [listGetWithDefaultMapAllRows _ matrix.rows rowIndex rowInRows]
  exact swapEntriesWithinRowPreservesEntryOffBoth (listGetWithDefault [] matrix.rows rowIndex)
    firstIndex secondIndex readCol isOffFirst isOffSecond

/-- **The move word preserves a low-low entry** — after `smithMoveToPivotOps pivotIndex foundRow foundCol`
(swap the found row into the pivot row, then the found column into the pivot column) a low-low cell
`(readRow, readCol)` with `readRow < pivotIndex ∧ readCol < pivotIndex` is unchanged, PROVIDED the found
position sits in the pivot window (`pivotIndex ≤ foundRow`, `pivotIndex ≤ foundCol` — the r10
`smithFindMinAbsInMinorFoundInRange` dependency).  The column swap leaves `readCol` fixed (neither
`pivotIndex` nor `foundCol`, both `> readCol`) via `swapColumnsPreservesEntryOffBothCols` on the
rect-preserved `afterMove`; the row swap leaves `readRow` fixed (neither `pivotIndex` nor `foundRow`) via
`swapRowsPreservesEntryOffBothRows`.  Mirrors the threading of `smithMoveToPivotEntryOnPivot`. -/
theorem smithMoveToPivotOpsPreservesLowLowEntry {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex foundRow foundCol readRow readCol : Nat)
    (readRowLtPivot : readRow < pivotIndex) (readColLtPivot : readCol < pivotIndex)
    (pivotLeFoundRow : pivotIndex ≤ foundRow) (pivotLeFoundCol : pivotIndex ≤ foundCol)
    (readRowInRange : readRow < height) :
    (matrix.applyOperations (smithMoveToPivotOps pivotIndex foundRow foundCol)).entryAt readRow readCol
      = matrix.entryAt readRow readCol := by
  have swapRowRect : (matrix.swapRows pivotIndex foundRow).IsRectangular height width :=
    applyRowOperationPreservesRectangular (ElementaryRowOperation.swapRows pivotIndex foundRow) matrix
      isRect
  show ((matrix.swapRows pivotIndex foundRow).swapColumns pivotIndex foundCol).entryAt readRow readCol
    = matrix.entryAt readRow readCol
  rw [swapColumnsPreservesEntryOffBothCols (matrix.swapRows pivotIndex foundRow) swapRowRect
      pivotIndex foundCol readRow readCol readRowInRange
      (Nat.ne_of_lt readColLtPivot)
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le readColLtPivot pivotLeFoundCol))]
  exact swapRowsPreservesEntryOffBothRows matrix pivotIndex foundRow readRow readCol
    (Nat.ne_of_lt readRowLtPivot)
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le readRowLtPivot pivotLeFoundRow))

/-- **The cascade preserves a low-low entry within its fuel** (H2-SMITH r11, B1 keystone) — for a
rectangular matrix with the pivot in range, `smithCascadeSweep fuel` leaves every settled-prefix cell
`(readRow, readCol)` with `readRow < pivotIndex ∧ readCol < pivotIndex` UNCHANGED.  Structural induction
on `fuel`, the entry-preservation mirror of `smithCascadeReachesCrossClear`.

  * **Base (`fuel = 0`)** and **step `none`**: the sweep is empty, the cell is trivially fixed.
  * **Step `some (foundRow, foundCol)`**: split the settle word `moveOps ++ signOps ++ columnClearOps ++
    rowClearOps` via `applyOperationsAppend`; the cell survives the move (off-both swaps, the found
    position pinned `≥ pivotIndex` by `smithFindMinAbsInMinorFoundInRange`), the sign (off-pivot row,
    `readRow ≠ pivotIndex`), the column clear (top row `readRow < pivotIndex + 1`), and the row clear
    (left column `readCol < pivotIndex + 1`).  Cross clear ⟹ the settle word is the whole sweep; NOT clear
    ⟹ the recursive tail on `afterRowClear` closes by IH (the pivot is loop-invariant), then chains with
    the settle preservation.

A function-correctness fact about the definite cascade word — immune to the r5/r6 refuted-pole shape (it
asserts entries stay UNCHANGED, never a re-diagonalization over arbitrary window-diagonal inputs).  It is
the settled-prefix monotonicity feeding the outer INV-DIAG induction — but delivers ONLY the prefix
conjunct of `repairWindowDiagHolds` (the bands + sub-block stay POLE-A-walled). -/
theorem smithCascadeSweepPreservesLowLowEntry :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width readRow readCol : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      readRow < pivotIndex → readCol < pivotIndex →
      (matrix.applyOperations (smithCascadeSweep fuel matrix pivotIndex height width)).entryAt readRow readCol
        = matrix.entryAt readRow readCol := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width readRow readCol _ _ _ _ _
      rfl
  | succ fuel ih =>
      intro matrix pivotIndex height width readRow readCol isRect pivotRowInRange pivotColInRange
        readRowLtPivot readColLtPivot
      have readRowInRange : readRow < height := Nat.lt_trans readRowLtPivot pivotRowInRange
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          rfl
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
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
          have afterMoveRect : afterMove.IsRectangular height width :=
            applyOperationsPreservesRectangular moveOps matrix isRect
          have afterSignRect : afterSign.IsRectangular height width :=
            applyOperationsPreservesRectangular signOps afterMove afterMoveRect
          have afterColumnClearRect : afterColumnClear.IsRectangular height width :=
            applyOperationsPreservesRectangular columnClearOps afterSign afterSignRect
          have afterRowClearRect : afterRowClear.IsRectangular height width :=
            applyOperationsPreservesRectangular rowClearOps afterColumnClear afterColumnClearRect
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pivotRowInRange pivotColInRange hFind
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          have afterRowClearPreserves :
              afterRowClear.entryAt readRow readCol = matrix.entryAt readRow readCol :=
            (smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width readRow
                readCol readRowInRange (width - (pivotIndex + 1)) (pivotIndex + 1) afterColumnClear
                afterColumnClearRect (Nat.lt_trans readColLtPivot (Nat.lt_succ_self pivotIndex))).trans
              ((smithClearColumnBelowStepsPreservesRow afterSign pivotIndex readRow readCol
                  (height - (pivotIndex + 1)) (pivotIndex + 1) afterSign
                  (Nat.lt_trans readRowLtPivot (Nat.lt_succ_self pivotIndex))).trans
                ((signNormalizeOpsPreserveEntryOffPivot afterMove pivotIndex readRow readCol
                    (Nat.ne_of_lt readRowLtPivot)).trans
                  (smithMoveToPivotOpsPreservesLowLowEntry matrix isRect pivotIndex foundRow foundCol
                    readRow readCol readRowLtPivot readColLtPivot foundInRange.1 foundInRange.2.2.1
                    readRowInRange)))
          have settledPreserves :
              (matrix.applyOperations settledOps).entryAt readRow readCol
                = matrix.entryAt readRow readCol :=
            (congrArg (fun reducedMatrix => reducedMatrix.entryAt readRow readCol) hApplySettled).trans
              afterRowClearPreserves
          have hSweep : smithCascadeSweep (fuel + 1) matrix pivotIndex height width
              = (match smithCrossIsClear afterRowClear pivotIndex height width with
                 | true => settledOps
                 | false => settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width) := by
            rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          rw [hSweep]
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true => exact settledPreserves
          | false =>
              rw [applyOperationsAppend, hApplySettled]
              exact (ih afterRowClear pivotIndex height width readRow readCol afterRowClearRect
                pivotRowInRange pivotColInRange readRowLtPivot readColLtPivot).trans
                afterRowClearPreserves

/-! ## The fold transport up the driver stack (H2-SMITH r11, B2) — low-low across the sweeps

The keystone is discharged at the STATIC seed fuel `smithMinorAbsSum` the driver actually seeds the
cascade with (the driver-path form, mirror of `smithCascadeSweepSeedReachesCrossClear`), then lifted
through the three per-pivot sweeps of the augmented driver:

  * `smithReduceTotalSweep` (the cross-clear phase `diagOps`) — per pivot a seed cascade;
  * `smithRepairPositionSweep` (the per-position divisibility fold loop) — per iteration an
    `addRowMultiple foundPos pivotIndex 1` fold (target row `pivotIndex`, off a low read row) then a seed
    cascade;
  * `smithDivisibilityRepairSweep` (the top-down repair phase `repairOps`) — per pivot a position sweep.

Each transport is structural on its fuel: a cell below the STARTING pivot survives every op the sweep
fires (the fold's target row is the pivot, the cascade preserves low-low), and stays below the advanced
pivot for the recursion.  The genuine "fold transport" the task's B2 asks for — refutation-immune
function-correctness facts about the definite driver words. -/

/-- **`Nat.min` sits below its right argument** — the propext-clean right companion of `natMinLeLeft`
(Init's `Nat.min_le_right` is propext-dirty): case the `if`-defined `Nat.min` guard, close by the guard
hypothesis (min = left ≤ right) or reflexivity (min = right). -/
theorem natMinLeRight (leftValue rightValue : Nat) :
    Nat.min leftValue rightValue ≤ rightValue := by
  show (if leftValue ≤ rightValue then leftValue else rightValue) ≤ rightValue
  cases Nat.decLe leftValue rightValue with
  | isTrue isLe =>
      rw [if_pos isLe]
      exact isLe
  | isFalse isNotLe =>
      rw [if_neg isNotLe]
      exact Nat.le.refl

/-- **The cascade at its ACTUAL seed fuel preserves a low-low entry** (driver-path form) — the keystone
`smithCascadeSweepPreservesLowLowEntry` discharged at `smithMinorAbsSum matrix pivotIndex height width`,
the static fuel the total driver and the repair seed the cascade with.  The direct low-low twin of
`smithCascadeSweepSeedReachesCrossClear`. -/
theorem smithCascadeSweepSeedPreservesLowLowEntry (matrix : IntMatrix)
    (pivotIndex height width readRow readCol : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (readRowLtPivot : readRow < pivotIndex) (readColLtPivot : readCol < pivotIndex) :
    (matrix.applyOperations
        (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width)).entryAt readRow readCol
      = matrix.entryAt readRow readCol :=
  smithCascadeSweepPreservesLowLowEntry (smithMinorAbsSum matrix pivotIndex height width) matrix
    pivotIndex height width readRow readCol isRect pivotRowInRange pivotColInRange readRowLtPivot
    readColLtPivot

/-- **The cross-clear total sweep preserves a low-low entry** — `smithReduceTotalSweep` leaves every cell
`(readRow, readCol)` strictly below its STARTING pivot unchanged.  Structural on the outer (pivot-budget)
fuel: the seed cascade at the current pivot preserves the cell (`smithCascadeSweepSeedPreservesLowLowEntry`,
pivot-in-range from the `pivotIndex + 1 ≤ min` guard), and the cell stays below the advanced pivot for the
recursion. -/
theorem smithReduceTotalSweepPreservesLowLowEntry :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width readRow readCol : Nat),
      matrix.IsRectangular height width →
      readRow < pivotIndex → readCol < pivotIndex →
      (matrix.applyOperations
          (smithReduceTotalSweep outerFuel matrix pivotIndex height width)).entryAt readRow readCol
        = matrix.entryAt readRow readCol := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width readRow readCol _ _ _
      rfl
  | succ outerFuel ih =>
      intro matrix pivotIndex height width readRow readCol isRect readRowLtPivot readColLtPivot
      show (matrix.applyOperations
          (if pivotIndex + 1 ≤ Nat.min height width then
            smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
              ++ smithReduceTotalSweep outerFuel
                  (matrix.applyOperations
                    (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                      height width))
                  (pivotIndex + 1) height width
           else [])).entryAt readRow readCol = matrix.entryAt readRow readCol
      split
      · rename_i hCond
        rw [applyOperationsAppend]
        have pivotRowInRange : pivotIndex < height := natLeTrans hCond (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans hCond (natMinLeRight height width)
        have seedPreserves :
            (matrix.applyOperations
                (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width)).entryAt readRow readCol
              = matrix.entryAt readRow readCol :=
          smithCascadeSweepSeedPreservesLowLowEntry matrix pivotIndex height width readRow readCol isRect
            pivotRowInRange pivotColInRange readRowLtPivot readColLtPivot
        have afterPivotRect :
            (matrix.applyOperations
                (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        exact (ih
            (matrix.applyOperations
              (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                height width))
            (pivotIndex + 1) height width readRow readCol afterPivotRect
            (Nat.lt_trans readRowLtPivot (Nat.lt_succ_self pivotIndex))
            (Nat.lt_trans readColLtPivot (Nat.lt_succ_self pivotIndex))).trans seedPreserves
      · rfl

/-- **`smithRepairPositionSweep` at successor fuel unfolds to its match body** — the definitional
unfolding of the structural recursion at `fuel + 1`, exposed as a rewrite target (`rfl`).  The
repair-loop analogue of `smithCascadeSweepSucc`. -/
theorem smithRepairPositionSweepSucc (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat) :
    smithRepairPositionSweep (fuel + 1) matrix pivotIndex height width
      = (match smithFindNonDividingLaterDiagonal matrix pivotIndex
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
             foldOps ++ clearOps ++ smithRepairPositionSweep fuel afterClear pivotIndex height width) :=
  rfl

/-- **The per-position divisibility repair preserves a low-low entry** — `smithRepairPositionSweep` leaves
every cell `(readRow, readCol)` strictly below its pivot unchanged.  Structural on the repair fuel: the
fold `addRowMultiple foundPos pivotIndex 1` targets row `pivotIndex` (off the low read row `readRow ≠
pivotIndex`, via `addRowMultiplePreservesEntryOffTargetRow`), the re-fired seed cascade preserves low-low,
and the loop stays at the SAME pivot so the IH applies verbatim.  Needs the pivot in range for the cascade
seed (supplied by the outer sweep's guard). -/
theorem smithRepairPositionSweepPreservesLowLowEntry :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width readRow readCol : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      readRow < pivotIndex → readCol < pivotIndex →
      (matrix.applyOperations
          (smithRepairPositionSweep fuel matrix pivotIndex height width)).entryAt readRow readCol
        = matrix.entryAt readRow readCol := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width readRow readCol _ _ _ _ _
      rfl
  | succ fuel ih =>
      intro matrix pivotIndex height width readRow readCol isRect pivotRowInRange pivotColInRange
        readRowLtPivot readColLtPivot
      cases hFind : smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) with
      | none =>
          rw [smithRepairPositionSweepSucc fuel matrix pivotIndex height width, hFind]
          rfl
      | some foundPos =>
          let foldOps :=
            [ ElementaryOperation.rowOperation
                (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ]
          let afterFold := matrix.applyOperations foldOps
          let clearOps :=
            smithCascadeSweep (smithMinorAbsSum afterFold pivotIndex height width)
              afterFold pivotIndex height width
          let afterClear := afterFold.applyOperations clearOps
          have afterFoldRect : afterFold.IsRectangular height width :=
            applyOperationsPreservesRectangular foldOps matrix isRect
          have afterClearRect : afterClear.IsRectangular height width :=
            applyOperationsPreservesRectangular clearOps afterFold afterFoldRect
          have foldPreserves : afterFold.entryAt readRow readCol = matrix.entryAt readRow readCol :=
            addRowMultiplePreservesEntryOffTargetRow matrix foundPos pivotIndex 1 readRow readCol
              (Nat.ne_of_lt readRowLtPivot)
          have clearPreserves : afterClear.entryAt readRow readCol = afterFold.entryAt readRow readCol :=
            smithCascadeSweepSeedPreservesLowLowEntry afterFold pivotIndex height width readRow readCol
              afterFoldRect pivotRowInRange pivotColInRange readRowLtPivot readColLtPivot
          have hUnfold : smithRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = foldOps ++ clearOps ++ smithRepairPositionSweep fuel afterClear pivotIndex height width := by
            rw [smithRepairPositionSweepSucc fuel matrix pivotIndex height width, hFind]
          rw [hUnfold, applyOperationsAppend, applyOperationsAppend]
          exact (ih afterClear pivotIndex height width readRow readCol afterClearRect pivotRowInRange
            pivotColInRange readRowLtPivot readColLtPivot).trans (clearPreserves.trans foldPreserves)

/-- **The top-down divisibility-repair sweep preserves a low-low entry** — `smithDivisibilityRepairSweep`
leaves every cell `(readRow, readCol)` strictly below its STARTING pivot unchanged.  Structural on the
outer fuel: the per-position repair at the current pivot preserves the cell
(`smithRepairPositionSweepPreservesLowLowEntry`, pivot-in-range from the guard), and the cell stays below
the advanced pivot for the recursion.  At the driver's top-level start `pivotIndex = 0` this is VACUOUS
(no cell below `0`) — the honest gap the recon flags: `repairWindowDiagHolds` demands the WHOLE window
off-diagonal-zero, and its sub-block + bands are POLE-A-walled, not settled-prefix monotonicity. -/
theorem smithDivisibilityRepairSweepPreservesLowLowEntry :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width readRow readCol : Nat),
      matrix.IsRectangular height width →
      readRow < pivotIndex → readCol < pivotIndex →
      (matrix.applyOperations
          (smithDivisibilityRepairSweep outerFuel matrix pivotIndex height width)).entryAt readRow readCol
        = matrix.entryAt readRow readCol := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width readRow readCol _ _ _
      rfl
  | succ outerFuel ih =>
      intro matrix pivotIndex height width readRow readCol isRect readRowLtPivot readColLtPivot
      show (matrix.applyOperations
          (if pivotIndex + 1 ≤ Nat.min height width then
            smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                height width
              ++ smithDivisibilityRepairSweep outerFuel
                  (matrix.applyOperations
                    (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix
                      pivotIndex height width))
                  (pivotIndex + 1) height width
           else [])).entryAt readRow readCol = matrix.entryAt readRow readCol
      split
      · rename_i hCond
        rw [applyOperationsAppend]
        have pivotRowInRange : pivotIndex < height := natLeTrans hCond (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans hCond (natMinLeRight height width)
        have positionPreserves :
            (matrix.applyOperations
                (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix
                  pivotIndex height width)).entryAt readRow readCol
              = matrix.entryAt readRow readCol :=
          smithRepairPositionSweepPreservesLowLowEntry (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width readRow readCol isRect pivotRowInRange pivotColInRange
            readRowLtPivot readColLtPivot
        have afterPositionRect :
            (matrix.applyOperations
                (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix
                  pivotIndex height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        exact (ih
            (matrix.applyOperations
              (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                height width))
            (pivotIndex + 1) height width readRow readCol afterPositionRect
            (Nat.lt_trans readRowLtPivot (Nat.lt_succ_self pivotIndex))
            (Nat.lt_trans readColLtPivot (Nat.lt_succ_self pivotIndex))).trans positionPreserves
      · rfl

/-! ## The sub-block postcondition + the named walls (H2-SMITH r11, B3) — the prefix conjunct only

`SmithNormalForm`'s `repairWindowDiagHolds` demands `IsWindowDiagonal (repair ∘ reduceTotal) 0 height
width` — EVERY off-diagonal cell of the window zero.  Partition the window by the pivot `p` being
processed (the recon gap audit):

  | region                              | who clears it                                              |
  | ----------------------------------- | ---------------------------------------------------------- |
  | **prefix** `r < p ∧ c < p`          | ✅ **r11 (below)** — pure low-low locality monotonicity     |
  | **cross strip at `p`**              | ✅ r10 `smithCascadeSweepSeedReachesCrossClear`             |
  | **below-left band** `r ≥ p ∧ c < p` | ❌ NOT locality — a row op touches `(r ≥ p, c < p)`; needs   |
  |                                     |    the INV-DIAG-fed "reads-only-zeros" argument (r7 driver-path reachability) |
  | **above-right band** `r < p ∧ c ≥ p`| ❌ NOT locality — mirror of the below-left band             |
  | **sub-block** `[p+1,·) × [p+1,·)`   | ❌ **POLE-A** — the cascade must RE-DIAGONALIZE the folded   |
  |                                     |    sub-block; refuted as a standalone pole (`SmithCascadeReDiagonalizesPostFoldStatement`), correct only along the min-abs-presorted driver path |

r11 delivers the **prefix conjunct ONLY**.  The two corollaries below transport the settled-prefix
off-diagonal ZEROS through the seed cascade and through the whole divisibility-repair sweep — the
"settled prefix stays settled" monotonicity the outer INV-DIAG induction consumes.  They do NOT close
`repairWindowDiagHolds` (the bands + sub-block are the named walls) nor `repairChainHolds` (the
invariant-factor gcd-chain — a SEPARATE POLE-A conjunct, its own later round).
`SmithReduceFullDriverStatement` stays uninhabited; NO flip. -/

/-- **Concrete truth probe for the prefix-off-diagonal transport** — on the `4 × 4`
`[[3,0,0,0],[0,4,0,0],[0,0,5,6],[0,0,7,4]]` (top-left `2 × 2` diagonal, so the prefix `[0, 2)²`
off-diagonal `(0, 1)`/`(1, 0)` is already zero) the seed cascade at pivot `2` FIRES a genuine 8-letter
word on the nonzero sub-minor `[[5, 6], [7, 4]]`, yet the prefix off-diagonal cell `(0, 1)` stays `0`.
Anonymous, so it carries no axiom footprint. -/
example :
    (({ rows := [[3,0,0,0],[0,4,0,0],[0,0,5,6],[0,0,7,4]] } : IntMatrix).applyOperations
        (smithCascadeSweep
          (smithMinorAbsSum ({ rows := [[3,0,0,0],[0,4,0,0],[0,0,5,6],[0,0,7,4]] } : IntMatrix) 2 4 4)
          ({ rows := [[3,0,0,0],[0,4,0,0],[0,0,5,6],[0,0,7,4]] } : IntMatrix) 2 4 4)).entryAt 0 1 = 0 := by
  decide

/-- **The seed cascade preserves the settled prefix's off-diagonal zeros** — if the prefix
`[0, pivotIndex) × [0, pivotIndex)` off-diagonal is zero on input, it stays zero after the seed cascade at
`pivotIndex`.  Each prefix cell is low-low (`< pivotIndex` in both coordinates), so
`smithCascadeSweepSeedPreservesLowLowEntry` freezes it at its zero input value.  The PREFIX conjunct of the
cascade's driver-path window postcondition — the bands + sub-block are the named walls above. -/
theorem smithCascadeSweepSeedPreservesPrefixOffDiagonal (matrix : IntMatrix)
    (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (prefixOffDiagZero : ∀ rowIndex colIndex, rowIndex < pivotIndex → colIndex < pivotIndex →
      rowIndex ≠ colIndex → matrix.entryAt rowIndex colIndex = 0) :
    ∀ rowIndex colIndex, rowIndex < pivotIndex → colIndex < pivotIndex → rowIndex ≠ colIndex →
      (matrix.applyOperations
          (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).entryAt rowIndex colIndex = 0 :=
  fun rowIndex colIndex rowLtPivot colLtPivot rowNeCol =>
    (smithCascadeSweepSeedPreservesLowLowEntry matrix pivotIndex height width rowIndex colIndex isRect
        pivotRowInRange pivotColInRange rowLtPivot colLtPivot).trans
      (prefixOffDiagZero rowIndex colIndex rowLtPivot colLtPivot rowNeCol)

/-- **The divisibility-repair sweep preserves the settled prefix's off-diagonal zeros** — if the prefix
`[0, pivotIndex) × [0, pivotIndex)` off-diagonal is zero on input, it stays zero after the whole
`smithDivisibilityRepairSweep` starting at `pivotIndex`.  Each prefix cell is low-low, frozen by
`smithDivisibilityRepairSweepPreservesLowLowEntry`.  At the driver's top-level start `pivotIndex = 0` this
is VACUOUS — the honest gap: `repairWindowDiagHolds` at window-start `0` demands the WHOLE window
(sub-block + bands POLE-A-walled), which settled-prefix monotonicity does not reach.  This is the outer
INV-DIAG induction's "prefix stays settled" STEP, not a discharge of the obligation. -/
theorem smithDivisibilityRepairSweepPreservesPrefixOffDiagonal (outerFuel : Nat) (matrix : IntMatrix)
    (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (prefixOffDiagZero : ∀ rowIndex colIndex, rowIndex < pivotIndex → colIndex < pivotIndex →
      rowIndex ≠ colIndex → matrix.entryAt rowIndex colIndex = 0) :
    ∀ rowIndex colIndex, rowIndex < pivotIndex → colIndex < pivotIndex → rowIndex ≠ colIndex →
      (matrix.applyOperations
          (smithDivisibilityRepairSweep outerFuel matrix pivotIndex height width)).entryAt rowIndex colIndex
        = 0 :=
  fun rowIndex colIndex rowLtPivot colLtPivot rowNeCol =>
    (smithDivisibilityRepairSweepPreservesLowLowEntry outerFuel matrix pivotIndex height width rowIndex
        colIndex isRect rowLtPivot colLtPivot).trans
      (prefixOffDiagZero rowIndex colIndex rowLtPivot colLtPivot rowNeCol)

/-! ## The band-zero re-expression + the settled-through-`p` frame (H2-SMITH r12, B1) — POLE-A driver path

r11 closed the PREFIX conjunct (`r < p ∧ c < p`) of the driver's window-diagonal postcondition by pure
low-low locality.  r12 opens the TWO BANDS around the remaining sub-block — the below-left `r ≥ p ∧ c < p`
and above-right `r < p ∧ c ≥ p` — via the joint zero-propagation argument: the `p+1` cascade ops carry the
settled band's zeros forward because the added multiples are of zero entries and the move-swap only permutes
zero entries among themselves.  The clean carrier is the SETTLED FRAME around the sub-block: everything
outside `[p, ·) × [p, ·)` is off-diagonal-zero.  This section re-expresses cross-clear as pointwise band
zeros (the `= true → pointwise` forward decode the r9 reverse `…OfPointwiseZero` never shipped) and states
`SmithPrefixSettled`, the decidable settled-frame predicate the single-step advances from `p` to `p+1`.

Every atom is a FUNCTION-CORRECTNESS fact about a definite word / flag on ONE matrix under `IsRectangular`
+ pivot-in-range — refutation-immune, NEVER a re-diagonalization claim over arbitrary window-diagonal inputs
(the r5/r6 refuted-pole shape).  The bands are the genuinely NEW content; the sub-block stays POLE-A-walled
(`SmithReduceFullDriverStatement` uninhabited; no flip). -/

/-- **Concrete truth probe for the band-zero re-expression** — on the settled `diag(3, 5, 7)` the pivot-`0`
cross is clear (`smithCrossIsClear = true`) and its cross/band cell `(0, 2)` reads `0`, so the forward
`= true → pointwise` decode `smithCrossIsClearPointwise` is non-vacuous on a genuine staged matrix.
Anonymous, so it carries no axiom footprint. -/
example : smithCrossIsClear ({ rows := [[3, 0, 0], [0, 5, 0], [0, 0, 7]] } : IntMatrix) 0 3 3 = true := by
  decide

example : ({ rows := [[3, 0, 0], [0, 5, 0], [0, 0, 7]] } : IntMatrix).entryAt 0 2 = 0 := by decide

/-- **`m == 0` decodes to `m = 0`** — the `true`-direction converse of the shipped `natBeqZeroFalseOfNe`:
the zero arm is `rfl`, the successor arm collapses `(succ _ == 0) = false` against the `true` hypothesis by
`Bool.noConfusion`.  Feeds the segment forward decode. -/
theorem natEqZeroOfBeqZeroTrue : ∀ magnitude : Nat, (magnitude == 0) = true → magnitude = 0
  | 0, _ => rfl
  | _ + 1, beqTrue => Bool.noConfusion beqTrue

/-- **Zero magnitude forces the integer zero** — `value.natAbs = 0 → value = 0`, structural on the `Int`
constructors: `ofNat 0` is `rfl`, and both `ofNat (m+1)` and `negSucc m` have magnitude `m+1`, refuted
against the `= 0` hypothesis by `Nat.noConfusion`.  Converts the segment's magnitude-zero decode to an
entry-zero fact (the band lemmas need the entry, not just its magnitude). -/
theorem intOfNatAbsZero : ∀ value : Int, value.natAbs = 0 → value = 0
  | .ofNat 0, _ => rfl
  | .ofNat (_ + 1), natAbsZero => Nat.noConfusion natAbsZero
  | .negSucc _, natAbsZero => Nat.noConfusion natAbsZero

/-- **Row segment all-zero decodes to pointwise zero** — the forward `= true → ∀ entry = 0` converse of the
shipped `smithRowSegmentAllZeroOfPointwiseZero`.  Structural on the column count: the head `== 0` guard
splits `false` (contradicts the `&&`-`true` hypothesis by `Bool.noConfusion`) versus `true` (the head entry
is zero by `natEqZeroOfBeqZeroTrue` + `intOfNatAbsZero`; the tail rides the IH).  The band-zero
re-expression of a cleared row segment. -/
theorem smithRowSegmentAllZeroPointwise (matrix : IntMatrix) (rowIndex : Nat) :
    ∀ (colCount colStart : Nat),
      smithRowSegmentAllZero matrix rowIndex colCount colStart = true →
      ∀ col, colStart ≤ col → col < colStart + colCount →
        matrix.entryAt rowIndex col = 0 := by
  intro colCount
  induction colCount with
  | zero =>
      intro colStart _ col colGe colLt
      exact absurd
        (Nat.lt_of_lt_of_le (Eq.mp (congrArg (col < ·) (Nat.add_zero colStart)) colLt) colGe)
        (Nat.lt_irrefl col)
  | succ colCount ih =>
      intro colStart segTrue col colGe colLt
      have segUnfold :
          (((matrix.entryAt rowIndex colStart).natAbs == 0) &&
            smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1)) = true := segTrue
      cases hGuard : (matrix.entryAt rowIndex colStart).natAbs == 0 with
      | false =>
          rw [hGuard] at segUnfold
          exact Bool.noConfusion segUnfold
      | true =>
          rw [hGuard] at segUnfold
          have restTrue : smithRowSegmentAllZero matrix rowIndex colCount (colStart + 1) = true := segUnfold
          cases Nat.eq_or_lt_of_le colGe with
          | inl colStartEqCol =>
              exact intOfNatAbsZero (matrix.entryAt rowIndex col)
                ((congrArg (fun position => (matrix.entryAt rowIndex position).natAbs) colStartEqCol).symm.trans
                  (natEqZeroOfBeqZeroTrue _ hGuard))
          | inr colStartLtCol =>
              exact ih (colStart + 1) restTrue col colStartLtCol
                (Eq.mp (congrArg (col < ·) (Nat.succ_add colStart colCount).symm) colLt)

/-- **Column segment all-zero decodes to pointwise zero** — the row mirror of
`smithRowSegmentAllZeroPointwise`, over `smithColSegmentAllZero`. -/
theorem smithColSegmentAllZeroPointwise (matrix : IntMatrix) (colIndex : Nat) :
    ∀ (rowCount rowStart : Nat),
      smithColSegmentAllZero matrix colIndex rowCount rowStart = true →
      ∀ row, rowStart ≤ row → row < rowStart + rowCount →
        matrix.entryAt row colIndex = 0 := by
  intro rowCount
  induction rowCount with
  | zero =>
      intro rowStart _ row rowGe rowLt
      exact absurd
        (Nat.lt_of_lt_of_le (Eq.mp (congrArg (row < ·) (Nat.add_zero rowStart)) rowLt) rowGe)
        (Nat.lt_irrefl row)
  | succ rowCount ih =>
      intro rowStart segTrue row rowGe rowLt
      have segUnfold :
          (((matrix.entryAt rowStart colIndex).natAbs == 0) &&
            smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1)) = true := segTrue
      cases hGuard : (matrix.entryAt rowStart colIndex).natAbs == 0 with
      | false =>
          rw [hGuard] at segUnfold
          exact Bool.noConfusion segUnfold
      | true =>
          rw [hGuard] at segUnfold
          have restTrue : smithColSegmentAllZero matrix colIndex rowCount (rowStart + 1) = true := segUnfold
          cases Nat.eq_or_lt_of_le rowGe with
          | inl rowStartEqRow =>
              exact intOfNatAbsZero (matrix.entryAt row colIndex)
                ((congrArg (fun position => (matrix.entryAt position colIndex).natAbs) rowStartEqRow).symm.trans
                  (natEqZeroOfBeqZeroTrue _ hGuard))
          | inr rowStartLtRow =>
              exact ih (rowStart + 1) restTrue row rowStartLtRow
                (Eq.mp (congrArg (row < ·) (Nat.succ_add rowStart rowCount).symm) rowLt)

/-- **Cross-clear re-expressed as pointwise band zeros** — `smithCrossIsClear = true` splits (structural
`&&` case) into: row `pivotIndex` is zero across columns `(pivotIndex, width)` AND column `pivotIndex` is
zero across rows `(pivotIndex, height)`.  The forward decode feeding the single-step's two cross-strip
regions, riding `smithRowSegmentAllZeroPointwise` / `smithColSegmentAllZeroPointwise` through the window
bridge `smithNatAddSubOfLe`.  (`pivotIndex < col` is `pivotIndex + 1 ≤ col` definitionally — the segment
window's lower bound.) -/
theorem smithCrossIsClearPointwise (matrix : IntMatrix) (pivotIndex height width : Nat)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (crossClear : smithCrossIsClear matrix pivotIndex height width = true) :
    (∀ col, pivotIndex < col → col < width → matrix.entryAt pivotIndex col = 0) ∧
      (∀ row, pivotIndex < row → row < height → matrix.entryAt row pivotIndex = 0) := by
  have crossUnfold :
      (smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) &&
        smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)) = true :=
    crossClear
  cases hRow : smithRowSegmentAllZero matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1) with
  | false =>
      rw [hRow] at crossUnfold
      exact Bool.noConfusion crossUnfold
  | true =>
      rw [hRow] at crossUnfold
      have colTrue :
          smithColSegmentAllZero matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1) = true :=
        crossUnfold
      refine ⟨fun col pivotLtCol colLtWidth => ?_, fun row pivotLtRow rowLtHeight => ?_⟩
      · exact smithRowSegmentAllZeroPointwise matrix pivotIndex (width - (pivotIndex + 1)) (pivotIndex + 1)
          hRow col pivotLtCol
          (Eq.mp (congrArg (col < ·) (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange).symm)
            colLtWidth)
      · exact smithColSegmentAllZeroPointwise matrix pivotIndex (height - (pivotIndex + 1)) (pivotIndex + 1)
          colTrue row pivotLtRow
          (Eq.mp (congrArg (row < ·) (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange).symm)
            rowLtHeight)

/-- **The settled-through-`pivotIndex` frame** — every off-diagonal cell OUTSIDE the remaining sub-block
`[pivotIndex, ·) × [pivotIndex, ·)` is zero: the prefix `r < p ∧ c < p` plus the two bands
(`r ≥ p ∧ c < p`, `r < p ∧ c ≥ p`), captured uniformly by the disjunct `rowIndex < pivotIndex ∨ colIndex <
pivotIndex`.  `SmithPrefixSettled matrix 0 …` is VACUOUS (the base) and `SmithPrefixSettled matrix (Nat.min
height width) height width` IS the full window-diagonal (`smithPrefixSettledAtMinIsWindowDiagonal`) — the
terminal frame `repairWindowDiagHolds` demands.  The single-step advances this frame `p → p+1`; the outer
fold to `min` is the named r13 node. -/
def SmithPrefixSettled (matrix : IntMatrix) (pivotIndex height width : Nat) : Prop :=
  ∀ rowIndex colIndex, rowIndex < height → colIndex < width → rowIndex ≠ colIndex →
    (rowIndex < pivotIndex ∨ colIndex < pivotIndex) →
      matrix.entryAt rowIndex colIndex = 0

/-- **The base frame is vacuous** — `SmithPrefixSettled matrix 0 height width` holds for every matrix: the
disjunct `rowIndex < 0 ∨ colIndex < 0` never fires (`Nat.not_lt_zero`).  The induction's starting point. -/
theorem smithPrefixSettledZero (matrix : IntMatrix) (height width : Nat) :
    SmithPrefixSettled matrix 0 height width :=
  fun _ _ _ _ _ frameHolds =>
    frameHolds.elim (fun rowLt0 => absurd rowLt0 (Nat.not_lt_zero _))
      (fun colLt0 => absurd colLt0 (Nat.not_lt_zero _))

/-- **The frame at `Nat.min` is the full window-diagonal** — `SmithPrefixSettled matrix (Nat.min height
width) height width` gives `IsWindowDiagonal`'s off-diagonal-vanishing over the whole `height × width`
window.  Any in-window off-diagonal `(r, c)` has `r < height` and `c < width`; unfold `Nat.min` to its
`if height ≤ width` and case `Nat.decLe` (the propext-clean route, mirroring `natMinLeLeft`; `Nat.min_eq_*`
leak): the `if`-true branch collapses `min` to `height` so the always-true `r < height` fires the frame
(`Or.inl`), the `if`-false branch collapses it to `width` so `c < width` fires it (`Or.inr`).  The terminal
anchoring the r13 outer fold consumes. -/
theorem smithPrefixSettledAtMinIsWindowDiagonal (matrix : IntMatrix) (height width : Nat)
    (settledAtMin : SmithPrefixSettled matrix (Nat.min height width) height width) :
    ∀ rowIndex colIndex, rowIndex < height → colIndex < width → rowIndex ≠ colIndex →
      matrix.entryAt rowIndex colIndex = 0 :=
  fun rowIndex colIndex rowLtHeight colLtWidth rowNeCol =>
    settledAtMin rowIndex colIndex rowLtHeight colLtWidth rowNeCol (by
      show rowIndex < (if height ≤ width then height else width) ∨
        colIndex < (if height ≤ width then height else width)
      cases Nat.decLe height width with
      | isTrue heightLeWidth =>
          rw [if_pos heightLeWidth]
          exact Or.inl rowLtHeight
      | isFalse heightGtWidth =>
          rw [if_neg heightGtWidth]
          exact Or.inr colLtWidth)

/-! ## The band-preservation lemmas (H2-SMITH r12, B2) — zeros propagate through the `p+1` ops

The two bands survive the cascade's settle word because the added multiples are of ZERO entries and the
move-swap only permutes zero entries among themselves.  This section ships the two NEW keystones — the
above-right ROW band (`lowRow < p`, columns `[p, width)`) and the below-left COLUMN band (`lowCol < p`,
rows `[p, height)`) — as whole-fuel structural inductions carrying the WHOLE-band `∀`-hypothesis (a single
cell is insufficient: the move-swap mixes DISTINCT band cells).  Three small atom groups feed them: the
`…AtSecond` swap readers (the move-swap `c = foundCol` / `r = foundRow` case, mirrors of the shipped
`…AtFirst`), and the zero-source clear preservers (the hard phase — the row-right clear reads the pivot
COLUMN as source, the column-below clear reads the pivot ROW; both are band-zero, so every transvection is a
no-op `old + coeff·0 = old`).

Every atom is a FUNCTION-CORRECTNESS fact about a definite word on ONE matrix under `IsRectangular` +
pivot-in-range — refutation-immune, entries-stay-unchanged, never a re-diagonalization (the sub-block stays
POLE-A-walled). -/

/-- **Within-row swap reads the other entry at the SECOND index** — the `…AtSecond` mirror of
`swapEntriesWithinRowAtFirst`: reading position `secondIndex` after `swapEntriesWithinRow row firstIndex
secondIndex` returns `listGetWithDefault 0 row firstIndex`.  The outer `listReplaceAt` at `secondIndex`
reads its new entry directly (`listGetWithDefaultReplaceAtEq`, no index case-split). -/
theorem swapEntriesWithinRowAtSecond (row : IntRow) (firstIndex secondIndex : Nat)
    (isFirstInRange : firstIndex < row.length) (isSecondInRange : secondIndex < row.length) :
    listGetWithDefault 0 (swapEntriesWithinRow row firstIndex secondIndex) secondIndex
      = listGetWithDefault 0 row firstIndex := by
  unfold IntMatrix.swapEntriesWithinRow
  rw [if_pos isFirstInRange, if_pos isSecondInRange]
  show listGetWithDefault 0
      (listReplaceAt (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
        (listGetWithDefault 0 row firstIndex)) secondIndex
    = listGetWithDefault 0 row firstIndex
  exact listGetWithDefaultReplaceAtEq 0
    (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
    (listGetWithDefault 0 row firstIndex)
    (Eq.mp (congrArg (secondIndex < ·)
      (listReplaceAtPreservesLength row firstIndex (listGetWithDefault 0 row secondIndex)).symm)
      isSecondInRange)

/-- **Swap reads the other row at the SECOND index** — the `…AtSecond` mirror of `swapRowsEntryAtFirst`:
reading row `secondIndex` after `swapRows firstIndex secondIndex` returns the whole `firstIndex` row.  The
outer `listReplaceAt` at `secondIndex` reads its new row directly (`listGetWithDefaultReplaceAtEq`). -/
theorem swapRowsEntryAtSecond (matrix : IntMatrix) (firstIndex secondIndex colIndex : Nat)
    (isFirstInRange : firstIndex < matrix.rows.length)
    (isSecondInRange : secondIndex < matrix.rows.length) :
    (matrix.swapRows firstIndex secondIndex).entryAt secondIndex colIndex
      = matrix.entryAt firstIndex colIndex := by
  have rowEq :
      listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows secondIndex
        = listGetWithDefault [] matrix.rows firstIndex := by
    unfold IntMatrix.swapRows
    rw [if_pos isFirstInRange, if_pos isSecondInRange]
    show listGetWithDefault []
        (listReplaceAt (listReplaceAt matrix.rows firstIndex
            (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
          (listGetWithDefault [] matrix.rows firstIndex)) secondIndex
      = listGetWithDefault [] matrix.rows firstIndex
    exact listGetWithDefaultReplaceAtEq []
      (listReplaceAt matrix.rows firstIndex (listGetWithDefault [] matrix.rows secondIndex)) secondIndex
      (listGetWithDefault [] matrix.rows firstIndex)
      (Eq.mp (congrArg (secondIndex < ·)
        (listReplaceAtPreservesLength matrix.rows firstIndex
          (listGetWithDefault [] matrix.rows secondIndex)).symm) isSecondInRange)
  show listGetWithDefault 0
      (listGetWithDefault [] (matrix.swapRows firstIndex secondIndex).rows secondIndex) colIndex
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows firstIndex) colIndex
  rw [rowEq]

/-- **Swap reads the other column at the SECOND index** — the `…AtSecond` mirror of
`swapColumnsEntryAtFirst`: reading column `secondIndex` of row `rowIndex` after `swapColumns firstIndex
secondIndex` returns `matrix.entryAt rowIndex firstIndex`.  Reads the mapped row
(`listGetWithDefaultMapAllRows`), then rides `swapEntriesWithinRowAtSecond`. -/
theorem swapColumnsEntryAtSecond {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (firstIndex secondIndex rowIndex : Nat)
    (isRowInRange : rowIndex < height)
    (isFirstInRange : firstIndex < width) (isSecondInRange : secondIndex < width) :
    (matrix.swapColumns firstIndex secondIndex).entryAt rowIndex secondIndex
      = matrix.entryAt rowIndex firstIndex := by
  obtain ⟨rowCount, rowWidths⟩ := isRect
  have rowInRows : rowIndex < matrix.rows.length :=
    Eq.mp (congrArg (rowIndex < ·) rowCount.symm) isRowInRange
  have rowHasWidth : (listGetWithDefault [] matrix.rows rowIndex).length = width :=
    listGetWithDefaultHasWidth matrix.rows rowIndex rowWidths rowInRows
  show listGetWithDefault 0 (listGetWithDefault []
      (mapAllRows (fun row => swapEntriesWithinRow row firstIndex secondIndex) matrix.rows) rowIndex)
      secondIndex
    = listGetWithDefault 0 (listGetWithDefault [] matrix.rows rowIndex) firstIndex
  rw [listGetWithDefaultMapAllRows _ matrix.rows rowIndex rowInRows]
  exact swapEntriesWithinRowAtSecond (listGetWithDefault [] matrix.rows rowIndex) firstIndex secondIndex
    (Eq.mp (congrArg (firstIndex < ·) rowHasWidth.symm) isFirstInRange)
    (Eq.mp (congrArg (secondIndex < ·) rowHasWidth.symm) isSecondInRange)

/-- **The row-right clear preserves a whole row whose pivot-column entry is zero** — if `workMatrix.entryAt
lowRow pivotIndex = 0` and the pivot sits left of the cleared window (`pivotIndex < startCol`), then every
column read of row `lowRow` survives `smithClearRowRightSteps` (each op is `addColumnMultiple pivotIndex
targetCol coeff`, source column `pivotIndex`, so on-target reads `old + coeff·0 = old` and the pivot column
— never a target — stays zero for the recursion).  Structural on `stepCount`; the read-column case split
rides `addColumnMultipleEntryOnTargetCol` (zeroed by `intMulZero`/`intAddZero`) versus
`addColumnMultipleEntryOffTargetCol`.  The hard phase of the above-right ROW band. -/
theorem smithClearRowRightStepsPreservesRowWithZeroPivotColumn (coeffMatrix : IntMatrix)
    (pivotIndex height width lowRow : Nat) :
    ∀ (stepCount startCol readCol : Nat) (workMatrix : IntMatrix),
      workMatrix.IsRectangular height width →
      lowRow < height →
      pivotIndex < startCol → startCol + stepCount ≤ width →
      workMatrix.entryAt lowRow pivotIndex = 0 →
      (workMatrix.applyOperations
          ((smithClearRowRightSteps coeffMatrix pivotIndex stepCount startCol).map
            ElementaryOperation.columnOperation)).entryAt lowRow readCol
        = workMatrix.entryAt lowRow readCol := by
  intro stepCount
  induction stepCount with
  | zero => intro _ _ _ _ _ _ _ _; rfl
  | succ stepCount ih =>
      intro startCol readCol workMatrix isRect lowRowInRange pivotLtStart allColsInRange zeroSource
      have pivotNeStart : pivotIndex ≠ startCol := Nat.ne_of_lt pivotLtStart
      have startColLtWidth : startCol < width :=
        Nat.lt_of_lt_of_le
          (Nat.lt_of_le_of_lt (Nat.le_add_right startCol stepCount) (Nat.lt_succ_self (startCol + stepCount)))
          allColsInRange
      have pivotColLtWidth : pivotIndex < width := Nat.lt_trans pivotLtStart startColLtWidth
      have nextRect :
          (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol)))).IsRectangular height width :=
        applyOperationPreservesRectangular
          (ElementaryOperation.columnOperation
            (ElementaryColumnOperation.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol))))) workMatrix isRect
      have nextZeroSource :
          (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol)))).entryAt lowRow pivotIndex = 0 :=
        (addColumnMultipleEntryOffTargetCol workMatrix isRect pivotIndex startCol lowRow pivotIndex _
          pivotNeStart lowRowInRange).trans zeroSource
      have headPreservesRead :
          (workMatrix.addColumnMultiple pivotIndex startCol
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt pivotIndex startCol)))).entryAt lowRow readCol
            = workMatrix.entryAt lowRow readCol := by
        cases Nat.decEq readCol startCol with
        | isTrue readEqStart =>
            rw [readEqStart,
              addColumnMultipleEntryOnTargetCol workMatrix isRect pivotIndex startCol lowRow _
                pivotNeStart lowRowInRange pivotColLtWidth startColLtWidth,
              zeroSource, intMulZero, intAddZero]
        | isFalse readNeStart =>
            exact addColumnMultipleEntryOffTargetCol workMatrix isRect pivotIndex startCol lowRow readCol _
              readNeStart lowRowInRange
      have allColsInRange' : startCol + 1 + stepCount ≤ width :=
        Eq.mp (congrArg (· ≤ width)
          ((Nat.add_succ startCol stepCount).trans (Nat.succ_add startCol stepCount).symm)) allColsInRange
      exact (ih (startCol + 1) readCol
          (workMatrix.addColumnMultiple pivotIndex startCol
            (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                (coeffMatrix.entryAt pivotIndex startCol))))
          nextRect lowRowInRange (Nat.lt_succ_of_lt pivotLtStart) allColsInRange' nextZeroSource).trans
        headPreservesRead

/-- **The column-below clear preserves a whole column whose pivot-row entry is zero** — the row mirror of
`smithClearRowRightStepsPreservesRowWithZeroPivotColumn`: if `workMatrix.entryAt pivotIndex lowCol = 0` and
`pivotIndex < startRow`, every row read of column `lowCol` survives `smithClearColumnBelowSteps` (each op is
`addRowMultiple pivotIndex targetRow coeff`, source ROW `pivotIndex`, so on-target reads `old + coeff·0 =
old`).  The hard phase of the below-left COLUMN band. -/
theorem smithClearColumnBelowStepsPreservesColumnWithZeroPivotRow (coeffMatrix : IntMatrix)
    (pivotIndex height width lowCol : Nat) :
    ∀ (stepCount startRow readRow : Nat) (workMatrix : IntMatrix),
      workMatrix.IsRectangular height width →
      lowCol < width →
      pivotIndex < startRow → startRow + stepCount ≤ height →
      workMatrix.entryAt pivotIndex lowCol = 0 →
      (workMatrix.applyOperations
          ((smithClearColumnBelowSteps coeffMatrix pivotIndex stepCount startRow).map
            ElementaryOperation.rowOperation)).entryAt readRow lowCol
        = workMatrix.entryAt readRow lowCol := by
  intro stepCount
  induction stepCount with
  | zero => intro _ _ _ _ _ _ _ _; rfl
  | succ stepCount ih =>
      intro startRow readRow workMatrix isRect lowColInRange pivotLtStart allRowsInRange zeroSource
      have pivotNeStart : pivotIndex ≠ startRow := Nat.ne_of_lt pivotLtStart
      have startRowLtHeight : startRow < height :=
        Nat.lt_of_lt_of_le
          (Nat.lt_of_le_of_lt (Nat.le_add_right startRow stepCount) (Nat.lt_succ_self (startRow + stepCount)))
          allRowsInRange
      have pivotRowLtHeight : pivotIndex < height := Nat.lt_trans pivotLtStart startRowLtHeight
      have nextRect :
          (workMatrix.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))).IsRectangular height width :=
        applyOperationPreservesRectangular
          (ElementaryOperation.rowOperation
            (ElementaryRowOperation.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex))))) workMatrix isRect
      have nextZeroSource :
          (workMatrix.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))).entryAt pivotIndex lowCol = 0 :=
        (addRowMultiplePreservesEntryOffTargetRow workMatrix pivotIndex startRow _ pivotIndex lowCol
          pivotNeStart).trans zeroSource
      have headPreservesRead :
          (workMatrix.addRowMultiple pivotIndex startRow
              (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                  (coeffMatrix.entryAt startRow pivotIndex)))).entryAt readRow lowCol
            = workMatrix.entryAt readRow lowCol := by
        cases Nat.decEq readRow startRow with
        | isTrue readEqStart =>
            rw [readEqStart,
              addRowMultipleEntryOnTargetRow workMatrix isRect pivotIndex startRow lowCol _
                pivotNeStart pivotRowLtHeight startRowLtHeight lowColInRange,
              zeroSource, intMulZero, intAddZero]
        | isFalse readNeStart =>
            exact addRowMultiplePreservesEntryOffTargetRow workMatrix pivotIndex startRow _ readRow lowCol
              readNeStart
      have allRowsInRange' : startRow + 1 + stepCount ≤ height :=
        Eq.mp (congrArg (· ≤ height)
          ((Nat.add_succ startRow stepCount).trans (Nat.succ_add startRow stepCount).symm)) allRowsInRange
      exact (ih (startRow + 1) readRow
          (workMatrix.addRowMultiple pivotIndex startRow
            (-(intPivotQuotient (coeffMatrix.entryAt pivotIndex pivotIndex)
                (coeffMatrix.entryAt startRow pivotIndex))))
          nextRect lowColInRange (Nat.lt_succ_of_lt pivotLtStart) allRowsInRange' nextZeroSource).trans
        headPreservesRead

/-- **The move word preserves an above-right ROW band** — after `smithMoveToPivotOps pivotIndex foundRow
foundCol` a settled row `lowRow < pivotIndex` keeps every band cell `(lowRow, col)`, `col ∈ [pivotIndex,
width)`, zero, PROVIDED the found position sits in the pivot window.  The row swap fixes row `lowRow`
entirely (off both `pivotIndex` and `foundRow`, both `> lowRow`); the column swap permutes the band columns
`{pivotIndex, foundCol}` among themselves (`swapColumnsEntryAtFirst`/`AtSecond` land the OTHER band column,
still zero) and fixes the rest (`swapColumnsPreservesEntryOffBothCols`).  All targets are band-zero on
input. -/
theorem smithMoveToPivotOpsPreservesRowBandZero {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex foundRow foundCol lowRow : Nat)
    (lowRowLtPivot : lowRow < pivotIndex)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (pivotLeFoundRow : pivotIndex ≤ foundRow) (pivotLeFoundCol : pivotIndex ≤ foundCol)
    (foundColLtWidth : foundCol < width)
    (bandZero : ∀ col, pivotIndex ≤ col → col < width → matrix.entryAt lowRow col = 0) :
    ∀ col, pivotIndex ≤ col → col < width →
      (matrix.applyOperations (smithMoveToPivotOps pivotIndex foundRow foundCol)).entryAt lowRow col = 0 := by
  intro col pivotLeCol colLtWidth
  have lowRowInRange : lowRow < height := Nat.lt_trans lowRowLtPivot pivotRowInRange
  have swapRowRect : (matrix.swapRows pivotIndex foundRow).IsRectangular height width :=
    applyRowOperationPreservesRectangular (ElementaryRowOperation.swapRows pivotIndex foundRow) matrix isRect
  have rowPreservedAt : ∀ readCol,
      (matrix.swapRows pivotIndex foundRow).entryAt lowRow readCol = matrix.entryAt lowRow readCol :=
    fun readCol => swapRowsPreservesEntryOffBothRows matrix pivotIndex foundRow lowRow readCol
      (Nat.ne_of_lt lowRowLtPivot) (Nat.ne_of_lt (Nat.lt_of_lt_of_le lowRowLtPivot pivotLeFoundRow))
  show ((matrix.swapRows pivotIndex foundRow).swapColumns pivotIndex foundCol).entryAt lowRow col = 0
  cases Nat.decEq col pivotIndex with
  | isTrue colEqPivot =>
      rw [colEqPivot,
        swapColumnsEntryAtFirst (matrix.swapRows pivotIndex foundRow) swapRowRect pivotIndex foundCol lowRow
          lowRowInRange pivotColInRange foundColLtWidth,
        rowPreservedAt foundCol]
      exact bandZero foundCol pivotLeFoundCol foundColLtWidth
  | isFalse colNePivot =>
      cases Nat.decEq col foundCol with
      | isTrue colEqFound =>
          rw [colEqFound,
            swapColumnsEntryAtSecond (matrix.swapRows pivotIndex foundRow) swapRowRect pivotIndex foundCol
              lowRow lowRowInRange pivotColInRange foundColLtWidth,
            rowPreservedAt pivotIndex]
          exact bandZero pivotIndex (Nat.le_refl pivotIndex) pivotColInRange
      | isFalse colNeFound =>
          rw [swapColumnsPreservesEntryOffBothCols (matrix.swapRows pivotIndex foundRow) swapRowRect
              pivotIndex foundCol lowRow col lowRowInRange colNePivot colNeFound,
            rowPreservedAt col]
          exact bandZero col pivotLeCol colLtWidth

/-- **The move word preserves a below-left COLUMN band** — the transpose mirror: after the move a settled
column `lowCol < pivotIndex` keeps every band cell `(row, lowCol)`, `row ∈ [pivotIndex, height)`, zero.  The
column swap fixes column `lowCol` (off both `pivotIndex` and `foundCol`, both `> lowCol`); the row swap
permutes the band rows `{pivotIndex, foundRow}` among themselves
(`swapRowsEntryAtFirst`/`AtSecond`) and fixes the rest (`swapRowsPreservesEntryOffBothRows`). -/
theorem smithMoveToPivotOpsPreservesColBandZero {height width : Nat} (matrix : IntMatrix)
    (isRect : matrix.IsRectangular height width)
    (pivotIndex foundRow foundCol lowCol : Nat)
    (lowColLtPivot : lowCol < pivotIndex)
    (pivotRowInRange : pivotIndex < height)
    (pivotLeFoundRow : pivotIndex ≤ foundRow) (pivotLeFoundCol : pivotIndex ≤ foundCol)
    (foundRowLtHeight : foundRow < height)
    (bandZero : ∀ row, pivotIndex ≤ row → row < height → matrix.entryAt row lowCol = 0) :
    ∀ row, pivotIndex ≤ row → row < height →
      (matrix.applyOperations (smithMoveToPivotOps pivotIndex foundRow foundCol)).entryAt row lowCol = 0 := by
  intro readRow pivotLeReadRow readRowLtHeight
  have swapRowRect : (matrix.swapRows pivotIndex foundRow).IsRectangular height width :=
    applyRowOperationPreservesRectangular (ElementaryRowOperation.swapRows pivotIndex foundRow) matrix isRect
  have pivotInRows : pivotIndex < matrix.rows.length :=
    Eq.mp (congrArg (pivotIndex < ·) isRect.1.symm) pivotRowInRange
  have foundInRows : foundRow < matrix.rows.length :=
    Eq.mp (congrArg (foundRow < ·) isRect.1.symm) foundRowLtHeight
  show ((matrix.swapRows pivotIndex foundRow).swapColumns pivotIndex foundCol).entryAt readRow lowCol = 0
  rw [swapColumnsPreservesEntryOffBothCols (matrix.swapRows pivotIndex foundRow) swapRowRect pivotIndex
      foundCol readRow lowCol readRowLtHeight (Nat.ne_of_lt lowColLtPivot)
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le lowColLtPivot pivotLeFoundCol))]
  cases Nat.decEq readRow pivotIndex with
  | isTrue readEqPivot =>
      rw [readEqPivot, swapRowsEntryAtFirst matrix pivotIndex foundRow lowCol pivotInRows foundInRows]
      exact bandZero foundRow pivotLeFoundRow foundRowLtHeight
  | isFalse readNePivot =>
      cases Nat.decEq readRow foundRow with
      | isTrue readEqFound =>
          rw [readEqFound, swapRowsEntryAtSecond matrix pivotIndex foundRow lowCol pivotInRows foundInRows]
          exact bandZero pivotIndex (Nat.le_refl pivotIndex) pivotRowInRange
      | isFalse readNeFound =>
          rw [swapRowsPreservesEntryOffBothRows matrix pivotIndex foundRow readRow lowCol readNePivot
            readNeFound]
          exact bandZero readRow pivotLeReadRow readRowLtHeight

/-- **Concrete truth probe for the two bands** — on `[[3, 0, 0], [0, 5, 6], [0, 7, 4]]` at pivot `1` the
sub-minor `[[5, 6], [7, 4]]` is nonzero, so the cascade FIRES a genuine move+sign+clear word (min-abs `4`
at `(2, 2)` swapped in via `swapRows 1↔2`, `swapColumns 1↔2`).  The settled above-right band cells `(0, 1)`,
`(0, 2)` (row `0 < 1`) and the settled below-left band cells `(1, 0)`, `(2, 0)` (column `0 < 1`) all start
zero and stay zero through the firing pivot — a distinct check from the r11 low-low probe (which only
touched a corner `< p` in BOTH coordinates).  Anonymous, no axiom footprint. -/
example :
    (({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix).applyOperations
        (smithCascadeSweep 6 ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix) 1 3 3)).entryAt 0 2
      = 0 := by decide

example :
    (({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix).applyOperations
        (smithCascadeSweep 6 ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix) 1 3 3)).entryAt 2 0
      = 0 := by decide

/-- **The cascade preserves an above-right ROW band within its fuel** (H2-SMITH r12, B2 keystone) — for a
rectangular matrix with the pivot in range, `smithCascadeSweep fuel` leaves every band cell `(lowRow, col)`
with `lowRow < pivotIndex` and `col ∈ [pivotIndex, width)` zero, given the WHOLE band zero on input.
Structural induction on `fuel`, the band mirror of `smithCascadeSweepPreservesLowLowEntry`.

  * **Base / step `none`**: the sweep is empty, the band is trivially fixed.
  * **Step `some (foundRow, foundCol)`**: split the settle word `moveOps ++ signOps ++ columnClearOps ++
    rowClearOps`; the band survives the move (`smithMoveToPivotOpsPreservesRowBandZero`, found position
    pinned `≥ pivotIndex`), the sign (off-pivot row), the column clear (top row `lowRow < pivotIndex + 1`,
    off-target), and the row clear (pivot COLUMN is band-zero so every transvection is a no-op —
    `smithClearRowRightStepsPreservesRowWithZeroPivotColumn`).  Cross clear ⟹ the settle word is the whole
    sweep; NOT clear ⟹ the recursion re-establishes the WHOLE-band hypothesis on `afterRowClear` and closes
    by IH.

The whole-band `∀`-hypothesis is load-bearing (the move-swap mixes distinct band cells).  Entries stay
UNCHANGED — immune to the r5/r6 refuted-pole shape; the sub-block stays POLE-A-walled. -/
theorem smithCascadeSweepPreservesAboveRightRowBandZero :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width lowRow : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      lowRow < pivotIndex →
      (∀ col, pivotIndex ≤ col → col < width → matrix.entryAt lowRow col = 0) →
      ∀ col, pivotIndex ≤ col → col < width →
        (matrix.applyOperations (smithCascadeSweep fuel matrix pivotIndex height width)).entryAt lowRow col
          = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width lowRow _ _ _ _ bandZero col pivotLeCol colLtWidth
      exact bandZero col pivotLeCol colLtWidth
  | succ fuel ih =>
      intro matrix pivotIndex height width lowRow isRect pivotRowInRange pivotColInRange lowRowLtPivot bandZero
      have lowRowInRange : lowRow < height := Nat.lt_trans lowRowLtPivot pivotRowInRange
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          intro col pivotLeCol colLtWidth
          exact bandZero col pivotLeCol colLtWidth
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
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
          have afterMoveRect : afterMove.IsRectangular height width :=
            applyOperationsPreservesRectangular moveOps matrix isRect
          have afterSignRect : afterSign.IsRectangular height width :=
            applyOperationsPreservesRectangular signOps afterMove afterMoveRect
          have afterColumnClearRect : afterColumnClear.IsRectangular height width :=
            applyOperationsPreservesRectangular columnClearOps afterSign afterSignRect
          have afterRowClearRect : afterRowClear.IsRectangular height width :=
            applyOperationsPreservesRectangular rowClearOps afterColumnClear afterColumnClearRect
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pivotRowInRange pivotColInRange hFind
          have afterMoveBandZero : ∀ col, pivotIndex ≤ col → col < width → afterMove.entryAt lowRow col = 0 :=
            smithMoveToPivotOpsPreservesRowBandZero matrix isRect pivotIndex foundRow foundCol lowRow
              lowRowLtPivot pivotRowInRange pivotColInRange foundInRange.1 foundInRange.2.2.1
              foundInRange.2.2.2 bandZero
          have afterSignBandZero : ∀ col, pivotIndex ≤ col → col < width → afterSign.entryAt lowRow col = 0 :=
            fun col pivotLeCol colLtWidth =>
              (signNormalizeOpsPreserveEntryOffPivot afterMove pivotIndex lowRow col
                (Nat.ne_of_lt lowRowLtPivot)).trans (afterMoveBandZero col pivotLeCol colLtWidth)
          have afterColumnClearBandZero :
              ∀ col, pivotIndex ≤ col → col < width → afterColumnClear.entryAt lowRow col = 0 :=
            fun col pivotLeCol colLtWidth =>
              (smithClearColumnBelowStepsPreservesRow afterSign pivotIndex lowRow col
                (height - (pivotIndex + 1)) (pivotIndex + 1) afterSign
                (Nat.lt_trans lowRowLtPivot (Nat.lt_succ_self pivotIndex))).trans
                (afterSignBandZero col pivotLeCol colLtWidth)
          have afterRowClearBandZero :
              ∀ col, pivotIndex ≤ col → col < width → afterRowClear.entryAt lowRow col = 0 :=
            fun col pivotLeCol colLtWidth =>
              (smithClearRowRightStepsPreservesRowWithZeroPivotColumn afterColumnClear pivotIndex height width
                  lowRow (width - (pivotIndex + 1)) (pivotIndex + 1) col afterColumnClear afterColumnClearRect
                  lowRowInRange (Nat.lt_succ_self pivotIndex)
                  (Nat.le_of_eq (smithNatAddSubOfLe (pivotIndex + 1) width pivotColInRange))
                  (afterColumnClearBandZero pivotIndex (Nat.le_refl pivotIndex) pivotColInRange)).trans
                (afterColumnClearBandZero col pivotLeCol colLtWidth)
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          have settledOpsBandZero :
              ∀ col, pivotIndex ≤ col → col < width →
                (matrix.applyOperations settledOps).entryAt lowRow col = 0 :=
            fun col pivotLeCol colLtWidth =>
              (congrArg (fun reducedMatrix => reducedMatrix.entryAt lowRow col) hApplySettled).trans
                (afterRowClearBandZero col pivotLeCol colLtWidth)
          have hSweep : smithCascadeSweep (fuel + 1) matrix pivotIndex height width
              = (match smithCrossIsClear afterRowClear pivotIndex height width with
                 | true => settledOps
                 | false => settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width) := by
            rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          rw [hSweep]
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true => exact settledOpsBandZero
          | false =>
              intro col pivotLeCol colLtWidth
              rw [applyOperationsAppend, hApplySettled]
              exact ih afterRowClear pivotIndex height width lowRow afterRowClearRect pivotRowInRange
                pivotColInRange lowRowLtPivot afterRowClearBandZero col pivotLeCol colLtWidth

/-- **The cascade preserves a below-left COLUMN band within its fuel** — the transpose mirror of
`smithCascadeSweepPreservesAboveRightRowBandZero`: `smithCascadeSweep fuel` leaves every band cell `(row,
lowCol)` with `lowCol < pivotIndex` and `row ∈ [pivotIndex, height)` zero, given the WHOLE band zero on
input.  The move rides `smithMoveToPivotOpsPreservesColBandZero`, the sign preserves the column (the `row =
pivotIndex` cell is band-zero, negated to `0`; off-pivot rows fixed), the row clear fixes the left column
(off-target, `lowCol < pivotIndex + 1`), and the column clear rides
`smithClearColumnBelowStepsPreservesColumnWithZeroPivotRow` (the pivot ROW is band-zero).  The sign phase
here needs a per-cell case (the pivot row IS in the band), handled by `negateRow`-on-zero. -/
theorem smithCascadeSweepPreservesBelowLeftColBandZero :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width lowCol : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      lowCol < pivotIndex →
      (∀ row, pivotIndex ≤ row → row < height → matrix.entryAt row lowCol = 0) →
      ∀ row, pivotIndex ≤ row → row < height →
        (matrix.applyOperations (smithCascadeSweep fuel matrix pivotIndex height width)).entryAt row lowCol
          = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width lowCol _ _ _ _ bandZero row pivotLeRow rowLtHeight
      exact bandZero row pivotLeRow rowLtHeight
  | succ fuel ih =>
      intro matrix pivotIndex height width lowCol isRect pivotRowInRange pivotColInRange lowColLtPivot bandZero
      have lowColInRange : lowCol < width := Nat.lt_trans lowColLtPivot pivotColInRange
      cases hFind : smithFindMinAbsInMinor matrix pivotIndex height width with
      | none =>
          rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          intro row pivotLeRow rowLtHeight
          exact bandZero row pivotLeRow rowLtHeight
      | some pair =>
          obtain ⟨foundRow, foundCol⟩ := pair
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
          have afterMoveRect : afterMove.IsRectangular height width :=
            applyOperationsPreservesRectangular moveOps matrix isRect
          have afterSignRect : afterSign.IsRectangular height width :=
            applyOperationsPreservesRectangular signOps afterMove afterMoveRect
          have afterColumnClearRect : afterColumnClear.IsRectangular height width :=
            applyOperationsPreservesRectangular columnClearOps afterSign afterSignRect
          have afterRowClearRect : afterRowClear.IsRectangular height width :=
            applyOperationsPreservesRectangular rowClearOps afterColumnClear afterColumnClearRect
          have foundInRange := smithFindMinAbsInMinorFoundInRange matrix pivotIndex height width
            foundRow foundCol pivotRowInRange pivotColInRange hFind
          have afterMoveBandZero : ∀ row, pivotIndex ≤ row → row < height → afterMove.entryAt row lowCol = 0 :=
            smithMoveToPivotOpsPreservesColBandZero matrix isRect pivotIndex foundRow foundCol lowCol
              lowColLtPivot pivotRowInRange foundInRange.1 foundInRange.2.2.1 foundInRange.2.1 bandZero
          have pivotInAfterMoveRows : pivotIndex < afterMove.rows.length :=
            Eq.mp (congrArg (pivotIndex < ·) afterMoveRect.1.symm) pivotRowInRange
          have afterSignBandZero : ∀ row, pivotIndex ≤ row → row < height → afterSign.entryAt row lowCol = 0 :=
            fun row pivotLeRow rowLtHeight =>
              signNormalizeOpsPreserveZeroEntry afterMove pivotIndex row lowCol pivotInAfterMoveRows
                (afterMoveBandZero row pivotLeRow rowLtHeight)
          have afterColumnClearBandZero :
              ∀ row, pivotIndex ≤ row → row < height → afterColumnClear.entryAt row lowCol = 0 :=
            fun row pivotLeRow rowLtHeight =>
              (smithClearColumnBelowStepsPreservesColumnWithZeroPivotRow afterSign pivotIndex height width
                  lowCol (height - (pivotIndex + 1)) (pivotIndex + 1) row afterSign afterSignRect lowColInRange
                  (Nat.lt_succ_self pivotIndex)
                  (Nat.le_of_eq (smithNatAddSubOfLe (pivotIndex + 1) height pivotRowInRange))
                  (afterSignBandZero pivotIndex (Nat.le_refl pivotIndex) pivotRowInRange)).trans
                (afterSignBandZero row pivotLeRow rowLtHeight)
          have afterRowClearBandZero :
              ∀ row, pivotIndex ≤ row → row < height → afterRowClear.entryAt row lowCol = 0 :=
            fun row pivotLeRow rowLtHeight =>
              (smithClearRowRightStepsPreservesColumn afterColumnClear pivotIndex height width row lowCol
                rowLtHeight (width - (pivotIndex + 1)) (pivotIndex + 1) afterColumnClear afterColumnClearRect
                (Nat.lt_succ_of_lt lowColLtPivot)).trans
                (afterColumnClearBandZero row pivotLeRow rowLtHeight)
          have hApplySettled : matrix.applyOperations settledOps = afterRowClear :=
            (applyOperationsAppend (moveOps ++ signOps ++ columnClearOps) rowClearOps matrix).trans
              (congrArg (fun reducedMatrix => reducedMatrix.applyOperations rowClearOps)
                ((applyOperationsAppend (moveOps ++ signOps) columnClearOps matrix).trans
                  (congrArg (fun reducedMatrix => reducedMatrix.applyOperations columnClearOps)
                    (applyOperationsAppend moveOps signOps matrix))))
          have settledOpsBandZero :
              ∀ row, pivotIndex ≤ row → row < height →
                (matrix.applyOperations settledOps).entryAt row lowCol = 0 :=
            fun row pivotLeRow rowLtHeight =>
              (congrArg (fun reducedMatrix => reducedMatrix.entryAt row lowCol) hApplySettled).trans
                (afterRowClearBandZero row pivotLeRow rowLtHeight)
          have hSweep : smithCascadeSweep (fuel + 1) matrix pivotIndex height width
              = (match smithCrossIsClear afterRowClear pivotIndex height width with
                 | true => settledOps
                 | false => settledOps ++ smithCascadeSweep fuel afterRowClear pivotIndex height width) := by
            rw [smithCascadeSweepSucc fuel matrix pivotIndex height width, hFind]
          rw [hSweep]
          cases hCross : smithCrossIsClear afterRowClear pivotIndex height width with
          | true => exact settledOpsBandZero
          | false =>
              intro row pivotLeRow rowLtHeight
              rw [applyOperationsAppend, hApplySettled]
              exact ih afterRowClear pivotIndex height width lowCol afterRowClearRect pivotRowInRange
                pivotColInRange lowColLtPivot afterRowClearBandZero row pivotLeRow rowLtHeight

/-- **The seed cascade preserves an above-right ROW band** (driver-path form) — the keystone
`smithCascadeSweepPreservesAboveRightRowBandZero` discharged at `smithMinorAbsSum matrix pivotIndex height
width`, the static fuel the driver seeds the cascade with.  The band twin of
`smithCascadeSweepSeedPreservesLowLowEntry`. -/
theorem smithCascadeSweepSeedPreservesAboveRightRowBandZero (matrix : IntMatrix)
    (pivotIndex height width lowRow : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (lowRowLtPivot : lowRow < pivotIndex)
    (bandZero : ∀ col, pivotIndex ≤ col → col < width → matrix.entryAt lowRow col = 0) :
    ∀ col, pivotIndex ≤ col → col < width →
      (matrix.applyOperations
          (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).entryAt lowRow col = 0 :=
  smithCascadeSweepPreservesAboveRightRowBandZero (smithMinorAbsSum matrix pivotIndex height width) matrix
    pivotIndex height width lowRow isRect pivotRowInRange pivotColInRange lowRowLtPivot bandZero

/-- **The seed cascade preserves a below-left COLUMN band** (driver-path form) — the transpose mirror. -/
theorem smithCascadeSweepSeedPreservesBelowLeftColBandZero (matrix : IntMatrix)
    (pivotIndex height width lowCol : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (lowColLtPivot : lowCol < pivotIndex)
    (bandZero : ∀ row, pivotIndex ≤ row → row < height → matrix.entryAt row lowCol = 0) :
    ∀ row, pivotIndex ≤ row → row < height →
      (matrix.applyOperations
          (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
            matrix pivotIndex height width)).entryAt row lowCol = 0 :=
  smithCascadeSweepPreservesBelowLeftColBandZero (smithMinorAbsSum matrix pivotIndex height width) matrix
    pivotIndex height width lowCol isRect pivotRowInRange pivotColInRange lowColLtPivot bandZero

/-! ## The single-step composed postcondition (H2-SMITH r12, B3) — the induction step body

One full driver step at `pivotIndex` under the settled-prefix precondition advances the settled frame from
`pivotIndex` to `pivotIndex + 1`.  The conclusion cell `(r, c)` of the advanced frame is dispatched into the
five regions the r12 gap audit named: prefix (r11 low-low), the two bands (r12 keystones), and the two new
cross strips (r10 cross-clear, decoded pointwise).  Assembled from r10 + r11 + B1 + B2; it NEVER mentions
the sub-block `[p+1, ·)²`, so it is immune to the r5/r6/POLE-A refutation by construction. -/

/-- **Concrete truth probe for the single step** — on `[[3, 0, 0], [0, 5, 6], [0, 7, 4]]` the seed cascade at
pivot `1` clears its cross, so the two new cross-strip cells `(1, 2)` and `(2, 1)` — the frame cells that
`pivotIndex → pivotIndex + 1` newly settles — read zero.  Anonymous, no axiom footprint. -/
example :
    (({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix).applyOperations
        (smithCascadeSweep
          (smithMinorAbsSum ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix) 1 3 3)
          ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix) 1 3 3)).entryAt 1 2 = 0 := by decide

example :
    (({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix).applyOperations
        (smithCascadeSweep
          (smithMinorAbsSum ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix) 1 3 3)
          ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix) 1 3 3)).entryAt 2 1 = 0 := by decide

/-- **One driver step advances the settled frame `p → p+1`** (H2-SMITH r12, B3) — the induction step body.
Under `SmithPrefixSettled matrix pivotIndex`, the seed cascade at `pivotIndex` leaves the matrix
`SmithPrefixSettled` at `pivotIndex + 1`.  The advanced-frame cell `(r, c)` dispatches (cases on `r`, `c`
versus `pivotIndex`) into:

  * **prefix** `r < p ∧ c < p`: r11 `smithCascadeSweepSeedPreservesLowLowEntry` freezes the input zero;
  * **above-right band** `r < p ∧ c ≥ p`: B2 `…SeedPreservesAboveRightRowBandZero` (band-zero from
    `isSettled`);
  * **below-left band** `r ≥ p ∧ c < p`: B2 `…SeedPreservesBelowLeftColBandZero`;
  * **row cross** `r = p ∧ c > p` / **column cross** `c = p ∧ r > p`: r10
    `smithCascadeSweepSeedReachesCrossClear` decoded by `smithCrossIsClearPointwise`.

The sub-block `r > p ∧ c > p` is OUTSIDE the advanced frame (neither `≤ p`) — never required, so POLE-A is
untouched.  `SmithReduceFullDriverStatement` stays uninhabited; NO flip. -/
theorem smithCascadeStepSettlesThroughPivot (matrix : IntMatrix) (pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width)
    (isSettled : SmithPrefixSettled matrix pivotIndex height width) :
    SmithPrefixSettled
      (matrix.applyOperations
        (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))
      (pivotIndex + 1) height width := by
  intro rowIndex colIndex rowLtHeight colLtWidth rowNeCol frameHolds
  cases Nat.lt_or_ge rowIndex pivotIndex with
  | inl rowLtPivot =>
      cases Nat.lt_or_ge colIndex pivotIndex with
      | inl colLtPivot =>
          exact (smithCascadeSweepSeedPreservesLowLowEntry matrix pivotIndex height width rowIndex colIndex
              isRect pivotRowInRange pivotColInRange rowLtPivot colLtPivot).trans
            (isSettled rowIndex colIndex rowLtHeight colLtWidth rowNeCol (Or.inl rowLtPivot))
      | inr colGePivot =>
          exact smithCascadeSweepSeedPreservesAboveRightRowBandZero matrix pivotIndex height width rowIndex
            isRect pivotRowInRange pivotColInRange rowLtPivot
            (fun bandCol pivotLeBandCol bandColLtWidth =>
              isSettled rowIndex bandCol rowLtHeight bandColLtWidth
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le rowLtPivot pivotLeBandCol)) (Or.inl rowLtPivot))
            colIndex colGePivot colLtWidth
  | inr rowGePivot =>
      cases Nat.lt_or_ge colIndex pivotIndex with
      | inl colLtPivot =>
          exact smithCascadeSweepSeedPreservesBelowLeftColBandZero matrix pivotIndex height width colIndex
            isRect pivotRowInRange pivotColInRange colLtPivot
            (fun bandRow pivotLeBandRow bandRowLtHeight =>
              isSettled bandRow colIndex bandRowLtHeight colLtWidth
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le colLtPivot pivotLeBandRow)).symm (Or.inr colLtPivot))
            rowIndex rowGePivot rowLtHeight
      | inr colGePivot =>
          have crossClear :
              smithCrossIsClear
                  (matrix.applyOperations
                    (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
                      matrix pivotIndex height width))
                  pivotIndex height width = true :=
            smithCascadeSweepSeedReachesCrossClear matrix pivotIndex height width isRect pivotRowInRange
              pivotColInRange
          have crossPointwise :=
            smithCrossIsClearPointwise
              (matrix.applyOperations
                (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width)
                  matrix pivotIndex height width))
              pivotIndex height width pivotRowInRange pivotColInRange crossClear
          cases frameHolds with
          | inl rowLtSucc =>
              have rowEqPivot : rowIndex = pivotIndex :=
                Nat.le_antisymm (Nat.le_of_lt_succ rowLtSucc) rowGePivot
              have pivotLtCol : pivotIndex < colIndex :=
                Nat.lt_of_le_of_ne colGePivot
                  (fun pivotEqCol => rowNeCol (rowEqPivot.trans pivotEqCol))
              rw [rowEqPivot]
              exact crossPointwise.1 colIndex pivotLtCol colLtWidth
          | inr colLtSucc =>
              have colEqPivot : colIndex = pivotIndex :=
                Nat.le_antisymm (Nat.le_of_lt_succ colLtSucc) colGePivot
              have pivotLtRow : pivotIndex < rowIndex :=
                Nat.lt_of_le_of_ne rowGePivot
                  (fun pivotEqRow => rowNeCol (pivotEqRow.symm.trans colEqPivot.symm))
              rw [colEqPivot]
              exact crossPointwise.2 rowIndex pivotLtRow rowLtHeight

/-! ## The descending-pivot induction skeleton (H2-SMITH r12, B4) — the growing-frame fold to `Nat.min`

The single-step advances the settled frame `p → p+1`.  The outer `smithReduceTotalSweep` fold threads it
across pivots: from `SmithPrefixSettled matrix pivotIndex` the whole sweep reaches `SmithPrefixSettled` at
`Nat.min (Nat.min height width) (pivotIndex + outerFuel)` — capped at `Nat.min height width` because the
sub-block is POLE-A-walled.  Structural on `outerFuel`: the guard-true step chains B3 (afterPivot settled at
`pivotIndex + 1`) with the IH on the advanced pivot; the guard-false / fuel-exhausted branches drop to the
capped frame by monotonicity.  At the driver start (`pivotIndex = 0`, `outerFuel = Nat.min height width`)
the cap collapses to `Nat.min height width`, giving `IsWindowDiagonal` of the total cross-clear driver's
output — a genuine POLE-A driver-path window-diagonal result, distinct from (and consistent with) the r4
refutation `smithReduceTotalIsNotFullyReducing` (which refutes only the divisibility CHAIN, not
off-diagonal vanishing).  It does NOT close `repairWindowDiagHolds` (that governs the repair phase, which
re-breaks diagonality per POLE-B); `SmithReduceFullDriverStatement` stays uninhabited; NO flip. -/

/-- **The settled frame is monotone down** — `SmithPrefixSettled matrix pivotIndex` implies
`SmithPrefixSettled matrix lowerIndex` for `lowerIndex ≤ pivotIndex` (a smaller frame is a weaker claim: its
disjunct `r < lowerIndex ∨ c < lowerIndex` implies `r < pivotIndex ∨ c < pivotIndex`).  Lets the outer fold
drop a fuel-exhausted or guard-stopped result to the capped frame index. -/
theorem smithPrefixSettledMonotone (matrix : IntMatrix) (pivotIndex height width lowerIndex : Nat)
    (isSettled : SmithPrefixSettled matrix pivotIndex height width) (lowerLe : lowerIndex ≤ pivotIndex) :
    SmithPrefixSettled matrix lowerIndex height width :=
  fun rowIndex colIndex rowLtHeight colLtWidth rowNeCol frameLower =>
    isSettled rowIndex colIndex rowLtHeight colLtWidth rowNeCol
      (frameLower.elim (fun rowLtLower => Or.inl (Nat.lt_of_lt_of_le rowLtLower lowerLe))
        (fun colLtLower => Or.inr (Nat.lt_of_lt_of_le colLtLower lowerLe)))

/-- **`Nat.min` of a value with itself** — the propext-clean idempotence (`Nat.min_self` may leak): unfold to
the `if value ≤ value` and take the reflexive branch. -/
theorem natMinSelf (value : Nat) : Nat.min value value = value := by
  show (if value ≤ value then value else value) = value
  rw [if_pos (Nat.le_refl value)]

/-- **The total cross-clear sweep advances the settled frame** (H2-SMITH r12, B4) — from
`SmithPrefixSettled matrix pivotIndex` the whole `smithReduceTotalSweep outerFuel` reaches
`SmithPrefixSettled` at `Nat.min (Nat.min height width) (pivotIndex + outerFuel)`.  Structural on
`outerFuel`, the growing-frame outer transport: the guard-true step composes `smithCascadeStepSettlesThroughPivot`
(the frame `p → p+1` advance) with the IH on the advanced pivot; the base and guard-false branches drop to
the capped frame by `smithPrefixSettledMonotone`. -/
theorem smithReduceTotalSweepSettlesThroughPivots :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      SmithPrefixSettled matrix pivotIndex height width →
      SmithPrefixSettled
        (matrix.applyOperations (smithReduceTotalSweep outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) height width := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ isSettled
      exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
        (natMinLeRight (Nat.min height width) (pivotIndex + 0))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect isSettled
      show SmithPrefixSettled (matrix.applyOperations
          (if pivotIndex + 1 ≤ Nat.min height width then
            smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height width
              ++ smithReduceTotalSweep outerFuel
                  (matrix.applyOperations
                    (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                      height width))
                  (pivotIndex + 1) height width
           else []))
        (Nat.min (Nat.min height width) (pivotIndex + (outerFuel + 1))) height width
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := natLeTrans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans guardTrue (natMinLeRight height width)
        have afterPivotSettled :
            SmithPrefixSettled
              (matrix.applyOperations
                (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width))
              (pivotIndex + 1) height width :=
          smithCascadeStepSettlesThroughPivot matrix pivotIndex height width isRect pivotRowInRange
            pivotColInRange isSettled
        have afterPivotRect :
            (matrix.applyOperations
                (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have ihResult := ih
          (matrix.applyOperations
            (smithCascadeSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex height
              width))
          (pivotIndex + 1) height width afterPivotRect afterPivotSettled
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
          (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1))) minLePivot)

/-- **Concrete truth probe for the total cross-clear window-diagonal** — on `[[3, 0, 0], [0, 5, 6], [0, 7,
4]]` the full driver `smithReduceTotalSweep 3 … 0 3 3` zeros every off-diagonal window cell (probed at
`(0, 1)` and `(1, 2)`); the input is genuinely non-diagonal, so the driver really works.  Anonymous, no
axiom footprint. -/
example :
    (({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix).applyOperations
        (smithReduceTotalSweep 3 ({ rows := [[3, 0, 0], [0, 5, 6], [0, 7, 4]] } : IntMatrix)
          0 3 3)).entryAt 1 2 = 0 := by decide

/-- **The total cross-clear driver output is window-diagonal** (H2-SMITH r12, B4 top) — every off-diagonal
cell of the `height × width` window vanishes after `smithReduceTotalSweep (Nat.min height width) matrix 0`
(the operations of `smithReduceTotal`).  Instantiate the growing-frame fold at the driver start; the cap
`Nat.min (Nat.min height width) (0 + Nat.min height width)` collapses to `Nat.min height width`
(`natMinSelf`), and `smithPrefixSettledAtMinIsWindowDiagonal` reads off the window-diagonal.  A POLE-A
driver-path result on the cross-clear phase ONLY — the repair phase's `repairWindowDiagHolds` /
`repairChainHolds` stay walled; NO flip. -/
theorem smithReduceTotalSweepDiagonalizes (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    ∀ rowIndex colIndex, rowIndex < height → colIndex < width → rowIndex ≠ colIndex →
      (matrix.applyOperations
          (smithReduceTotalSweep (Nat.min height width) matrix 0 height width)).entryAt rowIndex colIndex
        = 0 := by
  have generalResult :=
    smithReduceTotalSweepSettlesThroughPivots (Nat.min height width) matrix 0 height width isRect
      (smithPrefixSettledZero matrix height width)
  rw [Nat.zero_add, natMinSelf] at generalResult
  exact smithPrefixSettledAtMinIsWindowDiagonal
    (matrix.applyOperations (smithReduceTotalSweep (Nat.min height width) matrix 0 height width))
    height width generalResult

/-! ## The POLE-A arc ledger (H2-SMITH r12, B5) — what the driver-path Prop still owes; NO flip

**Shipped this round (r12).**  The two bands around the remaining sub-block are closed as driver-path
reachability facts, and the cross-clear driver's window-diagonal is assembled:

  * B1 — `SmithPrefixSettled` (the settled frame outside `[p, ·)²`), the cross-clear forward pointwise
    decode (`smithCrossIsClearPointwise`), the vacuous base and the `Nat.min` terminal
    (`smithPrefixSettledAtMinIsWindowDiagonal`).
  * B2 — `smithCascadeSweepPreservesAboveRightRowBandZero` / `…BelowLeftColBandZero` (+ seed forms): the
    settled bands survive the whole cascade because the added multiples are of ZERO entries and the
    move-swap permutes zero cells among themselves (the `…AtSecond` readers + the two zero-source clear
    preservers).
  * B3 — `smithCascadeStepSettlesThroughPivot`: one full driver step advances the frame `p → p+1`
    (5-way region dispatch, sub-block never mentioned).
  * B4 — `smithReduceTotalSweepSettlesThroughPivots` folds the step to the `Nat.min` cap, and
    `smithReduceTotalSweepDiagonalizes` reads off `IsWindowDiagonal` of the TOTAL CROSS-CLEAR driver output.

**Still owed toward `SmithNormalForm.SmithReduceFullDriverStatement` (UNINHABITED; NO flip).**  The two
surviving hypotheses of `smithReduceFullDriverOfRepairInvariants` are about the REPAIR sweep
(`smithDivisibilityRepairSweep`, = `fold + re-cascade`) layered on top of `smithReduceTotal`:

  * `repairWindowDiagHolds` — `IsWindowDiagonal (repair ∘ reduceTotal) 0 height width`.  The repair fold
    `addRowMultiple foundPos pivotIndex 1` MID-WAY re-breaks diagonality (POLE-B, refuted standalone on
    `diag(30, 20, 12)`: off-diagonal residue `60` at `(2, 1)`), so r12's cross-clear window-diagonal does
    NOT transport through it unchanged.  NAMED NODE: a `SmithPrefixSettled`-style frame transport for the
    repair FOLD step (the band machinery of B2 re-applied to `addRowMultiple foundPos pivotIndex 1` + the
    re-fired cascade), which the fold does NOT preserve pointwise — it needs the fold's OWN reachability
    argument, not settled-prefix monotonicity.
  * `repairChainHolds` — the invariant-factor chain `d_p ∣ d_{p+1}`.  A SEPARATE POLE-A conjunct (the
    gcd-landing of the folded operands), refuted standalone (`SmithRepairChainDiagonalizesStatement` on
    `diag(30, 20, 12)`), correct only along the min-abs-presorted driver path — its own later round.

**Discipline honoured.**  Every r12 statement is quantified over the driver's OWN seed word
(`smithCascadeSweep (smithMinorAbsSum …) …`) under `SmithPrefixSettled` + `IsRectangular` + pivot-in-range —
the r7 reachability template; NONE quantifies over an arbitrary window-diagonal input, and NONE concludes
"re-diagonalized" (they conclude "these zeros stay zero").  So the r12 family is immune to the r5/r6/POLE-A
refuted-pole shape by construction.  `SmithReduceFullDriverStatement` is NOT flipped; the sub-block gcd
chain and the repair-fold window-diagonal are the honest remaining walls. -/

/-! ## The repair-fold frame confinement (H2-SMITH r13, B1) — the fold touches only row `pivotIndex`

r12's `smithCascadeStepSettlesThroughPivot` advances the settled frame `p → p+1` through the CROSS-CLEAR
cascade, unconditionally, because the cascade always clears the cross at `p`.  The repair phase layers a
FOLD (`addRowMultiple foundPos pivotIndex 1`) before each re-fired cascade, and POLE-B (eval-confirmed on
`diag(30, 20, 12)`: the mid-fold cascade strands `20` at `(2, 1)`, and the terminal standalone repair keeps
residue `60` at `(2, 1)`) shows the fold+re-cascade can DRAG a residue into the sub-block — the frame does
NOT advance `p → p+1` through the repair for arbitrary settled inputs.

This section ships the honest UNCONDITIONAL half: the fold PRESERVES the settled frame AT `p` (it does not
break what is already settled).  The fold `addRowMultiple foundPos pivotIndex 1` writes ONLY row
`pivotIndex`; a frame cell off that row is frozen (`addRowMultiplePreservesEntryOffTargetRow`), and a frame
cell ON row `pivotIndex` is necessarily a settled COLUMN cell `(pivotIndex, colIndex)` with `colIndex <
pivotIndex` (row `pivotIndex` is not `< pivotIndex`, so the frame disjunct fires on the column), whose new
value `old(pivotIndex, colIndex) + 1 * old(foundPos, colIndex)` sums two settled-frame zeros
(`colIndex < pivotIndex` makes both `(pivotIndex, colIndex)` and `(foundPos, colIndex)` frame cells).  This
is the `foldPreservesSettledColumnZero` argument re-cast over the WEAKER `SmithPrefixSettled matrix
pivotIndex` hypothesis (the r12 frame, not the full window-diagonal): the fold does not disturb the frame at
`p`.  The genuinely-new content advancing `p → p+1` (clearing the new cross-strip at `p` WHEN the input's
cross-strip there is dirty) is exactly the POLE-B wall — NOT this lemma.  `SmithReduceFullDriverStatement`
stays uninhabited; NO flip. -/

/-- **The repair fold preserves the settled frame at `pivotIndex`** — folding a later row `foundPos` into the
pivot row (`addRowMultiple foundPos pivotIndex 1`) keeps `SmithPrefixSettled matrix pivotIndex` intact.  A
frame cell off row `pivotIndex` is frozen by `addRowMultiplePreservesEntryOffTargetRow`; a frame cell on row
`pivotIndex` has `colIndex < pivotIndex` (the disjunct forces the column, since `pivotIndex ≮ pivotIndex`),
and its post-fold value `old(pivotIndex, colIndex) + 1 * old(foundPos, colIndex)` is `0 + 1 * 0` because both
summand cells have column `< pivotIndex` (frame cells).  The r12 frame recast of
`foldPreservesSettledColumnZero` over the weaker `SmithPrefixSettled` hypothesis.  This preserves the SAME
frame (`p → p`); ADVANCING it (`p → p+1`) through the fold+re-cascade is the POLE-B wall. -/
theorem smithRepairFoldPreservesSettledFrame (matrix : IntMatrix) (pivotIndex foundPos height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotInWindow : pivotIndex < height)
    (pivotBelowFound : pivotIndex < foundPos) (foundInWindow : foundPos < height)
    (isSettled : SmithPrefixSettled matrix pivotIndex height width) :
    SmithPrefixSettled (matrix.addRowMultiple foundPos pivotIndex 1) pivotIndex height width := by
  intro rowIndex colIndex rowLtHeight colLtWidth rowNeCol frameHolds
  cases Nat.decEq rowIndex pivotIndex with
  | isFalse rowNePivot =>
      rw [addRowMultiplePreservesEntryOffTargetRow matrix foundPos pivotIndex 1 rowIndex colIndex rowNePivot]
      exact isSettled rowIndex colIndex rowLtHeight colLtWidth rowNeCol frameHolds
  | isTrue rowEqPivot =>
      have colLtPivot : colIndex < pivotIndex :=
        frameHolds.elim
          (fun rowLtPivot =>
            absurd (Eq.mp (congrArg (· < pivotIndex) rowEqPivot) rowLtPivot) (Nat.lt_irrefl pivotIndex))
          id
      have colLtFound : colIndex < foundPos := Nat.lt_trans colLtPivot pivotBelowFound
      have foundNePivot : foundPos ≠ pivotIndex :=
        fun foundEqPivot =>
          Nat.lt_irrefl pivotIndex (Eq.mp (congrArg (pivotIndex < ·) foundEqPivot) pivotBelowFound)
      have pivotEntryZero : matrix.entryAt pivotIndex colIndex = 0 :=
        isSettled pivotIndex colIndex pivotInWindow colLtWidth
          (fun pivotEqCol =>
            Nat.lt_irrefl colIndex (Eq.mp (congrArg (colIndex < ·) pivotEqCol) colLtPivot))
          (Or.inr colLtPivot)
      have foundEntryZero : matrix.entryAt foundPos colIndex = 0 :=
        isSettled foundPos colIndex foundInWindow colLtWidth
          (fun foundEqCol =>
            Nat.lt_irrefl colIndex (Eq.mp (congrArg (colIndex < ·) foundEqCol) colLtFound))
          (Or.inr colLtPivot)
      rw [rowEqPivot,
        addRowMultipleEntryOnTargetRow matrix isRect foundPos pivotIndex colIndex 1 foundNePivot
          foundInWindow pivotInWindow colLtWidth,
        pivotEntryZero, foundEntryZero, intOneMul]
      exact intZeroAdd 0

/-! ## The repair terminal re-clear (H2-SMITH r13, B2) — the fold's re-fired cascade clears the pivot cross

Each repair iteration folds a later row into the pivot row and RE-FIRES the shipped Euclid cascade at the
pivot.  The r10 seed `smithCascadeSweepSeedReachesCrossClear` — unconditional cross-clear of the seed cascade
on ANY rectangular matrix with the pivot in range — instantiates verbatim at the POST-FOLD matrix (the fold
preserves rectangularity via `applyOperationsPreservesRectangular`, the pivot range is the outer guard's).
`smithRepairFoldCascadeReachesCrossClear` packages that instantiation.

Folding it up the position loop, `smithRepairPositionSweepReachesCrossClear` shows the WHOLE per-position
repair keeps the pivot cross clear: given the input's cross is clear, the output's cross is clear — the
`none`/exhausted branches pass the hypothesis through untouched, and every fired iteration lands on the last
re-cascade's clear cross (B2 at the post-fold matrix) before the IH runs on it.  This is the MEDIUM
recon deliverable: an UNCONDITIONAL cross-strip clearing of the repair loop, riding r10 per-iteration.  It is
NOT the frame advance `p → p+1` (which additionally requires the input's cross-strip at `p` be MADE clean
when it is dirty — the POLE-B wall, since the repair only fires on DIAGONAL non-divisibility).
`SmithReduceFullDriverStatement` stays uninhabited; NO flip. -/

/-- **The repair fold's re-fired cascade clears the pivot cross** — after folding `foundPos`'s row into the
pivot row, the re-fired seed cascade at `pivotIndex` reaches `smithCrossIsClear = true`.  The r10 seed
`smithCascadeSweepSeedReachesCrossClear` at the POST-FOLD matrix (rectangular by
`applyOperationsPreservesRectangular`; pivot in range from the outer guard).  The single-iteration atom the
whole-loop cross-clear rides. -/
theorem smithRepairFoldCascadeReachesCrossClear (matrix : IntMatrix) (foundPos pivotIndex height width : Nat)
    (isRect : matrix.IsRectangular height width)
    (pivotRowInRange : pivotIndex < height) (pivotColInRange : pivotIndex < width) :
    smithCrossIsClear
      ((matrix.applyOperations
          [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ]).applyOperations
        (smithCascadeSweep
          (smithMinorAbsSum
            (matrix.applyOperations
              [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ])
            pivotIndex height width)
          (matrix.applyOperations
            [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ])
          pivotIndex height width))
      pivotIndex height width = true :=
  smithCascadeSweepSeedReachesCrossClear
    (matrix.applyOperations
      [ ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ])
    pivotIndex height width
    (applyOperationsPreservesRectangular _ matrix isRect)
    pivotRowInRange pivotColInRange

/-- **The per-position repair sweep keeps the pivot cross clear** — if the input's cross at `pivotIndex` is
clear, so is the output's, for every repair fuel.  Structural on the fuel: the `none` and zero-fuel branches
return the matrix unchanged (hypothesis passes through); a fired iteration lands on the post-fold cascade's
clear cross (`smithRepairFoldCascadeReachesCrossClear`), which feeds the IH on the reduced matrix.  The
MEDIUM r13 deliverable — an unconditional cross-strip clearing of the repair loop; the frame advance
`p → p+1` (making a DIRTY input cross-strip clean) stays the POLE-B wall. -/
theorem smithRepairPositionSweepReachesCrossClear :
    ∀ (fuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      pivotIndex < height → pivotIndex < width →
      smithCrossIsClear matrix pivotIndex height width = true →
      smithCrossIsClear
        (matrix.applyOperations (smithRepairPositionSweep fuel matrix pivotIndex height width))
        pivotIndex height width = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix pivotIndex height width _ _ _ crossClear
      exact crossClear
  | succ fuel ih =>
      intro matrix pivotIndex height width isRect pivotRowInRange pivotColInRange crossClear
      cases hFind : smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) with
      | none =>
          rw [smithRepairPositionSweepSucc fuel matrix pivotIndex height width, hFind]
          exact crossClear
      | some foundPos =>
          let foldOps :=
            [ ElementaryOperation.rowOperation
                (ElementaryRowOperation.addRowMultiple foundPos pivotIndex 1) ]
          let afterFold := matrix.applyOperations foldOps
          let clearOps :=
            smithCascadeSweep (smithMinorAbsSum afterFold pivotIndex height width)
              afterFold pivotIndex height width
          let afterClear := afterFold.applyOperations clearOps
          have afterFoldRect : afterFold.IsRectangular height width :=
            applyOperationsPreservesRectangular foldOps matrix isRect
          have afterClearRect : afterClear.IsRectangular height width :=
            applyOperationsPreservesRectangular clearOps afterFold afterFoldRect
          have afterClearCrossClear :
              smithCrossIsClear afterClear pivotIndex height width = true :=
            smithRepairFoldCascadeReachesCrossClear matrix foundPos pivotIndex height width isRect
              pivotRowInRange pivotColInRange
          have hUnfold : smithRepairPositionSweep (fuel + 1) matrix pivotIndex height width
              = foldOps ++ clearOps ++ smithRepairPositionSweep fuel afterClear pivotIndex height width := by
            rw [smithRepairPositionSweepSucc fuel matrix pivotIndex height width, hFind]
          rw [hUnfold, applyOperationsAppend, applyOperationsAppend]
          exact ih afterClear pivotIndex height width afterClearRect pivotRowInRange pivotColInRange
            afterClearCrossClear

/-! ## The composed repair postcondition (H2-SMITH r13, B3) — the conditional fold to window-diagonal

r12's cross-clear window-diagonal (`smithReduceTotalSweepDiagonalizes`) is assembled UNCONDITIONALLY because
its single-step `smithCascadeStepSettlesThroughPivot` advances the settled frame `p → p+1` for every settled
input: the cross-clear cascade always clears the cross at `p`.  The recon's honest adjudication (§2c) is that
the REPAIR single-step is NOT one-step-unconditional: the fold+re-cascade can DRAG a residue into the
sub-block (POLE-B, eval-confirmed) and the repair fires only on DIAGONAL non-divisibility, so a dirty
cross-strip at `p` that the diagonal already divides is left UNCLEARED — the frame does not advance for
arbitrary settled inputs.

So B3 ships the FULL-RE-RUN shape as a CONDITIONAL assembly, isolating the wall to ONE named `Prop`.
`SmithRepairStepSettlesStatement` is the repair analogue of `smithCascadeStepSettlesThroughPivot` (the
per-position repair sweep advances the settled frame `p → p+1`).  The growing-frame fold
`smithDivisibilityRepairSweepSettlesThroughPivots` — a verbatim mirror of the r12 cross-clear
`smithReduceTotalSweepSettlesThroughPivots`, with the single-step CALL replaced by the named HYPOTHESIS —
threads it across pivots; `smithDivisibilityRepairSweepDiagonalizes` reads off `IsWindowDiagonal` of the whole
repair output at the driver start.  Pure structural transport, propext-clean, no new math: the reusable
machinery that closes the repair window-diagonal THE MOMENT the single-step is available.

**Honest scope (retained, like POLE-B).**  `SmithRepairStepSettlesStatement` is REFUTABLE over the bare
`SmithPrefixSettled` frame: the eval-confirmed standalone `[[2, 0, 0], [0, 60, 0], [0, 60, -60]]` (the
pivot-0 repair output on the UNSORTED `diag(30, 20, 12)`) is `SmithPrefixSettled` at `1` and rectangular with
pivot `1` in range, yet the pivot-`1` repair sweep does NOTHING (`60 ∣ -60`, so `find` returns `none`),
leaving the frame-`2` cell `(2, 1) = 60 ≠ 0`.  Closing it needs a STRICTLY STRONGER driver-path invariant than
`SmithPrefixSettled` — the min-magnitude/pre-sort property of `smithReduceTotal`'s output that forbids the drag
(the deep POLE-A elimination-correctness).  So the fold is honest reusable transport, not a discharge;
`SmithReduceFullDriverStatement` stays uninhabited; NO flip. -/

/-- **The repair single-step advance (named, refutable over the bare frame)** — the per-position repair sweep
advances the settled frame `p → p+1`.  The repair analogue of the UNCONDITIONALLY-true cross-clear step
`smithCascadeStepSettlesThroughPivot`; here it is a HYPOTHESIS, REFUTED over the bare `SmithPrefixSettled`
frame by the POLE-B eval (`[[2,0,0],[0,60,0],[0,60,-60]]` at pivot `1`).  Isolates the repair-fold
window-diagonal wall to exactly this one `Prop`; discharging it needs the driver-path min-magnitude invariant,
not frame monotonicity. -/
def SmithRepairStepSettlesStatement : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width →
    pivotIndex < height → pivotIndex < width →
    SmithPrefixSettled matrix pivotIndex height width →
    SmithPrefixSettled
      (matrix.applyOperations
        (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))
      (pivotIndex + 1) height width

/-- **The divisibility-repair sweep advances the settled frame (conditional)** — GIVEN the repair single-step
`SmithRepairStepSettlesStatement`, from `SmithPrefixSettled matrix pivotIndex` the whole
`smithDivisibilityRepairSweep outerFuel` reaches `SmithPrefixSettled` at
`Nat.min (Nat.min height width) (pivotIndex + outerFuel)`.  A verbatim mirror of the r12 cross-clear fold
`smithReduceTotalSweepSettlesThroughPivots` — structural on `outerFuel`, the guard-true step chains the
hypothesised single-step (afterPosition settled at `pivotIndex + 1`) with the IH on the advanced pivot; the
base and guard-false branches drop to the capped frame by `smithPrefixSettledMonotone`.  The single-step is
the ONLY wall (refutable over the bare frame; NO flip). -/
theorem smithDivisibilityRepairSweepSettlesThroughPivots
    (stepSettles : SmithRepairStepSettlesStatement) :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      SmithPrefixSettled matrix pivotIndex height width →
      SmithPrefixSettled
        (matrix.applyOperations (smithDivisibilityRepairSweep outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) height width := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ isSettled
      exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
        (natMinLeRight (Nat.min height width) (pivotIndex + 0))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect isSettled
      show SmithPrefixSettled (matrix.applyOperations
          (if pivotIndex + 1 ≤ Nat.min height width then
            smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                height width
              ++ smithDivisibilityRepairSweep outerFuel
                  (matrix.applyOperations
                    (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix
                      pivotIndex height width))
                  (pivotIndex + 1) height width
           else []))
        (Nat.min (Nat.min height width) (pivotIndex + (outerFuel + 1))) height width
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := natLeTrans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans guardTrue (natMinLeRight height width)
        have afterPositionSettled :
            SmithPrefixSettled
              (matrix.applyOperations
                (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width))
              (pivotIndex + 1) height width :=
          stepSettles matrix pivotIndex height width isRect pivotRowInRange pivotColInRange isSettled
        have afterPositionRect :
            (matrix.applyOperations
                (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have ihResult := ih
          (matrix.applyOperations
            (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
              height width))
          (pivotIndex + 1) height width afterPositionRect afterPositionSettled
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
          (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1))) minLePivot)

/-- **The repair output is window-diagonal (conditional)** — GIVEN the repair single-step
`SmithRepairStepSettlesStatement`, every off-diagonal cell of the `height × width` window vanishes after
`smithDivisibilityRepairSweep (Nat.min height width) matrix 0`, for ANY rectangular `matrix`.  Instantiate the
conditional fold at the driver start (`pivotIndex = 0`, vacuous base `smithPrefixSettledZero`); the cap
`Nat.min (Nat.min height width) (0 + Nat.min height width)` collapses to `Nat.min height width` (`natMinSelf`),
and `smithPrefixSettledAtMinIsWindowDiagonal` reads off the window-diagonal.  This is EXACTLY the driver's
`repairWindowDiagHolds` shape (instantiated at `matrix := smithReduceTotal output` in B4); the single-step is
the ONLY residual (NO flip). -/
theorem smithDivisibilityRepairSweepDiagonalizes
    (stepSettles : SmithRepairStepSettlesStatement)
    (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    ∀ rowIndex colIndex, rowIndex < height → colIndex < width → rowIndex ≠ colIndex →
      (matrix.applyOperations
          (smithDivisibilityRepairSweep (Nat.min height width) matrix 0 height width)).entryAt rowIndex colIndex
        = 0 := by
  have generalResult :=
    smithDivisibilityRepairSweepSettlesThroughPivots stepSettles (Nat.min height width) matrix 0 height width
      isRect (smithPrefixSettledZero matrix height width)
  rw [Nat.zero_add, natMinSelf] at generalResult
  exact smithPrefixSettledAtMinIsWindowDiagonal
    (matrix.applyOperations (smithDivisibilityRepairSweep (Nat.min height width) matrix 0 height width))
    height width generalResult

/-! ## The verbatim repair-window-diagonal hypothesis + the audited driver movement (H2-SMITH r13, B4)

B3's `smithDivisibilityRepairSweepDiagonalizes` reads off `IsWindowDiagonal` of the repair output on ANY
rectangular input, conditional on the named single-step `SmithRepairStepSettlesStatement`.  B4 instantiates it
at the driver's ACTUAL repair input `afterDiag = matrix.applyOperations (smithReduceTotal …).operations` to hit
EXACTLY the shape of `smithReduceFullDriverOfRepairInvariants`'s first hypothesis `repairWindowDiagHolds`, then
composes with that upstream reduction to move `SmithReduceFullDriverStatement` off `repairWindowDiagHolds`.

**The audited driver-statement movement, stated exactly.**  Before B4 the two surviving hypotheses of
`smithReduceFullDriverOfRepairInvariants` were `repairWindowDiagHolds` (every off-diagonal cell of the WHOLE
`height × width` window vanishes after the repair sweep — a large ∀-over-cells obligation) and
`repairChainHolds`.  After B4 the window-diagonal half is DISCHARGED conditionally on
`SmithRepairStepSettlesStatement` (one per-position frame advance `p → p+1`), so
`SmithReduceFullDriverStatement` now rests on EXACTLY the two conjuncts

  * `SmithRepairStepSettlesStatement` — the named single-step, REFUTABLE over the bare `SmithPrefixSettled`
    frame (POLE-B eval `[[2,0,0],[0,60,0],[0,60,-60]]` at pivot `1`); discharging it needs the driver-path
    min-magnitude invariant, not frame monotonicity;
  * `repairChainHolds` — the invariant-factor chain, a SEPARATE POLE-A conjunct (untouched this round).

It does NOT rest on `repairChainHolds` ALONE: the window-diagonal half is not UNCONDITIONALLY inhabited
(that would need the strictly-stronger driver-path invariant B3's honesty scope names).  So the exact residual
of the window-diagonal half is the ONE named `Prop` `SmithRepairStepSettlesStatement`; the chain half is
`repairChainHolds`.  `SmithReduceFullDriverStatement` stays UNINHABITED; NO flip. -/

/-- **The verbatim `repairWindowDiagHolds` hypothesis, conditional on the single-step** — GIVEN the named
repair single-step `SmithRepairStepSettlesStatement`, the driver's repair output
`(afterDiag).applyOperations (smithDivisibilityRepairSweep (Nat.min height width) afterDiag 0 …)` is
window-diagonal at `0`, for every rectangular `matrix` (with `afterDiag = matrix.applyOperations
(smithReduceTotal …).operations`).  This is EXACTLY the type of `smithReduceFullDriverOfRepairInvariants`'s
first hypothesis: `smithDivisibilityRepairSweepDiagonalizes` instantiated at `matrix := afterDiag` (rectangular
by `applyOperationsPreservesRectangular`), the two `0 ≤ ·` window guards dropped.  A conditional discharge, NOT
an unconditional inhabitation — the single-step is refutable over the bare frame (POLE-B). -/
theorem repairWindowDiagHoldsOfRepairStep (stepSettles : SmithRepairStepSettlesStatement) :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      IsWindowDiagonal
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        0 height width := by
  intro matrix height width isRect
  intro rowIndex colIndex _zeroLeRow rowLtHeight _zeroLeCol colLtWidth rowNeCol
  exact smithDivisibilityRepairSweepDiagonalizes stepSettles
    (matrix.applyOperations (smithReduceTotal matrix height width).operations) height width
    (applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect)
    rowIndex colIndex rowLtHeight colLtWidth rowNeCol

/-- **The driver totality from the single-step and the chain (the audited movement)** — GIVEN the named repair
single-step `SmithRepairStepSettlesStatement` AND the invariant-factor chain `repairChainHolds` (verbatim its
`smithReduceFullDriverOfRepairInvariants` type), `SmithReduceFullDriverStatement` follows.  The window-diagonal
hypothesis is supplied by `repairWindowDiagHoldsOfRepairStep`, discharging one of the two prior driver
survivors and moving the whole totality onto EXACTLY `{SmithRepairStepSettlesStatement, repairChainHolds}`.  It
does NOT rest on `repairChainHolds` alone — the single-step is the residual of the window-diagonal half
(refutable over the bare frame; POLE-B).  `SmithReduceFullDriverStatement` stays UNINHABITED; NO flip. -/
theorem smithReduceFullDriverOfRepairStepAndChain
    (stepSettles : SmithRepairStepSettlesStatement)
    (repairChainHolds : ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithDivisibilityRepairSweep (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width) :
    SmithReduceFullDriverStatement :=
  smithReduceFullDriverOfRepairInvariants (repairWindowDiagHoldsOfRepairStep stepSettles) repairChainHolds

/-! ## The repair-transport arc ledger (H2-SMITH r13, B5, #2137) — what the driver still owes; NO flip

**#2137 state.**  `SmithNormalForm.SmithReduceFullDriverStatement` is UNINHABITED (no flip).  Before r13 its
totality reduced (`smithReduceFullDriverOfRepairInvariants`) to TWO hypotheses on the repair output
`afterRepair = smithDivisibilityRepairSweep (Nat.min h w) afterDiag 0` (with `afterDiag = smithReduceTotal`
output): `repairWindowDiagHolds` (window-diagonal at 0) and `repairChainHolds` (invariant-factor chain).  r13
DISCHARGES the first CONDITIONALLY and isolates its residual to ONE named per-step `Prop`.

**Shipped this round (r13), all independently axiom-free (`#print axioms` = "no axioms").**

  * B1 — `smithRepairFoldPreservesSettledFrame`: the repair fold `addRowMultiple foundPos pivotIndex 1`
    preserves `SmithPrefixSettled matrix pivotIndex` (UNCONDITIONAL — touches only row `pivotIndex`, whose
    frame cells are settled columns `0 + 1*0`).
  * B2 — `smithRepairFoldCascadeReachesCrossClear` + `smithRepairPositionSweepReachesCrossClear`: the whole
    per-position repair sweep keeps the pivot cross clear (UNCONDITIONAL, structural on the repair fuel; the
    MEDIUM recon deliverable, riding r10's seed cross-clear at the post-fold matrix).
  * B3 — `SmithRepairStepSettlesStatement` (the named wall), `smithDivisibilityRepairSweepSettlesThroughPivots`
    (conditional growing-frame fold, verbatim mirror of r12's `smithReduceTotalSweepSettlesThroughPivots` with
    the single-step CALL replaced by the HYPOTHESIS), and `smithDivisibilityRepairSweepDiagonalizes` (reads off
    `IsWindowDiagonal` of the repair output on ANY rectangular input, GIVEN the single-step).
  * B4 — `repairWindowDiagHoldsOfRepairStep`: `smithDivisibilityRepairSweepDiagonalizes` instantiated at the
    driver's actual `afterDiag`, matching `smithReduceFullDriverOfRepairInvariants`'s first hypothesis VERBATIM;
    `smithReduceFullDriverOfRepairStepAndChain` composes it, moving `SmithReduceFullDriverStatement` off
    `repairWindowDiagHolds` onto EXACTLY `{SmithRepairStepSettlesStatement, repairChainHolds}`.

**Still owed toward `SmithReduceFullDriverStatement` (UNINHABITED; NO flip) — two named jams.**

  * JAM 1 (the window-diagonal residual).  NAMED NODE: `SmithRepairStepSettlesStatement`.  Exact goal:
    for `matrix.IsRectangular height width`, `pivotIndex < height`, `pivotIndex < width`,
    `SmithPrefixSettled matrix pivotIndex height width`, prove
    `SmithPrefixSettled (matrix.applyOperations (smithRepairPositionSweep (smithMinorAbsSum matrix pivotIndex
    height width) matrix pivotIndex height width)) (pivotIndex + 1) height width`.  REFUTABLE over the bare
    `SmithPrefixSettled` frame: the eval-confirmed standalone `[[2,0,0],[0,60,0],[0,60,-60]]` (pivot-0 repair on
    the UNSORTED `diag(30, 20, 12)`) is settled at `1` with pivot `1` in range, yet the pivot-`1` repair does
    NOTHING (`60 ∣ -60`, `find = none`), leaving frame-`2` cell `(2, 1) = 60 ≠ 0`.  Discharging it needs a
    STRICTLY STRONGER driver-path invariant than `SmithPrefixSettled` — the min-magnitude/pre-sort property of
    `smithReduceTotal`'s output that forbids the drag (the deep POLE-A elimination-correctness the r8/r9
    docstrings name; the fuzz shows `afterDiag` is NOT magnitude-sorted, so even a sortedness lemma is not
    free-standing).
  * JAM 2 (the chain).  NAMED NODE: `smithReduceFullDriverOfRepairStepAndChain`'s `repairChainHolds`
    hypothesis (= `smithReduceFullDriverOfRepairInvariants`'s second, verbatim).  Exact goal: for
    `matrix.IsRectangular height width`, prove `SmithChainPrefix afterRepair (Nat.min height width) height
    width` — the invariant-factor divisibility `d_p ∣ d_{p+1}` of the repair output.  A SEPARATE POLE-A conjunct
    (the gcd-landing of the folded operands), correct only along the min-abs-presorted driver path; its own
    later round.  UNTOUCHED this round.

**Discipline honoured.**  Every r13 UNCONDITIONAL statement (B1, B2) is quantified over the driver's own
fold/re-cascade word under `SmithPrefixSettled`/`IsRectangular`/pivot-in-range (the r7 reachability template),
concluding "these zeros stay zero" / "the cross stays clear" — NEVER "re-diagonalized" over an arbitrary input.
Every CONDITIONAL statement (B3, B4) carries `SmithRepairStepSettlesStatement` as an explicit hypothesis and is
honest reusable transport, not a discharge.  The window-diagonal wall is isolated to that ONE named `Prop`; the
chain is the separate JAM 2.  `SmithReduceFullDriverStatement` is NOT flipped. -/

/-! ## The ideal / Z-combination stability atom (H2-SMITH r14, B4 — JAM 2-PRESERVE core)

The r14 recon refutes the round's pivot-is-min premise on-path (`smithReduceTotalPivotMinIsRefuted`,
`SmithNormalForm`), so the JAM 2 chain has no sorted-shortcut discharge.  Its honest UNCONDITIONAL,
refutation-immune deliverable is the PRESERVE half: a fixed divisor `d` that divides every entry of a
matrix keeps dividing every entry after ANY unimodular operation — the classical fact that the ideal
generated by the entries (hence the first determinantal divisor `d_1 = gcd` of all entries) is
invariant under row/column swaps, negations, and transvections, because each produces a `Z`-linear
combination of existing entries.

Three `Int` atoms — `d ∣ 0`, `d ∣ x ⇒ d ∣ -x`, `d ∣ a ∧ d ∣ b ⇒ d ∣ a + c*b` — lift through three
range-free structural slot-predicate preservers (`listReplaceAt`/`listModifyAt`/`mapAllRows`) to the
six primitive row/column transforms, then to every `ElementaryOperation`, then to whole words.  All
STRUCTURAL, propext-clean; the primitives are total so the operation guards split only on
in-range-vs-identity (the identity branch is the hypothesis verbatim), never on index arithmetic.

**Honest scope (retained).**  This is the WHOLE-MATRIX preserve.  Establishing the SUB-BLOCK hypothesis
`d_p ∣ [p,·)²` at each repair position's exit (for `p > 0`, where `d_p` does NOT divide the earlier
pivots) re-imports window-diagonality — the deep POLE-A no-drag node the recon names as JAM 1's wall.
So this atom shrinks JAM 2 to its ESTABLISH half (coupled to JAM 1), it does NOT close the chain;
`SmithReduceFullDriverStatement` stays UNINHABITED; NO flip. -/

/-- **`d ∣ 0`** — every divisor divides zero (witness `0`, over `intMulZero`). -/
theorem dividesExactlyZero (divisor : Int) : dividesExactly divisor 0 :=
  ⟨0, (intMulZero divisor).symm⟩

/-- **`d ∣ x ⇒ d ∣ -x`** — divisibility survives negation (witness the negated cofactor, over
`intMulNeg`). -/
theorem dividesExactlyNeg {divisor value : Int} (isDivisible : dividesExactly divisor value) :
    dividesExactly divisor (-value) :=
  match isDivisible with
  | ⟨factor, valueEq⟩ => ⟨-factor, (congrArg Neg.neg valueEq).trans (intMulNeg divisor factor).symm⟩

/-- **`d ∣ a ∧ d ∣ b ⇒ d ∣ a + c*b`** — the scaled-add (transvection) stays divisible (witness
`leftFactor + coefficient * rightFactor`, over `intLeftDistrib` and a comm/assoc `swapEq`).  The core
`Z`-combination stability. -/
theorem dividesExactlyAddScaled {divisor : Int} (coefficient : Int) {leftValue rightValue : Int}
    (isLeftDivisible : dividesExactly divisor leftValue)
    (isRightDivisible : dividesExactly divisor rightValue) :
    dividesExactly divisor (leftValue + coefficient * rightValue) :=
  match isLeftDivisible, isRightDivisible with
  | ⟨leftFactor, leftEq⟩, ⟨rightFactor, rightEq⟩ =>
      ⟨leftFactor + coefficient * rightFactor, by
        have swapEq :
            coefficient * (divisor * rightFactor) = divisor * (coefficient * rightFactor) :=
          (intMulAssoc coefficient divisor rightFactor).symm.trans
            ((congrArg (· * rightFactor) (intMulComm coefficient divisor)).trans
              (intMulAssoc divisor coefficient rightFactor))
        rw [leftEq, rightEq, intLeftDistrib, swapEq]⟩

/-- **`listReplaceAt` preserves a slot predicate** — if `predicate` holds of the default, the new entry,
and every original slot, it holds of every slot after the replace.  Range-free structural recursion over
the four `listReplaceAt` arms (the `[]` arms case the read index to hit the default). -/
theorem listReplaceAtPreservesSlotPredicate {Entry : Type} (defaultEntry : Entry)
    (predicate : Entry → Prop) (isDefaultOk : predicate defaultEntry) :
    ∀ (entries : List Entry) (position : Nat) (newEntry : Entry),
      predicate newEntry →
      (∀ index, predicate (listGetWithDefault defaultEntry entries index)) →
      ∀ index, predicate (listGetWithDefault defaultEntry (listReplaceAt entries position newEntry) index)
  | [], 0, _, _, _ => fun index => match index with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | [], _ + 1, _, _, _ => fun index => match index with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | _ :: _, 0, _, isNewOk, allSlotsOk => fun index =>
      match index with
      | 0 => isNewOk
      | successorIndex + 1 => allSlotsOk (successorIndex + 1)
  | _ :: remainingEntries, position + 1, newEntry, isNewOk, allSlotsOk => fun index =>
      match index with
      | 0 => allSlotsOk 0
      | successorIndex + 1 =>
          listReplaceAtPreservesSlotPredicate defaultEntry predicate isDefaultOk remainingEntries
            position newEntry isNewOk (fun laterIndex => allSlotsOk (laterIndex + 1)) successorIndex

/-- **`listModifyAt` preserves a slot predicate** — when the transform preserves it and it holds of the
default and every original slot, it holds of every slot after the modify.  Range-free structural
recursion. -/
theorem listModifyAtPreservesSlotPredicate {Entry : Type} (defaultEntry : Entry)
    (predicate : Entry → Prop) (transform : Entry → Entry) (isDefaultOk : predicate defaultEntry)
    (isTransformOk : ∀ entry, predicate entry → predicate (transform entry)) :
    ∀ (entries : List Entry) (position : Nat),
      (∀ index, predicate (listGetWithDefault defaultEntry entries index)) →
      ∀ index, predicate (listGetWithDefault defaultEntry (listModifyAt transform entries position) index)
  | [], 0, _ => fun index => match index with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | [], _ + 1, _ => fun index => match index with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | _ :: _, 0, allSlotsOk => fun index =>
      match index with
      | 0 => isTransformOk _ (allSlotsOk 0)
      | successorIndex + 1 => allSlotsOk (successorIndex + 1)
  | _ :: remainingEntries, position + 1, allSlotsOk => fun index =>
      match index with
      | 0 => allSlotsOk 0
      | successorIndex + 1 =>
          listModifyAtPreservesSlotPredicate defaultEntry predicate transform isDefaultOk
            isTransformOk remainingEntries position (fun laterIndex => allSlotsOk (laterIndex + 1))
            successorIndex

/-- **`mapAllRows` preserves a slot predicate** — when the row transform preserves it and it holds of the
empty row and every original row, it holds of every row after the map.  Range-free structural
recursion. -/
theorem mapAllRowsPreservesSlotPredicate (predicate : IntRow → Prop) (transform : IntRow → IntRow)
    (isDefaultOk : predicate []) (isTransformOk : ∀ row, predicate row → predicate (transform row)) :
    ∀ (rows : List IntRow),
      (∀ index, predicate (listGetWithDefault [] rows index)) →
      ∀ index, predicate (listGetWithDefault [] (mapAllRows transform rows) index)
  | [], _ => fun index => match index with | 0 => isDefaultOk | _ + 1 => isDefaultOk
  | _ :: remainingRows, allSlotsOk => fun index =>
      match index with
      | 0 => isTransformOk _ (allSlotsOk 0)
      | successorIndex + 1 =>
          mapAllRowsPreservesSlotPredicate predicate transform isDefaultOk isTransformOk remainingRows
            (fun laterIndex => allSlotsOk (laterIndex + 1)) successorIndex

/-- **Every slot of a row is `d`-divisible** — the row-level ideal predicate. -/
def RowSlotsDivisibleBy (divisor : Int) (row : IntRow) : Prop :=
  ∀ index, dividesExactly divisor (listGetWithDefault 0 row index)

/-- The empty row's slots are all `d`-divisible (every read is the default `0`). -/
theorem rowSlotsDivisibleByEmpty (divisor : Int) : RowSlotsDivisibleBy divisor [] :=
  fun index => match index with
    | 0 => dividesExactlyZero divisor
    | _ + 1 => dividesExactlyZero divisor

/-- **Every entry of a matrix is `d`-divisible** — the whole-matrix ideal predicate (as every row's
slots being `d`-divisible; unfolds to `∀ r c, d ∣ entryAt r c`). -/
def MatrixEntriesDivisibleBy (divisor : Int) (matrix : IntMatrix) : Prop :=
  ∀ rowIndex, RowSlotsDivisibleBy divisor (listGetWithDefault [] matrix.rows rowIndex)

/-- Read `MatrixEntriesDivisibleBy` at a single entry (defeq unfold of the nested slot reads). -/
theorem matrixEntriesDivisibleByAt {divisor : Int} {matrix : IntMatrix}
    (matrixDivisible : MatrixEntriesDivisibleBy divisor matrix) (rowIndex colIndex : Nat) :
    dividesExactly divisor (matrix.entryAt rowIndex colIndex) :=
  matrixDivisible rowIndex colIndex

/-- The row map-negation preserves row divisibility (each slot negates a divisible entry). -/
theorem rowSlotsDivisibleMapNeg {divisor : Int} {row : IntRow}
    (rowDivisible : RowSlotsDivisibleBy divisor row) :
    RowSlotsDivisibleBy divisor (row.map (fun entry => -entry)) :=
  fun index => by
    rw [listGetWithDefaultMapNeg]
    exact dividesExactlyNeg (rowDivisible index)

/-- The row scaled-add preserves row divisibility (each zipped slot is `target + c*source`, both
divisible; the ragged/past-end slots read `0`).  Structural on both rows. -/
theorem rowSlotsDivisibleAddScaledEntries {divisor : Int} (coefficient : Int) :
    ∀ (sourceRow targetRow : IntRow),
      RowSlotsDivisibleBy divisor sourceRow → RowSlotsDivisibleBy divisor targetRow →
      RowSlotsDivisibleBy divisor (addScaledEntries coefficient sourceRow targetRow)
  | [], [], _, _ => rowSlotsDivisibleByEmpty divisor
  | [], _ :: _, _, _ => rowSlotsDivisibleByEmpty divisor
  | _ :: _, [], _, _ => rowSlotsDivisibleByEmpty divisor
  | _ :: sourceRest, _ :: targetRest, sourceDivisible, targetDivisible =>
      fun index => match index with
        | 0 => dividesExactlyAddScaled coefficient (targetDivisible 0) (sourceDivisible 0)
        | successorIndex + 1 =>
            rowSlotsDivisibleAddScaledEntries coefficient sourceRest targetRest
              (fun laterIndex => sourceDivisible (laterIndex + 1))
              (fun laterIndex => targetDivisible (laterIndex + 1)) successorIndex

/-- The within-row column swap preserves row divisibility (a permutation; the two `listReplaceAt`
guards' identity branches return the hypothesis). -/
theorem rowSlotsDivisibleSwapEntries {divisor : Int} (row : IntRow) (firstIndex secondIndex : Nat)
    (rowDivisible : RowSlotsDivisibleBy divisor row) :
    RowSlotsDivisibleBy divisor (swapEntriesWithinRow row firstIndex secondIndex) := by
  unfold IntMatrix.swapEntriesWithinRow
  split
  · split
    · exact listReplaceAtPreservesSlotPredicate 0 (dividesExactly divisor) (dividesExactlyZero divisor)
        (listReplaceAt row firstIndex (listGetWithDefault 0 row secondIndex)) secondIndex
        (listGetWithDefault 0 row firstIndex) (rowDivisible firstIndex)
        (listReplaceAtPreservesSlotPredicate 0 (dividesExactly divisor) (dividesExactlyZero divisor)
          row firstIndex (listGetWithDefault 0 row secondIndex) (rowDivisible secondIndex) rowDivisible)
    · exact rowDivisible
  · exact rowDivisible

/-- The within-row column negation preserves row divisibility (a single `listModifyAt` of a negation). -/
theorem rowSlotsDivisibleModifyNeg {divisor : Int} (row : IntRow) (colIndex : Nat)
    (rowDivisible : RowSlotsDivisibleBy divisor row) :
    RowSlotsDivisibleBy divisor (listModifyAt (fun entry => -entry) row colIndex) :=
  listModifyAtPreservesSlotPredicate 0 (dividesExactly divisor) (fun entry => -entry)
    (dividesExactlyZero divisor) (fun _ isDivisible => dividesExactlyNeg isDivisible) row colIndex
    rowDivisible

/-- The within-row column scaled-add preserves row divisibility (the `listModifyAt` of `target +
c*source`; the range guard's identity branch returns the hypothesis). -/
theorem rowSlotsDivisibleAddScaledWithinRow {divisor : Int} (row : IntRow)
    (sourceIndex targetIndex : Nat) (coefficient : Int)
    (rowDivisible : RowSlotsDivisibleBy divisor row) :
    RowSlotsDivisibleBy divisor (addScaledEntryWithinRow row sourceIndex targetIndex coefficient) := by
  unfold IntMatrix.addScaledEntryWithinRow
  split
  · exact listModifyAtPreservesSlotPredicate 0 (dividesExactly divisor)
      (fun targetEntry => targetEntry + coefficient * listGetWithDefault 0 row sourceIndex)
      (dividesExactlyZero divisor)
      (fun _ isDivisible => dividesExactlyAddScaled coefficient isDivisible (rowDivisible sourceIndex))
      row targetIndex rowDivisible
  · exact rowDivisible

/-- **A single row operation preserves whole-matrix divisibility** — swap permutes rows, negate negates
a row, transvection scaled-adds a row; each identity guard returns the hypothesis. -/
theorem applyRowOperationPreservesEntriesDivisible {divisor : Int} (matrix : IntMatrix)
    (operation : ElementaryRowOperation)
    (matrixDivisible : MatrixEntriesDivisibleBy divisor matrix) :
    MatrixEntriesDivisibleBy divisor (matrix.applyRowOperation operation) := by
  cases operation with
  | swapRows firstIndex secondIndex =>
      show MatrixEntriesDivisibleBy divisor (matrix.swapRows firstIndex secondIndex)
      unfold IntMatrix.swapRows
      split
      · split
        · exact listReplaceAtPreservesSlotPredicate [] (RowSlotsDivisibleBy divisor)
            (rowSlotsDivisibleByEmpty divisor)
            (listReplaceAt matrix.rows firstIndex (listGetWithDefault [] matrix.rows secondIndex))
            secondIndex (listGetWithDefault [] matrix.rows firstIndex) (matrixDivisible firstIndex)
            (listReplaceAtPreservesSlotPredicate [] (RowSlotsDivisibleBy divisor)
              (rowSlotsDivisibleByEmpty divisor) matrix.rows firstIndex
              (listGetWithDefault [] matrix.rows secondIndex) (matrixDivisible secondIndex)
              matrixDivisible)
        · exact matrixDivisible
      · exact matrixDivisible
  | negateRow rowIndex =>
      show MatrixEntriesDivisibleBy divisor (matrix.negateRow rowIndex)
      exact listModifyAtPreservesSlotPredicate [] (RowSlotsDivisibleBy divisor)
        (fun row => row.map (fun entry => -entry)) (rowSlotsDivisibleByEmpty divisor)
        (fun _ rowDivisible => rowSlotsDivisibleMapNeg rowDivisible) matrix.rows rowIndex matrixDivisible
  | addRowMultiple sourceIndex targetIndex coefficient =>
      show MatrixEntriesDivisibleBy divisor
        (matrix.addRowMultiple sourceIndex targetIndex coefficient)
      unfold IntMatrix.addRowMultiple
      split
      · exact matrixDivisible
      · split
        · split
          · exact listModifyAtPreservesSlotPredicate [] (RowSlotsDivisibleBy divisor)
              (fun targetRow =>
                addScaledEntries coefficient (listGetWithDefault [] matrix.rows sourceIndex) targetRow)
              (rowSlotsDivisibleByEmpty divisor)
              (fun _ rowDivisible => rowSlotsDivisibleAddScaledEntries coefficient
                (listGetWithDefault [] matrix.rows sourceIndex) _ (matrixDivisible sourceIndex)
                rowDivisible)
              matrix.rows targetIndex matrixDivisible
          · exact matrixDivisible
        · exact matrixDivisible

/-- **A single column operation preserves whole-matrix divisibility** — swap/negate/transvection applied
row-locally via `mapAllRows`, over the within-row preservers. -/
theorem applyColumnOperationPreservesEntriesDivisible {divisor : Int} (matrix : IntMatrix)
    (operation : ElementaryColumnOperation)
    (matrixDivisible : MatrixEntriesDivisibleBy divisor matrix) :
    MatrixEntriesDivisibleBy divisor (matrix.applyColumnOperation operation) := by
  cases operation with
  | swapColumns firstIndex secondIndex =>
      show MatrixEntriesDivisibleBy divisor (matrix.swapColumns firstIndex secondIndex)
      exact mapAllRowsPreservesSlotPredicate (RowSlotsDivisibleBy divisor)
        (fun row => swapEntriesWithinRow row firstIndex secondIndex) (rowSlotsDivisibleByEmpty divisor)
        (fun row rowDivisible => rowSlotsDivisibleSwapEntries row firstIndex secondIndex rowDivisible)
        matrix.rows matrixDivisible
  | negateColumn colIndex =>
      show MatrixEntriesDivisibleBy divisor (matrix.negateColumn colIndex)
      exact mapAllRowsPreservesSlotPredicate (RowSlotsDivisibleBy divisor)
        (fun row => listModifyAt (fun entry => -entry) row colIndex) (rowSlotsDivisibleByEmpty divisor)
        (fun row rowDivisible => rowSlotsDivisibleModifyNeg row colIndex rowDivisible)
        matrix.rows matrixDivisible
  | addColumnMultiple sourceIndex targetIndex coefficient =>
      show MatrixEntriesDivisibleBy divisor
        (matrix.addColumnMultiple sourceIndex targetIndex coefficient)
      unfold IntMatrix.addColumnMultiple
      split
      · exact matrixDivisible
      · exact mapAllRowsPreservesSlotPredicate (RowSlotsDivisibleBy divisor)
          (fun row => addScaledEntryWithinRow row sourceIndex targetIndex coefficient)
          (rowSlotsDivisibleByEmpty divisor)
          (fun row rowDivisible =>
            rowSlotsDivisibleAddScaledWithinRow row sourceIndex targetIndex coefficient rowDivisible)
          matrix.rows matrixDivisible

/-- **A single elementary operation preserves whole-matrix divisibility** — dispatch to the row/column
halves. -/
theorem applyOperationPreservesEntriesDivisible {divisor : Int} (matrix : IntMatrix)
    (operation : ElementaryOperation)
    (matrixDivisible : MatrixEntriesDivisibleBy divisor matrix) :
    MatrixEntriesDivisibleBy divisor (matrix.applyOperation operation) :=
  match operation with
  | .rowOperation rowOp => applyRowOperationPreservesEntriesDivisible matrix rowOp matrixDivisible
  | .columnOperation colOp => applyColumnOperationPreservesEntriesDivisible matrix colOp matrixDivisible

/-- **A whole certificate word preserves whole-matrix divisibility** — the ideal-invariance atom: if `d`
divides every entry of `matrix`, it divides every entry of `matrix.applyOperations operations` for ANY
word.  Structural on the word.  The refutation-immune JAM 2-PRESERVE core (whole-matrix; the sub-block
establishment for `d_p`, `p > 0`, re-imports JAM 1's window-diagonality). -/
theorem applyOperationsPreservesEntriesDivisible {divisor : Int} :
    ∀ (operations : List ElementaryOperation) (matrix : IntMatrix),
      MatrixEntriesDivisibleBy divisor matrix →
      MatrixEntriesDivisibleBy divisor (matrix.applyOperations operations)
  | [], _, matrixDivisible => matrixDivisible
  | operation :: remainingOperations, matrix, matrixDivisible =>
      applyOperationsPreservesEntriesDivisible remainingOperations (matrix.applyOperation operation)
        (applyOperationPreservesEntriesDivisible matrix operation matrixDivisible)

/-- Whole-matrix divisibility gives every DIAGONAL entry divisible (`diagonalEntryAt p = entryAt p p`).
The read the invariant-factor chain consumes for the first factor `d_1 = gcd` of all entries. -/
theorem matrixEntriesDivisibleByDiagonal {divisor : Int} {matrix : IntMatrix}
    (matrixDivisible : MatrixEntriesDivisibleBy divisor matrix) (position : Nat) :
    dividesExactly divisor (matrix.diagonalEntryAt position) :=
  matrixEntriesDivisibleByAt matrixDivisible position position

/-! ## The pivot-is-min premise is REFUTED on-path (H2-SMITH r14, B1 — permanent regression)

The r14 round's central premise — "prove pivot-is-min-abs-of-tail as a `smithReduceTotal`
postcondition" — is FALSE on the driver's own path, and this permanently records it.  `smithReduceTotal`
is a selection sort ONLY on already-diagonal minors: when a pivot's cross is already clear it sits
UNREDUCED while a LATER pivot Euclid-reduces its disconnected sub-block below it.
`reduceTotal([[4,0,0],[0,6,10],[0,15,0]]) = diag(4, 1, 150)` — `d_0 = 4 > d_1 = 1` — so the reduceTotal
diagonal is NOT magnitude-nondecreasing.  (Zeros compound it: `reduceTotal(diag(1,54,0)) = diag(1,54,0)`,
`|0| = 0` smallest yet last.)  Any lemma "reduceTotal output is magnitude-sorted / pivot-is-min" is a
DEAD lemma; the true no-drag invariant is `SmithSuffixMinRepairInvariant` (B3), not sortedness. -/

/-- **Pivot-is-min AS a `smithReduceTotal` postcondition** — the (refuted) claim that the reduceTotal
diagonal is magnitude-nondecreasing: every pivot's magnitude bounds every later diagonal's. -/
def SmithReduceTotalPivotMinStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    ∀ pivotIndex laterIndex, pivotIndex ≤ laterIndex → laterIndex < Nat.min height width →
      ((matrix.applyOperations (smithReduceTotal matrix height width).operations).diagonalEntryAt
          pivotIndex).natAbs
        ≤ ((matrix.applyOperations (smithReduceTotal matrix height width).operations).diagonalEntryAt
          laterIndex).natAbs

set_option maxRecDepth 16384 in
/-- **Pivot-is-min is REFUTED on-path** — `SmithReduceTotalPivotMinStatement` is FALSE:
`smithReduceTotal` reduces `[[4,0,0],[0,6,10],[0,15,0]]` (rectangular) to `diag(4, 1, 150)`, whose
`|d_0| = 4 ≤ |d_1| = 1` is false.  So the round's pivot-is-min premise is a DEAD lemma; the discharge of
JAM 1 cannot go through it.  The two reduceTotal diagonals compute by defeq (`4` and `1`); `4 ≤ 1` is
absurd. -/
theorem smithReduceTotalPivotMinIsRefuted : ¬ SmithReduceTotalPivotMinStatement := by
  intro isPivotMin
  have pivotMinAt := isPivotMin { rows := [[4, 0, 0], [0, 6, 10], [0, 15, 0]] } 3 3
    ⟨rfl, rfl, rfl, rfl, True.intro⟩ 0 1 (by decide) (by decide)
  exact absurd (id (α := (4 : Nat) ≤ 1) pivotMinAt) (by decide)

/-! ## The strict-`<` / row-major tie-no-drag atom (H2-SMITH r14, B2)

`smithScanRowMinAbs` updates its running best on STRICT `<` only (`entry.natAbs < bestMag`), scanning
row-major with the pivot cross before deeper rows.  So on an equal magnitude (a tie) — or a larger one —
the earlier-scanned best is KEPT, not displaced.  This is the load-bearing tie-resolution the recon flags
(the self-attack): in the repair cross, an untouched later entry equal to the pivot's fold pair cannot
drag the best away, so a tie never strands residue.  Two atoms — the single-step position-keep and its
segment fold — witness it, refutation-immune (pure `if`/`match` reduction), STRUCTURAL. -/

/-- **Single-step tie keeps the best POSITION** — the row-scan update leaves its `some` best unchanged
(the position, stronger than the magnitude bound `smithScanRowUpdateSomeBound` gives) whenever the scanned
entry is not strictly smaller: the strict-`<` guard means a tie never replaces the earlier best. -/
theorem smithScanRowUpdateTieKeepsPosition (matrix : IntMatrix)
    (rowIndex colStart bestRow bestCol : Nat)
    (notStrictlySmaller : ¬ ((matrix.entryAt rowIndex colStart).natAbs
        < (matrix.entryAt bestRow bestCol).natAbs)) :
    (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
     else if (matrix.entryAt rowIndex colStart).natAbs
            < (matrix.entryAt bestRow bestCol).natAbs then some (rowIndex, colStart)
     else some (bestRow, bestCol)) = some (bestRow, bestCol) :=
  match (matrix.entryAt rowIndex colStart).natAbs == 0 with
  | true => rfl
  | false => (if_neg (fun isTrueEq => Bool.noConfusion isTrueEq)).trans (if_neg notStrictlySmaller)

/-- **Segment tie keeps the best** — scanning a whole column window from a `some` best returns that SAME
best position when no scanned entry is strictly smaller than it: ties and larger magnitudes never drag
the best away (a strictly-smaller entry is REQUIRED to move it).  Structural on the column count,
threading the single-step tie-keep with the shifted no-smaller hypothesis. -/
theorem smithScanRowMinAbsTieKeepsBest (matrix : IntMatrix) (rowIndex bestRow bestCol : Nat) :
    ∀ (colCount colStart : Nat),
      (∀ offset, offset < colCount →
        ¬ ((matrix.entryAt rowIndex (colStart + offset)).natAbs
            < (matrix.entryAt bestRow bestCol).natAbs)) →
      smithScanRowMinAbs matrix rowIndex colCount colStart (some (bestRow, bestCol))
        = some (bestRow, bestCol)
  | 0, _, _ => rfl
  | colCount + 1, colStart, noSmaller => by
      have hereNotSmaller : ¬ ((matrix.entryAt rowIndex colStart).natAbs
          < (matrix.entryAt bestRow bestCol).natAbs) := by
        have here := noSmaller 0 (Nat.zero_lt_succ colCount)
        rwa [Nat.add_zero] at here
      show smithScanRowMinAbs matrix rowIndex colCount (colStart + 1)
          (if (matrix.entryAt rowIndex colStart).natAbs == 0 then some (bestRow, bestCol)
           else if (matrix.entryAt rowIndex colStart).natAbs
                  < (matrix.entryAt bestRow bestCol).natAbs then some (rowIndex, colStart)
           else some (bestRow, bestCol)) = some (bestRow, bestCol)
      rw [smithScanRowUpdateTieKeepsPosition matrix rowIndex colStart bestRow bestCol hereNotSmaller]
      exact smithScanRowMinAbsTieKeepsBest matrix rowIndex bestRow bestCol colCount (colStart + 1)
        (fun offset offsetLt => by
          have later := noSmaller (offset + 1) (Nat.succ_lt_succ offsetLt)
          rw [Nat.add_succ, ← Nat.succ_add] at later
          exact later)

/-! ## The true no-drag reachability invariant, correctly stated (H2-SMITH r14, B3)

The r13 wall `SmithRepairStepSettlesStatement` is REFUTABLE over the bare `SmithPrefixSettled` frame
(POLE-B `[[2,0,0],[0,60,0],[0,60,-60]]` at pivot 1) and the round's pivot-is-min premise is REFUTED
outright (B1).  Strengthening to bare window-diagonality does NOT fix it either: the drag input
`diag(30,20,12)` is window-diagonal yet its pivot-0 position-repair drags `60` to `(2,1)`
(`pos0Sweep = [[2,0,0],[0,60,0],[0,60,-60]]`, eval-confirmed).  The CORRECT no-drag node is the SUFFIX-MIN
reachability invariant: the fold operand pair carries the suffix minimum, so no untouched later diagonal
is strictly smaller.

`SmithSuffixMinRepairInvariant` names it.  Two probes fix its meaning: it EXCLUDES the drag input
(`smithSuffixMinDragInputViolates` — `diag(30,20,12)` violates it, `min(30,20)=20 > d_2=12`), and it
HOLDS on the min-abs-presorted repair input the driver actually feeds
(`smithSuffixMinReduceTotalOnPathProbe` — the fixed point `diag(2,3)` satisfies it).  So it is a genuine,
non-vacuous strengthening that the POLE-B/pivot-is-min refuters do NOT satisfy — the correctly-stated
r14 wall replacing the refuted premise.

**Honest scope.**  This is the CORRECTLY-STATED wall, not its discharge.  Establishing the invariant
along the driver path (that `smithReduceTotal` presorts to it and the repair preserves it) is the deep
POLE-A elimination-correctness node; deriving window-diagonal preservation FROM it is the same wall.
Both remain open; `SmithReduceFullDriverStatement` stays UNINHABITED; NO flip. -/

/-- **The true no-drag reachability invariant (correctly stated; NOT the refuted pivot-is-min, NOT bare
window-diagonality)** — at every pivot `p`, whenever the repair's first-non-dividing later diagonal
search returns some `q`, the fold operand pair `(d_p, d_q)` carries the SUFFIX MINIMUM: its smaller
magnitude bounds every later diagonal `d_r` (`p < r`).  Exactly the drag-free condition (drag iff some
later `|d_r| < min(|d_p|,|d_q|)`). -/
def SmithSuffixMinRepairInvariant (matrix : IntMatrix) (height width : Nat) : Prop :=
  ∀ pivotIndex, pivotIndex < Nat.min height width →
    ∀ firstNonDividing,
      smithFindNonDividingLaterDiagonal matrix pivotIndex
          (Nat.min height width - (pivotIndex + 1)) (pivotIndex + 1) = some firstNonDividing →
      ∀ laterIndex, pivotIndex < laterIndex → laterIndex < Nat.min height width →
        Nat.min (matrix.diagonalEntryAt pivotIndex).natAbs
            (matrix.diagonalEntryAt firstNonDividing).natAbs
          ≤ (matrix.diagonalEntryAt laterIndex).natAbs

set_option maxRecDepth 4096 in
/-- **The drag input violates the invariant** — `diag(30, 20, 12)` refutes
`SmithSuffixMinRepairInvariant`: at `p = 0` the search returns `q = 1` (`30 ∤ 20`), the fold pair min is
`min(30, 20) = 20`, yet the untouched `d_2 = 12 < 20`.  So the invariant correctly EXCLUDES the exact
input whose single position-repair strands `60` at `(2, 1)` (JAM 1's refuter) — it is a genuine
strengthening, not vacuous. -/
theorem smithSuffixMinDragInputViolates :
    ¬ SmithSuffixMinRepairInvariant { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 3 3 := by
  intro invariant
  have bound := invariant 0 (by decide) 1 rfl 2 (by decide) (by decide)
  exact absurd (id (α := (20 : Nat) ≤ 12) bound) (by decide)

set_option maxRecDepth 4096 in
/-- **On-path witness: the invariant holds on a reduceTotal fixed point** — `diag(2, 3)` (which
`smithReduceTotal` leaves unchanged) SATISFIES `SmithSuffixMinRepairInvariant`: at `p = 0` the search
returns `q = 1` and `min(2, 3) = 2 ≤ d_1 = 3`; at `p = 1` the search is empty (vacuous).  Confirms the
invariant holds on the min-abs-presorted repair input the driver feeds, where the refuted pivot-is-min
does not. -/
theorem smithSuffixMinReduceTotalOnPathProbe :
    SmithSuffixMinRepairInvariant { rows := [[2, 0], [0, 3]] } 2 2 := by
  intro pivotIndex pivotLt firstNonDividing findEq laterIndex pivotLtLater laterLt
  have laterLt2 : laterIndex < 2 := Nat.lt_of_lt_of_le laterLt (natMinLeLeft 2 2)
  have pivotLt2 : pivotIndex < 2 := Nat.lt_of_lt_of_le pivotLt (natMinLeLeft 2 2)
  match pivotIndex, pivotLt2 with
  | 0, _ =>
      have fndEq : firstNonDividing = 1 :=
        (Option.some.inj (findEq : some 1 = some firstNonDividing)).symm
      subst fndEq
      match laterIndex, pivotLtLater, laterLt2 with
      | 0, gtZero, _ => exact absurd gtZero (Nat.lt_irrefl 0)
      | 1, _, _ => decide
      | _ + 2, _, ltTwo =>
          exact Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc ltTwo)))
  | 1, _ =>
      have contra : (none : Option Nat) = some firstNonDividing := findEq
      contradiction
  | _ + 2, ltTwo =>
      exact Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc ltTwo)))

/-! ## The repair-transport arc ledger (H2-SMITH r14, B5, #2137) — the round's honest state; NO flip

**#2137 state.**  `SmithNormalForm.SmithReduceFullDriverStatement` is UNINHABITED (no flip).  Its
totality rests on EXACTLY the two r13 residuals `{SmithRepairStepSettlesStatement (JAM 1),
repairChainHolds (JAM 2)}` (`smithReduceFullDriverOfRepairStepAndChain`, re-verified this round).  The
r14 round PROBED the sorted step-settles premise, found it REFUTED on-path, and shipped the honest
unconditional atoms + the correctly-stated wall; NEITHER jam closed, NO flip.

**The refutation (B1).**  The round's premise "prove pivot-is-min as a reduceTotal postcondition" is
FALSE: `reduceTotal([[4,0,0],[0,6,10],[0,15,0]]) = diag(4, 1, 150)`, `d_0 = 4 > d_1 = 1`
(`smithReduceTotalPivotMinIsRefuted`).  So JAM 1 has NO sorted shortcut; the r13 node stays the wall.

**Shipped this round (r14), all independently axiom-free (`#print axioms` = "no axioms").**

  * B1 — `SmithReduceTotalPivotMinStatement` + `smithReduceTotalPivotMinIsRefuted`: the round's
    pivot-is-min premise recorded as a permanent regression (a DEAD lemma).
  * B2 — `smithScanRowUpdateTieKeepsPosition` + `smithScanRowMinAbsTieKeepsBest`: the strict-`<` /
    row-major tie-no-drag atom (a tie never displaces the earlier-scanned best — the load-bearing
    tie-resolution).
  * B3 — `SmithSuffixMinRepairInvariant` (the correctly-stated no-drag wall) + `smithSuffixMinDragInputViolates`
    (excludes the drag input `diag(30,20,12)`) + `smithSuffixMinReduceTotalOnPathProbe` (holds on the
    on-path fixed point `diag(2,3)`) — a genuine, non-vacuous strengthening the refuters violate.
  * B4 — `applyOperationsPreservesEntriesDivisible` (+ its per-op/per-transform tower and the three
    `Int` atoms): the ideal / Z-combination stability core — whole-matrix `d`-divisibility preserved by
    every unimodular word (the JAM 2-PRESERVE half).

**Still owed toward `SmithReduceFullDriverStatement` (UNINHABITED; NO flip) — the two named jams, now
better-isolated.**

  * JAM 1 (window-diagonal).  Old node: `SmithRepairStepSettlesStatement` (refutable over the bare frame).
    NEW correctly-stated node: `SmithSuffixMinRepairInvariant` holding along the driver path (the drag
    input violates it, the on-path fixed point satisfies it) — the deep POLE-A no-drag /
    elimination-correctness.  Neither pivot-is-min (B1-refuted) nor bare window-diagonality (drag-input
    counterexample) is a free-standing bypass.
  * JAM 2 (the chain `repairChainHolds`).  PRESERVE half now UNCONDITIONAL (B4:
    `applyOperationsPreservesEntriesDivisible` — a fixed `d` dividing all entries survives every word).
    ESTABLISH half (that position `p`'s exit gives `d_p ∣` the whole sub-block, for `p > 0` where `d_p`
    does not divide the earlier pivots) re-imports JAM 1's window-diagonality — coupled, not orthogonal.

**Discipline honoured.**  Every UNCONDITIONAL r14 atom (B2 tie-keep, B4 ideal-preservation) is quantified
over an arbitrary scanned segment / arbitrary word and concludes "the best is kept" / "divisibility
survives" — never "re-diagonalized".  Every refutation (B1, B3 drag) is a permanent regression on a
LITERAL matrix.  The invariant (B3) is a DEFINITION naming the wall, pinned by two probes to be
non-vacuous and refuter-excluding — NOT a discharge.  `SmithReduceFullDriverStatement` is NOT flipped. -/

/-! ## The suffix-min repair invariant is REFUTED on the genuine driver path
    (H2-SMITH r15, B1/B3 — the PROBE outcome; permanent regression; NO flip)

r14 shipped `SmithSuffixMinRepairInvariant` as the correctly-stated no-drag wall and pinned it
non-vacuous on a 2x2 fixed point (`smithSuffixMinReduceTotalOnPathProbe`).  r15 PROBED it on a GENUINE
multi-pivot driver path (matrix 21 of the 35-matrix battery) and REFUTES it in two ways: the
divisibility repair does NOT preserve the invariant (R2, the crux), and the def is over-strong on
rank-deficient inputs (R1, below).  Both are permanent LITERAL regressions; the driver lands valid
Smith normal form on these inputs ANYWAY (the counterweights below), so the invariant names the WRONG
carrier and is retired to a DEAD node alongside `SmithReduceTotalPivotMinStatement`.

**The witness matrix.**  `smithSuffixMinRefuterInput` = diag(60, 90, 150, 210, 105); `smithReduceTotal`
min-abs-sorts it to `smithSuffixMinRepairWitness` = diag(60, 90, 105, 150, 210)
(`smithSuffixMinRepairWitnessMatchesReduceTotalDiagonal`, a genuine driver-path matrix, per-diagonal by
defeq).  The witness SATISFIES the suffix-min invariant at every pivot
(`smithSuffixMinRepairWitnessEstablishes`): the min-abs presort makes the index-first non-dividing
`d_q` a valid suffix-minimum operand.

**PRESERVATION FAILS (R2, the crux).**  Firing ONE pivot-0 position repair on the witness lands
`gcd`-descended pivots but lcm-INFLATES the non-dividing fold operands (60, 90 land gcd 15 at the pivot,
lcm residues -180, -210 down the diagonal) while the entries the pivot ALREADY divided (150, 210 —
skipped by `smithFindNonDividingLaterDiagonal`) stay put.  The result diag(15, -180, -210, 150, 210)
VIOLATES the invariant at pivot 1: the index-first non-dividing later diagonal is `q = 2` (value -210),
giving `min(|-180|, |-210|) = 180`, yet the untouched magnitude-smaller `d_3 = 150 < 180` sits below it.
So the repair does NOT preserve the invariant — `smithSuffixMinRepairDoesNotPreserve`.

**Why the r14 conjecture is wrong.**  The r14 footer conjectured "reduceTotal presorts to it AND the
repair preserves it".  The presort half holds (the establishment); the PRESERVE half is FALSE — the
selection is by INDEX not magnitude, and the pivot-p repair's lcm inflation destroys the min-abs order
the reduceTotal search guaranteed.  Correctness is carried NOT by a suffix-min precondition on the fold
pair but by the cascade's own min-abs re-search (which pulls the smaller 150 to the pivot on the very
next cascade step) — the true no-drag carrier, and the r16+ node (`SmithRepairStepSettlesStatement` via
cascade-min-abs-landing).  `SmithReduceFullDriverStatement` stays UNINHABITED; NO flip. -/

/-- The probe's matrix-21 INPUT: diag(60, 90, 150, 210, 105).  `smithReduceTotal` min-abs-sorts it to
the suffix-min witness `smithSuffixMinRepairWitness`. -/
def smithSuffixMinRefuterInput : IntMatrix :=
  { rows := [[60, 0, 0, 0, 0], [0, 90, 0, 0, 0], [0, 0, 150, 0, 0], [0, 0, 0, 210, 0],
      [0, 0, 0, 0, 105]] }

/-- The min-abs-presorted `smithReduceTotal` output diag(60, 90, 105, 150, 210) — the genuine repair
input on the driver path, and the witness on which the suffix-min invariant holds yet the repair breaks
it. -/
def smithSuffixMinRepairWitness : IntMatrix :=
  { rows := [[60, 0, 0, 0, 0], [0, 90, 0, 0, 0], [0, 0, 105, 0, 0], [0, 0, 0, 150, 0],
      [0, 0, 0, 0, 210]] }

set_option maxRecDepth 65536 in
/-- **The witness satisfies the suffix-min invariant** — at every pivot `p` of the min-abs-presorted
diag(60, 90, 105, 150, 210), the index-first non-dividing later diagonal is `p + 1`, and
`min(|d_p|, |d_{p+1}|) = |d_p|` bounds every later diagonal (the diagonal is magnitude-nondecreasing on
this rank-full presort).  Pinned non-vacuous: the antecedent of the (refuted) preservation node holds
here, so the refutation is genuine, not a vacuous strike on an unsatisfiable premise. -/
theorem smithSuffixMinRepairWitnessEstablishes :
    SmithSuffixMinRepairInvariant smithSuffixMinRepairWitness 5 5 := by
  intro pivotIndex pivotLt firstNonDividing findEq laterIndex pivotLtLater laterLt
  have laterLt5 : laterIndex < 5 := Nat.lt_of_lt_of_le laterLt (natMinLeLeft 5 5)
  have pivotLt5 : pivotIndex < 5 := Nat.lt_of_lt_of_le pivotLt (natMinLeLeft 5 5)
  match pivotIndex, pivotLt5 with
  | 0, _ =>
      have fnd : firstNonDividing = 1 :=
        (Option.some.inj (findEq : some 1 = some firstNonDividing)).symm
      subst fnd
      match laterIndex, pivotLtLater, laterLt5 with
      | 0, gt, _ => exact absurd gt (by decide)
      | 1, _, _ => decide
      | 2, _, _ => decide
      | 3, _, _ => decide
      | 4, _, _ => decide
      | _ + 5, _, lt5 =>
          exact Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc lt5))))))
  | 1, _ =>
      have fnd : firstNonDividing = 2 :=
        (Option.some.inj (findEq : some 2 = some firstNonDividing)).symm
      subst fnd
      match laterIndex, pivotLtLater, laterLt5 with
      | 0, gt, _ => exact absurd gt (by decide)
      | 1, gt, _ => exact absurd gt (by decide)
      | 2, _, _ => decide
      | 3, _, _ => decide
      | 4, _, _ => decide
      | _ + 5, _, lt5 =>
          exact Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc lt5))))))
  | 2, _ =>
      have fnd : firstNonDividing = 3 :=
        (Option.some.inj (findEq : some 3 = some firstNonDividing)).symm
      subst fnd
      match laterIndex, pivotLtLater, laterLt5 with
      | 0, gt, _ => exact absurd gt (by decide)
      | 1, gt, _ => exact absurd gt (by decide)
      | 2, gt, _ => exact absurd gt (by decide)
      | 3, _, _ => decide
      | 4, _, _ => decide
      | _ + 5, _, lt5 =>
          exact Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc lt5))))))
  | 3, _ =>
      have fnd : firstNonDividing = 4 :=
        (Option.some.inj (findEq : some 4 = some firstNonDividing)).symm
      subst fnd
      match laterIndex, pivotLtLater, laterLt5 with
      | 0, gt, _ => exact absurd gt (by decide)
      | 1, gt, _ => exact absurd gt (by decide)
      | 2, gt, _ => exact absurd gt (by decide)
      | 3, gt, _ => exact absurd gt (by decide)
      | 4, _, _ => decide
      | _ + 5, _, lt5 =>
          exact Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc lt5))))))
  | 4, _ =>
      have contra : (none : Option Nat) = some firstNonDividing := findEq
      contradiction
  | _ + 5, lt5 =>
      exact Nat.noConfusion (natEqZeroOfLeZero
        (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
          (natLeOfSuccLeSucc (natLeOfSuccLeSucc lt5))))))

set_option maxRecDepth 65536 in
/-- **The witness is the genuine `smithReduceTotal` output** — per diagonal position, the cross-clearing
driver reduces `smithSuffixMinRefuterInput` (diag(60, 90, 150, 210, 105)) to the min-abs-presorted
witness diag(60, 90, 105, 150, 210) by defeq.  Anchors the refutation on the ACTUAL driver path: the
witness is not an arbitrary literal but the matrix the divisibility-repair phase is fed. -/
theorem smithSuffixMinRepairWitnessMatchesReduceTotalDiagonal
    (position : Nat) (inRange : position < 5) :
    (smithSuffixMinRefuterInput.applyOperations
        (smithReduceTotal smithSuffixMinRefuterInput 5 5).operations).diagonalEntryAt position
      = smithSuffixMinRepairWitness.diagonalEntryAt position :=
  match position, inRange with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, lt5 =>
      Nat.noConfusion (natEqZeroOfLeZero
        (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
          (natLeOfSuccLeSucc (natLeOfSuccLeSucc lt5))))))

/-- **The (refuted) preservation node** — the claim that one pivot-0 divisibility-repair position sweep
PRESERVES the suffix-min invariant along the driver path (the frame advance `p -> p + 1` the r14 footer
conjectured).  This is the deeper node the round probes; `smithSuffixMinRepairDoesNotPreserve` refutes
it, with `smithSuffixMinRepairWitnessEstablishes` pinning the antecedent non-vacuous. -/
def SmithSuffixMinRepairPreservesStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    SmithSuffixMinRepairInvariant matrix height width →
    SmithSuffixMinRepairInvariant
      (matrix.applyOperations
        (smithRepairPositionSweep (smithMinorAbsSum matrix 0 height width) matrix 0 height width))
      height width

set_option maxRecDepth 65536 in
/-- **The divisibility repair does NOT preserve the suffix-min invariant (R2, the crux)** —
`SmithSuffixMinRepairPreservesStatement` is FALSE.  Applying it to the rectangular witness diag(60, 90,
105, 150, 210) (which SATISFIES the invariant, `smithSuffixMinRepairWitnessEstablishes`) would give the
invariant on the pivot-0 repair output diag(15, -180, -210, 150, 210); but at pivot 1 that output has
first-non-dividing `q = 2`, fold-pair magnitude `min(180, 210) = 180`, and the untouched later
`d_3 = 150 < 180` — a genuine-nonzero suffix-min violation the pivot-p lcm inflation created.  So the
repair does not preserve the invariant: it names the wrong carrier, and JAM 1 has no suffix-min
shortcut.  `SmithReduceFullDriverStatement` stays UNINHABITED; NO flip. -/
theorem smithSuffixMinRepairDoesNotPreserve : ¬ SmithSuffixMinRepairPreservesStatement := by
  intro preserves
  have m1Invariant := preserves smithSuffixMinRepairWitness 5 5
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩ smithSuffixMinRepairWitnessEstablishes
  have bound := m1Invariant 1 (by decide) 2 rfl 3 (by decide) (by decide)
  exact absurd (id (α := (180 : Nat) ≤ 150) bound) (by decide)

/-! ## The establishment fails on rank-deficient inputs (H2-SMITH r15, B2/R1 — permanent regression)

Beyond the preservation failure (B1), the suffix-min invariant is over-strong on rank-deficient
inputs.  `SmithSuffixMinRepairInvariant` quantifies its suffix bound over ALL later diagonals INCLUDING
zeros; on a reduceTotal output with a trailing zero (a rank-deficient input — zeros come last), the
static establishment fails outright: `min(|d_p|, |d_q|) <= |d_last| = 0` is false for any nonzero pivot
pair.  So the invariant cannot even be ESTABLISHED as a reduceTotal postcondition without excluding
zeros — a second permanent LITERAL regression witnessing the def names the wrong carrier (the driver's
`d_p | 0` chain closure, not a suffix-min bound, handles trailing zeros).  This is a FALSE ALARM for the
drag purpose (a 0 cannot be dragged into a smaller nonzero residue), but it refutes the invariant as
written. -/

set_option maxRecDepth 4096 in
/-- **The invariant fails on a rank-deficient diagonal (R1)** — `diag(4, 1, 150, 0)` refutes
`SmithSuffixMinRepairInvariant`: at `p = 0` the search returns `q = 1` (`4 ∤ 1`), the fold pair min is
`min(4, 1) = 1`, yet the trailing `d_3 = 0 < 1`.  The def's quantification over all later diagonals
(zeros included) makes it FALSE on any rank-deficient reduceTotal output, so it is not establishable
without excluding zeros — the establishment floor is hit as a refutation, not a discharge. -/
theorem smithSuffixMinEstablishFailsOnRankDeficient :
    ¬ SmithSuffixMinRepairInvariant
        { rows := [[4, 0, 0, 0], [0, 1, 0, 0], [0, 0, 150, 0], [0, 0, 0, 0]] } 4 4 := by
  intro invariant
  have bound := invariant 0 (by decide) 1 rfl 3 (by decide) (by decide)
  exact absurd (id (α := (1 : Nat) ≤ 0) bound) (by decide)

/-! ## The positive counterweight: the invariant is NOT necessary (H2-SMITH r15, B1-positive)

The suffix-min invariant is neither on-path-preserved (B1) nor establishable (B2) — yet the augmented
driver `smithReduceFull` lands VALID Smith normal form on the very inputs that break the r14 premises.
Two representatives of the 35-matrix probe battery (both eval-confirmed valid SNF for all 35), both the
EXACT r14 refuters, kernel-closed here by the driver-to-literal defeq (the `IsSmithNormalFormWithin`
off-diagonal/nonnegative fields decided on the literal output, the invariant-factor chain hand-built):
the drag input `diag(30, 20, 12)` (the r14 `smithSuffixMinDragInputViolates` witness) and the unsorted
minor `[[4,0,0],[0,6,10],[0,15,0]]` (the r14 `smithReduceTotalPivotMinIsRefuted` witness).  Correctness
is carried by the cascade min-abs re-search, NOT by any suffix-min precondition — so the refuted
invariant names a non-load-bearing property. -/

/-- The r14 drag input diag(30, 20, 12) — `smithSuffixMinDragInputViolates`'s witness. -/
def smithDragDiagonalInput : IntMatrix := { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] }

set_option maxRecDepth 200000 in
/-- **The drag input still reduces to valid Smith normal form** — the augmented driver reduces
`diag(30, 20, 12)` (which VIOLATES the suffix-min invariant, `smithSuffixMinDragInputViolates`) to
`diag(2, 60, 60)` (chain `2 | 60 | 60`, product `7200 = 30 * 20 * 12`, gcd `2`).  Witnesses that the
refuted invariant is NOT necessary for driver correctness. -/
theorem smithDragDiagonalDriverReducesToSmithForm :
    (smithDragDiagonalInput.applyOperations
        (smithReduceFull smithDragDiagonalInput 3 3).operations).IsSmithNormalFormWithin 3 3 :=
  show ({ rows := [[2, 0, 0], [0, 60, 0], [0, 0, 60]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0, 0], [0, 60, 0], [0, 0, 60]] } : IntMatrix).entryAt rowIndex colIndex = 0 :=
        by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨30, rfl⟩
      | 1, _ => ⟨1, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

/-- The r14 unsorted minor `[[4,0,0],[0,6,10],[0,15,0]]` — `smithReduceTotalPivotMinIsRefuted`'s witness
(reduceTotal leaves the unsorted diagonal `diag(4, 1, 150)`). -/
def smithUnsortedMinorInput : IntMatrix := { rows := [[4, 0, 0], [0, 6, 10], [0, 15, 0]] }

set_option maxRecDepth 200000 in
/-- **The unsorted minor still reduces to valid Smith normal form** — the augmented driver reduces
`[[4,0,0],[0,6,10],[0,15,0]]` (whose reduceTotal output `diag(4, 1, 150)` refuted pivot-is-min,
`smithReduceTotalPivotMinIsRefuted`) to `diag(1, 2, 300)` (chain `1 | 2 | 300`, product
`600 = |det|`, gcd `1`).  The divisibility-repair phase repairs the coprime/unsorted diagonal to the
full invariant-factor chain despite the suffix-min invariant being refuted. -/
theorem smithUnsortedMinorDriverReducesToSmithForm :
    (smithUnsortedMinorInput.applyOperations
        (smithReduceFull smithUnsortedMinorInput 3 3).operations).IsSmithNormalFormWithin 3 3 :=
  show ({ rows := [[1, 0, 0], [0, 2, 0], [0, 0, 300]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0], [0, 2, 0], [0, 0, 300]] } : IntMatrix).entryAt rowIndex colIndex = 0 :=
        by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨2, rfl⟩
      | 1, _ => ⟨150, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

/-! ## The repair-transport arc ledger (H2-SMITH r15, B4/B5, #2137) — the round's honest state; NO flip

**#2137 state.**  `SmithNormalForm.SmithReduceFullDriverStatement` is UNINHABITED (no flip).  Its
totality rests on EXACTLY the two r13 residuals `{SmithRepairStepSettlesStatement (JAM 1),
repairChainHolds (JAM 2)}` via `smithReduceFullDriverOfRepairStepAndChain` (re-verified this round,
UNCHANGED — it composes `repairWindowDiagHoldsOfRepairStep` onto `smithReduceFullDriverOfRepairInvariants`
and rests on the two named jams verbatim).  The r15 round PROBED the r14 suffix-min wall on a genuine
multi-pivot driver path, found it REFUTED (both preservation and establishment), and shipped the honest
double refutation + the positive counterweight; NEITHER jam closed, NO flip.

**The refutation (B1/B3, R2 — the crux).**  The r14 footer's conjecture "`smithReduceTotal` presorts to
[the suffix-min invariant] AND the repair preserves it" is FALSE on its PRESERVE half.  On the genuine
witness `smithReduceTotal(diag(60,90,150,210,105)) = diag(60,90,105,150,210)`
(`smithSuffixMinRepairWitnessMatchesReduceTotalDiagonal`) the invariant HOLDS
(`smithSuffixMinRepairWitnessEstablishes`), yet one pivot-0 divisibility-repair sweep lands
`diag(15,-180,-210,150,210)`, which VIOLATES it at pivot 1 (`min(180,210)=180 > untouched d_3=150`) —
the pivot-p lcm inflation drags a magnitude-smaller ALREADY-divided entry below the index-first fold
pair.  So `SmithSuffixMinRepairPreservesStatement` is refuted (`smithSuffixMinRepairDoesNotPreserve`).

**The refutation (B2, R1).**  The invariant is also over-strong on rank-deficient inputs:
`diag(4,1,150,0)` refutes it (`smithSuffixMinEstablishFailsOnRankDeficient` —
`min(4,1)=1 > trailing d_3=0`), since the def quantifies its suffix bound over all later diagonals
including zeros.  So it is not even ESTABLISHABLE as a reduceTotal postcondition without excluding
zeros.  (This is a false alarm for the drag purpose — a `0` cannot be dragged into a smaller nonzero
residue — but it refutes the invariant AS WRITTEN.)

**The discharge wiring (B4).**  The r14/r15 hope was an adapter
`SmithSuffixMinRepairInvariant (along the driver path) -> SmithRepairStepSettlesStatement`.  That adapter
is IMPOSSIBLE: its antecedent is FALSE on the driver path (the repair does not preserve the invariant,
R2), so no total function can produce it.  The discharge wiring is therefore UNCHANGED from r13
(`smithReduceFullDriverOfRepairStepAndChain` unmodified); the suffix-min invariant supplies ZERO
shortcut, and `SmithRepairStepSettlesStatement` stays the JAM-1 wall — to be discharged by the cascade
min-abs-landing (the TRUE no-drag carrier, r16+), not by any suffix-min node.

**The JAM-2-ESTABLISH re-audit (B4, conjunct map).**  JAM 2 =
`{applyOperationsPreservesEntriesDivisible (PRESERVE — landed r14, UNCONDITIONAL: a fixed `d` dividing
all entries survives every unimodular word, refutation-immune) + `d_p |` sub-block (ESTABLISH — position
`p`'s exit gives `d_p |` the whole sub-block for `p > 0`, re-importing JAM 1's window-diagonality —
COUPLED, not orthogonal)}`.  This round's probe does NOT touch JAM 2's coupling — it kills a proposed
JAM-1 BYPASS (the suffix-min node), not the chain.  UNCHANGED from r14.

**Shipped this round (r15), all independently axiom-free (`#print axioms` = "no axioms").**

  * B1/B3 — `smithSuffixMinRefuterInput` / `smithSuffixMinRepairWitness` (the witness pair),
    `smithSuffixMinRepairWitnessEstablishes` (the invariant holds on the witness, pinning non-vacuity),
    `smithSuffixMinRepairWitnessMatchesReduceTotalDiagonal` (the witness is the genuine reduceTotal
    output, per-diagonal by defeq), `SmithSuffixMinRepairPreservesStatement` (the deeper node) +
    `smithSuffixMinRepairDoesNotPreserve` (the preservation refutation, R2).
  * B2 — `smithSuffixMinEstablishFailsOnRankDeficient` (the rank-deficient establishment refutation, R1).
  * B1-positive — `smithDragDiagonalDriverReducesToSmithForm` (`diag(30,20,12) -> diag(2,60,60)`) +
    `smithUnsortedMinorDriverReducesToSmithForm` (`[[4,0,0],[0,6,10],[0,15,0]] -> diag(1,2,300)`): the
    exact r14 refuters still land valid Smith normal form — the invariant is NOT necessary.

**Dead-node retirement.**  `SmithSuffixMinRepairInvariant` joins `SmithReduceTotalPivotMinStatement` as a
DEAD node (both refuted).  It keeps its name and meaning (the r14 docstrings verbatim-intact); its r14
pins are now understood as VACUOUS FOR PRESERVATION — `smithSuffixMinReduceTotalOnPathProbe` (`diag(2,3)`)
is a 2x2 with no multi-pivot evolution, and matrix 21 (5x5) is the first genuine test, which refutes.
`smithSuffixMinDragInputViolates` remains a correct exclusion probe.

**Still owed toward `SmithReduceFullDriverStatement` (UNINHABITED; NO flip) — the two named jams.**

  * JAM 1 (window-diagonal).  NAMED NODE: `SmithRepairStepSettlesStatement` (refutable over the bare
    `SmithPrefixSettled` frame; POLE-B).  NO suffix-min bypass (this round's double refutation).  The
    true discharge is the cascade min-abs-landing elimination-correctness — "the re-fired
    `smithCascadeSweep` lands the sub-minor's min-abs at the pivot AND re-diagonalizes the sub-block"
    (r13 `smithRepairFoldCascadeReachesCrossClear` gives the cross-clear half; the missing half is
    min-abs-at-pivot + sub-block-diagonal).  The r16+ wall.
  * JAM 2 (the chain `repairChainHolds`).  PRESERVE UNCONDITIONAL (r14); ESTABLISH coupled to JAM 1.

`SmithReduceFullDriverStatement` is NOT flipped. -/

/-! ## The driver totality target is REFUTED — the r16 escalation (H2-SMITH r16, B1, #2137); NO flip

r13/r14/r15 carried `SmithNormalForm.SmithReduceFullDriverStatement` as an UNINHABITED wall pending a
JAM-1 discharge.  The r16 round probed the cascade-landing carrier on a 24-matrix curated battery plus a
400-matrix random stress, found NO surviving window-diagonal carrier, and escalated to a KERNEL-CONFIRMED
REFUTATION OF THE DRIVER ITSELF: `SmithReduceFullDriverStatement` is FALSE, not walled.

**The witness.**  `smithReduceFullDriverRefuterInput` = diag(10, 10, 6, 9), a rectangular 4x4.
`smithReduceTotal` min-abs-sorts it to diag(6, 9, 10, 10); the top-down single-pass divisibility repair
then pushes an lcm-inflated residue down the diagonal and its sub-block permutation strands a NONZERO
off-diagonal at (3, 2):
  `smithReduceFull(diag(10,10,6,9))` |> applyOperations = `[[1,0,0,0],[0,2,0,0],[0,0,30,0],[0,0,30,90]]`
(machine-checked `#eval`).  This is the exact r13-refuter shape `[[2,0,0],[0,60,0],[0,60,-60]]` arising on
a genuine reduceTotal-min-abs-sorted path — falsifying the r13/r14/r15 hope that the presort forbids the
drag.

**Non-vacuity, both directions.**  (1) the witness IS rectangular
(`smithReduceFullDriverRefuterInputIsRectangular`), so the statement's hypothesis is satisfiable; (2) the
stranded off-diagonal IS nonzero (`smithReduceFullStrandsOffDiagonalWitness` pins it at 30), so
`IsSmithNormalFormWithin.offDiagonalVanishes 3 2` is genuinely violated.  The 4x4 is the SMALLEST
refuting input; its full-driver defeq reduces at `maxRecDepth 200000` (~1.2 s), under the r15 5x5
stack-overflow line. -/

/-- The r16 refuter INPUT: diag(10, 10, 6, 9), a rectangular 4x4.  `smithReduceTotal` min-abs-sorts it to
diag(6, 9, 10, 10) (machine-checked `#eval`), the smallest driver-path input whose single-pass
divisibility repair strands a nonzero off-diagonal in a later pivot's cross-strip. -/
def smithReduceFullDriverRefuterInput : IntMatrix :=
  { rows := [[10, 0, 0, 0], [0, 10, 0, 0], [0, 0, 6, 0], [0, 0, 0, 9]] }

/-- **Non-vacuity, direction 1 (rectangular)** — the refuter input is rectangular, so the driver
totality statement's hypothesis is satisfiable and `smithReduceFullDriverIsRefuted` exercises the genuine
conclusion, not a vacuous strike on an ill-formed input. -/
theorem smithReduceFullDriverRefuterInputIsRectangular :
    smithReduceFullDriverRefuterInput.IsRectangular 4 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, True.intro⟩

set_option maxRecDepth 200000 in
/-- **Non-vacuity, direction 2 (nonzero strand)** — the augmented driver reduces diag(10, 10, 6, 9) to
`[[1,0,0,0],[0,2,0,0],[0,0,30,0],[0,0,30,90]]` (machine-checked `#eval`), leaving `entryAt 3 2 = 30` OFF
the diagonal.  Pins the violated off-diagonal by defeq (`= 30`), so the refutation below is not a vacuous
`0 = 0`; this is the exact r13-refuter cross-strip on a genuine reduceTotal-min-abs-sorted path. -/
theorem smithReduceFullStrandsOffDiagonalWitness :
    (smithReduceFullDriverRefuterInput.applyOperations
        (smithReduceFull smithReduceFullDriverRefuterInput 4 4).operations).entryAt 3 2 = 30 := by
  decide

set_option maxRecDepth 200000 in
/-- **The fourth refutation: `SmithReduceFullDriverStatement` is FALSE** — if the driver were total, the
rectangular `smithReduceFullDriverRefuterInput` would give `offDiagonalVanishes 3 2 : entryAt 3 2 = 0`;
but the driver strands `entryAt 3 2 = 30` (`smithReduceFullStrandsOffDiagonalWitness`).  So
`smithReduceFull` produces non-Smith-normal-form output on a rectangular integer matrix, and the
total-correctness Prop is a permanent NEGATIVE regression.  `SmithReduceFullDriverStatement` verbatim
UNTOUCHED; NO flip (there is no positive inhabitant to flip). -/
theorem smithReduceFullDriverIsRefuted : ¬ SmithReduceFullDriverStatement := by
  intro isDriverTotal
  have offDiagonalVanishesAt32 :=
    (isDriverTotal smithReduceFullDriverRefuterInput 4 4
        smithReduceFullDriverRefuterInputIsRectangular).offDiagonalVanishes 3 2
      (by decide) (by decide) (by decide)
  exact absurd offDiagonalVanishesAt32 (by decide)

/-! ## The JAM-1 wall ledger, RETRACTED to a driver refutation (H2-SMITH r16, B2/B3/B5, #2137); NO flip

**#2137 state — driver-totality, exact.**  `SmithNormalForm.SmithReduceFullDriverStatement` is REFUTED
(FALSE), witnessed by `smithReduceFullDriverIsRefuted` on the rectangular `diag(10, 10, 6, 9)`.  The r13
totality assembly `smithReduceFullDriverOfRepairStepAndChain` (UNCHANGED, re-verified) still rests on the
two named jams `{SmithRepairStepSettlesStatement (JAM 1), repairChainHolds (JAM 2)}` — but that assembly
is now moot AS A ROUTE TO TRUTH: since the global Prop is false, NO precondition can rescue it, and
neither jam can be discharged into a total driver.  The r13/r14/r15 "uninhabited wall pending JAM-1
discharge" framing is RETRACTED.

**The four dead candidates + their refuters.**  Every window-diagonal carrier for JAM 1 is refuted:

  1. pivot-is-min (r14 `SmithReduceTotalPivotMinStatement`) — DEAD via `smithReduceTotalPivotMinIsRefuted`
     (`reduceTotal([[4,0,0],[0,6,10],[0,15,0]]) = diag(4,1,150)`, `d_0=4 > d_1=1`).
  2. suffix-min (r15 `SmithSuffixMinRepairInvariant` / `SmithSuffixMinRepairPreservesStatement`) — DEAD
     via `smithSuffixMinRepairDoesNotPreserve` (the pivot-0 repair of diag(60,90,105,150,210) breaks the
     min-abs order) and `smithSuffixMinEstablishFailsOnRankDeficient` (over-strong on trailing zeros).
  3. frame-advance (`SmithRepairStepSettlesStatement` over `SmithPrefixSettled` — the JAM-1 node itself) —
     DEAD: it survives the r16 24-matrix curated battery (the frame at `p+1` does not constrain the
     sub-block the drag lands in) but the 400-matrix random stress breaks it 4x, and the global refutation
     moots it outright.
  4. per-step window-diagonality (whole-matrix or `(p+1..)`-suffix) — DEAD: the complete pivot-1 repair of
     the drag family diag(15,-180,-210,150,210) strands `-1050` at (3,2), a later pivot's cross-strip, so
     full window-diagonality cannot be a per-step invariant.

  The r15 footer named "the cascade min-abs-landing" as the r16 carrier; the r16 probe found it is NOT a
  distinct carrier — the per-position repair `smithRepairPositionSweep` ALREADY includes the re-cascade and
  the fold-then-re-cascade loop `SmithSuffixMinRepairPreservesStatement` measured, so it supplies no new
  precondition.  There is no surviving carrier.

**The elimination-correctness route (an algorithmic bug, not a proof wall).**  `smithReduceFull` composes
`diagOps ++ repairOps ++ signOps` with `repairOps = smithDivisibilityRepairSweep`; the per-pivot cross-clear
inside `smithRepairPositionSweep` fires only when `smithFindNonDividingLaterDiagonal` returns `some` — a
pivot whose diagonal already divides all its successors is SKIPPED.  When an earlier pivot's push-down
lcm-inflates a residue into such a later-pivot cross-strip (here `30 | 90`, so pivot 2 is skipped), the
strand is never re-cleared and survives to the output.  The MINIMAL fix is to run the divisibility-repair
cross-clear UNCONDITIONALLY at each pivot (drop the `smithFindNonDividingLaterDiagonal`-nonempty gate), OR
append a second `smithReduceTotal` cross-clear pass after `repairOps`.  `smithReduceTotal`'s
window-diagonalization (r12 `smithReduceTotalSweepDiagonalizes`) and the JAM-2 PRESERVE core (r14
`applyOperationsPreservesEntriesDivisible`) are CORRECT and untouched — the bug is isolated to the
divisibility-REPAIR phase's gating.

**Park-and-pivot (B3).**  This arc PARKS: the total-correctness goal `SmithReduceFullDriverStatement` is
retired as a refuted Prop, not a wall.  The named lane successor is WP-ENDO #2255, which must inherit
EITHER a FIXED driver (unconditional per-pivot cross-clear, or a second `smithReduceTotal` pass) OR the
per-input-only correctness contract (the B4 battery: `smithReduceFull` as an untrusted producer whose only
guarantee is the kernel-checked literal reductions).  It must NOT inherit a "discharge JAM 1" mandate —
there is nothing to discharge into.

**The named jams, mooted (B5).**  Both jams keep their names and exact goals; both are now unreachable:

  * JAM 1 — `SmithRepairStepSettlesStatement`: exact goal = the frame advance `SmithPrefixSettled p ->
    SmithPrefixSettled (p+1)` after a complete position sweep; refutable over the bare frame (POLE-B) and
    mooted by the global refutation.
  * JAM 2 — `repairChainHolds`: PRESERVE half UNCONDITIONAL (r14 `applyOperationsPreservesEntriesDivisible`),
    ESTABLISH half coupled to JAM 1; mooted with it.

**Counterweights (B4).**  The historical refuters still land VALID Smith normal form (untouched, re-pinned
axiom-free this round): `smithDragDiagonalDriverReducesToSmithForm` (`diag(30,20,12) -> diag(2,60,60)`) and
`smithUnsortedMinorDriverReducesToSmithForm` (`[[4,0,0],[0,6,10],[0,15,0]] -> diag(1,2,300)`).  The bug is
input-specific, not a total failure.

**Discipline honoured.**  The refutation is a permanent regression on a LITERAL rectangular matrix,
non-vacuity pinned both directions (rectangular input + nonzero strand).  No carrier is fabricated; the
statement is NOT flipped.  The 3x3-scale defeq ceiling is respected: the 4x4 witness is the SMALLEST
genuine refuter and its full-driver defeq reduces at `maxRecDepth 200000`; the 5x5 companion
diag(-9,-7,-6,4,9) (stranding (4,3)=36 / (3,4)=126) is recorded in prose only, NOT built, to stay under
the r15 5x5 stack-overflow line. -/

/-! ## The corrected driver lands the refuter — the B4 battery (H2-SMITH r17, B1, #2261)

`smithReduceComplete` (the UNCONDITIONAL-clearing driver, SmithNormalForm §"The CORRECTED driver") lands
VALID Smith normal form on exactly the input `smithReduceFull` was REFUTED on, plus the historical
counterweights, plus a RECTANGULAR member.  Each closed against its literal Smith normal form by defeq
(the driver computes to the literal; off-diagonal + nonnegativity via `decide` on the LITERAL, chain via
hand-built witnesses).  The honest pair juxtaposed: `smithReduceFullDriverIsRefuted` (the OLD driver
strands `entryAt 3 2 = 30`) versus `smithReduceCompleteDriverRefuterLandsSmithForm` (the corrected driver
lands `diag(1, 2, 30, 90)`) — a genuine flip on the SMALLEST refuting input.

The r15 5x5 whole-driver-defeq stack line is respected: the largest member is the 4x4 refuter, reducing at
`maxRecDepth 200000`; the 5x5 companion is recorded in prose only (SmithNormalForm/ledger), NOT built. -/

set_option maxRecDepth 200000 in
/-- **The refuter LANDS — the corrected driver on `diag(10, 10, 6, 9)`.**  Where `smithReduceFull` strands
`entryAt 3 2 = 30` (`smithReduceFullStrandsOffDiagonalWitness`), `smithReduceComplete` reduces the same
rectangular `diag(10, 10, 6, 9)` to the clean Smith normal form `diag(1, 2, 30, 90)`: the `none`-branch
cross-clear at the SKIPPED pivot 2 (`30 | 90`) clears the stranded residue.  All three fields hold — the
chain `1 | 2 | 30 | 90` is the hand-built `2 = 1*2`, `30 = 2*15`, `90 = 30*3`.  The direct positive flip of
`smithReduceFullDriverIsRefuted`. -/
theorem smithReduceCompleteDriverRefuterLandsSmithForm :
    (smithReduceFullDriverRefuterInput.applyOperations
        (smithReduceComplete smithReduceFullDriverRefuterInput 4 4).operations).IsSmithNormalFormWithin
      4 4 :=
  show ({ rows := [[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 30, 0], [0, 0, 0, 90]] } : IntMatrix).IsSmithNormalFormWithin
      4 4 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 4 → ∀ colIndex, colIndex < 4 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 30, 0], [0, 0, 0, 90]] } : IntMatrix).entryAt
              rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨2, rfl⟩
      | 1, _ => ⟨15, rfl⟩
      | 2, _ => ⟨3, rfl⟩
      | _ + 3, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
                (natLeOfSuccLeSucc isBeyondDiagonal))))) }

set_option maxRecDepth 16384 in
/-- **Counterweight — the drag `diag(30, 20, 12)` through the corrected driver.**  Re-lands `diag(2, 60, 60)`
(the r14/r15 `smithReduceFull` counterweight, now through `smithReduceComplete`).  Chain `2 | 60 | 60`. -/
theorem smithDragDiagonalByCompleteDriver :
    (({ rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } : IntMatrix).applyOperations
        (smithReduceComplete { rows := [[30, 0, 0], [0, 20, 0], [0, 0, 12]] } 3 3).operations).IsSmithNormalFormWithin
      3 3 :=
  show ({ rows := [[2, 0, 0], [0, 60, 0], [0, 0, 60]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0, 0], [0, 60, 0], [0, 0, 60]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨30, rfl⟩
      | 1, _ => ⟨1, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

set_option maxRecDepth 16384 in
/-- **Counterweight — the unsorted minor `[[4,0,0],[0,6,10],[0,15,0]]` through the corrected driver.**
Re-lands `diag(1, 2, 300)` (the r14/r15 counterweight).  Chain `1 | 2 | 300`. -/
theorem smithUnsortedMinorByCompleteDriver :
    (({ rows := [[4, 0, 0], [0, 6, 10], [0, 15, 0]] } : IntMatrix).applyOperations
        (smithReduceComplete { rows := [[4, 0, 0], [0, 6, 10], [0, 15, 0]] } 3 3).operations).IsSmithNormalFormWithin
      3 3 :=
  show ({ rows := [[1, 0, 0], [0, 2, 0], [0, 0, 300]] } : IntMatrix).IsSmithNormalFormWithin 3 3 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 3 → ∀ colIndex, colIndex < 3 →
          rowIndex ≠ colIndex →
          ({ rows := [[1, 0, 0], [0, 2, 0], [0, 0, 300]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨2, rfl⟩
      | 1, _ => ⟨150, rfl⟩
      | _ + 2, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero
              (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal)))) }

set_option maxRecDepth 16384 in
/-- **Counterweight — the coprime `diag(2, 3)` through the corrected driver.**  Lands `diag(1, 6)` (the
`smithReduceTotal` cross-only driver leaves `2 ∤ 3` in place; the repair Euclid-clears to `gcd = 1`, `lcm = 6`).
Chain `1 | 6`. -/
theorem smithCoprimeByCompleteDriver :
    (({ rows := [[2, 0], [0, 3]] } : IntMatrix).applyOperations
        (smithReduceComplete { rows := [[2, 0], [0, 3]] } 2 2).operations).IsSmithNormalFormWithin 2 2 :=
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

set_option maxRecDepth 16384 in
/-- **The RECTANGULAR member — the `2 x 4` `[[6,0,0,0],[0,10,0,0]]` through the corrected driver.**  Lands
`[[2,0,0,0],[0,30,0,0]]`: `Nat.min 2 4 = 2` diagonal positions, `gcd(6, 10) = 2` at pivot 0, `lcm = 30`
pushed to pivot 1.  Confirms the fix preserves rectangular handling (the guard `pivotIndex + 1 ≤ Nat.min`
is untouched).  Chain `2 | 30` on the single interior step. -/
theorem smithRectangularByCompleteDriver :
    (({ rows := [[6, 0, 0, 0], [0, 10, 0, 0]] } : IntMatrix).applyOperations
        (smithReduceComplete { rows := [[6, 0, 0, 0], [0, 10, 0, 0]] } 2 4).operations).IsSmithNormalFormWithin
      2 4 :=
  show ({ rows := [[2, 0, 0, 0], [0, 30, 0, 0]] } : IntMatrix).IsSmithNormalFormWithin 2 4 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 4 →
          rowIndex ≠ colIndex →
          ({ rows := [[2, 0, 0, 0], [0, 30, 0, 0]] } : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨15, rfl⟩
      | _ + 1, isBeyondDiagonal =>
          Nat.noConfusion
            (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyondDiagonal))) }

/-! ## PHASE B — the corrected repair-sweep transport to the two named crux residuals (H2-SMITH r17, B3, #2261)

The r13 conditional-transport structure (`smithDivisibilityRepairSweepSettlesThroughPivots` /
`…Diagonalizes` / `repairWindowDiagHoldsOfRepairStep` / `smithReduceFullDriverOfRepairStepAndChain`) is
MIRRORED VERBATIM for the UNCONDITIONAL-clearing repair sweep.  The named single-step
`SmithRepairClearingStepSettles` is the clearing analogue of the r13 `SmithRepairStepSettlesStatement`.
Composed with the Phase-C assembly (`smithReduceCompleteDriverOfRepairInvariants`), this moves
`SmithReduceCompleteDriverStatement` onto EXACTLY the two conjuncts `{SmithRepairClearingStepSettles,
repairChainHolds}` — the r17 crux, over an EMPIRICALLY-CORRECT driver (the B4 battery).

**The crux flip vs. r13.**  The r13 single-step `SmithRepairStepSettlesStatement` was REFUTABLE over the bare
`SmithPrefixSettled` frame (POLE-B: `[[2,0,0],[0,60,0],[0,60,-60]]` at pivot 1, where the OLD sweep's `find`
returns `none` and does NOTHING — the frame is not advanced).  `SmithRepairClearingStepSettles` over the SAME
frame is TRUE: route (i)'s `none`-branch fires the standalone `smithCascadeSweep`, whose frame advance is the
shipped hypothesis-free `smithCascadeStepSettlesThroughPivot`.  So the wall the r13-r16 rounds could not
discharge (the POLE-B refutation) is GONE for the corrected driver — the two residuals are TRUE, not
refutable.

**Honest scope — the two residuals still owed (r18).**

  * `SmithRepairClearingStepSettles` (Phase B-diag).  Exact goal: for rectangular `matrix` with
    `SmithPrefixSettled matrix pivotIndex`, prove `SmithPrefixSettled (matrix.applyOperations
    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex …) matrix pivotIndex …))
    (pivotIndex + 1)`.  Discharge PATH (route (i), TRUE): the `none`-branch is `smithCascadeStepSettlesThroughPivot`
    directly; the `some` fold+cascade LOOP preserves the frame at `pivotIndex` (`smithRepairFoldPreservesSettledFrame`
    + cascade low-low/band preservers) and terminates at a `none`-branch (fuel adequacy: `smithRepairDecreasesPivotSize`
    strictly drops the pivot each genuine fold — the r13 `smithRepairPositionSweepReachesCrossClear` template for the
    Bool cross-clear, lifted to the frame).  The remaining WORK is that loop-frame-preservation + termination lift.
  * `repairChainHolds` (Phase B-chain).  Exact goal: `SmithChainPrefix` of the clearing-repair output at
    `Nat.min height width`.  PRESERVE half UNCONDITIONAL and shipped (`applyOperationsPreservesEntriesDivisible`:
    a fixed `d` dividing all entries survives every later word, and the cross-clear at pivot `p` is confined to
    rows/cols `≥ p` by locality, so it never disturbs a settled `d_earlier`, `earlier < p`).  ESTABLISH half (the
    r18 promotion): find-loop exit at pivot `p` (`smithFindNonDividingLaterDiagonal … = none` ⟹ `d_p` divides every
    later DIAGONAL) combined with window-diagonality of the sub-block (off-diagonals are `0`, trivially divisible)
    promotes to `MatrixEntriesDivisibleBy d_p` over the whole sub-block `≥ p+1`; `d_{p-1} | d_p` closes via PRESERVE
    (the landed gcd is a Z-combination).

`SmithReduceCompleteDriverStatement` is thus reduced to two NAMED residuals, both TRUE over the corrected
driver — a material advance past the r16 "driver is FALSE, no surviving carrier".  NO fabricated discharge. -/

/-- **The named single-step for the corrected repair sweep** — the clearing analogue of the r13
`SmithRepairStepSettlesStatement`: the clearing per-position repair advances the settled frame
`pivotIndex → pivotIndex + 1`.  TRUE over the bare `SmithPrefixSettled` frame (unlike the refutable r13
statement) because route (i)'s `none`-branch fires the frame-advancing `smithCascadeSweep`.  The r17 crux
residual (Phase B-diag), pending the loop-frame-preservation + fuel-termination lift (r18). -/
def SmithRepairClearingStepSettles : Prop :=
  ∀ (matrix : IntMatrix) (pivotIndex height width : Nat),
    matrix.IsRectangular height width →
    pivotIndex < height → pivotIndex < width →
    SmithPrefixSettled matrix pivotIndex height width →
    SmithPrefixSettled
      (matrix.applyOperations
        (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width)
          matrix pivotIndex height width))
      (pivotIndex + 1) height width

/-- **The clearing repair sweep advances the settled frame (conditional)** — GIVEN the named single-step
`SmithRepairClearingStepSettles`, the whole `smithDivisibilityRepairSweepClearing outerFuel` reaches
`SmithPrefixSettled` at `Nat.min (Nat.min height width) (pivotIndex + outerFuel)`.  Verbatim mirror of the
r13 `smithDivisibilityRepairSweepSettlesThroughPivots` — structural on `outerFuel`, the guard-true step
chains the hypothesised single-step with the IH on the advanced pivot, the base / guard-false branches drop
to the capped frame by `smithPrefixSettledMonotone`. -/
theorem smithDivisibilityRepairSweepClearingSettlesThroughPivots
    (stepSettles : SmithRepairClearingStepSettles) :
    ∀ (outerFuel : Nat) (matrix : IntMatrix) (pivotIndex height width : Nat),
      matrix.IsRectangular height width →
      SmithPrefixSettled matrix pivotIndex height width →
      SmithPrefixSettled
        (matrix.applyOperations
          (smithDivisibilityRepairSweepClearing outerFuel matrix pivotIndex height width))
        (Nat.min (Nat.min height width) (pivotIndex + outerFuel)) height width := by
  intro outerFuel
  induction outerFuel with
  | zero =>
      intro matrix pivotIndex height width _ isSettled
      exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
        (natMinLeRight (Nat.min height width) (pivotIndex + 0))
  | succ outerFuel ih =>
      intro matrix pivotIndex height width isRect isSettled
      show SmithPrefixSettled (matrix.applyOperations
          (if pivotIndex + 1 ≤ Nat.min height width then
            smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                height width
              ++ smithDivisibilityRepairSweepClearing outerFuel
                  (matrix.applyOperations
                    (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width) matrix
                      pivotIndex height width))
                  (pivotIndex + 1) height width
           else []))
        (Nat.min (Nat.min height width) (pivotIndex + (outerFuel + 1))) height width
      split
      · rename_i guardTrue
        have pivotRowInRange : pivotIndex < height := natLeTrans guardTrue (natMinLeLeft height width)
        have pivotColInRange : pivotIndex < width := natLeTrans guardTrue (natMinLeRight height width)
        have afterPositionSettled :
            SmithPrefixSettled
              (matrix.applyOperations
                (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width))
              (pivotIndex + 1) height width :=
          stepSettles matrix pivotIndex height width isRect pivotRowInRange pivotColInRange isSettled
        have afterPositionRect :
            (matrix.applyOperations
                (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
                  height width)).IsRectangular height width :=
          applyOperationsPreservesRectangular _ matrix isRect
        have ihResult := ih
          (matrix.applyOperations
            (smithRepairPositionSweepClearing (smithMinorAbsSum matrix pivotIndex height width) matrix pivotIndex
              height width))
          (pivotIndex + 1) height width afterPositionRect afterPositionSettled
        rw [Nat.succ_add pivotIndex outerFuel] at ihResult
        rw [applyOperationsAppend]
        exact ihResult
      · rename_i guardFalse
        have minLePivot : Nat.min height width ≤ pivotIndex :=
          Nat.le_of_lt_succ (Nat.not_le.1 guardFalse)
        exact smithPrefixSettledMonotone matrix pivotIndex height width _ isSettled
          (Nat.le_trans (natMinLeLeft (Nat.min height width) (pivotIndex + (outerFuel + 1))) minLePivot)

/-- **The clearing repair output is window-diagonal (conditional)** — GIVEN the single-step
`SmithRepairClearingStepSettles`, every off-diagonal cell of the window vanishes after
`smithDivisibilityRepairSweepClearing (Nat.min height width) matrix 0`.  Verbatim mirror of the r13
`smithDivisibilityRepairSweepDiagonalizes`: instantiate the fold at the driver start (`pivotIndex = 0`,
vacuous base), collapse the cap (`natMinSelf`), read off with `smithPrefixSettledAtMinIsWindowDiagonal`. -/
theorem smithDivisibilityRepairSweepClearingDiagonalizes
    (stepSettles : SmithRepairClearingStepSettles)
    (matrix : IntMatrix) (height width : Nat)
    (isRect : matrix.IsRectangular height width) :
    ∀ rowIndex colIndex, rowIndex < height → colIndex < width → rowIndex ≠ colIndex →
      (matrix.applyOperations
          (smithDivisibilityRepairSweepClearing (Nat.min height width) matrix 0 height width)).entryAt rowIndex colIndex
        = 0 := by
  have generalResult :=
    smithDivisibilityRepairSweepClearingSettlesThroughPivots stepSettles (Nat.min height width) matrix 0 height width
      isRect (smithPrefixSettledZero matrix height width)
  rw [Nat.zero_add, natMinSelf] at generalResult
  exact smithPrefixSettledAtMinIsWindowDiagonal
    (matrix.applyOperations (smithDivisibilityRepairSweepClearing (Nat.min height width) matrix 0 height width))
    height width generalResult

/-- **The verbatim `repairWindowDiagHolds` hypothesis for the corrected driver, conditional on the single-step**
— GIVEN `SmithRepairClearingStepSettles`, the corrected driver's repair output is window-diagonal at `0`, for
every rectangular `matrix`.  EXACTLY the shape of `smithReduceCompleteDriverOfRepairInvariants`'s first
hypothesis; the r13 `repairWindowDiagHoldsOfRepairStep` mirror over the clearing sweep. -/
theorem repairWindowDiagHoldsOfClearingStep (stepSettles : SmithRepairClearingStepSettles) :
    ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      IsWindowDiagonal
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithDivisibilityRepairSweepClearing (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        0 height width := by
  intro matrix height width isRect
  intro rowIndex colIndex _zeroLeRow rowLtHeight _zeroLeCol colLtWidth rowNeCol
  exact smithDivisibilityRepairSweepClearingDiagonalizes stepSettles
    (matrix.applyOperations (smithReduceTotal matrix height width).operations) height width
    (applyOperationsPreservesRectangular (smithReduceTotal matrix height width).operations matrix isRect)
    rowIndex colIndex rowLtHeight colLtWidth rowNeCol

/-- **The corrected driver totality from the single-step and the chain** — GIVEN
`SmithRepairClearingStepSettles` AND the invariant-factor chain `repairChainHolds` (verbatim the
`smithReduceCompleteDriverOfRepairInvariants` type), `SmithReduceCompleteDriverStatement` follows.  The
window-diagonal hypothesis is supplied by `repairWindowDiagHoldsOfClearingStep`, moving the whole totality onto
EXACTLY `{SmithRepairClearingStepSettles, repairChainHolds}` — both TRUE over the corrected (empirically-clean)
driver, pending the r18 loop-lift + ESTABLISH promotion.  The r13 `smithReduceFullDriverOfRepairStepAndChain`
structure, over a driver that LANDS the r16 refuter (not one that is refuted by it). -/
theorem smithReduceCompleteDriverOfClearingStepAndChain
    (stepSettles : SmithRepairClearingStepSettles)
    (repairChainHolds : ∀ (matrix : IntMatrix) (height width : Nat),
      matrix.IsRectangular height width →
      SmithChainPrefix
        ((matrix.applyOperations (smithReduceTotal matrix height width).operations).applyOperations
          (smithDivisibilityRepairSweepClearing (Nat.min height width)
            (matrix.applyOperations (smithReduceTotal matrix height width).operations) 0 height width))
        (Nat.min height width) height width) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfRepairInvariants (repairWindowDiagHoldsOfClearingStep stepSettles) repairChainHolds

/-! ## The corrected-driver arc ledger (H2-SMITH r17, B4/B5, #2261) — the honest pair; a CONDITIONAL flip

**#2261 state, exact.**  Two drivers now coexist, byte-disjoint:

  * `smithReduceFull` — REFUTED.  `smithReduceFullDriverIsRefuted` : `¬ SmithReduceFullDriverStatement`,
    witnessed on the rectangular `diag(10, 10, 6, 9)` (`smithReduceFullStrandsOffDiagonalWitness` pins the
    stranded `entryAt 3 2 = 30`).  UNCHANGED this round (byte-intact, re-verified).
  * `smithReduceComplete` — the CORRECTED driver (route (i): the divisibility-repair cross-clear fires
    UNCONDITIONALLY at each pivot).  `SmithReduceCompleteDriverStatement` is reduced (NOT yet unconditionally
    inhabited) to EXACTLY the two named residuals `{SmithRepairClearingStepSettles, repairChainHolds}` via
    `smithReduceCompleteDriverOfClearingStepAndChain`; Phase A (`smithReduceTotalSweepDiagonalizes`) and
    Phase C (`smithReduceCompleteDiagonalNonneg` + the sign preservers) are DISCHARGED.  The B4 battery pins
    per-input correctness by kernel defeq: `smithReduceCompleteDriverRefuterLandsSmithForm`
    (`diag(10,10,6,9) ↝ diag(1,2,30,90)` — the direct positive flip), the drag / unsorted / coprime
    counterweights, and the RECTANGULAR `2 x 4` member.

**The honest pair.**  On the smallest refuting input the OLD driver strands `30` off-diagonal
(`smithReduceFullDriverIsRefuted`) while the corrected driver lands clean Smith normal form
(`smithReduceCompleteDriverRefuterLandsSmithForm`).  This is a CONDITIONAL flip: the totality Prop is not
unconditionally inhabited, but the r16 verdict "driver is FALSE, no surviving carrier" is superseded by
"corrected driver, empirically clean, totality on two TRUE named residuals".

**The crux flip.**  The r13 window-diagonal single-step `SmithRepairStepSettlesStatement` was REFUTABLE
(POLE-B); its clearing analogue `SmithRepairClearingStepSettles` is TRUE over the SAME bare frame (route
(i)'s `none`-branch = the hypothesis-free `smithCascadeStepSettlesThroughPivot`).  So the r13-r16 wall is
gone; what remains is the r18 lift (the loop-frame-preservation + fuel-termination for Phase B-diag) and the
Phase B-chain ESTABLISH promotion (PRESERVE shipped: `applyOperationsPreservesEntriesDivisible`).

**Discipline.**  Additive only (532 insertions, 0 deletions in the two core files); `smithReduceFull` and its
refutation byte-intact; the certificate API (`SmithReductionCertificate` / `IsSmithNormalFormWithin`,
consumed by Homology through `IntMatrix`) untouched.  Zero-axiom (independent `#print axioms` clean per
public decl).  The 5x5 whole-driver-defeq stack line respected: the largest battery member is the 4x4
refuter at `maxRecDepth 200000`; the 5x5 companion is prose-only, NOT built.  NO fabricated battery pass, NO
fabricated phase discharge. -/

end FX1Poly.ComputerAlgebra
