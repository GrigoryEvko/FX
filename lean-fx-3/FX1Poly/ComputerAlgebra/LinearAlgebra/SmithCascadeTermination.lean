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

**The r10 residual (DESIGN-LOCKED, NOT shipped): the fuel-adequacy induction
`smithCascadeReachesCrossClear`** — a strong induction on `smithCascadeSweep`'s inner fuel that threads
the PIVOT MAGNITUDE (measure = the found min-abs pivot's `natAbs`; NEVER the abs-sum — the fuel is the
STATIC budget `smithMinorAbsSum`, read ONCE at cascade entry, so the r8 transient abs-sum growth is
IRRELEVANT).  With joints (b) and the move swap-entry bridge now shipped, what remains for the recursive
step is the pivot-magnitude PACKAGING plus the ASSEMBLY: (i) a `smithFindMinAbsInMinorFoundInRange` scan
companion (the found position sits in `[pivotIndex, height) × [pivotIndex, width)`, feeding
`smithMoveToPivotEntryOnPivot`'s in-range hypotheses — a structural mirror of the shipped
`…FoundNonzero`); (ii) the sign-phase magnitude bridge (`(afterSign pivot).natAbs = (afterMove
pivot).natAbs`, from the shipped `signNormalizeOpsEntryOnPivotIsSignedInput` since `|-x| = |x|`, then the
shipped `smithClearColumnBelowStepsPreservesRow` carries it through the column clear, and
`signNormalizeOpsEntryOnPivotNonneg` gives nonnegativity) so that `pivotMag = (matrix.entryAt foundRow
foundCol).natAbs = cascadeMeasure matrix ≤ f + 1` and is positive (`smithFindMinAbsInMinorFoundNonzero`);
and (iii) the induction body itself — the `false`-branch bound `cascadeMeasure afterRowClear ≤ f` via
`smithCrossNotClearWitness` → `smithClear{RowRight,ColumnBelow}StepsCrossEntryStrictlyDecreases`
(+ `smithClearRowRightStepsPreservesColumn` for the column segment) → `smithFindMinAbsInMinorBoundsWitness`,
placing the residue witness strictly below `pivotMag ≤ f + 1`.  Every joint is now a NAMED shipped lemma
except (i) and the assembly wiring.  Even a COMPLETE `smithCascadeReachesCrossClear` delivers ONLY the
cross-clear conjunct of obligation (a); the sub-block-stays-diagonal + gcd-divides-folded-operands (iv) +
chain conjuncts feeding `SmithNormalForm`'s `repairWindowDiagHolds` / `repairChainHolds` remain the r10+
wall — so those two surviving repair hypotheses stay UNCLOSED (no flip; `SmithReduceFullDriverStatement`
uninhabited).

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

end FX1Poly.ComputerAlgebra
