import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalReducedEchelon

/-! # LinearAlgebra/RationalMatrixRank — the RANK / pivot-column apparatus over
    the exact `QnfRat` field (WP-PROP-3 keystone)

The `RationalLinearRelations` kit (prefix `ihq`) ships row-space membership
(`IhqMemSpan`), the echelon staircase (`IhqEchelonFrom`), a canonical
echelonizer (`ihqEchelonize`), the reduction engine (`ihqReduceAgainst`) and the
mutual-reduction span decision (`ihqSpanEqB`).  `RationalReducedEchelon` (prefix
`rre`) added leading-1 normalization and reduced the RREF-uniqueness wall to
pivot-SET invariance for dimension >= 2.  This file BUILDS that apparatus.

  * `rmrRank rows := (ihqEchelonize rows).length` — the number of pivots (= the
    number of nonzero echelon rows; `ihqInsertRow` drops dependent/zero rows);
  * `rmrRankLeWidth` — rank <= width (strictly increasing leads bounded by width);
  * `rmrReduceCoeffMissingPivot` — reduction against a row list PRESERVES the
    coefficient at any column that is not a lead of the list, as long as the
    vector vanishes strictly below that column (the pivot-preservation nucleus);
  * `rmrAchievableLeadIsPivot` — **the pivot-column determination theorem**: the
    lead of ANY span member is a lead of the echelon form.  Since this
    characterizes the pivot columns purely by span membership, it is the core of
    pivot-SET invariance;
  * `rmrPivotSetSpanInvariant` — span-equal echelon forms have the same pivot
    columns (both directions of `rmrHasLead`);
  * `rmrLeadDominationLe` / `rmrRankSpanInvariant` — **the dimension theorem**:
    span-equal matrices have equal rank (a strictly-increasing-lead injection
    into the dominating echelon form, symmetrized through `ihqNatLe`
    antisymmetry).

The residual (T3): full byte-level RREF uniqueness (`ihqRrefUniquenessStatement`)
additionally needs that the reduced ROW at each shared pivot is identical — the
back-substituted unit-lead vector is the unique reduced representative of its
coset.  That last row-value step is walled here (`rmrHasRrefRowUniqueness`),
naming the exact unjoined obstruction; T1 (rank) and T2 (pivot set) LAND.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no `List.append`, no `Nat.sub/div/mod/min/max` order lemmas, no
wildcard match arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the small structural `ihqNatLe` kit for the rank bound -/

/-- `ihqNatLe` is monotone under adding a common offset on the right. -/
theorem rmrNatLeAddMonoRight (offset : Nat) :
    (firstValue secondValue : Nat) -> ihqNatLe firstValue secondValue = true ->
    ihqNatLe (firstValue + offset) (secondValue + offset) = true := by
  intro firstValue secondValue hLe
  induction offset with
  | zero => exact hLe
  | succ offsetPred hOffset => exact hOffset

/-- `ihqNatLe` antisymmetry: mutual `<=` on `Nat` collapses to equality. -/
theorem rmrNatLeAntisymm : (firstValue secondValue : Nat) ->
    ihqNatLe firstValue secondValue = true -> ihqNatLe secondValue firstValue = true ->
    firstValue = secondValue
  | 0, 0, _hForward, _hBackward => rfl
  | 0, _secondPred + 1, _hForward, hBackward => Bool.noConfusion hBackward
  | _firstPred + 1, 0, hForward, _hBackward => Bool.noConfusion hForward
  | firstPred + 1, secondPred + 1, hForward, hBackward =>
      congrArg (fun innerValue => innerValue + 1)
        (rmrNatLeAntisymm firstPred secondPred hForward hBackward)

/-- The transitivity of the strict comparator: `a < b < c` gives `a < c`. -/
theorem rmrNatCompareLtTrans (firstValue secondValue thirdValue : Nat)
    (hFirst : ihqNatCompare firstValue secondValue = IhqOrder.isLt)
    (hSecond : ihqNatCompare secondValue thirdValue = IhqOrder.isLt) :
    ihqNatCompare firstValue thirdValue = IhqOrder.isLt := by
  have hFirstLe : ihqNatLe (firstValue + 1) secondValue = true :=
    ihqNatLeSuccOfCompareLt firstValue secondValue hFirst
  have hSecondLe : ihqNatLe (secondValue + 1) thirdValue = true :=
    ihqNatLeSuccOfCompareLt secondValue thirdValue hSecond
  have hSecondWeak : ihqNatLe secondValue thirdValue = true :=
    ihqNatLeTrans secondValue (secondValue + 1) thirdValue
      (ihqNatLeSuccRight secondValue secondValue (ihqNatLeRefl secondValue)) hSecondLe
  exact ihqNatCompareLtOfLeSucc firstValue thirdValue
    (ihqNatLeTrans (firstValue + 1) secondValue thirdValue hFirstLe hSecondWeak)

/-! ## Stage 1 — the rank function and the width bound -/

/-- **RANK** := the number of nonzero rows in the canonical echelon form, i.e.
the number of pivots (`ihqInsertRow` drops all-zero / dependent vectors, so every
echelon row is a genuine pivot row with a strictly increasing lead). -/
def rmrRank (rows : List (List QnfRat)) : Nat := (ihqEchelonize rows).length

/-- The leading position of a nonzero row is strictly inside the row. -/
theorem rmrLeadLtLength : (row : List QnfRat) -> (leadPosition : Nat) ->
    ihqLead row = some leadPosition -> ihqNatLe (leadPosition + 1) row.length = true
  | [], _leadPosition, hLead => nomatch hLead
  | headCoeff :: restCoeffs, leadPosition, hLead => by
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false =>
          rw [ihqLeadConsShape, hBeq] at hLead
          have hZero : leadPosition = 0 := (Option.some.inj hLead).symm
          rw [hZero]
          show ihqNatLe (0 + 1) (restCoeffs.length + 1) = true
          exact ihqNatLeZeroLeft restCoeffs.length
      | true =>
          have hSplit := ihqLeadZeroConsSome headCoeff restCoeffs hBeq leadPosition hLead
          cases hSplit with
          | intro restLead hBoth =>
              rw [hBoth.right]
              show ihqNatLe (restLead + 1 + 1) (restCoeffs.length + 1) = true
              exact rmrLeadLtLength restCoeffs restLead hBoth.left

/-- Length bound for an echelon list of pinned width: the offset plus the row
count never exceeds the width. -/
theorem rmrEchelonLengthBound {width : Nat} : (lowerBound : Nat) ->
    (rows : List (List QnfRat)) -> IhqEchelonFrom lowerBound rows ->
    IhqAllWidth width rows -> ihqNatLe lowerBound width = true ->
    ihqNatLe (lowerBound + rows.length) width = true
  | lowerBound, [], _hEch, _hAll, hBound => hBound
  | lowerBound, headRow :: restRows, hEch, hAll, hBound => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLead hHeadBound hRest =>
          have hLeadLt : ihqNatLe (headLead + 1) width = true := by
            rw [<- hHead]
            exact rmrLeadLtLength headRow headLead hLead
          have hRestBound : ihqNatLe ((headLead + 1) + restRows.length) width = true :=
            rmrEchelonLengthBound (headLead + 1) restRows hRest hRestAll hLeadLt
          have hMono : ihqNatLe (lowerBound + restRows.length) (headLead + restRows.length)
              = true :=
            rmrNatLeAddMonoRight restRows.length lowerBound headLead hHeadBound
          have hMonoSucc :
              ihqNatLe ((lowerBound + restRows.length) + 1) ((headLead + restRows.length) + 1)
                = true := hMono
          have hRestBoundRe : ihqNatLe ((headLead + restRows.length) + 1) width = true := by
            rw [Nat.succ_add headLead restRows.length] at hRestBound
            exact hRestBound
          show ihqNatLe (lowerBound + (restRows.length + 1)) width = true
          exact ihqNatLeTrans ((lowerBound + restRows.length) + 1)
            ((headLead + restRows.length) + 1) width hMonoSucc hRestBoundRe

/-- **T1**: the rank never exceeds the width. -/
theorem rmrRankLeWidth {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : ihqNatLe (rmrRank rows) width = true := by
  have hBound := rmrEchelonLengthBound (width := width) 0 (ihqEchelonize rows)
    (ihqEchelonizeEchelon rows hAll) (ihqEchelonizeWidth rows hAll)
    (ihqNatLeZeroLeft width)
  rw [Nat.zero_add] at hBound
  exact hBound

/-! ## Stage 2 — pivot-column determination (the T2 nucleus)

`ihqReduceAgainst` walks the row list in order.  For a target column `j`:
rows with lead `< j` are SKIPPED (the target vanishes there, by the vanish-below
hypothesis); rows with lead `> j` are zero at column `j` (echelon), so their
elimination never touches it.  If NO row has lead exactly `j`, the target's
coefficient at `j` is invariant through the whole reduction.  This is the engine
behind "the lead of any span member is a pivot column". -/

/-- Self-comparison is `isEq`. -/
theorem rmrNatCompareSelf : (value : Nat) -> ihqNatCompare value value = IhqOrder.isEq
  | 0 => rfl
  | valuePred + 1 => rmrNatCompareSelf valuePred

/-- The coefficient of an elimination step at a column where the pivot row
already vanishes equals the target's coefficient there. -/
theorem rmrElimStepCoeffWhereZero {width : Nat} (vector headRow : List QnfRat)
    (leadPos position : Nat) (hVecLen : vector.length = width)
    (hHeadLen : headRow.length = width)
    (hHeadZero : ihqGetCoeff headRow position = qnfZero) :
    ihqGetCoeff (ihqElimStep vector headRow leadPos) position
      = ihqGetCoeff vector position := by
  show ihqGetCoeff
      (ihqRowAdd (ihqRowScale (ihqElimCoeff vector headRow leadPos) headRow) vector) position
    = ihqGetCoeff vector position
  rw [ihqGetCoeffAdd (ihqRowScale (ihqElimCoeff vector headRow leadPos) headRow) vector
      (by rw [ihqRowScaleLength, hHeadLen, hVecLen]) position,
    ihqGetCoeffScale (ihqElimCoeff vector headRow leadPos) headRow position,
    hHeadZero, grqQnfMulZeroRight, qnfAddZeroLeft]

/-- **THE PIVOT-PRESERVATION NUCLEUS**: reduction against a row list whose leads
all miss `pivotColumn` preserves the vector's coefficient at `pivotColumn`,
provided the vector vanishes strictly below `pivotColumn`. -/
theorem rmrReduceCoeffMissingPivot {width : Nat} :
    (echelonRows : List (List QnfRat)) -> (vector : List QnfRat) -> (pivotColumn : Nat) ->
    IhqAllWidth width echelonRows -> vector.length = width ->
    ((row : List QnfRat) -> IhqRowMem row echelonRows -> ihqLead row ≠ some pivotColumn) ->
    ((belowPosition : Nat) -> ihqNatCompare belowPosition pivotColumn = IhqOrder.isLt ->
      ihqGetCoeff vector belowPosition = qnfZero) ->
    ihqGetCoeff (ihqReduceAgainst echelonRows vector) pivotColumn
      = ihqGetCoeff vector pivotColumn
  | [], _vector, _pivotColumn, _hAll, _hVecLen, _hNoPivot, _hVanish => rfl
  | headRow :: restRows, vector, pivotColumn, hAll, hVecLen, hNoPivot, hVanish => by
      have hHead : headRow.length = width := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hRestNoPivot : (row : List QnfRat) -> IhqRowMem row restRows ->
          ihqLead row ≠ some pivotColumn :=
        fun row hRow => hNoPivot row (IhqRowMem.tail hRow)
      cases hLeadH : ihqLead headRow with
      | none =>
          rw [ihqReduceAgainstConsNone restRows headRow vector hLeadH]
          exact rmrReduceCoeffMissingPivot restRows vector pivotColumn hRestAll hVecLen
            hRestNoPivot hVanish
      | some headLead =>
          have hHeadNe : ihqLead headRow ≠ some pivotColumn :=
            hNoPivot headRow (IhqRowMem.head headRow restRows)
          cases hCompare : ihqNatCompare headLead pivotColumn with
          | isEq =>
              have hEq : headLead = pivotColumn :=
                ihqNatCompareEqImpliesEq headLead pivotColumn hCompare
              rw [hEq] at hLeadH
              exact absurd hLeadH hHeadNe
          | isLt =>
              have hCoeffZero : ihqGetCoeff vector headLead = qnfZero := hVanish headLead hCompare
              rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH
                (ihqQnfBeqZeroTrueOfEqZero hCoeffZero)]
              exact rmrReduceCoeffMissingPivot restRows vector pivotColumn hRestAll hVecLen
                hRestNoPivot hVanish
          | isGt =>
              have hPivotLtLead : ihqNatCompare pivotColumn headLead = IhqOrder.isLt :=
                ihqNatCompareGtFlip headLead pivotColumn hCompare
              cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
              | true =>
                  rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH hCoeff]
                  exact rmrReduceCoeffMissingPivot restRows vector pivotColumn hRestAll hVecLen
                    hRestNoPivot hVanish
              | false =>
                  rw [ihqReduceAgainstConsElim restRows headRow vector headLead hLeadH hCoeff]
                  have hElimLen : (ihqElimStep vector headRow headLead).length = width :=
                    ihqElimStepLength vector headRow headLead hVecLen hHead
                  have hHeadZeroAtPivot : ihqGetCoeff headRow pivotColumn = qnfZero :=
                    ihqLeadCoeffBelowZero headRow headLead pivotColumn hLeadH hPivotLtLead
                  have hElimVanish : (belowPosition : Nat) ->
                      ihqNatCompare belowPosition pivotColumn = IhqOrder.isLt ->
                      ihqGetCoeff (ihqElimStep vector headRow headLead) belowPosition
                        = qnfZero := by
                    intro belowPosition hBelow
                    have hBelowLead : ihqNatCompare belowPosition headLead = IhqOrder.isLt :=
                      rmrNatCompareLtTrans belowPosition pivotColumn headLead hBelow hPivotLtLead
                    have hHeadZeroBelow : ihqGetCoeff headRow belowPosition = qnfZero :=
                      ihqLeadCoeffBelowZero headRow headLead belowPosition hLeadH hBelowLead
                    rw [rmrElimStepCoeffWhereZero vector headRow headLead belowPosition hVecLen
                      hHead hHeadZeroBelow]
                    exact hVanish belowPosition hBelow
                  have hRec := rmrReduceCoeffMissingPivot restRows
                    (ihqElimStep vector headRow headLead) pivotColumn hRestAll hElimLen
                    hRestNoPivot hElimVanish
                  rw [hRec, rmrElimStepCoeffWhereZero vector headRow headLead pivotColumn hVecLen
                    hHead hHeadZeroAtPivot]

/-! ## Stage 3 — the pivot-column predicate and its span characterization -/

/-- Does some row of the list lead at exactly `pivotColumn`? -/
def rmrHasLead : List (List QnfRat) -> Nat -> Bool
  | [], _pivotColumn => false
  | headRow :: restRows, pivotColumn =>
      match ihqLead headRow with
      | none => rmrHasLead restRows pivotColumn
      | some headLead =>
          match ihqNatCompare headLead pivotColumn with
          | IhqOrder.isEq => true
          | IhqOrder.isLt => rmrHasLead restRows pivotColumn
          | IhqOrder.isGt => rmrHasLead restRows pivotColumn

theorem rmrHasLeadConsShape (headRow : List QnfRat) (restRows : List (List QnfRat))
    (pivotColumn : Nat) :
    rmrHasLead (headRow :: restRows) pivotColumn
      = match ihqLead headRow with
        | none => rmrHasLead restRows pivotColumn
        | some headLead =>
            match ihqNatCompare headLead pivotColumn with
            | IhqOrder.isEq => true
            | IhqOrder.isLt => rmrHasLead restRows pivotColumn
            | IhqOrder.isGt => rmrHasLead restRows pivotColumn := rfl

/-- Lead-`none` unfold. -/
theorem rmrHasLeadConsNone (headRow : List QnfRat) (restRows : List (List QnfRat))
    (pivotColumn : Nat) (hLeadH : ihqLead headRow = none) :
    rmrHasLead (headRow :: restRows) pivotColumn = rmrHasLead restRows pivotColumn := by
  rw [rmrHasLeadConsShape, hLeadH]

/-- Lead-`some` unfold: the predicate reduces to the three-way comparison. -/
theorem rmrHasLeadConsSome (headRow : List QnfRat) (restRows : List (List QnfRat))
    (pivotColumn headLead : Nat) (hLeadH : ihqLead headRow = some headLead) :
    rmrHasLead (headRow :: restRows) pivotColumn
      = match ihqNatCompare headLead pivotColumn with
        | IhqOrder.isEq => true
        | IhqOrder.isLt => rmrHasLead restRows pivotColumn
        | IhqOrder.isGt => rmrHasLead restRows pivotColumn := by
  rw [rmrHasLeadConsShape, hLeadH]

/-- If the predicate is `false`, no row leads at `pivotColumn`. -/
theorem rmrHasLeadFalseNoPivot : (rows : List (List QnfRat)) -> (pivotColumn : Nat) ->
    rmrHasLead rows pivotColumn = false ->
    (row : List QnfRat) -> IhqRowMem row rows -> ihqLead row ≠ some pivotColumn
  | [], _pivotColumn, _hFalse, _row, hRow => nomatch hRow
  | headRow :: restRows, pivotColumn, hFalse, row, hRow => by
      intro hRowLead
      cases hLeadH : ihqLead headRow with
      | none =>
          rw [rmrHasLeadConsNone headRow restRows pivotColumn hLeadH] at hFalse
          cases hRow with
          | head => rw [hLeadH] at hRowLead; exact nomatch hRowLead
          | tail hRowRest =>
              exact rmrHasLeadFalseNoPivot restRows pivotColumn hFalse row hRowRest hRowLead
      | some headLead =>
          rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH] at hFalse
          cases hCompare : ihqNatCompare headLead pivotColumn with
          | isEq => rw [hCompare] at hFalse; exact Bool.noConfusion hFalse
          | isLt =>
              rw [hCompare] at hFalse
              cases hRow with
              | head =>
                  rw [hLeadH] at hRowLead
                  have hEq : headLead = pivotColumn := Option.some.inj hRowLead
                  rw [hEq, rmrNatCompareSelf pivotColumn] at hCompare
                  exact IhqOrder.noConfusion hCompare
              | tail hRowRest =>
                  exact rmrHasLeadFalseNoPivot restRows pivotColumn hFalse row hRowRest hRowLead
          | isGt =>
              rw [hCompare] at hFalse
              cases hRow with
              | head =>
                  rw [hLeadH] at hRowLead
                  have hEq : headLead = pivotColumn := Option.some.inj hRowLead
                  rw [hEq, rmrNatCompareSelf pivotColumn] at hCompare
                  exact IhqOrder.noConfusion hCompare
              | tail hRowRest =>
                  exact rmrHasLeadFalseNoPivot restRows pivotColumn hFalse row hRowRest hRowLead

/-- If the predicate is `true`, some member row leads at `pivotColumn`. -/
theorem rmrHasLeadTrueMember : (rows : List (List QnfRat)) -> (pivotColumn : Nat) ->
    rmrHasLead rows pivotColumn = true ->
    Exists fun row => IhqRowMem row rows /\ ihqLead row = some pivotColumn
  | [], _pivotColumn, hTrue => Bool.noConfusion hTrue
  | headRow :: restRows, pivotColumn, hTrue => by
      cases hLeadH : ihqLead headRow with
      | none =>
          rw [rmrHasLeadConsNone headRow restRows pivotColumn hLeadH] at hTrue
          have hRest := rmrHasLeadTrueMember restRows pivotColumn hTrue
          cases hRest with
          | intro row hBoth =>
              exact Exists.intro row (And.intro (IhqRowMem.tail hBoth.left) hBoth.right)
      | some headLead =>
          rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH] at hTrue
          cases hCompare : ihqNatCompare headLead pivotColumn with
          | isEq =>
              have hEq : headLead = pivotColumn :=
                ihqNatCompareEqImpliesEq headLead pivotColumn hCompare
              refine Exists.intro headRow (And.intro (IhqRowMem.head headRow restRows) ?_)
              rw [hLeadH, hEq]
          | isLt =>
              rw [hCompare] at hTrue
              have hRest := rmrHasLeadTrueMember restRows pivotColumn hTrue
              cases hRest with
              | intro row hBoth =>
                  exact Exists.intro row (And.intro (IhqRowMem.tail hBoth.left) hBoth.right)
          | isGt =>
              rw [hCompare] at hTrue
              have hRest := rmrHasLeadTrueMember restRows pivotColumn hTrue
              cases hRest with
              | intro row hBoth =>
                  exact Exists.intro row (And.intro (IhqRowMem.tail hBoth.left) hBoth.right)

/-- **THE PIVOT-COLUMN DETERMINATION THEOREM (T2 core)**: the lead of ANY span
member of an echelon form is a pivot column of that form.  Because the pivot
columns are thus characterized purely by span membership, they are a span
invariant. -/
theorem rmrAchievableLeadIsPivot {width lowerBound : Nat}
    (echelonRows : List (List QnfRat)) (vector : List QnfRat) (pivotColumn : Nat)
    (hAll : IhqAllWidth width echelonRows)
    (hEch : IhqEchelonFrom lowerBound echelonRows)
    (hMem : IhqMemSpan width echelonRows vector)
    (hLead : ihqLead vector = some pivotColumn) :
    rmrHasLead echelonRows pivotColumn = true := by
  cases hHas : rmrHasLead echelonRows pivotColumn with
  | true => rfl
  | false =>
      have hVecLen : vector.length = width := ihqMemSpanWidth hAll hMem
      have hNoPivot := rmrHasLeadFalseNoPivot echelonRows pivotColumn hHas
      have hVanish : (belowPosition : Nat) ->
          ihqNatCompare belowPosition pivotColumn = IhqOrder.isLt ->
          ihqGetCoeff vector belowPosition = qnfZero :=
        fun belowPosition hBelow =>
          ihqLeadCoeffBelowZero vector pivotColumn belowPosition hLead hBelow
      have hPreserve := rmrReduceCoeffMissingPivot echelonRows vector pivotColumn hAll hVecLen
        hNoPivot hVanish
      have hReduceZero : ihqAreAllCoeffsZero (ihqReduceAgainst echelonRows vector) = true :=
        ihqReduceAgainstComplete echelonRows vector hAll hEch hMem
      have hCoeffJZero : ihqGetCoeff (ihqReduceAgainst echelonRows vector) pivotColumn = qnfZero :=
        ihqAreAllCoeffsZeroGetCoeff (ihqReduceAgainst echelonRows vector) hReduceZero pivotColumn
      have hVecJZero : ihqGetCoeff vector pivotColumn = qnfZero := hPreserve.symm.trans hCoeffJZero
      have hVecJNe : ihqGetCoeff vector pivotColumn ≠ qnfZero :=
        ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse vector pivotColumn hLead)
      exact absurd hVecJZero hVecJNe

/-- **T2 (pivot-SET invariance)**: two echelon forms with equal row space have
exactly the same pivot columns. -/
theorem rmrPivotSetSpanInvariant {width lbA lbB : Nat}
    (rowsA rowsB : List (List QnfRat))
    (hAllA : IhqAllWidth width rowsA) (hAllB : IhqAllWidth width rowsB)
    (hEchA : IhqEchelonFrom lbA rowsA) (hEchB : IhqEchelonFrom lbB rowsB)
    (hSpanEq : (vector : List QnfRat) ->
      (IhqMemSpan width rowsA vector <-> IhqMemSpan width rowsB vector))
    (pivotColumn : Nat) :
    rmrHasLead rowsA pivotColumn = true <-> rmrHasLead rowsB pivotColumn = true := by
  refine Iff.intro (fun hA => ?_) (fun hB => ?_)
  · have hMember := rmrHasLeadTrueMember rowsA pivotColumn hA
    cases hMember with
    | intro row hBoth =>
        have hInA : IhqMemSpan width rowsA row := ihqMemSpanElem hAllA hBoth.left
        have hInB : IhqMemSpan width rowsB row := (hSpanEq row).mp hInA
        exact rmrAchievableLeadIsPivot rowsB row pivotColumn hAllB hEchB hInB hBoth.right
  · have hMember := rmrHasLeadTrueMember rowsB pivotColumn hB
    cases hMember with
    | intro row hBoth =>
        have hInB : IhqMemSpan width rowsB row := ihqMemSpanElem hAllB hBoth.left
        have hInA : IhqMemSpan width rowsA row := (hSpanEq row).mpr hInB
        exact rmrAchievableLeadIsPivot rowsA row pivotColumn hAllA hEchA hInA hBoth.right

/-! ## Stage 4 — the dimension theorem: rank is a span invariant

A strictly-increasing-lead injection of the smaller echelon form into the
dominating one.  Every lead of `rowsA` is a pivot column of `rowsB` (from T2), so
walking both staircases in lock-step gives `length rowsA <= length rowsB`;
symmetrizing through `ihqNatLe` antisymmetry pins the ranks equal. -/

/-- Comparator flip: `a < b` gives `b > a`. -/
theorem rmrNatCompareGtOfLtFlip : (firstValue secondValue : Nat) ->
    ihqNatCompare firstValue secondValue = IhqOrder.isLt ->
    ihqNatCompare secondValue firstValue = IhqOrder.isGt
  | 0, 0, hLt => IhqOrder.noConfusion hLt
  | 0, _secondPred + 1, _hLt => rfl
  | _firstPred + 1, 0, hLt => IhqOrder.noConfusion hLt
  | firstPred + 1, secondPred + 1, hLt => rmrNatCompareGtOfLtFlip firstPred secondPred hLt

/-- No echelon row leads at a column strictly below the echelon's lower bound. -/
theorem rmrHasLeadFalseOfEchelonAbove : (rows : List (List QnfRat)) ->
    (lowerBound pivotColumn : Nat) -> IhqEchelonFrom lowerBound rows ->
    ihqNatCompare pivotColumn lowerBound = IhqOrder.isLt ->
    rmrHasLead rows pivotColumn = false
  | [], _lowerBound, _pivotColumn, _hEch, _hLt => rfl
  | headRow :: restRows, lowerBound, pivotColumn, hEch, hLt => by
      cases hEch with
      | cons headLead hLeadH hBound hRest =>
          rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH]
          have hPcLtLb : ihqNatLe (pivotColumn + 1) lowerBound = true :=
            ihqNatLeSuccOfCompareLt pivotColumn lowerBound hLt
          have hPcLtHead : ihqNatCompare pivotColumn headLead = IhqOrder.isLt :=
            ihqNatCompareLtOfLeSucc pivotColumn headLead
              (ihqNatLeTrans (pivotColumn + 1) lowerBound headLead hPcLtLb hBound)
          have hHeadGtPc : ihqNatCompare headLead pivotColumn = IhqOrder.isGt :=
            rmrNatCompareGtOfLtFlip pivotColumn headLead hPcLtHead
          rw [hHeadGtPc]
          have hPcLtNext : ihqNatCompare pivotColumn (headLead + 1) = IhqOrder.isLt :=
            rmrNatCompareLtTrans pivotColumn headLead (headLead + 1) hPcLtHead
              (ihqNatCompareLtOfLeSucc headLead (headLead + 1) (ihqNatLeRefl (headLead + 1)))
          exact rmrHasLeadFalseOfEchelonAbove restRows (headLead + 1) pivotColumn hRest hPcLtNext

/-- Reading past a head pivot: if the query column is strictly above the head
lead, membership descends to the tail. -/
theorem rmrHasLeadDropHead (headRow : List QnfRat) (restRows : List (List QnfRat))
    (pivotColumn headLead : Nat) (hLeadH : ihqLead headRow = some headLead)
    (hAbove : ihqNatCompare headLead pivotColumn = IhqOrder.isLt) :
    rmrHasLead (headRow :: restRows) pivotColumn = rmrHasLead restRows pivotColumn := by
  rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH, hAbove]

/-- **THE DIMENSION INEQUALITY**: if every lead of the echelon form `rowsA` is a
pivot column of the echelon form `rowsB`, then `rowsA` is no longer than `rowsB`. -/
theorem rmrLeadDominationLe :
    (rowsB : List (List QnfRat)) -> (rowsA : List (List QnfRat)) -> (lbA lbB : Nat) ->
    IhqEchelonFrom lbA rowsA -> IhqEchelonFrom lbB rowsB ->
    ((row : List QnfRat) -> IhqRowMem row rowsA -> (rowLead : Nat) ->
      ihqLead row = some rowLead -> rmrHasLead rowsB rowLead = true) ->
    ihqNatLe rowsA.length rowsB.length = true
  | rowsB, [], _lbA, _lbB, _hEchA, _hEchB, _hDom => ihqNatLeZeroLeft rowsB.length
  | [], headRowA :: _restA, _lbA, _lbB, hEchA, _hEchB, hDom => by
      cases hEchA with
      | cons headLeadA hLeadA _hBoundA _hRestA =>
          have hFalse := hDom headRowA (IhqRowMem.head headRowA _restA) headLeadA hLeadA
          exact Bool.noConfusion hFalse
  | headRowB :: restB, headRowA :: restA, lbA, lbB, hEchA, hEchB, hDom => by
      cases hEchA with
      | cons headLeadA hLeadA hBoundA hRestA =>
          cases hEchB with
          | cons headLeadB hLeadB hBoundB hRestB =>
              have hDomHead := hDom headRowA (IhqRowMem.head headRowA restA) headLeadA hLeadA
              cases hCompare : ihqNatCompare headLeadA headLeadB with
              | isEq =>
                  have hSame : headLeadA = headLeadB :=
                    ihqNatCompareEqImpliesEq headLeadA headLeadB hCompare
                  have hDomRest : (row : List QnfRat) -> IhqRowMem row restA ->
                      (rowLead : Nat) -> ihqLead row = some rowLead ->
                      rmrHasLead restB rowLead = true := by
                    intro row hRowMem rowLead hRowLead
                    have hInfo := ihqEchelonFromRowLead restA (headLeadA + 1) row hRestA hRowMem
                    cases hInfo with
                    | intro actualLead hBoth =>
                        have hRowLeadEq : rowLead = actualLead :=
                          Option.some.inj (hRowLead.symm.trans hBoth.left)
                        have hAbove : ihqNatCompare headLeadB rowLead = IhqOrder.isLt := by
                          rw [<- hSame, hRowLeadEq]
                          exact ihqNatCompareLtOfLeSucc headLeadA actualLead hBoth.right
                        have hFull := hDom row (IhqRowMem.tail hRowMem) rowLead hRowLead
                        rw [rmrHasLeadDropHead headRowB restB rowLead headLeadB hLeadB hAbove]
                          at hFull
                        exact hFull
                  exact rmrLeadDominationLe restB restA (headLeadA + 1) (headLeadB + 1)
                    hRestA hRestB hDomRest
              | isLt =>
                  -- headLeadA < headLeadB: rowsA's minimal lead is below all of rowsB
                  have hBGtA : ihqNatCompare headLeadB headLeadA = IhqOrder.isGt :=
                    rmrNatCompareGtOfLtFlip headLeadA headLeadB hCompare
                  have hAViaB : rmrHasLead (headRowB :: restB) headLeadA
                      = rmrHasLead restB headLeadA := by
                    rw [rmrHasLeadConsSome headRowB restB headLeadA headLeadB hLeadB]
                    have hFlip : ihqNatCompare headLeadB headLeadA = IhqOrder.isGt := hBGtA
                    rw [hFlip]
                  rw [hAViaB] at hDomHead
                  have hRestFalse : rmrHasLead restB headLeadA = false := by
                    have hLtNext : ihqNatCompare headLeadA (headLeadB + 1) = IhqOrder.isLt :=
                      rmrNatCompareLtTrans headLeadA headLeadB (headLeadB + 1) hCompare
                        (ihqNatCompareLtOfLeSucc headLeadB (headLeadB + 1)
                          (ihqNatLeRefl (headLeadB + 1)))
                    exact rmrHasLeadFalseOfEchelonAbove restB (headLeadB + 1) headLeadA hRestB
                      hLtNext
                  rw [hRestFalse] at hDomHead
                  exact Bool.noConfusion hDomHead
              | isGt =>
                  -- headLeadA > headLeadB: rowsB's head lead is extra; drop it
                  have hDomDropB : (row : List QnfRat) -> IhqRowMem row (headRowA :: restA) ->
                      (rowLead : Nat) -> ihqLead row = some rowLead ->
                      rmrHasLead restB rowLead = true := by
                    intro row hRowMem rowLead hRowLead
                    have hLeadGeA : ihqNatLe headLeadA rowLead = true := by
                      cases hRowMem with
                      | head =>
                          have hEq : headLeadA = rowLead :=
                            Option.some.inj (hLeadA.symm.trans hRowLead)
                          rw [hEq]; exact ihqNatLeRefl rowLead
                      | tail hRowRest =>
                          have hInfo :=
                            ihqEchelonFromRowLead restA (headLeadA + 1) row hRestA hRowRest
                          cases hInfo with
                          | intro actualLead hBoth =>
                              have hRowLeadEq : rowLead = actualLead :=
                                Option.some.inj (hRowLead.symm.trans hBoth.left)
                              rw [hRowLeadEq]
                              exact ihqNatLeTrans headLeadA (headLeadA + 1) actualLead
                                (ihqNatLeSuccRight headLeadA headLeadA (ihqNatLeRefl headLeadA))
                                hBoth.right
                    have hBLtA : ihqNatCompare headLeadB headLeadA = IhqOrder.isLt :=
                      ihqNatCompareGtFlip headLeadA headLeadB hCompare
                    have hBLeSucc : ihqNatLe (headLeadB + 1) headLeadA = true :=
                      ihqNatLeSuccOfCompareLt headLeadB headLeadA hBLtA
                    have hAbove : ihqNatCompare headLeadB rowLead = IhqOrder.isLt :=
                      ihqNatCompareLtOfLeSucc headLeadB rowLead
                        (ihqNatLeTrans (headLeadB + 1) headLeadA rowLead hBLeSucc hLeadGeA)
                    have hFull := hDom row hRowMem rowLead hRowLead
                    rw [rmrHasLeadDropHead headRowB restB rowLead headLeadB hLeadB hAbove] at hFull
                    exact hFull
                  have hRec := rmrLeadDominationLe restB (headRowA :: restA) lbA (headLeadB + 1)
                    (IhqEchelonFrom.cons headLeadA hLeadA hBoundA hRestA) hRestB hDomDropB
                  show ihqNatLe ((headRowA :: restA).length) (restB.length + 1) = true
                  exact ihqNatLeSuccRight (headRowA :: restA).length restB.length hRec

/-- **T1 (the dimension theorem)**: span-equal matrices have equal rank. -/
theorem rmrRankSpanInvariant {width : Nat} (rowsA rowsB : List (List QnfRat))
    (hAllA : IhqAllWidth width rowsA) (hAllB : IhqAllWidth width rowsB)
    (hSpanEqB : ihqSpanEqB rowsA rowsB = true) : rmrRank rowsA = rmrRank rowsB := by
  have hSpanIff : (vector : List QnfRat) ->
      (IhqMemSpan width rowsA vector <-> IhqMemSpan width rowsB vector) :=
    ihqSpanEqBSound hAllA hAllB hSpanEqB
  have hEchAllA : IhqAllWidth width (ihqEchelonize rowsA) := ihqEchelonizeWidth rowsA hAllA
  have hEchAllB : IhqAllWidth width (ihqEchelonize rowsB) := ihqEchelonizeWidth rowsB hAllB
  have hEchEchA : IhqEchelonFrom 0 (ihqEchelonize rowsA) := ihqEchelonizeEchelon rowsA hAllA
  have hEchEchB : IhqEchelonFrom 0 (ihqEchelonize rowsB) := ihqEchelonizeEchelon rowsB hAllB
  -- span of an echelonized form lands in the target span both ways
  have hEchSpanIff : (vector : List QnfRat) ->
      (IhqMemSpan width (ihqEchelonize rowsA) vector <->
        IhqMemSpan width (ihqEchelonize rowsB) vector) := by
    intro vector
    refine Iff.intro (fun hMem => ?_) (fun hMem => ?_)
    · have hInA := ihqEchelonizeSpanSub1 rowsA hAllA hMem
      exact ihqEchelonizeSpanSub2 rowsB hAllB ((hSpanIff vector).mp hInA)
    · have hInB := ihqEchelonizeSpanSub1 rowsB hAllB hMem
      exact ihqEchelonizeSpanSub2 rowsA hAllA ((hSpanIff vector).mpr hInB)
  have hDomAB : (row : List QnfRat) -> IhqRowMem row (ihqEchelonize rowsA) ->
      (rowLead : Nat) -> ihqLead row = some rowLead ->
      rmrHasLead (ihqEchelonize rowsB) rowLead = true := by
    intro row hRowMem rowLead hRowLead
    have hInA : IhqMemSpan width (ihqEchelonize rowsA) row := ihqMemSpanElem hEchAllA hRowMem
    have hInB : IhqMemSpan width (ihqEchelonize rowsB) row := (hEchSpanIff row).mp hInA
    exact rmrAchievableLeadIsPivot (ihqEchelonize rowsB) row rowLead hEchAllB hEchEchB hInB
      hRowLead
  have hDomBA : (row : List QnfRat) -> IhqRowMem row (ihqEchelonize rowsB) ->
      (rowLead : Nat) -> ihqLead row = some rowLead ->
      rmrHasLead (ihqEchelonize rowsA) rowLead = true := by
    intro row hRowMem rowLead hRowLead
    have hInB : IhqMemSpan width (ihqEchelonize rowsB) row := ihqMemSpanElem hEchAllB hRowMem
    have hInA : IhqMemSpan width (ihqEchelonize rowsA) row := (hEchSpanIff row).mpr hInB
    exact rmrAchievableLeadIsPivot (ihqEchelonize rowsA) row rowLead hEchAllA hEchEchA hInA
      hRowLead
  have hLeAB : ihqNatLe (ihqEchelonize rowsA).length (ihqEchelonize rowsB).length = true :=
    rmrLeadDominationLe (ihqEchelonize rowsB) (ihqEchelonize rowsA) 0 0 hEchEchA hEchEchB hDomAB
  have hLeBA : ihqNatLe (ihqEchelonize rowsB).length (ihqEchelonize rowsA).length = true :=
    rmrLeadDominationLe (ihqEchelonize rowsA) (ihqEchelonize rowsB) 0 0 hEchEchB hEchEchA hDomBA
  exact rmrNatLeAntisymm (ihqEchelonize rowsA).length (ihqEchelonize rowsB).length hLeAB hLeBA

/-! ## Stage 5 — the RREF row-value wall (T3)

Rank (T1) and pivot-SET invariance (T2) LAND above.  Full byte-level RREF
uniqueness (`ihqRrefUniquenessStatement`: span-equal inputs give a literally
equal reduced echelon form) needs one further step this brick does NOT close: at
each shared pivot column the reduced ROW must be identical.  Two forms with the
same pivot columns can still differ in the FREE (non-pivot) columns unless one
proves that back-substitution against a shared reduced basis forces the same
entries — i.e. that the leading-1, all-other-pivots-zero row of a given pivot is
the UNIQUE reduced representative of its coset in the row space.  That coset-
representative uniqueness is the residual; the pivot machinery here supplies the
pivot columns and the leading-1 normalization (`rre`), but not the free-column
determination.

Attacks burned:
  (1) direct row-equality induction on the two echelon forms — the pivot columns
      align (T2) but the entries in the non-pivot columns are governed by the
      back-reduced coefficients, which this kit exposes only through the reduction
      engine, not as a canonical coordinate; no lemma pins them equal;
  (2) reduce-difference-to-zero — the difference of the two candidate RREF rows at
      a shared pivot lies in the span and reduces to zero, but concluding the rows
      are LITERALLY equal from "difference reduces to zero" is again RREF
      uniqueness (circular) without an independent coordinate for the free
      columns. -/

/-- Owner FALSE: the free-column (coset-representative) uniqueness needed to turn
pivot-set equality into byte-level RREF equality is not discharged here. -/
def rmrHasRrefRowUniqueness : Bool := false

/-! ## Stage 6 — kernel-`rfl` fires (early smoke, before the heavy proofs) -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Fire (dependent row collapses): `rank [[1,2],[2,4]] = 1` — the second row is
`2 *` the first, so the echelon form has ONE pivot. -/
theorem rmrFireRankDependentIsOne :
    rmrRank [[qnfOfInt 1, qnfOfInt 2], [qnfOfInt 2, qnfOfInt 4]] = 1 := rfl

/-- Fire (independent rows): `rank [[1,0],[0,1]] = 2` — the identity has two
pivots. -/
theorem rmrFireRankIdentityIsTwo :
    rmrRank [[qnfOfInt 1, qnfOfInt 0], [qnfOfInt 0, qnfOfInt 1]] = 2 := rfl

/-- Fire (single nonzero row): `rank [[1,2]] = 1`. -/
theorem rmrFireRankSingleRow :
    rmrRank [[qnfOfInt 1, qnfOfInt 2]] = 1 := rfl

/-- Fire (empty span): `rank [] = 0`. -/
theorem rmrFireRankNilIsZero : rmrRank ([] : List (List QnfRat)) = 0 := rfl

/-- Fire (pivot column of a single row): `[1,2]` leads at column 0. -/
theorem rmrFirePivotSingleRowAtZero :
    rmrHasLead (ihqEchelonize [[qnfOfInt 1, qnfOfInt 2]]) 0 = true := rfl

/-- Fire (**pivot-set agreement of span-equal matrices**): `[1,2]` and `[2,4]`
are the same line, so their pivot column (0) agrees. -/
theorem rmrFirePivotSpanEqualAgree :
    rmrHasLead (ihqEchelonize [[qnfOfInt 1, qnfOfInt 2]]) 0
      = rmrHasLead (ihqEchelonize [[qnfOfInt 2, qnfOfInt 4]]) 0 := rfl

/-- Fire (pivot control, missing at 0): the `y`-axis line `[0,1]` has NO pivot at
column 0 — its pivot is column 1. -/
theorem rmrFirePivotYaxisMissesZero :
    rmrHasLead (ihqEchelonize [[qnfOfInt 0, qnfOfInt 1]]) 0 = false := rfl

/-- Fire (pivot control, present at 1): the `y`-axis line `[0,1]` leads at
column 1. -/
theorem rmrFirePivotYaxisAtOne :
    rmrHasLead (ihqEchelonize [[qnfOfInt 0, qnfOfInt 1]]) 1 = true := rfl

/-- Fire (**rank/pivot control on non-span-equal matrices**, present side): the
`x`-axis line `[1,0]` HAS a pivot at column 0. -/
theorem rmrFireRankPivotControlPresent :
    rmrHasLead (ihqEchelonize [[qnfOfInt 1, qnfOfInt 0]]) 0 = true := rfl

/-- Fire (**rank/pivot control on non-span-equal matrices**, absent side): the
`y`-axis line `[0,1]` LACKS a pivot at column 0 — distinct pivot columns match
the distinct spans. -/
theorem rmrFireRankPivotControlAbsent :
    rmrHasLead (ihqEchelonize [[qnfOfInt 0, qnfOfInt 1]]) 0 = false := rfl

/-! ## Stage 7 — content markers -/

/-- DECIDED: the rank function (`rmrRank`) with the width bound (`rmrRankLeWidth`)
and the full span-invariance dimension theorem (`rmrRankSpanInvariant`). -/
def rmrHasRankApparatus : Bool := true

/-- DECIDED: pivot-column determination (`rmrAchievableLeadIsPivot`) and pivot-SET
span invariance (`rmrPivotSetSpanInvariant`). -/
def rmrHasPivotSetInvariance : Bool := true

end FX1Poly.ComputerAlgebra
