import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalMatrixRank

/-! # LinearAlgebra/RationalFreeColumnUniqueness — the reduced-basis
    characterization and RREF uniqueness over the exact `QnfRat` field
    (WP-PROP-3, the last uniqueness brick)

`RationalReducedEchelon` (prefix `rre`) shipped the leading-1 canonicalizer
`rreRref` with unit pivots + row-space invariance, and `RationalMatrixRank`
(prefix `rmr`) shipped the rank apparatus: pivot-column determination
(`rmrAchievableLeadIsPivot`), pivot-SET span invariance
(`rmrPivotSetSpanInvariant`) and the rank dimension theorem
(`rmrRankSpanInvariant`).  Both walled the FINAL step — that two RREFs with the
same row space are LITERALLY equal — citing a missing rank/exchange apparatus.

That wall is a red herring: the apparatus is `rmr`.  This file lands the genuine
new content — **the reduced-basis support characterization**:

  * `rfcZeroAtEveryPivotIsZeroRow` — a span member of an echelon form that
    vanishes at EVERY pivot column is the zero row (its lead would be a pivot
    column by `rmrAchievableLeadIsPivot`, yet it vanishes there);
  * `rfcReducedSupportUnique` — **T1**: two span members that AGREE at every
    pivot column are equal (their difference vanishes at every pivot, so is the
    zero row).  This is the span-determinacy of a reduced pivot row: a vector in
    the row space is pinned by its pivot-column coordinates, so its FREE-column
    coordinates are span-determined;
  * `RfcIsReducedEchelonFrom` + `rfcReducedEchelonUnique` — **T2/T3 (abstract)**:
    two forms in reduced row echelon form (echelon staircase + unit leads + zero
    at every OTHER pivot) with the SAME row space are literally equal, by
    simultaneous induction using T1 at each pivot row;
  * `rfcBackReduceEchelonReduced` — **the walled step CLOSED**: back-reduction of
    an echelon form is again echelon (leads preserved) AND makes every row zero at
    every other pivot.  Built from the reduction-engine lemmas
    `rfcReduceCoeffWhereRowsZero` (a coefficient survives where all rows vanish)
    and `rfcReduceZeroAtEveryLead` (back-substitution zeroes every pivot) — the
    free-column coordinate determination the earlier `rre`/`rmr` bricks lacked;
  * `rfcRreRrefIsReducedEchelon` + `rfcRreRrefUnique` /
    `rfcRreRrefUniqueOfSpanEqB` — **T3 (the payoff)**: span-equal inputs have
    LITERALLY equal reduced row echelon forms `rreRref`.  This is the TRUE
    RREF-uniqueness theorem over `QnfRat`.

One correction to the upstream owner flags: `ihqRrefUniquenessStatement` targets
the UN-normalized `ihqRref` (no leading-1 pass) and is FALSE as literally stated —
`[[1,2]]` and `[[2,4]]` span the same line yet have distinct `ihqRref` — so it is
REFUTED here (`rfcIhqRrefUniquenessRefuted`).  The canonical target is the
normalized `rreRref`, and IT is unique (T3).  No wall remains.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no `List.append`, no `Nat.sub/div/mod/min/max` order lemmas, no
wildcard match arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — coefficient of a negated row -/

/-- The coefficient of a negated row is the negation of the coefficient. -/
theorem rfcGetCoeffNeg (row : List QnfRat) (position : Nat) :
    ihqGetCoeff (ihqRowNeg row) position = qnfNeg (ihqGetCoeff row position) := by
  rw [ihqRowNegAsScale row, ihqGetCoeffScale (qnfNeg qnfOne) row position,
    grqQnfMulNegLeft qnfOne (ihqGetCoeff row position),
    qnfMulOneLeft (ihqGetCoeff row position)]

/-! ## Stage 1 — the reduced-basis support characterization (T1) -/

/-- A span member of an echelon form that vanishes at EVERY pivot column is the
zero row: its lead would be a pivot column by `rmrAchievableLeadIsPivot`, yet the
member vanishes there, so it can have no lead. -/
theorem rfcZeroAtEveryPivotIsZeroRow {width lowerBound : Nat}
    (echelonRows : List (List QnfRat)) (vector : List QnfRat)
    (hAll : IhqAllWidth width echelonRows)
    (hEch : IhqEchelonFrom lowerBound echelonRows)
    (hMem : IhqMemSpan width echelonRows vector)
    (hZeroAtPivots : (pivotColumn : Nat) -> rmrHasLead echelonRows pivotColumn = true ->
      ihqGetCoeff vector pivotColumn = qnfZero) :
    vector = ihqZeroRow width := by
  have hVecLen : vector.length = width := ihqMemSpanWidth hAll hMem
  cases hLead : ihqLead vector with
  | none => exact ihqLeadNoneToZeroRow vector hVecLen hLead
  | some pivotColumn =>
      have hIsPivot : rmrHasLead echelonRows pivotColumn = true :=
        rmrAchievableLeadIsPivot echelonRows vector pivotColumn hAll hEch hMem hLead
      have hVecZero : ihqGetCoeff vector pivotColumn = qnfZero :=
        hZeroAtPivots pivotColumn hIsPivot
      have hVecNe : ihqGetCoeff vector pivotColumn ≠ qnfZero :=
        ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse vector pivotColumn hLead)
      exact absurd hVecZero hVecNe

/-- **T1 (THE REDUCED-BASIS SUPPORT-UNIQUENESS)**: two span members of an echelon
form that AGREE at every pivot column are equal.  Their difference is a span
member that vanishes at every pivot, hence is the zero row; equal-difference
gives equal vectors.  This pins a row-space vector by its pivot coordinates, so
its FREE-column coordinates are span-determined. -/
theorem rfcReducedSupportUnique {width lowerBound : Nat}
    (echelonRows : List (List QnfRat)) (leftVec rightVec : List QnfRat)
    (hAll : IhqAllWidth width echelonRows)
    (hEch : IhqEchelonFrom lowerBound echelonRows)
    (hLeftMem : IhqMemSpan width echelonRows leftVec)
    (hRightMem : IhqMemSpan width echelonRows rightVec)
    (hAgree : (pivotColumn : Nat) -> rmrHasLead echelonRows pivotColumn = true ->
      ihqGetCoeff leftVec pivotColumn = ihqGetCoeff rightVec pivotColumn) :
    leftVec = rightVec := by
  have hLeftLen : leftVec.length = width := ihqMemSpanWidth hAll hLeftMem
  have hRightLen : rightVec.length = width := ihqMemSpanWidth hAll hRightMem
  have hNegLen : (ihqRowNeg rightVec).length = width :=
    (ihqRowNegLength rightVec).trans hRightLen
  have hDiffMem : IhqMemSpan width echelonRows (ihqRowAdd leftVec (ihqRowNeg rightVec)) :=
    ihqMemSpanAddClosed hAll hLeftMem (ihqMemSpanNegClosed hRightMem)
  have hDiffZeroAtPivots : (pivotColumn : Nat) ->
      rmrHasLead echelonRows pivotColumn = true ->
      ihqGetCoeff (ihqRowAdd leftVec (ihqRowNeg rightVec)) pivotColumn = qnfZero := by
    intro pivotColumn hIsPivot
    rw [ihqGetCoeffAdd leftVec (ihqRowNeg rightVec) (hLeftLen.trans hNegLen.symm) pivotColumn,
      rfcGetCoeffNeg rightVec pivotColumn, hAgree pivotColumn hIsPivot]
    exact qnfAddNegRight (ihqGetCoeff rightVec pivotColumn)
  have hDiffZero : ihqRowAdd leftVec (ihqRowNeg rightVec) = ihqZeroRow width :=
    rfcZeroAtEveryPivotIsZeroRow echelonRows (ihqRowAdd leftVec (ihqRowNeg rightVec))
      hAll hEch hDiffMem hDiffZeroAtPivots
  exact ihqRowsEqOfAddNegEqZero leftVec rightVec width hLeftLen hRightLen hDiffZero

/-! ## Stage 2 — structural helpers for the abstract uniqueness induction -/

/-- The all-zero row has no leading position. -/
theorem rfcLeadZeroRowNone : (width : Nat) -> ihqLead (ihqZeroRow width) = none
  | 0 => rfl
  | widthPred + 1 => by
      show ihqLead (qnfZero :: ihqZeroRow widthPred) = none
      rw [ihqLeadConsShape, qnfBeqSelfIsTrue qnfZero, rfcLeadZeroRowNone widthPred]

/-- Pivot-column monotonicity: a pivot of the tail is a pivot of the whole. -/
theorem rfcHasLeadConsMonotone (headRow : List QnfRat) (restRows : List (List QnfRat))
    (pivotColumn : Nat) (hRest : rmrHasLead restRows pivotColumn = true) :
    rmrHasLead (headRow :: restRows) pivotColumn = true := by
  cases hLeadH : ihqLead headRow with
  | none => rw [rmrHasLeadConsNone headRow restRows pivotColumn hLeadH]; exact hRest
  | some headLead =>
      rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH]
      cases hCompare : ihqNatCompare headLead pivotColumn with
      | isEq => rfl
      | isLt => exact hRest
      | isGt => exact hRest

/-- Every pivot column of an echelon form is at or above the head lead: the head
lead is the minimal pivot. -/
theorem rfcPivotGeHeadLead (headRow : List QnfRat) (restRows : List (List QnfRat))
    (headLead pivotColumn : Nat) (hHeadLead : ihqLead headRow = some headLead)
    (hRestEch : IhqEchelonFrom (headLead + 1) restRows)
    (hHas : rmrHasLead (headRow :: restRows) pivotColumn = true) :
    ihqNatLe headLead pivotColumn = true := by
  cases hCompare : ihqNatCompare headLead pivotColumn with
  | isEq =>
      have hEq : headLead = pivotColumn :=
        ihqNatCompareEqImpliesEq headLead pivotColumn hCompare
      rw [hEq]; exact ihqNatLeRefl pivotColumn
  | isLt =>
      exact ihqNatLeTrans headLead (headLead + 1) pivotColumn
        (ihqNatLeSuccRight headLead headLead (ihqNatLeRefl headLead))
        (ihqNatLeSuccOfCompareLt headLead pivotColumn hCompare)
  | isGt =>
      have hPcLtHead : ihqNatCompare pivotColumn headLead = IhqOrder.isLt :=
        ihqNatCompareGtFlip headLead pivotColumn hCompare
      have hPcLtNext : ihqNatCompare pivotColumn (headLead + 1) = IhqOrder.isLt :=
        rmrNatCompareLtTrans pivotColumn headLead (headLead + 1) hPcLtHead
          (ihqNatCompareLtOfLeSucc headLead (headLead + 1) (ihqNatLeRefl (headLead + 1)))
      have hRestFalse : rmrHasLead restRows pivotColumn = false :=
        rmrHasLeadFalseOfEchelonAbove restRows (headLead + 1) pivotColumn hRestEch hPcLtNext
      rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hHeadLead, hCompare,
        hRestFalse] at hHas
      exact Bool.noConfusion hHas

/-- **THE TAIL-SPAN CHARACTERIZATION**: a span member of a reduced echelon form
that vanishes at the head pivot lies in the span of the tail.  (The head scalar
is forced to zero by the unit head pivot; the tail rows already vanish at the
head pivot by the staircase.) -/
theorem rfcTailSpanOfHeadZero {width lowerBound : Nat} (headRow : List QnfRat)
    (restRows : List (List QnfRat)) (vector : List QnfRat)
    (hAll : IhqAllWidth width (headRow :: restRows))
    (hEch : IhqEchelonFrom lowerBound (headRow :: restRows))
    (headLead : Nat) (hHeadLead : ihqLead headRow = some headLead)
    (hHeadUnit : ihqGetCoeff headRow headLead = qnfOne)
    (hMem : IhqMemSpan width (headRow :: restRows) vector)
    (hZeroAtHead : ihqGetCoeff vector headLead = qnfZero) :
    IhqMemSpan width restRows vector := by
  have hHead : headRow.length = width := by cases hAll with | cons hHead _hRest => exact hHead
  have hRestAll : IhqAllWidth width restRows := by
    cases hAll with | cons _hHead hRest => exact hRest
  have hRestEch : IhqEchelonFrom (headLead + 1) restRows := by
    cases hEch with
    | cons headLead2 hLead2 _hBound hRest =>
        have hLeadEq : headLead2 = headLead := Option.some.inj (hLead2.symm.trans hHeadLead)
        rw [hLeadEq] at hRest; exact hRest
  have hRestZeroAtHead : (row : List QnfRat) -> IhqRowMem row restRows ->
      ihqGetCoeff row headLead = qnfZero :=
    fun row hRow => ihqEchelonRowsCoeffZero hRestEch row hRow
  cases ihqMemSpanConsInv hMem with
  | inl hInRest => exact hInRest
  | inr hSplit =>
      cases hSplit with
      | intro scalar hPack =>
          cases hPack with
          | intro partner hBoth =>
              have hPartnerMem : IhqMemSpan width restRows partner := hBoth.left
              have hVecEq : vector = ihqRowAdd (ihqRowScale scalar headRow) partner :=
                hBoth.right
              have hPartnerLen : partner.length = width := ihqMemSpanWidth hRestAll hPartnerMem
              have hPartnerZeroAtHead : ihqGetCoeff partner headLead = qnfZero :=
                ihqMemSpanCoeffZero headLead hRestAll hRestZeroAtHead hPartnerMem
              have hScalarZero : scalar = qnfZero := by
                have hExpand := hZeroAtHead
                rw [hVecEq,
                  ihqGetCoeffAdd (ihqRowScale scalar headRow) partner
                    ((ihqRowScaleLength scalar headRow).trans (hHead.trans hPartnerLen.symm))
                    headLead,
                  ihqGetCoeffScale scalar headRow headLead, hHeadUnit,
                  qnfMulOneRight scalar, hPartnerZeroAtHead, qnfAddZeroRight scalar] at hExpand
                exact hExpand
              rw [hVecEq, hScalarZero, ihqRowScaleZeroScalar headRow, hHead,
                ihqRowAddZeroLeft partner width hPartnerLen]
              exact hPartnerMem

/-! ## Stage 2b — the reduction engine: free-column coordinate determination

These lemmas expose the back-substitution coordinate as a materialized entry:
`ihqReduceAgainst` preserves a coefficient at any column where every row vanishes
(`rfcReduceCoeffWhereRowsZero`) and zeroes the vector at every lead of an echelon
list (`rfcReduceZeroAtEveryLead`) — the engine that determines the free-column
coordinates during back-substitution. -/

/-- Reduction against a row list preserves the vector's coefficient at any column
where EVERY row vanishes. -/
theorem rfcReduceCoeffWhereRowsZero {width : Nat} :
    (rows : List (List QnfRat)) -> (vector : List QnfRat) -> (position : Nat) ->
    IhqAllWidth width rows -> vector.length = width ->
    ((row : List QnfRat) -> IhqRowMem row rows -> ihqGetCoeff row position = qnfZero) ->
    ihqGetCoeff (ihqReduceAgainst rows vector) position = ihqGetCoeff vector position
  | [], _vector, _position, _hAll, _hVecLen, _hZero => rfl
  | headRow :: restRows, vector, position, hAll, hVecLen, hRowsZero => by
      have hHead : headRow.length = width := by cases hAll with | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with | cons _hHead hRest => exact hRest
      have hHeadZero : ihqGetCoeff headRow position = qnfZero :=
        hRowsZero headRow (IhqRowMem.head headRow restRows)
      have hRestZero : (row : List QnfRat) -> IhqRowMem row restRows ->
          ihqGetCoeff row position = qnfZero :=
        fun row hRow => hRowsZero row (IhqRowMem.tail hRow)
      cases hLeadH : ihqLead headRow with
      | none =>
          rw [ihqReduceAgainstConsNone restRows headRow vector hLeadH]
          exact rfcReduceCoeffWhereRowsZero restRows vector position hRestAll hVecLen hRestZero
      | some headLead =>
          cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
          | true =>
              rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH hCoeff]
              exact rfcReduceCoeffWhereRowsZero restRows vector position hRestAll hVecLen
                hRestZero
          | false =>
              rw [ihqReduceAgainstConsElim restRows headRow vector headLead hLeadH hCoeff]
              have hElimLen : (ihqElimStep vector headRow headLead).length = width :=
                ihqElimStepLength vector headRow headLead hVecLen hHead
              rw [rfcReduceCoeffWhereRowsZero restRows (ihqElimStep vector headRow headLead)
                  position hRestAll hElimLen hRestZero,
                rmrElimStepCoeffWhereZero vector headRow headLead position hVecLen hHead
                  hHeadZero]

/-- **THE LEAD-DETERMINATION HELPER**: a row that vanishes strictly below `k` and
is nonzero at `k` leads exactly at `k`. -/
theorem rfcLeadOfBelowZeroNonzero : (row : List QnfRat) -> (leadPosition : Nat) ->
    ((position : Nat) -> ihqNatCompare position leadPosition = IhqOrder.isLt ->
      ihqGetCoeff row position = qnfZero) ->
    qnfBeq (ihqGetCoeff row leadPosition) qnfZero = false ->
    ihqLead row = some leadPosition
  | [], _leadPosition, _hBelow, hNonzero => by
      have hZ : qnfBeq (ihqGetCoeff ([] : List QnfRat) _leadPosition) qnfZero = true :=
        qnfBeqSelfIsTrue qnfZero
      exact Bool.noConfusion (hZ.symm.trans hNonzero)
  | headCoeff :: _restCoeffs, 0, _hBelow, hNonzero => by
      have hN : qnfBeq headCoeff qnfZero = false := hNonzero
      rw [ihqLeadConsShape, hN]
  | headCoeff :: restCoeffs, leadPred + 1, hBelow, hNonzero => by
      have hHeadZero : ihqGetCoeff (headCoeff :: restCoeffs) 0 = qnfZero := hBelow 0 rfl
      have hHeadBeq : qnfBeq headCoeff qnfZero = true :=
        ihqQnfBeqZeroTrueOfEqZero hHeadZero
      have hRestLead : ihqLead restCoeffs = some leadPred := by
        refine rfcLeadOfBelowZeroNonzero restCoeffs leadPred (fun position hLt => ?_) hNonzero
        exact hBelow (position + 1) hLt
      rw [ihqLeadConsShape, hHeadBeq, hRestLead]

/-- **BACK-SUBSTITUTION ZEROES EVERY PIVOT**: reduction against an echelon list
zeroes the vector at every lead (pivot column) of the list. -/
theorem rfcReduceZeroAtEveryLead {width : Nat} :
    (lowerBound : Nat) -> (echelonRows : List (List QnfRat)) -> (vector : List QnfRat) ->
    (pivotColumn : Nat) -> IhqAllWidth width echelonRows -> vector.length = width ->
    IhqEchelonFrom lowerBound echelonRows ->
    rmrHasLead echelonRows pivotColumn = true ->
    ihqGetCoeff (ihqReduceAgainst echelonRows vector) pivotColumn = qnfZero
  | _lb, [], _vector, _pivotColumn, _hAll, _hVecLen, _hEch, hHas => by
      have hFalse : (false : Bool) = true := hHas
      exact Bool.noConfusion hFalse
  | _lb, headRow :: restRows, vector, pivotColumn, hAll, hVecLen, hEch, hHas => by
      have hHead : headRow.length = width := by cases hAll with | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLeadH hBound hRestEch =>
          have hRestZeroAtHead : (row : List QnfRat) -> IhqRowMem row restRows ->
              ihqGetCoeff row headLead = qnfZero :=
            fun row hRow => ihqEchelonRowsCoeffZero hRestEch row hRow
          cases hpc : ihqNatCompare pivotColumn headLead with
          | isEq =>
              have hPcEq : pivotColumn = headLead :=
                ihqNatCompareEqImpliesEq pivotColumn headLead hpc
              cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
              | true =>
                  rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH hCoeff,
                    hPcEq,
                    rfcReduceCoeffWhereRowsZero restRows vector headLead hRestAll hVecLen
                      hRestZeroAtHead]
                  exact ihqQnfEqZeroOfBeqZeroTrue hCoeff
              | false =>
                  rw [ihqReduceAgainstConsElim restRows headRow vector headLead hLeadH hCoeff]
                  have hElimLen : (ihqElimStep vector headRow headLead).length = width :=
                    ihqElimStepLength vector headRow headLead hVecLen hHead
                  rw [hPcEq,
                    rfcReduceCoeffWhereRowsZero restRows (ihqElimStep vector headRow headLead)
                      headLead hRestAll hElimLen hRestZeroAtHead]
                  exact ihqElimStepCancelsPivot vector headRow headLead hVecLen hHead
                    (ihqLeadCoeffBeqFalse headRow headLead hLeadH)
          | isLt =>
              have hHeadGtPc : ihqNatCompare headLead pivotColumn = IhqOrder.isGt :=
                rmrNatCompareGtOfLtFlip pivotColumn headLead hpc
              have hPcLtNext : ihqNatCompare pivotColumn (headLead + 1) = IhqOrder.isLt :=
                rmrNatCompareLtTrans pivotColumn headLead (headLead + 1) hpc
                  (ihqNatCompareLtOfLeSucc headLead (headLead + 1) (ihqNatLeRefl (headLead + 1)))
              have hRestFalse : rmrHasLead restRows pivotColumn = false :=
                rmrHasLeadFalseOfEchelonAbove restRows (headLead + 1) pivotColumn hRestEch hPcLtNext
              rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH, hHeadGtPc,
                hRestFalse] at hHas
              exact Bool.noConfusion hHas
          | isGt =>
              have hHeadLtPc : ihqNatCompare headLead pivotColumn = IhqOrder.isLt :=
                ihqNatCompareGtFlip pivotColumn headLead hpc
              have hRestHas : rmrHasLead restRows pivotColumn = true := by
                rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH,
                  hHeadLtPc] at hHas
                exact hHas
              cases hCoeff : qnfBeq (ihqGetCoeff vector headLead) qnfZero with
              | true =>
                  rw [ihqReduceAgainstConsSkip restRows headRow vector headLead hLeadH hCoeff]
                  exact rfcReduceZeroAtEveryLead (headLead + 1) restRows vector pivotColumn
                    hRestAll hVecLen hRestEch hRestHas
              | false =>
                  rw [ihqReduceAgainstConsElim restRows headRow vector headLead hLeadH hCoeff]
                  have hElimLen : (ihqElimStep vector headRow headLead).length = width :=
                    ihqElimStepLength vector headRow headLead hVecLen hHead
                  exact rfcReduceZeroAtEveryLead (headLead + 1) restRows
                    (ihqElimStep vector headRow headLead) pivotColumn hRestAll hElimLen hRestEch
                    hRestHas

/-- Every row of an echelon form vanishes strictly below its lower bound. -/
theorem rfcEchelonRowsCoeffZeroLe (bound : Nat) (rows : List (List QnfRat))
    (hEch : IhqEchelonFrom bound rows) (row : List QnfRat) (hRow : IhqRowMem row rows)
    (position : Nat) (hLt : ihqNatCompare position bound = IhqOrder.isLt) :
    ihqGetCoeff row position = qnfZero := by
  cases ihqEchelonFromRowLead rows bound row hEch hRow with
  | intro rowLead hBoth =>
      have hPosLtLead : ihqNatCompare position rowLead = IhqOrder.isLt :=
        ihqNatCompareLtOfLeSucc position rowLead
          (ihqNatLeTrans (position + 1) bound rowLead
            (ihqNatLeSuccOfCompareLt position bound hLt) hBoth.right)
      exact ihqLeadCoeffBelowZero row rowLead position hBoth.left hPosLtLead

/-! ## Stage 2c — the back-reduce structural theorem (T2/T3 connection)

`ihqBackReduce` on an echelon form preserves each row's lead (so the echelon
staircase survives) AND makes every row zero at every OTHER pivot column — the
reduced-support property.  This is the structural fact the earlier `rre`/`rmr`
bricks walled; it is proven here from the reduction-engine lemmas above. -/

/-- **THE BACK-REDUCE STRUCTURAL THEOREM**: back-reduction of an echelon form is
again an echelon form (leads preserved) whose every row vanishes at every pivot
column that is not its own lead. -/
theorem rfcBackReduceEchelonReduced {width : Nat} :
    (lowerBound : Nat) -> (echelonRows : List (List QnfRat)) ->
    IhqAllWidth width echelonRows -> IhqEchelonFrom lowerBound echelonRows ->
    IhqEchelonFrom lowerBound (ihqBackReduce echelonRows)
      /\ ((row : List QnfRat) -> (pivotColumn : Nat) ->
          IhqRowMem row (ihqBackReduce echelonRows) ->
          rmrHasLead echelonRows pivotColumn = true -> ihqLead row ≠ some pivotColumn ->
          ihqGetCoeff row pivotColumn = qnfZero)
  | _lowerBound, [], _hAll, hEch =>
      And.intro hEch (fun _row _pc hRowMem _hHas _hNe => nomatch hRowMem)
  | _lowerBound, headRow :: restRows, hAll, hEch => by
      have hHead : headRow.length = width := by cases hAll with | cons hHead _hRest => exact hHead
      have hRestAll : IhqAllWidth width restRows := by
        cases hAll with | cons _hHead hRest => exact hRest
      cases hEch with
      | cons headLead hLeadH hBound hRestEch =>
          have hIH := rfcBackReduceEchelonReduced (headLead + 1) restRows hRestAll hRestEch
          have hTailEch : IhqEchelonFrom (headLead + 1) (ihqBackReduce restRows) := hIH.left
          have hCRest := hIH.right
          have hTailAll : IhqAllWidth width (ihqBackReduce restRows) :=
            ihqBackReduceWidth restRows hRestAll
          -- the tail rows vanish at every column at or below the head lead
          have hTailZeroLe : (position : Nat) ->
              ihqNatCompare position (headLead + 1) = IhqOrder.isLt ->
              (row : List QnfRat) -> IhqRowMem row (ihqBackReduce restRows) ->
              ihqGetCoeff row position = qnfZero :=
            fun position hLt row hRow =>
              rfcEchelonRowsCoeffZeroLe (headLead + 1) (ihqBackReduce restRows) hTailEch row hRow
                position hLt
          have hHeadLeadLtNext : ihqNatCompare headLead (headLead + 1) = IhqOrder.isLt :=
            ihqNatCompareLtOfLeSucc headLead (headLead + 1) (ihqNatLeRefl (headLead + 1))
          -- the head of the back-reduced form leads at exactly `headLead`
          have hR0Lead :
              ihqLead (ihqReduceAgainst (ihqBackReduce restRows) headRow) = some headLead := by
            refine rfcLeadOfBelowZeroNonzero (ihqReduceAgainst (ihqBackReduce restRows) headRow)
              headLead (fun position hpLt => ?_) ?_
            · have hpLtNext : ihqNatCompare position (headLead + 1) = IhqOrder.isLt :=
                rmrNatCompareLtTrans position headLead (headLead + 1) hpLt hHeadLeadLtNext
              rw [rfcReduceCoeffWhereRowsZero (ihqBackReduce restRows) headRow position hTailAll
                  hHead (hTailZeroLe position hpLtNext)]
              exact ihqLeadCoeffBelowZero headRow headLead position hLeadH hpLt
            · rw [rfcReduceCoeffWhereRowsZero (ihqBackReduce restRows) headRow headLead hTailAll
                  hHead (hTailZeroLe headLead hHeadLeadLtNext)]
              exact ihqLeadCoeffBeqFalse headRow headLead hLeadH
          -- the tail pivots are exactly the restRows pivots (same span, both echelon)
          have hTailPivotIff : (pivotColumn : Nat) ->
              (rmrHasLead restRows pivotColumn = true <->
                rmrHasLead (ihqBackReduce restRows) pivotColumn = true) :=
            rmrPivotSetSpanInvariant restRows (ihqBackReduce restRows) hRestAll hTailAll
              hRestEch hTailEch
              (fun vector => Iff.intro
                (fun hv => ihqBackReduceSpanSub2 restRows hRestAll hv)
                (fun hv => ihqBackReduceSpanSub1 restRows hRestAll hv))
          refine And.intro (IhqEchelonFrom.cons headLead hR0Lead hBound hTailEch) ?_
          intro row pivotColumn hRowMem hHasP hLeadNe
          have hRowMem' : IhqRowMem row
              (ihqReduceAgainst (ihqBackReduce restRows) headRow :: ihqBackReduce restRows) :=
            hRowMem
          cases hRowMem' with
          | head =>
              -- row is the back-reduced head; its lead is headLead, so pivotColumn ≠ headLead
              have hPcNeHead : pivotColumn ≠ headLead := by
                intro hEq
                exact hLeadNe (by rw [hEq]; exact hR0Lead)
              have hRestHasP : rmrHasLead restRows pivotColumn = true := by
                rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH] at hHasP
                cases hCmp : ihqNatCompare headLead pivotColumn with
                | isEq =>
                    exact absurd (ihqNatCompareEqImpliesEq headLead pivotColumn hCmp).symm hPcNeHead
                | isLt => rw [hCmp] at hHasP; exact hHasP
                | isGt => rw [hCmp] at hHasP; exact hHasP
              have hTailHasP : rmrHasLead (ihqBackReduce restRows) pivotColumn = true :=
                (hTailPivotIff pivotColumn).mp hRestHasP
              exact rfcReduceZeroAtEveryLead (headLead + 1) (ihqBackReduce restRows) headRow
                pivotColumn hTailAll hHead hTailEch hTailHasP
          | tail hRowRest =>
              cases hDec : Nat.decEq pivotColumn headLead with
              | isTrue hEq =>
                  rw [hEq]
                  exact ihqEchelonRowsCoeffZero hTailEch row hRowRest
              | isFalse hNe =>
                  have hRestHasP : rmrHasLead restRows pivotColumn = true := by
                    rw [rmrHasLeadConsSome headRow restRows pivotColumn headLead hLeadH] at hHasP
                    cases hCmp : ihqNatCompare headLead pivotColumn with
                    | isEq =>
                        exact absurd (ihqNatCompareEqImpliesEq headLead pivotColumn hCmp).symm hNe
                    | isLt => rw [hCmp] at hHasP; exact hHasP
                    | isGt => rw [hCmp] at hHasP; exact hHasP
                  exact hCRest row pivotColumn hRowRest hRestHasP hLeadNe

/-! ## Stage 3 — the abstract reduced-echelon uniqueness theorem (T2/T3) -/

/-- A list of rows is in REDUCED row echelon form above a lower bound: correct
width, echelon staircase (strictly increasing leads at or above the bound), every
leading coefficient `qnfOne`, and every row zero at every OTHER pivot column of
the form (its own lead excepted). -/
def RfcIsReducedEchelonFrom (width lowerBound : Nat) (rows : List (List QnfRat)) : Prop :=
  IhqAllWidth width rows
    /\ IhqEchelonFrom lowerBound rows
    /\ ((row : List QnfRat) -> (pivotPosition : Nat) -> IhqRowMem row rows ->
        ihqLead row = some pivotPosition -> ihqGetCoeff row pivotPosition = qnfOne)
    /\ ((row : List QnfRat) -> (pivotColumn : Nat) -> IhqRowMem row rows ->
        rmrHasLead rows pivotColumn = true -> ihqLead row ≠ some pivotColumn ->
        ihqGetCoeff row pivotColumn = qnfZero)

/-- **T2/T3 (ABSTRACT UNIQUENESS)**: two reduced row echelon forms above the same
lower bound with the SAME row space are literally equal.  Simultaneous structural
induction on the first form: the minimal pivots agree (pivot-set invariance +
head-lead minimality), the head rows agree at every pivot so are equal by the
reduced-support characterization (T1), and the tails have equal row space (the
head coordinate is forced to zero), closing by the induction hypothesis. -/
theorem rfcReducedEchelonUniqueFrom {width : Nat} :
    (lowerBound : Nat) -> (rowsA rowsB : List (List QnfRat)) ->
    RfcIsReducedEchelonFrom width lowerBound rowsA ->
    RfcIsReducedEchelonFrom width lowerBound rowsB ->
    ((vector : List QnfRat) ->
      (IhqMemSpan width rowsA vector <-> IhqMemSpan width rowsB vector)) ->
    rowsA = rowsB
  | _lowerBound, [], rowsB, _hRedA, hRedB, hSpanEq => by
      cases rowsB with
      | nil => rfl
      | cons headRowB restRowsB =>
          have hAllB := hRedB.left
          have hEchB := hRedB.right.left
          cases hEchB with
          | cons headLeadB hHeadLeadB _hBoundB _hRestB =>
              have hMemB : IhqMemSpan width (headRowB :: restRowsB) headRowB :=
                ihqMemSpanElem hAllB (IhqRowMem.head headRowB restRowsB)
              have hInNil : IhqMemSpan width [] headRowB := (hSpanEq headRowB).mpr hMemB
              have hZeroRow : headRowB = ihqZeroRow width := ihqMemSpanNilInv hInNil
              rw [hZeroRow, rfcLeadZeroRowNone width] at hHeadLeadB
              exact nomatch hHeadLeadB
  | _lowerBound, headRowA :: restRowsA, rowsB, hRedA, hRedB, hSpanEq => by
      cases rowsB with
      | nil =>
          have hAllA := hRedA.left
          have hEchA := hRedA.right.left
          cases hEchA with
          | cons headLeadA hHeadLeadA _hBoundA _hRestA =>
              have hMemA : IhqMemSpan width (headRowA :: restRowsA) headRowA :=
                ihqMemSpanElem hAllA (IhqRowMem.head headRowA restRowsA)
              have hInNil : IhqMemSpan width [] headRowA := (hSpanEq headRowA).mp hMemA
              have hZeroRow : headRowA = ihqZeroRow width := ihqMemSpanNilInv hInNil
              rw [hZeroRow, rfcLeadZeroRowNone width] at hHeadLeadA
              exact nomatch hHeadLeadA
      | cons headRowB restRowsB =>
          have hAllA := hRedA.left
          have hUnitA := hRedA.right.right.left
          have hReducedA := hRedA.right.right.right
          have hAllB := hRedB.left
          have hUnitB := hRedB.right.right.left
          have hReducedB := hRedB.right.right.right
          have hRestAllA : IhqAllWidth width restRowsA := by
            cases hAllA with | cons _hHead hRest => exact hRest
          have hRestAllB : IhqAllWidth width restRowsB := by
            cases hAllB with | cons _hHead hRest => exact hRest
          cases hRedA.right.left with
          | cons headLeadA hHeadLeadA hBoundA hRestEchA =>
              cases hRedB.right.left with
              | cons headLeadB hHeadLeadB hBoundB hRestEchB =>
                  have hEchAFull : IhqEchelonFrom _ (headRowA :: restRowsA) :=
                    IhqEchelonFrom.cons headLeadA hHeadLeadA hBoundA hRestEchA
                  have hEchBFull : IhqEchelonFrom _ (headRowB :: restRowsB) :=
                    IhqEchelonFrom.cons headLeadB hHeadLeadB hBoundB hRestEchB
                  have hHeadAMem : IhqRowMem headRowA (headRowA :: restRowsA) :=
                    IhqRowMem.head headRowA restRowsA
                  have hHeadBMem : IhqRowMem headRowB (headRowB :: restRowsB) :=
                    IhqRowMem.head headRowB restRowsB
                  have hHeadUnitA : ihqGetCoeff headRowA headLeadA = qnfOne :=
                    hUnitA headRowA headLeadA hHeadAMem hHeadLeadA
                  have hHeadUnitB : ihqGetCoeff headRowB headLeadB = qnfOne :=
                    hUnitB headRowB headLeadB hHeadBMem hHeadLeadB
                  -- minimal pivots exist on both sides
                  have hHasAA : rmrHasLead (headRowA :: restRowsA) headLeadA = true := by
                    cases hCheck : rmrHasLead (headRowA :: restRowsA) headLeadA with
                    | true => rfl
                    | false =>
                        exact absurd hHeadLeadA
                          (rmrHasLeadFalseNoPivot (headRowA :: restRowsA) headLeadA hCheck
                            headRowA hHeadAMem)
                  have hHasBB : rmrHasLead (headRowB :: restRowsB) headLeadB = true := by
                    cases hCheck : rmrHasLead (headRowB :: restRowsB) headLeadB with
                    | true => rfl
                    | false =>
                        exact absurd hHeadLeadB
                          (rmrHasLeadFalseNoPivot (headRowB :: restRowsB) headLeadB hCheck
                            headRowB hHeadBMem)
                  have hPivotIff : (pivotColumn : Nat) ->
                      (rmrHasLead (headRowA :: restRowsA) pivotColumn = true <->
                        rmrHasLead (headRowB :: restRowsB) pivotColumn = true) :=
                    rmrPivotSetSpanInvariant (headRowA :: restRowsA) (headRowB :: restRowsB)
                      hAllA hAllB hEchAFull hEchBFull hSpanEq
                  have hHasBA : rmrHasLead (headRowB :: restRowsB) headLeadA = true :=
                    (hPivotIff headLeadA).mp hHasAA
                  have hHasAB : rmrHasLead (headRowA :: restRowsA) headLeadB = true :=
                    (hPivotIff headLeadB).mpr hHasBB
                  have hLeBA : ihqNatLe headLeadB headLeadA = true :=
                    rfcPivotGeHeadLead headRowB restRowsB headLeadB headLeadA hHeadLeadB
                      hRestEchB hHasBA
                  have hLeAB : ihqNatLe headLeadA headLeadB = true :=
                    rfcPivotGeHeadLead headRowA restRowsA headLeadA headLeadB hHeadLeadA
                      hRestEchA hHasAB
                  have hLeadEq : headLeadA = headLeadB :=
                    rmrNatLeAntisymm headLeadA headLeadB hLeAB hLeBA
                  -- head rows agree at every pivot, so are equal (T1)
                  have hHeadAInSpanA : IhqMemSpan width (headRowA :: restRowsA) headRowA :=
                    ihqMemSpanElem hAllA hHeadAMem
                  have hHeadBInSpanB : IhqMemSpan width (headRowB :: restRowsB) headRowB :=
                    ihqMemSpanElem hAllB hHeadBMem
                  have hHeadBInSpanA : IhqMemSpan width (headRowA :: restRowsA) headRowB :=
                    (hSpanEq headRowB).mpr hHeadBInSpanB
                  have hAgree : (pivotColumn : Nat) ->
                      rmrHasLead (headRowA :: restRowsA) pivotColumn = true ->
                      ihqGetCoeff headRowA pivotColumn = ihqGetCoeff headRowB pivotColumn := by
                    intro pivotColumn hHasp
                    cases hDec : Nat.decEq pivotColumn headLeadA with
                    | isTrue hEq =>
                        have hLeadAp : ihqLead headRowA = some pivotColumn := by
                          rw [hEq]; exact hHeadLeadA
                        have hLeadBp : ihqLead headRowB = some pivotColumn := by
                          rw [hEq, hLeadEq]; exact hHeadLeadB
                        rw [hUnitA headRowA pivotColumn hHeadAMem hLeadAp,
                          hUnitB headRowB pivotColumn hHeadBMem hLeadBp]
                    | isFalse hNe =>
                        have hLeadANep : ihqLead headRowA ≠ some pivotColumn := by
                          intro hc
                          exact hNe (Option.some.inj (hHeadLeadA.symm.trans hc)).symm
                        have hLeadBNep : ihqLead headRowB ≠ some pivotColumn := by
                          intro hc
                          exact hNe
                            (hLeadEq.trans (Option.some.inj (hHeadLeadB.symm.trans hc))).symm
                        have hHaspB : rmrHasLead (headRowB :: restRowsB) pivotColumn = true :=
                          (hPivotIff pivotColumn).mp hHasp
                        rw [hReducedA headRowA pivotColumn hHeadAMem hHasp hLeadANep,
                          hReducedB headRowB pivotColumn hHeadBMem hHaspB hLeadBNep]
                  have hHeadEq : headRowA = headRowB :=
                    rfcReducedSupportUnique (headRowA :: restRowsA) headRowA headRowB
                      hAllA hEchAFull hHeadAInSpanA hHeadBInSpanA hAgree
                  -- the tails have equal row space
                  have hTailSpanEq : (vector : List QnfRat) ->
                      (IhqMemSpan width restRowsA vector <->
                        IhqMemSpan width restRowsB vector) := by
                    intro vector
                    refine Iff.intro (fun hV => ?_) (fun hV => ?_)
                    · have hInWholeA : IhqMemSpan width (headRowA :: restRowsA) vector :=
                        ihqMemSpanWeaken headRowA hV
                      have hVZeroAtA : ihqGetCoeff vector headLeadA = qnfZero :=
                        ihqMemSpanCoeffZero headLeadA hRestAllA
                          (fun row hRow => ihqEchelonRowsCoeffZero hRestEchA row hRow) hV
                      have hInWholeB : IhqMemSpan width (headRowB :: restRowsB) vector :=
                        (hSpanEq vector).mp hInWholeA
                      have hVZeroAtB : ihqGetCoeff vector headLeadB = qnfZero := by
                        rw [<- hLeadEq]; exact hVZeroAtA
                      exact rfcTailSpanOfHeadZero headRowB restRowsB vector hAllB hEchBFull
                        headLeadB hHeadLeadB hHeadUnitB hInWholeB hVZeroAtB
                    · have hInWholeB : IhqMemSpan width (headRowB :: restRowsB) vector :=
                        ihqMemSpanWeaken headRowB hV
                      have hVZeroAtB : ihqGetCoeff vector headLeadB = qnfZero :=
                        ihqMemSpanCoeffZero headLeadB hRestAllB
                          (fun row hRow => ihqEchelonRowsCoeffZero hRestEchB row hRow) hV
                      have hInWholeA : IhqMemSpan width (headRowA :: restRowsA) vector :=
                        (hSpanEq vector).mpr hInWholeB
                      have hVZeroAtA : ihqGetCoeff vector headLeadA = qnfZero := by
                        rw [hLeadEq]; exact hVZeroAtB
                      exact rfcTailSpanOfHeadZero headRowA restRowsA vector hAllA hEchAFull
                        headLeadA hHeadLeadA hHeadUnitA hInWholeA hVZeroAtA
                  -- reduced echelon structure for the tails
                  have hUnitRestA : (row : List QnfRat) -> (pivotPosition : Nat) ->
                      IhqRowMem row restRowsA -> ihqLead row = some pivotPosition ->
                      ihqGetCoeff row pivotPosition = qnfOne :=
                    fun row pivotPosition hRow hLead =>
                      hUnitA row pivotPosition (IhqRowMem.tail hRow) hLead
                  have hReducedRestA : (row : List QnfRat) -> (pivotColumn : Nat) ->
                      IhqRowMem row restRowsA -> rmrHasLead restRowsA pivotColumn = true ->
                      ihqLead row ≠ some pivotColumn -> ihqGetCoeff row pivotColumn = qnfZero :=
                    fun row pivotColumn hRow hHasRest hNe =>
                      hReducedA row pivotColumn (IhqRowMem.tail hRow)
                        (rfcHasLeadConsMonotone headRowA restRowsA pivotColumn hHasRest) hNe
                  have hUnitRestB : (row : List QnfRat) -> (pivotPosition : Nat) ->
                      IhqRowMem row restRowsB -> ihqLead row = some pivotPosition ->
                      ihqGetCoeff row pivotPosition = qnfOne :=
                    fun row pivotPosition hRow hLead =>
                      hUnitB row pivotPosition (IhqRowMem.tail hRow) hLead
                  have hReducedRestB : (row : List QnfRat) -> (pivotColumn : Nat) ->
                      IhqRowMem row restRowsB -> rmrHasLead restRowsB pivotColumn = true ->
                      ihqLead row ≠ some pivotColumn -> ihqGetCoeff row pivotColumn = qnfZero :=
                    fun row pivotColumn hRow hHasRest hNe =>
                      hReducedB row pivotColumn (IhqRowMem.tail hRow)
                        (rfcHasLeadConsMonotone headRowB restRowsB pivotColumn hHasRest) hNe
                  have hRestEchB' : IhqEchelonFrom (headLeadA + 1) restRowsB := by
                    rw [hLeadEq]; exact hRestEchB
                  have hRedRestA : RfcIsReducedEchelonFrom width (headLeadA + 1) restRowsA :=
                    And.intro hRestAllA (And.intro hRestEchA
                      (And.intro hUnitRestA hReducedRestA))
                  have hRedRestB : RfcIsReducedEchelonFrom width (headLeadA + 1) restRowsB :=
                    And.intro hRestAllB (And.intro hRestEchB'
                      (And.intro hUnitRestB hReducedRestB))
                  have hTailEq : restRowsA = restRowsB :=
                    rfcReducedEchelonUniqueFrom (headLeadA + 1) restRowsA restRowsB
                      hRedRestA hRedRestB hTailSpanEq
                  rw [hHeadEq, hTailEq]

/-- **T3 (ABSTRACT, from 0)**: two reduced row echelon forms with the same row
space are equal.  Specialization of `rfcReducedEchelonUniqueFrom` at bound 0. -/
theorem rfcReducedEchelonUnique {width : Nat} (rowsA rowsB : List (List QnfRat))
    (hRedA : RfcIsReducedEchelonFrom width 0 rowsA)
    (hRedB : RfcIsReducedEchelonFrom width 0 rowsB)
    (hSpanEq : (vector : List QnfRat) ->
      (IhqMemSpan width rowsA vector <-> IhqMemSpan width rowsB vector)) :
    rowsA = rowsB :=
  rfcReducedEchelonUniqueFrom 0 rowsA rowsB hRedA hRedB hSpanEq

/-! ## Stage 4 — the concrete RREF uniqueness over `rreRref` (T3) -/

/-- The unit-lead normalize map preserves the pivot-column predicate (it preserves
each row's lead). -/
theorem rfcMapNormalizeHasLead : (rows : List (List QnfRat)) -> (pivotColumn : Nat) ->
    rmrHasLead (ihqMapRows rreNormalizeRow rows) pivotColumn = rmrHasLead rows pivotColumn
  | [], _pivotColumn => rfl
  | headRow :: restRows, pivotColumn => by
      show rmrHasLead (rreNormalizeRow headRow :: ihqMapRows rreNormalizeRow restRows) pivotColumn
        = rmrHasLead (headRow :: restRows) pivotColumn
      rw [rmrHasLeadConsShape (rreNormalizeRow headRow) (ihqMapRows rreNormalizeRow restRows)
          pivotColumn,
        rmrHasLeadConsShape headRow restRows pivotColumn, rreNormalizeRowLeadEq headRow,
        rfcMapNormalizeHasLead restRows pivotColumn]

/-- Normalization preserves a vanishing coefficient (it is a scaling). -/
theorem rfcNormalizeCoeffZero (sourceRow : List QnfRat) (position : Nat)
    (hZero : ihqGetCoeff sourceRow position = qnfZero) :
    ihqGetCoeff (rreNormalizeRow sourceRow) position = qnfZero := by
  cases hLead : ihqLead sourceRow with
  | none => rw [rreNormalizeRowNone sourceRow hLead]; exact hZero
  | some pivotPosition =>
      rw [rreNormalizeRowSome sourceRow pivotPosition hLead,
        ihqGetCoeffScale (qnfInv (ihqGetCoeff sourceRow pivotPosition)) sourceRow position, hZero,
        grqQnfMulZeroRight]

/-- **T3 (CONCRETE) — `rreRref` LANDS IN REDUCED ROW ECHELON FORM**: echelonize +
back-reduce + unit-lead normalization produces a genuine reduced row echelon form
(echelon staircase, unit pivots, zero at every other pivot). -/
theorem rfcRreRrefIsReducedEchelon {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : RfcIsReducedEchelonFrom width 0 (rreRref rows) := by
  have hEchAll : IhqAllWidth width (ihqEchelonize rows) := ihqEchelonizeWidth rows hAll
  have hEchEch : IhqEchelonFrom 0 (ihqEchelonize rows) := ihqEchelonizeEchelon rows hAll
  have hBR := rfcBackReduceEchelonReduced 0 (ihqEchelonize rows) hEchAll hEchEch
  refine And.intro (rreRrefWidth rows hAll) (And.intro ?_ (And.intro ?_ ?_))
  · exact rreMapEchelonFrom 0 (ihqRref rows) hBR.left
  · intro row pivotPosition hRow hLead
    exact rreRrefAllUnitLead rows row pivotPosition hRow hLead
  · intro row pivotColumn hRow hHasP hLeadNe
    cases ihqMapRowsMemInv rreNormalizeRow (ihqRref rows) hRow with
    | intro sourceRow hBoth =>
        have hRowEq : row = rreNormalizeRow sourceRow := hBoth.right
        have hSourceMem : IhqRowMem sourceRow (ihqRref rows) := hBoth.left
        have hSourceLeadNe : ihqLead sourceRow ≠ some pivotColumn := by
          intro hc
          apply hLeadNe
          rw [hRowEq, rreNormalizeRowLeadEq sourceRow]; exact hc
        have hEchHasP : rmrHasLead (ihqEchelonize rows) pivotColumn = true := by
          have hRrefHasP : rmrHasLead (ihqRref rows) pivotColumn = true := by
            rw [<- rfcMapNormalizeHasLead (ihqRref rows) pivotColumn]; exact hHasP
          have hPivotIff := rmrPivotSetSpanInvariant (ihqEchelonize rows) (ihqRref rows)
            hEchAll (ihqRrefWidth rows hAll) hEchEch hBR.left
            (fun vector => Iff.intro
              (fun hv => ihqBackReduceSpanSub2 (ihqEchelonize rows) hEchAll hv)
              (fun hv => ihqBackReduceSpanSub1 (ihqEchelonize rows) hEchAll hv))
          exact (hPivotIff pivotColumn).mpr hRrefHasP
        have hSourceZero : ihqGetCoeff sourceRow pivotColumn = qnfZero :=
          hBR.right sourceRow pivotColumn hSourceMem hEchHasP hSourceLeadNe
        rw [hRowEq]
        exact rfcNormalizeCoeffZero sourceRow pivotColumn hSourceZero

/-- **T3 (THE PAYOFF)**: span-equal inputs have LITERALLY equal reduced row
echelon forms `rreRref`.  This is the TRUE RREF-uniqueness theorem over the exact
`QnfRat` field — the reduced normalization (`rreRref`), NOT the un-normalized
`ihqRref` (which is refuted below). -/
theorem rfcRreRrefUnique {width : Nat} (rowsA rowsB : List (List QnfRat))
    (hAllA : IhqAllWidth width rowsA) (hAllB : IhqAllWidth width rowsB)
    (hSpanEq : (vector : List QnfRat) ->
      (IhqMemSpan width rowsA vector <-> IhqMemSpan width rowsB vector)) :
    rreRref rowsA = rreRref rowsB := by
  have hRrefSpanEq : (vector : List QnfRat) ->
      (IhqMemSpan width (rreRref rowsA) vector <-> IhqMemSpan width (rreRref rowsB) vector) :=
    fun vector => Iff.trans (rreRrefSpanIff rowsA hAllA vector)
      (Iff.trans (hSpanEq vector) (rreRrefSpanIff rowsB hAllB vector).symm)
  exact rfcReducedEchelonUnique (rreRref rowsA) (rreRref rowsB)
    (rfcRreRrefIsReducedEchelon rowsA hAllA) (rfcRreRrefIsReducedEchelon rowsB hAllB) hRrefSpanEq

/-- **T3 (Bool-hypothesis form)**: `ihqSpanEqB a b = true` gives equal reduced
forms — the decision-procedure-facing statement. -/
theorem rfcRreRrefUniqueOfSpanEqB {width : Nat} (rowsA rowsB : List (List QnfRat))
    (hAllA : IhqAllWidth width rowsA) (hAllB : IhqAllWidth width rowsB)
    (hSpanEqB : ihqSpanEqB rowsA rowsB = true) :
    rreRref rowsA = rreRref rowsB :=
  rfcRreRrefUnique rowsA rowsB hAllA hAllB
    (fun vector => ihqSpanEqBSound hAllA hAllB hSpanEqB vector)

/-! ## Stage 5 — the un-normalized `ihqRrefUniquenessStatement` is FALSE

The committed `ihqRrefUniquenessStatement` targets the UN-normalized `ihqRref`
(back-reduce without leading-1 normalization).  Over ℚ this is FALSE: `[[1, 2]]`
and `[[2, 4]]` span the same line, yet `ihqRref` leaves each pivot un-normalized,
so their reduced forms are the scalar-distinct `[[1, 2]]` and `[[2, 4]]`.  The
provable canonical target is the NORMALIZED `rreRref` (T3 above). -/

/-- The `(0,0)` coefficient of a matrix (canonical zero on empty). -/
def rfcHeadRowCoeff (rows : List (List QnfRat)) : QnfRat :=
  match rows with
  | [] => qnfZero
  | headRow :: _restRows => ihqGetCoeff headRow 0

/-- The un-normalized RREF-uniqueness statement is REFUTED (false as written): the
correct canonical target is `rreRref`, not `ihqRref`. -/
theorem rfcIhqRrefUniquenessRefuted : ¬ ihqRrefUniquenessStatement := by
  intro hUniq
  have hAllA : IhqAllWidth 2 [[qnfOfInt 1, qnfOfInt 2]] :=
    IhqAllWidth.cons rfl IhqAllWidth.nil
  have hAllB : IhqAllWidth 2 [[qnfOfInt 2, qnfOfInt 4]] :=
    IhqAllWidth.cons rfl IhqAllWidth.nil
  have hSpanEqB : ihqSpanEqB [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 2, qnfOfInt 4]] = true := rfl
  have hEq := hUniq 2 [[qnfOfInt 1, qnfOfInt 2]] [[qnfOfInt 2, qnfOfInt 4]] hAllA hAllB
    (fun vector => ihqSpanEqBSound hAllA hAllB hSpanEqB vector)
  have hLists : ihqRref [[qnfOfInt 1, qnfOfInt 2]] = ihqRref [[qnfOfInt 2, qnfOfInt 4]] := hEq
  have hNumEq : qnfOfInt 1 = qnfOfInt 2 := congrArg rfcHeadRowCoeff hLists
  have hBeqTrue : qnfBeq (qnfOfInt 1) (qnfOfInt 2) = true := (qnfBeqIffEq _ _).mpr hNumEq
  have hBeqFalse : qnfBeq (qnfOfInt 1) (qnfOfInt 2) = false := rfl
  exact Bool.noConfusion (hBeqTrue.symm.trans hBeqFalse)

/-! ## Stage 6 — kernel-`rfl` fires (T4) -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Fire (span-equal, single row): `[[1,2]]` and `[[2,4]]` are the same line, so
their reduced forms are EQUAL. -/
theorem rfcFireSpanEqualSingleRow :
    rreRref [[qnfOfInt 1, qnfOfInt 2]] = rreRref [[qnfOfInt 2, qnfOfInt 4]] := rfl

/-- Fire (span-equal, 2×2 with a zero row): `[[1,2],[0,0]]` and `[[2,4],[0,0]]`
have EQUAL reduced forms. -/
theorem rfcFireSpanEqualTwoByTwo :
    rreRref [[qnfOfInt 1, qnfOfInt 2], [qnfOfInt 0, qnfOfInt 0]]
      = rreRref [[qnfOfInt 2, qnfOfInt 4], [qnfOfInt 0, qnfOfInt 0]] := rfl

/-- Fire (the reduced form IS the identity for full-rank input): back-substitution
zeroes the free column — `[[1,2],[1,3]]` reduces to the identity. -/
theorem rfcFireIdentityReduced :
    rreRref [[qnfOfInt 1, qnfOfInt 2], [qnfOfInt 1, qnfOfInt 3]]
      = [[qnfOfInt 1, qnfOfInt 0], [qnfOfInt 0, qnfOfInt 1]] := rfl

/-- Fire (FALSE control): the two axis lines `[[1,0]]` and `[[0,1]]` are NOT
span-equal, so their reduced forms DIFFER — pinned as a `Bool` inequality. -/
theorem rfcFireDistinctNonSpanEqual :
    ihqSpanEqB [[qnfOfInt 1, qnfOfInt 0]] [[qnfOfInt 0, qnfOfInt 1]] = false := rfl

/-- Fire (FALSE control, the un-normalized `ihqRref` really differs): `ihqRref`
leaves `[[2,4]]` un-normalized — the concrete witness behind the refutation. -/
theorem rfcFireIhqRrefNotCanonical :
    ihqRref [[qnfOfInt 2, qnfOfInt 4]] = [[qnfOfInt 2, qnfOfInt 4]] := rfl

/-! ## Content marker -/

/-- Full RREF uniqueness over `QnfRat` is decided: span-equal inputs have literally equal reduced row echelon
forms `rreRref` (`rfcRreRrefUnique` / `rfcRreRrefUniqueOfSpanEqB`). The reduced-basis support characterization
(`rfcReducedSupportUnique`: a row-space vector is pinned by its pivot-column coordinates) and the back-reduce
structural theorem (`rfcBackReduceEchelonReduced`: back-reduction of an echelon form makes every row zero at
every other pivot — the free-column coordinate determination the earlier `rre`/`rmr` bricks walled) are the
new content, assembled through the abstract `rfcReducedEchelonUnique`. The committed `ihqRrefUniquenessStatement`
targets the un-normalized `ihqRref` and is refuted (`rfcIhqRrefUniquenessRefuted`, since `[[1,2]]` and `[[2,4]]`
span the same line with distinct `ihqRref`); the canonical target is the normalized `rreRref`, which is
unique. -/
def rfcHasRreRrefUniqueness : Bool := true

end FX1Poly.ComputerAlgebra
