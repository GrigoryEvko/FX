import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalLinearRelations

/-! # LinearAlgebra/RationalReducedEchelon — leading-1 normalization for the ℚ
    reduced row echelon form (WP-PROP-3 canonicity leg)

The QnfRat span/relations kit (`RationalLinearRelations`, prefix `ihq`) ships a
row-echelon canonicalizer `ihqRref = ihqBackReduce ∘ ihqEchelonize` with its
row-space preservation (`ihqRrefSpansSame`) but WITHOUT pivot normalization to
leading-1s — the one gap its own docstring flags (`ihqRrefUniquenessStatement`,
owner FALSE).  This file adds the missing normalization pass over the exact
`QnfRat` field: each row with a leading position is scaled by the inverse of its
leading coefficient (`qnfInv`), turning every pivot into `qnfOne`.

  * `rreNormalizeRow`   — scale a row to unit lead (all-zero rows are fixed);
  * `rreRef  rows`      — unit-lead ROW echelon form (`ihqEchelonize` then
                          normalize) — FULLY certified `RreIsUnitEchelon`
                          (echelon staircase + unit leads + width + span);
  * `rreRref rows`      — unit-lead REDUCED form (`ihqRref` then normalize) —
                          certified width + unit leads + row-space invariance.

Certified content (T1/T2):
  * `rreNormalizeRowUnitLead`  — the normalized pivot is `qnfOne`;
  * `rreNormalizeRowLeadEq`    — nonzero scaling preserves the leading position;
  * `rreMapEchelonFrom`        — the normalize map preserves the echelon invariant;
  * `rreRefIsUnitEchelon`      — `rreRef` output is a unit-lead row echelon form;
  * `rreRrefSpanIff` / `rreRrefSpanEqB` — the normalized form has the SAME row
                          space as the input (both the `IhqMemSpan` iff and the
                          Bool `ihqSpanEqB` pin);
  * `rreNormalizeRowScaleInvariant` — the normalized row is INVARIANT under any
                          nonzero scaling of the input (the rank-1 uniqueness
                          nucleus: two single generators of the same line
                          normalize identically).

The WALL (T3): full RREF uniqueness (span-equal ⇒ literally equal reduced form,
i.e. `ihqRrefUniquenessStatement`) is NOT discharged — see
`rreHasRrefUniqueness := false`.  Two genuinely-different attacks failed for the
same classical reason as the upstream F2 precedent: uniqueness of RREF is a
pivot-column-invariance theorem needing a rank/independence/exchange apparatus
absent from this Init-only kit.  Every DECISION use is already served by
`ihqSpanEqBSound`/`ihqSpanEqBComplete`; this brick reduces the wall to
pivot-SET invariance and lands the leading-1 canonicalizer + span invariance +
the scale-invariance nucleus. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — QnfRat scalar telescopes for the normalization pass -/

/-- A product of two nonzero scalars is nonzero (integral domain). -/
theorem rreQnfMulNeZero {leftValue rightValue : QnfRat}
    (hLeft : leftValue ≠ qnfZero) (hRight : rightValue ≠ qnfZero) :
    qnfMul leftValue rightValue ≠ qnfZero := by
  intro hZero
  exact hRight (ihqQnfFactorZeroOfMulPivotZero hLeft
    ((qnfMulComm rightValue leftValue).trans hZero))

/-- The inverse of a nonzero scalar is nonzero. -/
theorem rreQnfInvNeZero (value : QnfRat) (hValue : value ≠ qnfZero) :
    qnfInv value ≠ qnfZero := by
  intro hInvZero
  have hCancel : qnfMul value (qnfInv value) = qnfOne := qnfMulInvCancels hValue
  rw [hInvZero, grqQnfMulZeroRight value] at hCancel
  exact qnfZeroNeOne hCancel

/-- Multiplying by a nonzero scalar preserves the zero-comparison of the other
factor — the Bool identity behind lead-position preservation under scaling. -/
theorem rreQnfMulBeqZero (scalar coeff : QnfRat) (hScalar : scalar ≠ qnfZero) :
    qnfBeq (qnfMul scalar coeff) qnfZero = qnfBeq coeff qnfZero := by
  cases hBeq : qnfBeq coeff qnfZero with
  | true =>
      have hCoeffZero : coeff = qnfZero := ihqQnfEqZeroOfBeqZeroTrue hBeq
      rw [hCoeffZero, grqQnfMulZeroRight scalar, qnfBeqSelfIsTrue]
  | false =>
      have hCoeffNe : coeff ≠ qnfZero := ihqQnfNeZeroOfBeqZeroFalse hBeq
      cases hBeq2 : qnfBeq (qnfMul scalar coeff) qnfZero with
      | false => rfl
      | true =>
          have hProdZero : qnfMul scalar coeff = qnfZero := ihqQnfEqZeroOfBeqZeroTrue hBeq2
          have hCoeffZero : coeff = qnfZero :=
            ihqQnfFactorZeroOfMulPivotZero hScalar
              ((qnfMulComm coeff scalar).trans hProdZero)
          exact absurd hCoeffZero hCoeffNe

/-- Right cancellation by a nonzero scalar. -/
theorem rreQnfMulRightCancel {leftValue rightValue divisor : QnfRat}
    (hDivisor : divisor ≠ qnfZero)
    (hEq : qnfMul leftValue divisor = qnfMul rightValue divisor) :
    leftValue = rightValue := by
  have hLeft : leftValue = qnfMul (qnfMul leftValue divisor) (qnfInv divisor) := by
    rw [qnfMulAssoc leftValue divisor (qnfInv divisor),
      qnfMulInvCancels hDivisor, qnfMulOneRight leftValue]
  have hRight : rightValue = qnfMul (qnfMul rightValue divisor) (qnfInv divisor) := by
    rw [qnfMulAssoc rightValue divisor (qnfInv divisor),
      qnfMulInvCancels hDivisor, qnfMulOneRight rightValue]
  rw [hLeft, hRight, hEq]

/-- Scaling a row by a nonzero scalar preserves its leading position. -/
theorem rreLeadScaleEq (scalar : QnfRat) (hScalar : scalar ≠ qnfZero) :
    (row : List QnfRat) -> ihqLead (ihqRowScale scalar row) = ihqLead row
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show ihqLead (qnfMul scalar headCoeff :: ihqRowScale scalar restCoeffs)
        = ihqLead (headCoeff :: restCoeffs)
      rw [ihqLeadConsShape (qnfMul scalar headCoeff) (ihqRowScale scalar restCoeffs),
        ihqLeadConsShape headCoeff restCoeffs,
        rreQnfMulBeqZero scalar headCoeff hScalar,
        rreLeadScaleEq scalar hScalar restCoeffs]

/-! ## Stage 1 — the row normalizer: scale to unit lead -/

/-- Normalize a row to unit leading coefficient: scale by the inverse of the
leading entry (all-zero rows have no lead and are fixed points). -/
def rreNormalizeRow (row : List QnfRat) : List QnfRat :=
  match ihqLead row with
  | none => row
  | some pivotPosition => ihqRowScale (qnfInv (ihqGetCoeff row pivotPosition)) row

/-- Unfolding: an all-zero row is fixed. -/
theorem rreNormalizeRowNone (row : List QnfRat) (hLead : ihqLead row = none) :
    rreNormalizeRow row = row := by
  show (match ihqLead row with
    | none => row
    | some pivotPosition => ihqRowScale (qnfInv (ihqGetCoeff row pivotPosition)) row) = row
  rw [hLead]

/-- Unfolding: a row with a lead is scaled by the pivot inverse. -/
theorem rreNormalizeRowSome (row : List QnfRat) (pivotPosition : Nat)
    (hLead : ihqLead row = some pivotPosition) :
    rreNormalizeRow row = ihqRowScale (qnfInv (ihqGetCoeff row pivotPosition)) row := by
  show (match ihqLead row with
    | none => row
    | some pivotPosition => ihqRowScale (qnfInv (ihqGetCoeff row pivotPosition)) row)
    = ihqRowScale (qnfInv (ihqGetCoeff row pivotPosition)) row
  rw [hLead]

/-- Normalization preserves width. -/
theorem rreNormalizeRowLength (row : List QnfRat) :
    (rreNormalizeRow row).length = row.length := by
  cases hLead : ihqLead row with
  | none => rw [rreNormalizeRowNone row hLead]
  | some pivotPosition =>
      rw [rreNormalizeRowSome row pivotPosition hLead, ihqRowScaleLength]

/-- Normalization preserves the leading position. -/
theorem rreNormalizeRowLeadEq (row : List QnfRat) :
    ihqLead (rreNormalizeRow row) = ihqLead row := by
  cases hLead : ihqLead row with
  | none => rw [rreNormalizeRowNone row hLead]; exact hLead
  | some pivotPosition =>
      have hCoeffNe : ihqGetCoeff row pivotPosition ≠ qnfZero :=
        ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse row pivotPosition hLead)
      rw [rreNormalizeRowSome row pivotPosition hLead,
        rreLeadScaleEq (qnfInv (ihqGetCoeff row pivotPosition))
          (rreQnfInvNeZero (ihqGetCoeff row pivotPosition) hCoeffNe) row]
      exact hLead

/-- **THE NEW CONTENT**: after normalization, the leading coefficient is `qnfOne`. -/
theorem rreNormalizeRowUnitLead (row : List QnfRat) (pivotPosition : Nat)
    (hLead : ihqLead row = some pivotPosition) :
    ihqGetCoeff (rreNormalizeRow row) pivotPosition = qnfOne := by
  have hCoeffNe : ihqGetCoeff row pivotPosition ≠ qnfZero :=
    ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse row pivotPosition hLead)
  rw [rreNormalizeRowSome row pivotPosition hLead,
    ihqGetCoeffScale (qnfInv (ihqGetCoeff row pivotPosition)) row pivotPosition,
    qnfInvMulCancels hCoeffNe]

/-- An all-zero row is fixed by any scaling. -/
theorem rreScaleAllZeroRow (scalar : QnfRat) : (row : List QnfRat) ->
    ihqAreAllCoeffsZero row = true -> ihqRowScale scalar row = row
  | [], _hAll => rfl
  | headCoeff :: restCoeffs, hAll => by
      rw [ihqAreAllCoeffsZeroConsShape] at hAll
      cases hBeq : qnfBeq headCoeff qnfZero with
      | false => rw [hBeq] at hAll; exact Bool.noConfusion hAll
      | true =>
          rw [hBeq] at hAll
          have hHeadZero : headCoeff = qnfZero := ihqQnfEqZeroOfBeqZeroTrue hBeq
          show qnfMul scalar headCoeff :: ihqRowScale scalar restCoeffs
            = headCoeff :: restCoeffs
          rw [hHeadZero, grqQnfMulZeroRight scalar,
            rreScaleAllZeroRow scalar restCoeffs hAll]

/-- **THE RANK-1 UNIQUENESS NUCLEUS**: the normalized row is INVARIANT under any
nonzero scaling of the input — two single generators of the same line normalize
to the identical row. -/
theorem rreNormalizeRowScaleInvariant (scalar : QnfRat) (hScalar : scalar ≠ qnfZero)
    (row : List QnfRat) :
    rreNormalizeRow (ihqRowScale scalar row) = rreNormalizeRow row := by
  cases hLead : ihqLead row with
  | none =>
      have hScaledLead : ihqLead (ihqRowScale scalar row) = none := by
        rw [rreLeadScaleEq scalar hScalar row]; exact hLead
      rw [rreNormalizeRowNone (ihqRowScale scalar row) hScaledLead,
        rreNormalizeRowNone row hLead]
      exact rreScaleAllZeroRow scalar row (ihqLeadNoneAllZero row hLead)
  | some pivotPosition =>
      have hScaledLead : ihqLead (ihqRowScale scalar row) = some pivotPosition := by
        rw [rreLeadScaleEq scalar hScalar row]; exact hLead
      have hCoeffNe : ihqGetCoeff row pivotPosition ≠ qnfZero :=
        ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse row pivotPosition hLead)
      have hProdNe : qnfMul scalar (ihqGetCoeff row pivotPosition) ≠ qnfZero :=
        rreQnfMulNeZero hScalar hCoeffNe
      rw [rreNormalizeRowSome (ihqRowScale scalar row) pivotPosition hScaledLead,
        rreNormalizeRowSome row pivotPosition hLead,
        ihqGetCoeffScale scalar row pivotPosition,
        ihqRowScaleScale (qnfInv (qnfMul scalar (ihqGetCoeff row pivotPosition))) scalar row]
      congr 1
      apply rreQnfMulRightCancel hCoeffNe
      rw [qnfMulAssoc (qnfInv (qnfMul scalar (ihqGetCoeff row pivotPosition))) scalar
          (ihqGetCoeff row pivotPosition),
        qnfInvMulCancels hProdNe, qnfInvMulCancels hCoeffNe]

/-! ## Stage 2 — the normalize map and its span invariance (T2) -/

/-- A normalized generator lies in the original span (it is a scalar multiple of
a generator). -/
theorem rreNormalizeRowInSpan {width : Nat} {base : List (List QnfRat)}
    (hBaseAll : IhqAllWidth width base) {sourceRow : List QnfRat}
    (hRow : IhqRowMem sourceRow base) :
    IhqMemSpan width base (rreNormalizeRow sourceRow) := by
  cases hLead : ihqLead sourceRow with
  | none =>
      rw [rreNormalizeRowNone sourceRow hLead]
      exact ihqMemSpanElem hBaseAll hRow
  | some pivotPosition =>
      rw [rreNormalizeRowSome sourceRow pivotPosition hLead]
      exact ihqMemSpanScaleClosed (qnfInv (ihqGetCoeff sourceRow pivotPosition))
        (ihqMemSpanElem hBaseAll hRow)

/-- **SPAN INVARIANCE of the normalize map**: mapping `rreNormalizeRow` over a
generator list preserves the row space exactly. -/
theorem rreNormMapSpanIff {width : Nat} (base : List (List QnfRat))
    (hBaseAll : IhqAllWidth width base) (vector : List QnfRat) :
    IhqMemSpan width (ihqMapRows rreNormalizeRow base) vector
      <-> IhqMemSpan width base vector := by
  have hMappedAll : IhqAllWidth width (ihqMapRows rreNormalizeRow base) :=
    ihqMapRowsWidth rreNormalizeRow
      (fun row hLen => (rreNormalizeRowLength row).trans hLen) base hBaseAll
  refine Iff.intro (fun hMem => ?_) (fun hMem => ?_)
  · refine ihqMemSpanSub hBaseAll ?_ hMem
    intro row hRow
    have hInv := ihqMapRowsMemInv rreNormalizeRow base hRow
    cases hInv with
    | intro sourceRow hBoth =>
        rw [hBoth.right]
        exact rreNormalizeRowInSpan hBaseAll hBoth.left
  · refine ihqMemSpanSub hMappedAll ?_ hMem
    intro sourceRow hRow
    cases hLead : ihqLead sourceRow with
    | none =>
        have hMapMem : IhqRowMem (rreNormalizeRow sourceRow)
            (ihqMapRows rreNormalizeRow base) :=
          ihqMapRowsMemIntro rreNormalizeRow base hRow
        rw [rreNormalizeRowNone sourceRow hLead] at hMapMem
        exact ihqMemSpanElem hMappedAll hMapMem
    | some pivotPosition =>
        have hCoeffNe : ihqGetCoeff sourceRow pivotPosition ≠ qnfZero :=
          ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse sourceRow pivotPosition hLead)
        have hMapMem : IhqRowMem (rreNormalizeRow sourceRow)
            (ihqMapRows rreNormalizeRow base) :=
          ihqMapRowsMemIntro rreNormalizeRow base hRow
        rw [rreNormalizeRowSome sourceRow pivotPosition hLead] at hMapMem
        have hRecover : ihqRowScale (ihqGetCoeff sourceRow pivotPosition)
            (ihqRowScale (qnfInv (ihqGetCoeff sourceRow pivotPosition)) sourceRow)
            = sourceRow := by
          rw [ihqRowScaleScale (ihqGetCoeff sourceRow pivotPosition)
              (qnfInv (ihqGetCoeff sourceRow pivotPosition)) sourceRow,
            qnfMulInvCancels hCoeffNe, ihqRowScaleOne sourceRow]
        have hScaledMem := ihqMemSpanScaleClosed
          (ihqGetCoeff sourceRow pivotPosition)
          (ihqMemSpanElem hMappedAll hMapMem)
        rw [hRecover] at hScaledMem
        exact hScaledMem

/-- The normalize map preserves the echelon invariant (leads are unchanged). -/
theorem rreMapEchelonFrom : (lowerBound : Nat) -> (base : List (List QnfRat)) ->
    IhqEchelonFrom lowerBound base ->
    IhqEchelonFrom lowerBound (ihqMapRows rreNormalizeRow base)
  | lowerBound, [], _hEch => IhqEchelonFrom.nil lowerBound
  | _lowerBound, headRow :: restRows, hEch => by
      cases hEch with
      | cons headLead hLead hBound hRest =>
          show IhqEchelonFrom _
            (rreNormalizeRow headRow :: ihqMapRows rreNormalizeRow restRows)
          refine IhqEchelonFrom.cons headLead ?_ hBound
            (rreMapEchelonFrom (headLead + 1) restRows hRest)
          rw [rreNormalizeRowLeadEq headRow]
          exact hLead

/-! ## Stage 3 — the canonicalizers (T1) -/

/-- Unit-lead ROW echelon form: echelonize, then normalize each pivot to `qnfOne`. -/
def rreRef (rows : List (List QnfRat)) : List (List QnfRat) :=
  ihqMapRows rreNormalizeRow (ihqEchelonize rows)

/-- Unit-lead REDUCED row echelon form: back-substituted RREF, then normalize
each pivot to `qnfOne`. -/
def rreRref (rows : List (List QnfRat)) : List (List QnfRat) :=
  ihqMapRows rreNormalizeRow (ihqRref rows)

theorem rreRefWidth {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : IhqAllWidth width (rreRef rows) :=
  ihqMapRowsWidth rreNormalizeRow
    (fun row hLen => (rreNormalizeRowLength row).trans hLen)
    (ihqEchelonize rows) (ihqEchelonizeWidth rows hAll)

theorem rreRrefWidth {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : IhqAllWidth width (rreRref rows) :=
  ihqMapRowsWidth rreNormalizeRow
    (fun row hLen => (rreNormalizeRowLength row).trans hLen)
    (ihqRref rows) (ihqRrefWidth rows hAll)

/-- A list is in unit-lead row echelon form: correct width, strictly increasing
leads (staircase), and every leading coefficient equal to `qnfOne`. -/
def RreIsUnitEchelon (width : Nat) (rows : List (List QnfRat)) : Prop :=
  IhqAllWidth width rows
    /\ IhqEchelonFrom 0 rows
    /\ ((row : List QnfRat) -> (pivotPosition : Nat) -> IhqRowMem row rows ->
        ihqLead row = some pivotPosition -> ihqGetCoeff row pivotPosition = qnfOne)

/-- **T1 (FULLY CERTIFIED)**: `rreRef` outputs a unit-lead row echelon form. -/
theorem rreRefIsUnitEchelon {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : RreIsUnitEchelon width (rreRef rows) := by
  refine And.intro (rreRefWidth rows hAll) (And.intro ?_ ?_)
  · exact rreMapEchelonFrom 0 (ihqEchelonize rows) (ihqEchelonizeEchelon rows hAll)
  · intro row pivotPosition hRow hLead
    have hInv := ihqMapRowsMemInv rreNormalizeRow (ihqEchelonize rows) hRow
    cases hInv with
    | intro sourceRow hBoth =>
        have hRowEq : row = rreNormalizeRow sourceRow := hBoth.right
        have hSourceLead : ihqLead sourceRow = some pivotPosition := by
          rw [<- rreNormalizeRowLeadEq sourceRow, <- hRowEq]; exact hLead
        rw [hRowEq]
        exact rreNormalizeRowUnitLead sourceRow pivotPosition hSourceLead

/-- **T1 (reduced form)**: every leading coefficient of `rreRref` is `qnfOne`. -/
theorem rreRrefAllUnitLead (rows : List (List QnfRat)) (row : List QnfRat)
    (pivotPosition : Nat) (hRow : IhqRowMem row (rreRref rows))
    (hLead : ihqLead row = some pivotPosition) :
    ihqGetCoeff row pivotPosition = qnfOne := by
  have hInv := ihqMapRowsMemInv rreNormalizeRow (ihqRref rows) hRow
  cases hInv with
  | intro sourceRow hBoth =>
      have hRowEq : row = rreNormalizeRow sourceRow := hBoth.right
      have hSourceLead : ihqLead sourceRow = some pivotPosition := by
        rw [<- rreNormalizeRowLeadEq sourceRow, <- hRowEq]; exact hLead
      rw [hRowEq]
      exact rreNormalizeRowUnitLead sourceRow pivotPosition hSourceLead

/-! ## Stage 4 — span invariance of the canonicalizers (T2) -/

/-- `rreRef` preserves the row space (`IhqMemSpan` iff). -/
theorem rreRefSpanIff {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) (vector : List QnfRat) :
    IhqMemSpan width (rreRef rows) vector <-> IhqMemSpan width rows vector :=
  Iff.trans (rreNormMapSpanIff (ihqEchelonize rows) (ihqEchelonizeWidth rows hAll) vector)
    (Iff.intro (fun hMem => ihqEchelonizeSpanSub1 rows hAll hMem)
      (fun hMem => ihqEchelonizeSpanSub2 rows hAll hMem))

/-- **T2**: `rreRref` preserves the row space (`IhqMemSpan` iff). -/
theorem rreRrefSpanIff {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) (vector : List QnfRat) :
    IhqMemSpan width (rreRref rows) vector <-> IhqMemSpan width rows vector :=
  Iff.trans (rreNormMapSpanIff (ihqRref rows) (ihqRrefWidth rows hAll) vector)
    (ihqRrefSpansSame rows hAll vector)

/-- **T2 (Bool)**: `rreRef` has the same span as the input by the span decision. -/
theorem rreRefSpanEqB {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : ihqSpanEqB rows (rreRef rows) = true :=
  ihqSpanEqBComplete hAll (rreRefWidth rows hAll)
    (fun vector => (rreRefSpanIff rows hAll vector).symm)

/-- **T2 (Bool)**: `rreRref` has the same span as the input by the span decision. -/
theorem rreRrefSpanEqB {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : ihqSpanEqB rows (rreRref rows) = true :=
  ihqSpanEqBComplete hAll (rreRrefWidth rows hAll)
    (fun vector => (rreRrefSpanIff rows hAll vector).symm)

/-! ## Stage 5 — the uniqueness wall (T3) and the reduction (T4)

`ihqRrefUniquenessStatement` (span-equal inputs give LITERALLY equal reduced
forms) remains OWNER-FALSE upstream and is NOT discharged here.

Attacks tried:
  (1) pivot-column determination — the standard Hoffman–Kunze argument (pivot
      positions are a function of the row space; the column-prefix rank
      induction) requires a rank/dimension apparatus (linear independence, the
      exchange lemma) that this Init-only kit has no theory for;
  (2) byte-canonicalization via the leading-1s landed here — even with unit
      pivots and back-substituted columns, equality of outputs still reduces to
      (1) on the pivot SET (which columns are pivots).

What this brick DOES land, reducing the wall:
  * the leading-1 canonicalizer (`rreRref`) with certified unit pivots;
  * row-space invariance (`rreRrefSpanIff` / `rreRrefSpanEqB`);
  * the rank-1 nucleus (`rreNormalizeRowScaleInvariant`): a single generator's
    normalized form depends only on its LINE, so uniqueness holds for the
    dimension-≤1 fragment (single-generator matrices).

The residual is exactly pivot-SET invariance for dimension ≥ 2, i.e. the
classical rank apparatus.  Every DECISION consumer is served by
`ihqSpanEqBSound`/`ihqSpanEqBComplete`, so this is a canonical-byte-form gap
only. -/

/-- Owner FALSE: full RREF-uniqueness (`ihqRrefUniquenessStatement`) is not
discharged; the residual is pivot-SET invariance for dimension ≥ 2. -/
def rreHasRrefUniqueness : Bool := false

/-! ## Stage 6 — kernel-`rfl` fires (T5) -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Fire (single-row normalization): `[(2, 4)]` reduces to unit lead `[(1, 2)]`. -/
theorem rreFireNormalizeSingleRow :
    rreRref [[qnfOfInt 2, qnfOfInt 4]] = [[qnfOfInt 1, qnfOfInt 2]] := rfl

/-- Fire (2×2 to the identity): `[(2, 4), (1, 3)]` — full forward + back
substitution + leading-1 normalization — is the identity matrix. -/
theorem rreFireIdentityTwoByTwo :
    rreRref [[qnfOfInt 2, qnfOfInt 4], [qnfOfInt 1, qnfOfInt 3]]
      = [[qnfOfInt 1, qnfOfInt 0], [qnfOfInt 0, qnfOfInt 1]] := rfl

/-- Fire (**concrete uniqueness**): the span-equal matrices `[(2, 4)]` and
`[(1, 2)]` — same line, scalar-2 apart — have the IDENTICAL reduced form. -/
theorem rreFireSpanEqualConverge :
    rreRref [[qnfOfInt 2, qnfOfInt 4]] = rreRref [[qnfOfInt 1, qnfOfInt 2]] := rfl

/-- Fire (FALSE control, first axis): the `x`-axis line is its own reduced form. -/
theorem rreFireFalseControlFirst :
    rreRref [[qnfOfInt 1, qnfOfInt 0]] = [[qnfOfInt 1, qnfOfInt 0]] := rfl

/-- Fire (FALSE control, second axis): the `y`-axis line is its own reduced
form — DISTINCT from the first, matching their distinct spans. -/
theorem rreFireFalseControlSecond :
    rreRref [[qnfOfInt 0, qnfOfInt 1]] = [[qnfOfInt 0, qnfOfInt 1]] := rfl

/-- Fire (FALSE control, span side): the two axis lines are NOT span-equal, so
distinct reduced forms is the correct behaviour. -/
theorem rreFireDistinctRrefNonSpanEqual :
    ihqSpanEqB [[qnfOfInt 1, qnfOfInt 0]] [[qnfOfInt 0, qnfOfInt 1]] = false := rfl

/-! ## Stage 7 — content markers -/

/-- DECIDED: the leading-1 canonicalizer is SHIPPED — `rreRref` normalizes every
pivot to `qnfOne`, certified by `rreRrefAllUnitLead` and (for the row-echelon
variant `rreRef`) the full `RreIsUnitEchelon` predicate. -/
def rreHasUnitLeadCanonicalizer : Bool := true

/-- DECIDED: the normalized form is row-space invariant — `rreRrefSpanIff` (the
`IhqMemSpan` iff) and `rreRrefSpanEqB` (the Bool `ihqSpanEqB` pin). -/
def rreHasSpanInvariance : Bool := true

end FX1Poly.ComputerAlgebra
