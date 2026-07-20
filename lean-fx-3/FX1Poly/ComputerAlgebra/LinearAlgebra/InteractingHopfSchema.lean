import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfWhisker

/-! # LinearAlgebra/InteractingHopfSchema — the IH_Q scalar schemas + NF census seed (WP-PROP-3 brick 4)

THE SCALAR-SCHEMA ADJUDICATION (HALF A, executing the brick-3 route note on
`ihwHasWhiskerCongruence` item (2) by SUPERSESSION): the committed presentation
(`InteractingHopfSeed`) ships its scalar-indexed axiom families only at
INSTANTIATED scalars (k in {2, 3, 5, 6, -1, 0, 1}); the faithful BSZ reading
(arXiv:1403.7048v4 Definition 6.1) is that those families are SCHEMAS indexed
by k in Q.  This brick mints `IhzRowMove`: PARAMETERIZED scalar row
constructors — product/sum/antipode-cancel/unit-absorption and the
through-(co)add/(co)copy commutation families, each in BOTH orientations —
alongside an embedding arm for EVERY committed `IhsRowTag` row.  Each schema's
soundness is a THEOREM-level span equality quantified over the scalar
arguments (via the qnf ring/field laws and per-cell pair-membership specs),
NOT an `rfl` pin — the brick-2 report showed general diagram-level rows are
not `rfl`-decidable (echelonization scrutinizes the symbolic scalar), which
blocks GATE pins but NOT quantified soundness lemmas.  On top: the whisker
congruence `IhzConv` over the schema rows (the `IhwStep.pad` shape, reusing
the committed pad machinery), soundness `ihzConvSound`, the refutation bridge
`ihzConvSpanEqB`, the embedding `IhwConv -> IhzConv`, and FRESH-SCALAR fires —
`scalarBox 4 ; scalarBox (1/2)` converts to `scalarBox 2` (scalars NOT in the
committed row set: THE pin that the schema gap is closed), an antipode-family
fire at the fresh scalar 4, and a FALSE control at fresh scalars.

THE NF CARRIER + CENSUS SEED (HALF B, partial per the stall policy): the
CANONICAL NF chooser `ihzCanonicalRows` (leading-one reduced row echelon form:
`ihqRref` from brick 1 plus pivot normalization through `qnfInv`) with span
preservation, width invariants, and kernel-`rfl` fires; the BSZ Theorem 6.4
factorized-shape BASE CASES as diagrams (the zero-relation diagram — the
`rows = []` normal form — fully proven at THEOREM level for arbitrary
boundaries); the OWNER-FALSE statements `ihzNormalFormStatement` (the full
span-of-matrices carrier) and `ihzReachabilityStatement` (completeness of
`IhzConv`), each carrying the precise residual for brick 5.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfSchema.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — list-shape and span-inversion helpers -/

/-- A length-one coefficient row is a singleton. -/
theorem ihzLengthOneShape : (vector : List QnfRat) -> vector.length = 1 ->
    Exists fun headCoeff => vector = [headCoeff]
  | [], hLen => nomatch hLen
  | headCoeff :: restCoeffs, hLen =>
      Exists.intro headCoeff
        (congrArg (fun tailPart => headCoeff :: tailPart)
          (ihsLengthZeroNil restCoeffs (Nat.succ.inj hLen)))

/-- A length-two coefficient row is a literal pair. -/
theorem ihzLengthTwoShape (vector : List QnfRat) (hLen : vector.length = 2) :
    Exists fun firstCoeff => Exists fun secondCoeff =>
      vector = [firstCoeff, secondCoeff] := by
  cases vector with
  | nil => exact nomatch hLen
  | cons headCoeff restCoeffs =>
      cases ihzLengthOneShape restCoeffs (Nat.succ.inj hLen) with
      | intro secondCoeff hRest =>
          exact Exists.intro headCoeff (Exists.intro secondCoeff
            (congrArg (fun tailPart => headCoeff :: tailPart) hRest))

/-- Span inversion for a single generator: every member is one scalar multiple. -/
theorem ihzMemSpanSingleInv {width : Nat} {row vector : List QnfRat}
    (hRowLen : row.length = width) (hMem : IhqMemSpan width [row] vector) :
    Exists fun pickCoeff => vector = ihqRowScale pickCoeff row := by
  cases ihqMemSpanConsInv hMem with
  | inl hInNil =>
      refine Exists.intro qnfZero ?_
      rw [ihqMemSpanNilInv hInNil, ihqRowScaleZeroScalar row, hRowLen]
  | inr hSplit =>
      cases hSplit with
      | intro headScalar hPack =>
          cases hPack with
          | intro partner hBoth =>
              refine Exists.intro headScalar ?_
              rw [hBoth.right, ihqMemSpanNilInv hBoth.left]
              exact ihqRowAddZeroRight (ihqRowScale headScalar row) width
                ((ihqRowScaleLength headScalar row).trans hRowLen)

/-- Span introduction for a single generator. -/
theorem ihzMemSpanSingleIntro {width : Nat} (row : List QnfRat)
    (pickCoeff : QnfRat) (hRowLen : row.length = width) :
    IhqMemSpan width [row] (ihqRowScale pickCoeff row) := by
  have hPicked := IhqMemSpan.pick (width := width) (rows := [row]) pickCoeff row
    (IhqRowMem.head row []) IhqMemSpan.zero
  rw [ihqRowAddZeroRight (ihqRowScale pickCoeff row) width
    ((ihqRowScaleLength pickCoeff row).trans hRowLen)] at hPicked
  exact hPicked

/-- Span inversion for two generators: every member is a two-term combination. -/
theorem ihzMemSpanPairInv {width : Nat} {firstRow secondRow vector : List QnfRat}
    (hFirstLen : firstRow.length = width) (hSecondLen : secondRow.length = width)
    (hMem : IhqMemSpan width [firstRow, secondRow] vector) :
    Exists fun firstCoeff => Exists fun secondCoeff =>
      vector = ihqRowAdd (ihqRowScale firstCoeff firstRow)
        (ihqRowScale secondCoeff secondRow) := by
  cases ihqMemSpanConsInv hMem with
  | inl hInRest =>
      cases ihzMemSpanSingleInv hSecondLen hInRest with
      | intro secondCoeff hVecEq =>
          refine Exists.intro qnfZero (Exists.intro secondCoeff ?_)
          rw [hVecEq, ihqRowScaleZeroScalar firstRow, hFirstLen,
            ihqRowAddZeroLeft (ihqRowScale secondCoeff secondRow) width
              ((ihqRowScaleLength secondCoeff secondRow).trans hSecondLen)]
  | inr hSplit =>
      cases hSplit with
      | intro firstCoeff hPack =>
          cases hPack with
          | intro partner hBoth =>
              cases ihzMemSpanSingleInv hSecondLen hBoth.left with
              | intro secondCoeff hPartnerEq =>
                  refine Exists.intro firstCoeff (Exists.intro secondCoeff ?_)
                  rw [hBoth.right, hPartnerEq]

/-- Span introduction for two generators. -/
theorem ihzMemSpanPairIntro {width : Nat} (firstRow secondRow : List QnfRat)
    (firstCoeff secondCoeff : QnfRat) (_hFirstLen : firstRow.length = width)
    (hSecondLen : secondRow.length = width) :
    IhqMemSpan width [firstRow, secondRow]
      (ihqRowAdd (ihqRowScale firstCoeff firstRow)
        (ihqRowScale secondCoeff secondRow)) := by
  have hSecondPicked := IhqMemSpan.pick (width := width)
    (rows := [firstRow, secondRow]) secondCoeff secondRow
    (IhqRowMem.tail (IhqRowMem.head secondRow [])) IhqMemSpan.zero
  rw [ihqRowAddZeroRight (ihqRowScale secondCoeff secondRow) width
    ((ihqRowScaleLength secondCoeff secondRow).trans hSecondLen)] at hSecondPicked
  exact IhqMemSpan.pick firstCoeff firstRow
    (IhqRowMem.head firstRow [secondRow]) hSecondPicked

/-- Right cancellation in the qnf field: equal products with a common NONZERO
right factor have equal left factors (the I1 forward-cancel workhorse). -/
theorem ihzMulRightCancel {firstFactor secondFactor scaleFactor : QnfRat}
    (hNonzero : scaleFactor ≠ qnfZero)
    (hEq : qnfMul firstFactor scaleFactor = qnfMul secondFactor scaleFactor) :
    firstFactor = secondFactor := by
  have hChain : firstFactor
      = qnfMul (qnfMul firstFactor scaleFactor) (qnfInv scaleFactor) := by
    rw [qnfMulAssoc, qnfMulInvCancels hNonzero, qnfMulOneRight]
  rw [hChain, hEq, qnfMulAssoc, qnfMulInvCancels hNonzero, qnfMulOneRight]

/-! ## Stage 1 — pair-membership specs for the generator matrices

Each spec characterizes `IhqPairMem` of one cell's (or one two-cell scalar
layer's) generator matrix.  These are the semantic atoms every schema
soundness proof chains through `ihqComposeSpec`. -/

/-- The empty generator matrix relates exactly the zero vectors. -/
theorem ihzNilRelationSpec (domWidth codWidth : Nat) (domVec codVec : List QnfRat) :
    IhqPairMem domWidth codWidth [] domVec codVec
      <-> (domVec = ihqZeroRow domWidth /\ codVec = ihqZeroRow codWidth) := by
  refine Iff.intro ?_ ?_
  · intro hPair
    have hCatZero := ihqMemSpanNilInv hPair.right.right
    rw [<- ihqCatZeroZero domWidth codWidth] at hCatZero
    have hSplit := ihqCatInj domVec codVec (ihqZeroRow domWidth)
      (ihqZeroRow codWidth)
      (hPair.left.trans (ihqZeroRowLength domWidth).symm) hCatZero
    exact hSplit
  · intro hBoth
    refine And.intro ?_ (And.intro ?_ ?_)
    · rw [hBoth.left]
      exact ihqZeroRowLength domWidth
    · rw [hBoth.right]
      exact ihqZeroRowLength codWidth
    · rw [hBoth.left, hBoth.right, ihqCatZeroZero domWidth codWidth]
      exact IhqMemSpan.zero

/-- The white unit (zero state, `0 -> 1`): the empty matrix pins the output at 0. -/
theorem ihzZeroStateSpec (domVec codVec : List QnfRat) :
    IhqPairMem 0 1 [] domVec codVec
      <-> (domVec = [] /\ codVec = [qnfZero]) :=
  ihzNilRelationSpec 0 1 domVec codVec

/-- The white counit (cozero, `1 -> 0`): the empty matrix pins the input at 0. -/
theorem ihzCozeroStateSpec (domVec codVec : List QnfRat) :
    IhqPairMem 1 0 [] domVec codVec
      <-> (domVec = [qnfZero] /\ codVec = []) :=
  ihzNilRelationSpec 1 0 domVec codVec

/-- The scalar box graph `[[1, k]]` relates `[a]` to `[a * k]`. -/
theorem ihzScalarGraphSpec (scalarValue : QnfRat) (domVec codVec : List QnfRat) :
    IhqPairMem 1 1 [[qnfOne, scalarValue]] domVec codVec
      <-> Exists fun inputCoeff =>
            domVec = [inputCoeff] /\ codVec = [qnfMul inputCoeff scalarValue] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthOneShape domVec hPair.left with
    | intro inputCoeff hDomEq =>
        cases ihzLengthOneShape codVec hPair.right.left with
        | intro outputCoeff hCodEq =>
            have hMem := hPair.right.right
            rw [hDomEq, hCodEq] at hMem
            cases ihzMemSpanSingleInv (width := 2) rfl hMem with
            | intro pickCoeff hVecEq =>
                have hHeadEq : inputCoeff = qnfMul pickCoeff qnfOne :=
                  congrArg (fun row => ihqGetCoeff row 0) hVecEq
                have hTailEq : outputCoeff = qnfMul pickCoeff scalarValue :=
                  congrArg (fun row => ihqGetCoeff row 1) hVecEq
                have hPickIsInput : inputCoeff = pickCoeff :=
                  hHeadEq.trans (qnfMulOneRight pickCoeff)
                refine Exists.intro inputCoeff (And.intro hDomEq ?_)
                rw [hCodEq, hTailEq, hPickIsInput]
  · intro hExists
    cases hExists with
    | intro inputCoeff hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left]
          exact rfl
        · rw [hBoth.right]
          exact rfl
        · rw [hBoth.left, hBoth.right]
          have hCombo : ihqRowScale inputCoeff [qnfOne, scalarValue]
              = [inputCoeff, qnfMul inputCoeff scalarValue] := by
            show [qnfMul inputCoeff qnfOne, qnfMul inputCoeff scalarValue]
              = [inputCoeff, qnfMul inputCoeff scalarValue]
            rw [qnfMulOneRight inputCoeff]
          have hMem := ihzMemSpanSingleIntro (width := 2)
            [qnfOne, scalarValue] inputCoeff rfl
          rw [hCombo] at hMem
          exact hMem

/-- The mirror scalar box graph `[[k, 1]]` relates `[o * k]` to `[o]`. -/
theorem ihzScalarMirrorSpec (scalarValue : QnfRat) (domVec codVec : List QnfRat) :
    IhqPairMem 1 1 [[scalarValue, qnfOne]] domVec codVec
      <-> Exists fun outputCoeff =>
            domVec = [qnfMul outputCoeff scalarValue] /\ codVec = [outputCoeff] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthOneShape domVec hPair.left with
    | intro inputCoeff hDomEq =>
        cases ihzLengthOneShape codVec hPair.right.left with
        | intro outputCoeff hCodEq =>
            have hMem := hPair.right.right
            rw [hDomEq, hCodEq] at hMem
            cases ihzMemSpanSingleInv (width := 2) rfl hMem with
            | intro pickCoeff hVecEq =>
                have hHeadEq : inputCoeff = qnfMul pickCoeff scalarValue :=
                  congrArg (fun row => ihqGetCoeff row 0) hVecEq
                have hTailEq : outputCoeff = qnfMul pickCoeff qnfOne :=
                  congrArg (fun row => ihqGetCoeff row 1) hVecEq
                have hPickIsOutput : outputCoeff = pickCoeff :=
                  hTailEq.trans (qnfMulOneRight pickCoeff)
                refine Exists.intro outputCoeff (And.intro ?_ hCodEq)
                rw [hDomEq, hHeadEq, hPickIsOutput]
  · intro hExists
    cases hExists with
    | intro outputCoeff hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left]
          exact rfl
        · rw [hBoth.right]
          exact rfl
        · rw [hBoth.left, hBoth.right]
          have hCombo : ihqRowScale outputCoeff [scalarValue, qnfOne]
              = [qnfMul outputCoeff scalarValue, outputCoeff] := by
            show [qnfMul outputCoeff scalarValue, qnfMul outputCoeff qnfOne]
              = [qnfMul outputCoeff scalarValue, outputCoeff]
            rw [qnfMulOneRight outputCoeff]
          have hMem := ihzMemSpanSingleIntro (width := 2)
            [scalarValue, qnfOne] outputCoeff rfl
          rw [hCombo] at hMem
          exact hMem

/-- The wire graph `[[1, 1]]` relates `[c]` to `[c]`. -/
theorem ihzWireSpec (domVec codVec : List QnfRat) :
    IhqPairMem 1 1 [[qnfOne, qnfOne]] domVec codVec
      <-> Exists fun throughCoeff =>
            domVec = [throughCoeff] /\ codVec = [throughCoeff] := by
  refine Iff.trans (ihzScalarGraphSpec qnfOne domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro inputCoeff hBoth =>
        refine Exists.intro inputCoeff (And.intro hBoth.left ?_)
        rw [hBoth.right, qnfMulOneRight]
  · intro hExists
    cases hExists with
    | intro throughCoeff hBoth =>
        refine Exists.intro throughCoeff (And.intro hBoth.left ?_)
        rw [hBoth.right, qnfMulOneRight]

/-- The copy graph (`blackComult`, `1 -> 2`, matrix `[[1,1,1]]`). -/
theorem ihzCopySpec (domVec codVec : List QnfRat) :
    IhqPairMem 1 2 [[qnfOne, qnfOne, qnfOne]] domVec codVec
      <-> Exists fun throughCoeff =>
            domVec = [throughCoeff] /\ codVec = [throughCoeff, throughCoeff] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthOneShape domVec hPair.left with
    | intro inputCoeff hDomEq =>
        cases ihzLengthTwoShape codVec hPair.right.left with
        | intro firstOut hPack =>
            cases hPack with
            | intro secondOut hCodEq =>
                have hMem := hPair.right.right
                rw [hDomEq, hCodEq] at hMem
                cases ihzMemSpanSingleInv (width := 3) rfl hMem with
                | intro pickCoeff hVecEq =>
                    have hInEq : inputCoeff = qnfMul pickCoeff qnfOne :=
                      congrArg (fun row => ihqGetCoeff row 0) hVecEq
                    have hFirstEq : firstOut = qnfMul pickCoeff qnfOne :=
                      congrArg (fun row => ihqGetCoeff row 1) hVecEq
                    have hSecondEq : secondOut = qnfMul pickCoeff qnfOne :=
                      congrArg (fun row => ihqGetCoeff row 2) hVecEq
                    refine Exists.intro inputCoeff (And.intro hDomEq ?_)
                    rw [hCodEq, hFirstEq, hSecondEq, hInEq]
  · intro hExists
    cases hExists with
    | intro throughCoeff hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left]
          exact rfl
        · rw [hBoth.right]
          exact rfl
        · rw [hBoth.left, hBoth.right]
          have hCombo : ihqRowScale throughCoeff [qnfOne, qnfOne, qnfOne]
              = [throughCoeff, throughCoeff, throughCoeff] := by
            show [qnfMul throughCoeff qnfOne, qnfMul throughCoeff qnfOne,
                qnfMul throughCoeff qnfOne]
              = [throughCoeff, throughCoeff, throughCoeff]
            rw [qnfMulOneRight throughCoeff]
          have hMem := ihzMemSpanSingleIntro (width := 3)
            [qnfOne, qnfOne, qnfOne] throughCoeff rfl
          rw [hCombo] at hMem
          exact hMem

/-- The cocopy graph (`blackMult`, `2 -> 1`, the same matrix `[[1,1,1]]` split
`2 + 1`): equal inputs, output the common value. -/
theorem ihzCocopySpec (domVec codVec : List QnfRat) :
    IhqPairMem 2 1 [[qnfOne, qnfOne, qnfOne]] domVec codVec
      <-> Exists fun throughCoeff =>
            domVec = [throughCoeff, throughCoeff] /\ codVec = [throughCoeff] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthTwoShape domVec hPair.left with
    | intro firstIn hPack =>
        cases hPack with
        | intro secondIn hDomEq =>
            cases ihzLengthOneShape codVec hPair.right.left with
            | intro outputCoeff hCodEq =>
                have hMem := hPair.right.right
                rw [hDomEq, hCodEq] at hMem
                cases ihzMemSpanSingleInv (width := 3) rfl hMem with
                | intro pickCoeff hVecEq =>
                    have hFirstEq : firstIn = qnfMul pickCoeff qnfOne :=
                      congrArg (fun row => ihqGetCoeff row 0) hVecEq
                    have hSecondEq : secondIn = qnfMul pickCoeff qnfOne :=
                      congrArg (fun row => ihqGetCoeff row 1) hVecEq
                    have hOutEq : outputCoeff = qnfMul pickCoeff qnfOne :=
                      congrArg (fun row => ihqGetCoeff row 2) hVecEq
                    refine Exists.intro outputCoeff (And.intro ?_ hCodEq)
                    rw [hDomEq, hFirstEq, hSecondEq, hOutEq]
  · intro hExists
    cases hExists with
    | intro throughCoeff hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left]
          exact rfl
        · rw [hBoth.right]
          exact rfl
        · rw [hBoth.left, hBoth.right]
          have hCombo : ihqRowScale throughCoeff [qnfOne, qnfOne, qnfOne]
              = [throughCoeff, throughCoeff, throughCoeff] := by
            show [qnfMul throughCoeff qnfOne, qnfMul throughCoeff qnfOne,
                qnfMul throughCoeff qnfOne]
              = [throughCoeff, throughCoeff, throughCoeff]
            rw [qnfMulOneRight throughCoeff]
          have hMem := ihzMemSpanSingleIntro (width := 3)
            [qnfOne, qnfOne, qnfOne] throughCoeff rfl
          rw [hCombo] at hMem
          exact hMem

/-- The addition graph (`whiteMult`, `2 -> 1`, matrix `[[1,0,1],[0,1,1]]`). -/
theorem ihzAddSpec (domVec codVec : List QnfRat) :
    IhqPairMem 2 1 [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
      domVec codVec
      <-> Exists fun firstIn => Exists fun secondIn =>
            domVec = [firstIn, secondIn] /\ codVec = [qnfAdd firstIn secondIn] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthTwoShape domVec hPair.left with
    | intro firstIn hPack =>
        cases hPack with
        | intro secondIn hDomEq =>
            cases ihzLengthOneShape codVec hPair.right.left with
            | intro outputCoeff hCodEq =>
                have hMem := hPair.right.right
                rw [hDomEq, hCodEq] at hMem
                cases ihzMemSpanPairInv (width := 3) rfl rfl hMem with
                | intro firstCoeff hInnerPack =>
                    cases hInnerPack with
                    | intro secondCoeff hVecEq =>
                        have hFirstEq : firstIn
                            = qnfAdd (qnfMul firstCoeff qnfOne)
                                (qnfMul secondCoeff qnfZero) :=
                          congrArg (fun row => ihqGetCoeff row 0) hVecEq
                        have hSecondEq : secondIn
                            = qnfAdd (qnfMul firstCoeff qnfZero)
                                (qnfMul secondCoeff qnfOne) :=
                          congrArg (fun row => ihqGetCoeff row 1) hVecEq
                        have hOutEq : outputCoeff
                            = qnfAdd (qnfMul firstCoeff qnfOne)
                                (qnfMul secondCoeff qnfOne) :=
                          congrArg (fun row => ihqGetCoeff row 2) hVecEq
                        have hFirstIs : firstIn = firstCoeff := by
                          rw [hFirstEq, qnfMulOneRight,
                            grqQnfMulZeroRight, qnfAddZeroRight]
                        have hSecondIs : secondIn = secondCoeff := by
                          rw [hSecondEq, qnfMulOneRight,
                            grqQnfMulZeroRight, qnfAddZeroLeft]
                        refine Exists.intro firstIn (Exists.intro secondIn
                          (And.intro hDomEq ?_))
                        rw [hCodEq, hOutEq, qnfMulOneRight, qnfMulOneRight,
                          hFirstIs, hSecondIs]
  · intro hExists
    cases hExists with
    | intro firstIn hPack =>
        cases hPack with
        | intro secondIn hBoth =>
            refine And.intro ?_ (And.intro ?_ ?_)
            · rw [hBoth.left]
              exact rfl
            · rw [hBoth.right]
              exact rfl
            · rw [hBoth.left, hBoth.right]
              have hCombo : ihqRowAdd
                  (ihqRowScale firstIn [qnfOne, qnfZero, qnfOne])
                  (ihqRowScale secondIn [qnfZero, qnfOne, qnfOne])
                  = [firstIn, secondIn, qnfAdd firstIn secondIn] := by
                show [qnfAdd (qnfMul firstIn qnfOne) (qnfMul secondIn qnfZero),
                    qnfAdd (qnfMul firstIn qnfZero) (qnfMul secondIn qnfOne),
                    qnfAdd (qnfMul firstIn qnfOne) (qnfMul secondIn qnfOne)]
                  = [firstIn, secondIn, qnfAdd firstIn secondIn]
                rw [qnfMulOneRight firstIn, qnfMulOneRight secondIn,
                  grqQnfMulZeroRight firstIn, grqQnfMulZeroRight secondIn,
                  qnfAddZeroRight firstIn, qnfAddZeroLeft secondIn]
              have hMem := ihzMemSpanPairIntro (width := 3)
                [qnfOne, qnfZero, qnfOne] [qnfZero, qnfOne, qnfOne]
                firstIn secondIn rfl rfl
              rw [hCombo] at hMem
              exact hMem

/-- The coaddition graph (`whiteComult`, `1 -> 2`, matrix `[[1,1,0],[1,0,1]]`). -/
theorem ihzCoaddSpec (domVec codVec : List QnfRat) :
    IhqPairMem 1 2 [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
      domVec codVec
      <-> Exists fun firstOut => Exists fun secondOut =>
            domVec = [qnfAdd firstOut secondOut]
              /\ codVec = [firstOut, secondOut] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthOneShape domVec hPair.left with
    | intro inputCoeff hDomEq =>
        cases ihzLengthTwoShape codVec hPair.right.left with
        | intro firstOut hPack =>
            cases hPack with
            | intro secondOut hCodEq =>
                have hMem := hPair.right.right
                rw [hDomEq, hCodEq] at hMem
                cases ihzMemSpanPairInv (width := 3) rfl rfl hMem with
                | intro firstCoeff hInnerPack =>
                    cases hInnerPack with
                    | intro secondCoeff hVecEq =>
                        have hInEq : inputCoeff
                            = qnfAdd (qnfMul firstCoeff qnfOne)
                                (qnfMul secondCoeff qnfOne) :=
                          congrArg (fun row => ihqGetCoeff row 0) hVecEq
                        have hFirstEq : firstOut
                            = qnfAdd (qnfMul firstCoeff qnfOne)
                                (qnfMul secondCoeff qnfZero) :=
                          congrArg (fun row => ihqGetCoeff row 1) hVecEq
                        have hSecondEq : secondOut
                            = qnfAdd (qnfMul firstCoeff qnfZero)
                                (qnfMul secondCoeff qnfOne) :=
                          congrArg (fun row => ihqGetCoeff row 2) hVecEq
                        have hFirstIs : firstOut = firstCoeff := by
                          rw [hFirstEq, qnfMulOneRight,
                            grqQnfMulZeroRight, qnfAddZeroRight]
                        have hSecondIs : secondOut = secondCoeff := by
                          rw [hSecondEq, qnfMulOneRight,
                            grqQnfMulZeroRight, qnfAddZeroLeft]
                        refine Exists.intro firstOut (Exists.intro secondOut
                          (And.intro ?_ hCodEq))
                        rw [hDomEq, hInEq, qnfMulOneRight, qnfMulOneRight,
                          hFirstIs, hSecondIs]
  · intro hExists
    cases hExists with
    | intro firstOut hPack =>
        cases hPack with
        | intro secondOut hBoth =>
            refine And.intro ?_ (And.intro ?_ ?_)
            · rw [hBoth.left]
              exact rfl
            · rw [hBoth.right]
              exact rfl
            · rw [hBoth.left, hBoth.right]
              have hCombo : ihqRowAdd
                  (ihqRowScale firstOut [qnfOne, qnfOne, qnfZero])
                  (ihqRowScale secondOut [qnfOne, qnfZero, qnfOne])
                  = [qnfAdd firstOut secondOut, firstOut, secondOut] := by
                show [qnfAdd (qnfMul firstOut qnfOne) (qnfMul secondOut qnfOne),
                    qnfAdd (qnfMul firstOut qnfOne) (qnfMul secondOut qnfZero),
                    qnfAdd (qnfMul firstOut qnfZero) (qnfMul secondOut qnfOne)]
                  = [qnfAdd firstOut secondOut, firstOut, secondOut]
                rw [qnfMulOneRight firstOut, qnfMulOneRight secondOut,
                  grqQnfMulZeroRight firstOut, grqQnfMulZeroRight secondOut,
                  qnfAddZeroRight firstOut, qnfAddZeroLeft secondOut]
              have hMem := ihzMemSpanPairIntro (width := 3)
                [qnfOne, qnfOne, qnfZero] [qnfOne, qnfZero, qnfOne]
                firstOut secondOut rfl rfl
              rw [hCombo] at hMem
              exact hMem

/-- The discard graph (`blackCounit`, `1 -> 0`, matrix `[[1]]`): the full line. -/
theorem ihzDiscardSpec (domVec codVec : List QnfRat) :
    IhqPairMem 1 0 [[qnfOne]] domVec codVec
      <-> Exists fun inputCoeff => domVec = [inputCoeff] /\ codVec = [] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthOneShape domVec hPair.left with
    | intro inputCoeff hDomEq =>
        exact Exists.intro inputCoeff
          (And.intro hDomEq (ihsLengthZeroNil codVec hPair.right.left))
  · intro hExists
    cases hExists with
    | intro inputCoeff hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left]
          exact rfl
        · rw [hBoth.right]
          exact rfl
        · rw [hBoth.left, hBoth.right]
          have hCombo : ihqRowScale inputCoeff [qnfOne] = [inputCoeff] := by
            show [qnfMul inputCoeff qnfOne] = [inputCoeff]
            rw [qnfMulOneRight inputCoeff]
          have hMem := ihzMemSpanSingleIntro (width := 1) [qnfOne] inputCoeff rfl
          rw [hCombo] at hMem
          exact hMem

/-- The black unit graph (`blackUnit`, `0 -> 1`, matrix `[[1]]`): the full line. -/
theorem ihzBlackUnitSpec (domVec codVec : List QnfRat) :
    IhqPairMem 0 1 [[qnfOne]] domVec codVec
      <-> Exists fun outputCoeff => domVec = [] /\ codVec = [outputCoeff] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthOneShape codVec hPair.right.left with
    | intro outputCoeff hCodEq =>
        exact Exists.intro outputCoeff
          (And.intro (ihsLengthZeroNil domVec hPair.left) hCodEq)
  · intro hExists
    cases hExists with
    | intro outputCoeff hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left]
          exact rfl
        · rw [hBoth.right]
          exact rfl
        · rw [hBoth.left, hBoth.right]
          have hCombo : ihqRowScale outputCoeff [qnfOne] = [outputCoeff] := by
            show [qnfMul outputCoeff qnfOne] = [outputCoeff]
            rw [qnfMulOneRight outputCoeff]
          have hMem := ihzMemSpanSingleIntro (width := 1) [qnfOne] outputCoeff rfl
          rw [hCombo] at hMem
          exact hMem

/-- The parallel scalar layer `[scalarBox k1, scalarBox k2]`
(matrix `[[1,0,k1,0],[0,1,0,k2]]`, `2 -> 2`): componentwise scaling. -/
theorem ihzScalarPairLayerSpec (firstScalar secondScalar : QnfRat)
    (domVec codVec : List QnfRat) :
    IhqPairMem 2 2
      [[qnfOne, qnfZero, firstScalar, qnfZero],
        [qnfZero, qnfOne, qnfZero, secondScalar]] domVec codVec
      <-> Exists fun firstIn => Exists fun secondIn =>
            domVec = [firstIn, secondIn]
              /\ codVec = [qnfMul firstIn firstScalar,
                    qnfMul secondIn secondScalar] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthTwoShape domVec hPair.left with
    | intro firstIn hPack =>
        cases hPack with
        | intro secondIn hDomEq =>
            cases ihzLengthTwoShape codVec hPair.right.left with
            | intro firstOut hPack2 =>
                cases hPack2 with
                | intro secondOut hCodEq =>
                    have hMem := hPair.right.right
                    rw [hDomEq, hCodEq] at hMem
                    cases ihzMemSpanPairInv (width := 4) rfl rfl hMem with
                    | intro firstCoeff hInnerPack =>
                        cases hInnerPack with
                        | intro secondCoeff hVecEq =>
                            have hIn1 : firstIn
                                = qnfAdd (qnfMul firstCoeff qnfOne)
                                    (qnfMul secondCoeff qnfZero) :=
                              congrArg (fun row => ihqGetCoeff row 0) hVecEq
                            have hIn2 : secondIn
                                = qnfAdd (qnfMul firstCoeff qnfZero)
                                    (qnfMul secondCoeff qnfOne) :=
                              congrArg (fun row => ihqGetCoeff row 1) hVecEq
                            have hOut1 : firstOut
                                = qnfAdd (qnfMul firstCoeff firstScalar)
                                    (qnfMul secondCoeff qnfZero) :=
                              congrArg (fun row => ihqGetCoeff row 2) hVecEq
                            have hOut2 : secondOut
                                = qnfAdd (qnfMul firstCoeff qnfZero)
                                    (qnfMul secondCoeff secondScalar) :=
                              congrArg (fun row => ihqGetCoeff row 3) hVecEq
                            have hIn1Is : firstIn = firstCoeff := by
                              rw [hIn1, qnfMulOneRight,
                                grqQnfMulZeroRight, qnfAddZeroRight]
                            have hIn2Is : secondIn = secondCoeff := by
                              rw [hIn2, qnfMulOneRight,
                                grqQnfMulZeroRight, qnfAddZeroLeft]
                            have hOut1Is : firstOut
                                = qnfMul firstIn firstScalar := by
                              rw [hOut1, grqQnfMulZeroRight,
                                qnfAddZeroRight, hIn1Is]
                            have hOut2Is : secondOut
                                = qnfMul secondIn secondScalar := by
                              rw [hOut2, grqQnfMulZeroRight,
                                qnfAddZeroLeft, hIn2Is]
                            refine Exists.intro firstIn (Exists.intro secondIn
                              (And.intro hDomEq ?_))
                            rw [hCodEq, hOut1Is, hOut2Is]
  · intro hExists
    cases hExists with
    | intro firstIn hPack =>
        cases hPack with
        | intro secondIn hBoth =>
            refine And.intro ?_ (And.intro ?_ ?_)
            · rw [hBoth.left]
              exact rfl
            · rw [hBoth.right]
              exact rfl
            · rw [hBoth.left, hBoth.right]
              have hCombo : ihqRowAdd
                  (ihqRowScale firstIn [qnfOne, qnfZero, firstScalar, qnfZero])
                  (ihqRowScale secondIn [qnfZero, qnfOne, qnfZero, secondScalar])
                  = [firstIn, secondIn, qnfMul firstIn firstScalar,
                      qnfMul secondIn secondScalar] := by
                show [qnfAdd (qnfMul firstIn qnfOne) (qnfMul secondIn qnfZero),
                    qnfAdd (qnfMul firstIn qnfZero) (qnfMul secondIn qnfOne),
                    qnfAdd (qnfMul firstIn firstScalar) (qnfMul secondIn qnfZero),
                    qnfAdd (qnfMul firstIn qnfZero) (qnfMul secondIn secondScalar)]
                  = [firstIn, secondIn, qnfMul firstIn firstScalar,
                      qnfMul secondIn secondScalar]
                rw [qnfMulOneRight firstIn, qnfMulOneRight secondIn,
                  grqQnfMulZeroRight firstIn, grqQnfMulZeroRight secondIn,
                  qnfAddZeroRight firstIn, qnfAddZeroLeft secondIn,
                  qnfAddZeroRight (qnfMul firstIn firstScalar),
                  qnfAddZeroLeft (qnfMul secondIn secondScalar)]
              have hMem := ihzMemSpanPairIntro (width := 4)
                [qnfOne, qnfZero, firstScalar, qnfZero]
                [qnfZero, qnfOne, qnfZero, secondScalar]
                firstIn secondIn rfl rfl
              rw [hCombo] at hMem
              exact hMem

/-- The parallel mirror scalar layer `[scalarBoxMirror k1, scalarBoxMirror k2]`
(matrix `[[k1,0,1,0],[0,k2,0,1]]`, `2 -> 2`): componentwise unscaling. -/
theorem ihzScalarMirrorPairLayerSpec (firstScalar secondScalar : QnfRat)
    (domVec codVec : List QnfRat) :
    IhqPairMem 2 2
      [[firstScalar, qnfZero, qnfOne, qnfZero],
        [qnfZero, secondScalar, qnfZero, qnfOne]] domVec codVec
      <-> Exists fun firstOut => Exists fun secondOut =>
            domVec = [qnfMul firstOut firstScalar, qnfMul secondOut secondScalar]
              /\ codVec = [firstOut, secondOut] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihzLengthTwoShape domVec hPair.left with
    | intro firstIn hPack =>
        cases hPack with
        | intro secondIn hDomEq =>
            cases ihzLengthTwoShape codVec hPair.right.left with
            | intro firstOut hPack2 =>
                cases hPack2 with
                | intro secondOut hCodEq =>
                    have hMem := hPair.right.right
                    rw [hDomEq, hCodEq] at hMem
                    cases ihzMemSpanPairInv (width := 4) rfl rfl hMem with
                    | intro firstCoeff hInnerPack =>
                        cases hInnerPack with
                        | intro secondCoeff hVecEq =>
                            have hIn1 : firstIn
                                = qnfAdd (qnfMul firstCoeff firstScalar)
                                    (qnfMul secondCoeff qnfZero) :=
                              congrArg (fun row => ihqGetCoeff row 0) hVecEq
                            have hIn2 : secondIn
                                = qnfAdd (qnfMul firstCoeff qnfZero)
                                    (qnfMul secondCoeff secondScalar) :=
                              congrArg (fun row => ihqGetCoeff row 1) hVecEq
                            have hOut1 : firstOut
                                = qnfAdd (qnfMul firstCoeff qnfOne)
                                    (qnfMul secondCoeff qnfZero) :=
                              congrArg (fun row => ihqGetCoeff row 2) hVecEq
                            have hOut2 : secondOut
                                = qnfAdd (qnfMul firstCoeff qnfZero)
                                    (qnfMul secondCoeff qnfOne) :=
                              congrArg (fun row => ihqGetCoeff row 3) hVecEq
                            have hOut1Is : firstOut = firstCoeff := by
                              rw [hOut1, qnfMulOneRight,
                                grqQnfMulZeroRight, qnfAddZeroRight]
                            have hOut2Is : secondOut = secondCoeff := by
                              rw [hOut2, qnfMulOneRight,
                                grqQnfMulZeroRight, qnfAddZeroLeft]
                            have hIn1Is : firstIn
                                = qnfMul firstOut firstScalar := by
                              rw [hIn1, grqQnfMulZeroRight,
                                qnfAddZeroRight, hOut1Is]
                            have hIn2Is : secondIn
                                = qnfMul secondOut secondScalar := by
                              rw [hIn2, grqQnfMulZeroRight,
                                qnfAddZeroLeft, hOut2Is]
                            refine Exists.intro firstOut (Exists.intro secondOut
                              (And.intro ?_ hCodEq))
                            rw [hDomEq, hIn1Is, hIn2Is]
  · intro hExists
    cases hExists with
    | intro firstOut hPack =>
        cases hPack with
        | intro secondOut hBoth =>
            refine And.intro ?_ (And.intro ?_ ?_)
            · rw [hBoth.left]
              exact rfl
            · rw [hBoth.right]
              exact rfl
            · rw [hBoth.left, hBoth.right]
              have hCombo : ihqRowAdd
                  (ihqRowScale firstOut [firstScalar, qnfZero, qnfOne, qnfZero])
                  (ihqRowScale secondOut [qnfZero, secondScalar, qnfZero, qnfOne])
                  = [qnfMul firstOut firstScalar, qnfMul secondOut secondScalar,
                      firstOut, secondOut] := by
                show [qnfAdd (qnfMul firstOut firstScalar)
                      (qnfMul secondOut qnfZero),
                    qnfAdd (qnfMul firstOut qnfZero)
                      (qnfMul secondOut secondScalar),
                    qnfAdd (qnfMul firstOut qnfOne) (qnfMul secondOut qnfZero),
                    qnfAdd (qnfMul firstOut qnfZero) (qnfMul secondOut qnfOne)]
                  = [qnfMul firstOut firstScalar, qnfMul secondOut secondScalar,
                      firstOut, secondOut]
                rw [qnfMulOneRight firstOut, qnfMulOneRight secondOut,
                  grqQnfMulZeroRight firstOut, grqQnfMulZeroRight secondOut,
                  qnfAddZeroRight firstOut, qnfAddZeroLeft secondOut,
                  qnfAddZeroRight (qnfMul firstOut firstScalar),
                  qnfAddZeroLeft (qnfMul secondOut secondScalar)]
              have hMem := ihzMemSpanPairIntro (width := 4)
                [firstScalar, qnfZero, qnfOne, qnfZero]
                [qnfZero, secondScalar, qnfZero, qnfOne]
                firstOut secondOut rfl rfl
              rw [hCombo] at hMem
              exact hMem

/-! ## Stage 2 — pipeline characterizations (compose chains ending in the identity) -/

/-- Pair membership through a two-stage pipeline `first ; (second ; id)`. -/
theorem ihzPairTwoStageIff (domWidth midWidth codWidth : Nat)
    (firstRows secondRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + codWidth) secondRows)
    (domVec codVec : List QnfRat) :
    IhqPairMem domWidth codWidth
      (ihqComposeRows domWidth midWidth codWidth firstRows
        (ihqComposeRows midWidth codWidth codWidth secondRows
          (ihqIdRows codWidth)))
      domVec codVec
    <-> Exists fun midVec =>
          IhqPairMem domWidth midWidth firstRows domVec midVec
            /\ IhqPairMem midWidth codWidth secondRows midVec codVec := by
  have hInnerAll := ihqComposeRowsWidth midWidth codWidth codWidth secondRows
    (ihqIdRows codWidth) hSecondAll (ihqIdRowsWidth codWidth)
  refine Iff.trans (ihqComposeSpec domWidth midWidth codWidth firstRows _
    hFirstAll hInnerAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        exact Exists.intro midVec (And.intro hBoth.left
          ((ihsComposeIdRight midWidth codWidth secondRows hSecondAll
            midVec codVec).mp hBoth.right))
  · intro hExists
    cases hExists with
    | intro midVec hBoth =>
        exact Exists.intro midVec (And.intro hBoth.left
          ((ihsComposeIdRight midWidth codWidth secondRows hSecondAll
            midVec codVec).mpr hBoth.right))

/-- Pair membership through a three-stage pipeline
`first ; (second ; (third ; id))`. -/
theorem ihzPairThreeStageIff (domWidth midWidth secondMidWidth codWidth : Nat)
    (firstRows secondRows thirdRows : List (List QnfRat))
    (hFirstAll : IhqAllWidth (domWidth + midWidth) firstRows)
    (hSecondAll : IhqAllWidth (midWidth + secondMidWidth) secondRows)
    (hThirdAll : IhqAllWidth (secondMidWidth + codWidth) thirdRows)
    (domVec codVec : List QnfRat) :
    IhqPairMem domWidth codWidth
      (ihqComposeRows domWidth midWidth codWidth firstRows
        (ihqComposeRows midWidth secondMidWidth codWidth secondRows
          (ihqComposeRows secondMidWidth codWidth codWidth thirdRows
            (ihqIdRows codWidth))))
      domVec codVec
    <-> Exists fun firstMidVec => Exists fun secondMidVec =>
          IhqPairMem domWidth midWidth firstRows domVec firstMidVec
            /\ IhqPairMem midWidth secondMidWidth secondRows
                firstMidVec secondMidVec
            /\ IhqPairMem secondMidWidth codWidth thirdRows
                secondMidVec codVec := by
  have hThirdIdAll := ihqComposeRowsWidth secondMidWidth codWidth codWidth
    thirdRows (ihqIdRows codWidth) hThirdAll (ihqIdRowsWidth codWidth)
  have hTailAll := ihqComposeRowsWidth midWidth secondMidWidth codWidth
    secondRows _ hSecondAll hThirdIdAll
  refine Iff.trans (ihqComposeSpec domWidth midWidth codWidth firstRows _
    hFirstAll hTailAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstMidVec hBoth =>
        cases (ihzPairTwoStageIff midWidth secondMidWidth codWidth secondRows
          thirdRows hSecondAll hThirdAll firstMidVec codVec).mp hBoth.right with
        | intro secondMidVec hTailBoth =>
            exact Exists.intro firstMidVec (Exists.intro secondMidVec
              (And.intro hBoth.left
                (And.intro hTailBoth.left hTailBoth.right)))
  · intro hExists
    cases hExists with
    | intro firstMidVec hPack =>
        cases hPack with
        | intro secondMidVec hFacts =>
            refine Exists.intro firstMidVec (And.intro hFacts.left ?_)
            exact (ihzPairTwoStageIff midWidth secondMidWidth codWidth secondRows
              thirdRows hSecondAll hThirdAll firstMidVec codVec).mpr
              (Exists.intro secondMidVec
                (And.intro hFacts.right.left hFacts.right.right))

/-! ## Stage 3 — layer-denotation kernel pins (the defeq the schema proofs ride)

Every pin is `rfl` WITH THE SCALARS SYMBOLIC: the layer denotation pipeline
(`ihsLayerDenote` -> `ihsTensorRows` -> embeds -> `ihqCat`) is purely
structural, so it reduces without ever scrutinizing a scalar payload.  This is
exactly why the brick-2 `rfl` wall (echelonization scrutinizes the scalar) does
NOT apply at the layer level. -/

theorem ihzScalarLayerDenote (scalarValue : QnfRat) :
    ihsLayerDenote [IhsCell.scalarBox scalarValue] = [[qnfOne, scalarValue]] := rfl

theorem ihzScalarMirrorLayerDenote (scalarValue : QnfRat) :
    ihsLayerDenote [IhsCell.scalarBoxMirror scalarValue]
      = [[scalarValue, qnfOne]] := rfl

theorem ihzScalarPairLayerDenote (firstScalar secondScalar : QnfRat) :
    ihsLayerDenote [IhsCell.scalarBox firstScalar, IhsCell.scalarBox secondScalar]
      = [[qnfOne, qnfZero, firstScalar, qnfZero],
          [qnfZero, qnfOne, qnfZero, secondScalar]] := rfl

theorem ihzScalarMirrorPairLayerDenote (firstScalar secondScalar : QnfRat) :
    ihsLayerDenote
        [IhsCell.scalarBoxMirror firstScalar, IhsCell.scalarBoxMirror secondScalar]
      = [[firstScalar, qnfZero, qnfOne, qnfZero],
          [qnfZero, secondScalar, qnfZero, qnfOne]] := rfl

theorem ihzCopyLayerDenote :
    ihsLayerDenote [IhsCell.blackComult] = [[qnfOne, qnfOne, qnfOne]] := rfl

theorem ihzCocopyLayerDenote :
    ihsLayerDenote [IhsCell.blackMult] = [[qnfOne, qnfOne, qnfOne]] := rfl

theorem ihzAddLayerDenote :
    ihsLayerDenote [IhsCell.whiteMult]
      = [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]] := rfl

theorem ihzCoaddLayerDenote :
    ihsLayerDenote [IhsCell.whiteComult]
      = [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]] := rfl

theorem ihzDiscardLayerDenote :
    ihsLayerDenote [IhsCell.blackCounit] = [[qnfOne]] := rfl

theorem ihzBlackUnitLayerDenote :
    ihsLayerDenote [IhsCell.blackUnit] = [[qnfOne]] := rfl

theorem ihzWhiteUnitLayerDenote : ihsLayerDenote [IhsCell.whiteUnit] = [] := rfl

theorem ihzCozeroLayerDenote : ihsLayerDenote [IhsCell.whiteCounit] = [] := rfl

theorem ihzWireLayerDenote :
    ihsLayerDenote [IhsCell.wire] = [[qnfOne, qnfOne]] := rfl

/-! ## Stage 4 — named width witnesses and singleton/pair extraction -/

theorem ihzScalarRowsAllWidth (scalarValue : QnfRat) :
    IhqAllWidth 2 [[qnfOne, scalarValue]] :=
  IhqAllWidth.cons rfl IhqAllWidth.nil

theorem ihzScalarMirrorRowsAllWidth (scalarValue : QnfRat) :
    IhqAllWidth 2 [[scalarValue, qnfOne]] :=
  IhqAllWidth.cons rfl IhqAllWidth.nil

theorem ihzWireRowsAllWidth : IhqAllWidth 2 [[qnfOne, qnfOne]] :=
  IhqAllWidth.cons rfl IhqAllWidth.nil

theorem ihzUnitLineRowsAllWidth : IhqAllWidth 1 [[qnfOne]] :=
  IhqAllWidth.cons rfl IhqAllWidth.nil

theorem ihzCopyRowsAllWidth : IhqAllWidth 3 [[qnfOne, qnfOne, qnfOne]] :=
  IhqAllWidth.cons rfl IhqAllWidth.nil

theorem ihzAddRowsAllWidth :
    IhqAllWidth 3 [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]] :=
  IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)

theorem ihzCoaddRowsAllWidth :
    IhqAllWidth 3 [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]] :=
  IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)

theorem ihzScalarPairRowsAllWidth (firstScalar secondScalar : QnfRat) :
    IhqAllWidth 4 [[qnfOne, qnfZero, firstScalar, qnfZero],
      [qnfZero, qnfOne, qnfZero, secondScalar]] :=
  IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)

theorem ihzScalarMirrorPairRowsAllWidth (firstScalar secondScalar : QnfRat) :
    IhqAllWidth 4 [[firstScalar, qnfZero, qnfOne, qnfZero],
      [qnfZero, secondScalar, qnfZero, qnfOne]] :=
  IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)

/-- Heads of equal singletons are equal. -/
theorem ihzHeadOfSingletonEq {firstValue secondValue : QnfRat}
    (hEq : ([firstValue] : List QnfRat) = [secondValue]) :
    firstValue = secondValue :=
  congrArg (fun row => ihqGetCoeff row 0) hEq

/-- Heads of equal literal pairs are equal. -/
theorem ihzPairHeadEq {firstValue secondValue thirdValue fourthValue : QnfRat}
    (hEq : ([firstValue, secondValue] : List QnfRat) = [thirdValue, fourthValue]) :
    firstValue = thirdValue :=
  congrArg (fun row => ihqGetCoeff row 0) hEq

/-- Tails of equal literal pairs are equal. -/
theorem ihzPairTailEq {firstValue secondValue thirdValue fourthValue : QnfRat}
    (hEq : ([firstValue, secondValue] : List QnfRat) = [thirdValue, fourthValue]) :
    secondValue = fourthValue :=
  congrArg (fun row => ihqGetCoeff row 1) hEq

/-- Bundle assembly from its five parts (the schema-side introduction: the
span component is a THEOREM here, never an `ihqSpanEqB` pin — the brick-2 wall
blocks kernel decision at symbolic scalars, not quantified soundness). -/
theorem ihzBundleOfParts (firstDiagram secondDiagram : IhsDiagram)
    (hSourceEq : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCodEq : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram)
    (hFirstWF : IhsDiagramWF firstDiagram) (hSecondWF : IhsDiagramWF secondDiagram)
    (hEquiv : IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
      (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram)) :
    IhsConvBundle firstDiagram secondDiagram :=
  And.intro hSourceEq (And.intro hCodEq
    (And.intro hFirstWF (And.intro hSecondWF hEquiv)))

/-! ## Stage 5 — THE SCHEMA SOUNDNESS THEOREMS (HALF A, T1)

One `IhsConvBundle` theorem per scalar-indexed census family, quantified over
the scalar argument(s).  Diagram shapes are the committed seed row shapes with
the instance scalars replaced by variables (verified against the seed by the
Stage-8 instance pins). -/

/-- A12 product schema, sound at EVERY scalar pair:
`scalarBox k1 ; scalarBox k2  =  scalarBox (k1 * k2)` (1->1). -/
theorem ihzProductSchemaBundle (firstScalar secondScalar : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBox firstScalar], [IhsCell.scalarBox secondScalar]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox (qnfMul firstScalar secondScalar)]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 1 [[qnfOne, firstScalar]]
    [[qnfOne, secondScalar]] (ihzScalarRowsAllWidth firstScalar)
    (ihzScalarRowsAllWidth secondScalar) domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 1 [[qnfOne, qnfMul firstScalar secondScalar]]
        (ihzScalarRowsAllWidth (qnfMul firstScalar secondScalar))) domVec codVec)
      (ihzScalarGraphSpec (qnfMul firstScalar secondScalar) domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarGraphSpec firstScalar domVec midVec).mp hStages.left with
        | intro inputCoeff hFirst =>
            cases (ihzScalarGraphSpec secondScalar midVec codVec).mp hStages.right with
            | intro midCoeff hSecond =>
                have hMidHead : midCoeff = qnfMul inputCoeff firstScalar :=
                  ihzHeadOfSingletonEq (hSecond.left.symm.trans hFirst.right)
                refine Exists.intro inputCoeff (And.intro hFirst.left ?_)
                rw [hSecond.right, hMidHead,
                  qnfMulAssoc inputCoeff firstScalar secondScalar]
  · intro hExists
    cases hExists with
    | intro inputCoeff hBoth =>
        refine Exists.intro [qnfMul inputCoeff firstScalar] (And.intro ?_ ?_)
        · exact (ihzScalarGraphSpec firstScalar domVec
            [qnfMul inputCoeff firstScalar]).mpr
            (Exists.intro inputCoeff (And.intro hBoth.left rfl))
        · refine (ihzScalarGraphSpec secondScalar
            [qnfMul inputCoeff firstScalar] codVec).mpr ?_
          refine Exists.intro (qnfMul inputCoeff firstScalar) (And.intro rfl ?_)
          rw [hBoth.right, qnfMulAssoc inputCoeff firstScalar secondScalar]

/-- A12op product-mirror schema, sound at EVERY scalar pair:
`k1-mirror ; k2-mirror  =  (k1 * k2)-mirror` (1->1). -/
theorem ihzProductMirrorSchemaBundle (firstScalar secondScalar : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror firstScalar],
          [IhsCell.scalarBoxMirror secondScalar]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror (qnfMul firstScalar secondScalar)]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 1 [[firstScalar, qnfOne]]
    [[secondScalar, qnfOne]] (ihzScalarMirrorRowsAllWidth firstScalar)
    (ihzScalarMirrorRowsAllWidth secondScalar) domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 1 [[qnfMul firstScalar secondScalar, qnfOne]]
        (ihzScalarMirrorRowsAllWidth (qnfMul firstScalar secondScalar)))
        domVec codVec)
      (ihzScalarMirrorSpec (qnfMul firstScalar secondScalar) domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarMirrorSpec firstScalar domVec midVec).mp hStages.left with
        | intro firstOut hFirst =>
            cases (ihzScalarMirrorSpec secondScalar midVec codVec).mp hStages.right with
            | intro secondOut hSecond =>
                have hMidHead : firstOut = qnfMul secondOut secondScalar :=
                  ihzHeadOfSingletonEq (hFirst.right.symm.trans hSecond.left)
                refine Exists.intro secondOut (And.intro ?_ hSecond.right)
                rw [hFirst.left, hMidHead,
                  qnfMulAssoc secondOut secondScalar firstScalar,
                  qnfMulComm secondScalar firstScalar]
  · intro hExists
    cases hExists with
    | intro outputCoeff hBoth =>
        refine Exists.intro [qnfMul outputCoeff secondScalar] (And.intro ?_ ?_)
        · refine (ihzScalarMirrorSpec firstScalar domVec
            [qnfMul outputCoeff secondScalar]).mpr ?_
          refine Exists.intro (qnfMul outputCoeff secondScalar) (And.intro ?_ rfl)
          rw [hBoth.left, qnfMulAssoc outputCoeff secondScalar firstScalar,
            qnfMulComm secondScalar firstScalar]
        · exact (ihzScalarMirrorSpec secondScalar
            [qnfMul outputCoeff secondScalar] codVec).mpr
            (Exists.intro outputCoeff (And.intro rfl hBoth.right))

/-- A13 scalar-through-add schema, sound at EVERY scalar:
`add ; k  =  (k (x) k) ; add` (2->1). -/
theorem ihzThroughAddSchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 2
        layers := [[IhsCell.whiteMult], [IhsCell.scalarBox scalarValue]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBox scalarValue, IhsCell.scalarBox scalarValue],
          [IhsCell.whiteMult]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 2 1 1
    [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
    [[qnfOne, scalarValue]] ihzAddRowsAllWidth (ihzScalarRowsAllWidth scalarValue)
    domVec codVec) ?_
  refine Iff.trans ?_ (ihzPairTwoStageIff 2 2 1
    [[qnfOne, qnfZero, scalarValue, qnfZero], [qnfZero, qnfOne, qnfZero, scalarValue]]
    [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
    (ihzScalarPairRowsAllWidth scalarValue scalarValue) ihzAddRowsAllWidth
    domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzAddSpec domVec midVec).mp hStages.left with
        | intro firstIn hPack =>
            cases hPack with
            | intro secondIn hAdd =>
                cases (ihzScalarGraphSpec scalarValue midVec codVec).mp
                  hStages.right with
                | intro sumCoeff hScalar =>
                    have hSumHead : sumCoeff = qnfAdd firstIn secondIn :=
                      ihzHeadOfSingletonEq (hScalar.left.symm.trans hAdd.right)
                    refine Exists.intro
                      [qnfMul firstIn scalarValue, qnfMul secondIn scalarValue]
                      (And.intro ?_ ?_)
                    · exact (ihzScalarPairLayerSpec scalarValue scalarValue domVec
                        [qnfMul firstIn scalarValue, qnfMul secondIn scalarValue]).mpr
                        (Exists.intro firstIn (Exists.intro secondIn
                          (And.intro hAdd.left rfl)))
                    · refine (ihzAddSpec
                        [qnfMul firstIn scalarValue, qnfMul secondIn scalarValue]
                        codVec).mpr ?_
                      refine Exists.intro (qnfMul firstIn scalarValue)
                        (Exists.intro (qnfMul secondIn scalarValue)
                          (And.intro rfl ?_))
                      rw [hScalar.right, hSumHead,
                        qnfMulRightDistrib firstIn secondIn scalarValue]
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarPairLayerSpec scalarValue scalarValue domVec midVec).mp
          hStages.left with
        | intro firstIn hPack =>
            cases hPack with
            | intro secondIn hPair =>
                cases (ihzAddSpec midVec codVec).mp hStages.right with
                | intro firstScaled hPack2 =>
                    cases hPack2 with
                    | intro secondScaled hAdd =>
                        have hMidEq := hAdd.left.symm.trans hPair.right
                        have hFirstScaled : firstScaled
                            = qnfMul firstIn scalarValue := ihzPairHeadEq hMidEq
                        have hSecondScaled : secondScaled
                            = qnfMul secondIn scalarValue := ihzPairTailEq hMidEq
                        refine Exists.intro [qnfAdd firstIn secondIn]
                          (And.intro ?_ ?_)
                        · exact (ihzAddSpec domVec [qnfAdd firstIn secondIn]).mpr
                            (Exists.intro firstIn (Exists.intro secondIn
                              (And.intro hPair.left rfl)))
                        · refine (ihzScalarGraphSpec scalarValue
                            [qnfAdd firstIn secondIn] codVec).mpr ?_
                          refine Exists.intro (qnfAdd firstIn secondIn)
                            (And.intro rfl ?_)
                          rw [hAdd.right, hFirstScaled, hSecondScaled,
                            qnfMulRightDistrib firstIn secondIn scalarValue]

/-- A13op scalar-through-coadd schema, sound at EVERY scalar:
`k-mirror ; coadd  =  coadd ; (k-mirror (x) k-mirror)` (1->2). -/
theorem ihzThroughCoaddSchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror scalarValue], [IhsCell.whiteComult]] }
      { sourceArity := 1
        layers := [[IhsCell.whiteComult],
          [IhsCell.scalarBoxMirror scalarValue, IhsCell.scalarBoxMirror scalarValue]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 2 [[scalarValue, qnfOne]]
    [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
    (ihzScalarMirrorRowsAllWidth scalarValue) ihzCoaddRowsAllWidth domVec codVec) ?_
  refine Iff.trans ?_ (ihzPairTwoStageIff 1 2 2
    [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
    [[scalarValue, qnfZero, qnfOne, qnfZero], [qnfZero, scalarValue, qnfZero, qnfOne]]
    ihzCoaddRowsAllWidth (ihzScalarMirrorPairRowsAllWidth scalarValue scalarValue)
    domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarMirrorSpec scalarValue domVec midVec).mp hStages.left with
        | intro throughOut hMirror =>
            cases (ihzCoaddSpec midVec codVec).mp hStages.right with
            | intro firstOut hPack =>
                cases hPack with
                | intro secondOut hCoadd =>
                    have hMidHead : throughOut = qnfAdd firstOut secondOut :=
                      ihzHeadOfSingletonEq (hMirror.right.symm.trans hCoadd.left)
                    refine Exists.intro
                      [qnfMul firstOut scalarValue, qnfMul secondOut scalarValue]
                      (And.intro ?_ ?_)
                    · refine (ihzCoaddSpec domVec
                        [qnfMul firstOut scalarValue,
                          qnfMul secondOut scalarValue]).mpr ?_
                      refine Exists.intro (qnfMul firstOut scalarValue)
                        (Exists.intro (qnfMul secondOut scalarValue)
                          (And.intro ?_ rfl))
                      rw [hMirror.left, hMidHead,
                        qnfMulRightDistrib firstOut secondOut scalarValue]
                    · exact (ihzScalarMirrorPairLayerSpec scalarValue scalarValue
                        [qnfMul firstOut scalarValue, qnfMul secondOut scalarValue]
                        codVec).mpr
                        (Exists.intro firstOut (Exists.intro secondOut
                          (And.intro rfl hCoadd.right)))
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzCoaddSpec domVec midVec).mp hStages.left with
        | intro firstScaled hPack =>
            cases hPack with
            | intro secondScaled hCoadd =>
                cases (ihzScalarMirrorPairLayerSpec scalarValue scalarValue
                  midVec codVec).mp hStages.right with
                | intro firstOut hPack2 =>
                    cases hPack2 with
                    | intro secondOut hMirrorPair =>
                        have hMidEq := hMirrorPair.left.symm.trans hCoadd.right
                        have hFirstScaled : qnfMul firstOut scalarValue
                            = firstScaled := ihzPairHeadEq hMidEq
                        have hSecondScaled : qnfMul secondOut scalarValue
                            = secondScaled := ihzPairTailEq hMidEq
                        refine Exists.intro [qnfAdd firstOut secondOut]
                          (And.intro ?_ ?_)
                        · refine (ihzScalarMirrorSpec scalarValue domVec
                            [qnfAdd firstOut secondOut]).mpr ?_
                          refine Exists.intro (qnfAdd firstOut secondOut)
                            (And.intro ?_ rfl)
                          rw [hCoadd.left, <- hFirstScaled, <- hSecondScaled,
                            qnfMulRightDistrib firstOut secondOut scalarValue]
                        · exact (ihzCoaddSpec [qnfAdd firstOut secondOut] codVec).mpr
                            (Exists.intro firstOut (Exists.intro secondOut
                              (And.intro rfl hMirrorPair.right)))

/-- A14 zero-absorption schema, sound at EVERY scalar:
`zero ; k  =  zero` (0->1); diagram-level companion of the committed
raw-compose `ihsScalarZeroAbsorbGeneral`. -/
theorem ihzZeroAbsorbSchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 0
        layers := [[IhsCell.whiteUnit], [IhsCell.scalarBox scalarValue]] }
      { sourceArity := 0, layers := [[IhsCell.whiteUnit]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 0 1 1 [] [[qnfOne, scalarValue]]
    IhqAllWidth.nil (ihzScalarRowsAllWidth scalarValue) domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 0 1 [] IhqAllWidth.nil) domVec codVec)
      (ihzZeroStateSpec domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        have hZero := (ihzZeroStateSpec domVec midVec).mp hStages.left
        cases (ihzScalarGraphSpec scalarValue midVec codVec).mp hStages.right with
        | intro inputCoeff hScalar =>
            have hInputZero : inputCoeff = qnfZero :=
              ihzHeadOfSingletonEq (hScalar.left.symm.trans hZero.right)
            refine And.intro hZero.left ?_
            rw [hScalar.right, hInputZero, grqQnfMulZeroLeft scalarValue]
  · intro hBoth
    refine Exists.intro [qnfZero] (And.intro ?_ ?_)
    · exact (ihzZeroStateSpec domVec [qnfZero]).mpr (And.intro hBoth.left rfl)
    · refine (ihzScalarGraphSpec scalarValue [qnfZero] codVec).mpr ?_
      refine Exists.intro qnfZero (And.intro rfl ?_)
      rw [hBoth.right, grqQnfMulZeroLeft scalarValue]

/-- A14op cozero-absorption schema, sound at EVERY scalar:
`k-mirror ; cozero  =  cozero` (1->0); diagram-level companion of the committed
raw-compose `ihsScalarCozeroAbsorbGeneral`. -/
theorem ihzCozeroAbsorbSchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror scalarValue], [IhsCell.whiteCounit]] }
      { sourceArity := 1, layers := [[IhsCell.whiteCounit]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 0 [[scalarValue, qnfOne]] []
    (ihzScalarMirrorRowsAllWidth scalarValue) IhqAllWidth.nil domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 0 [] IhqAllWidth.nil) domVec codVec)
      (ihzCozeroStateSpec domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarMirrorSpec scalarValue domVec midVec).mp hStages.left with
        | intro outputCoeff hMirror =>
            have hCozero := (ihzCozeroStateSpec midVec codVec).mp hStages.right
            have hOutputZero : outputCoeff = qnfZero :=
              ihzHeadOfSingletonEq (hMirror.right.symm.trans hCozero.left)
            refine And.intro ?_ hCozero.right
            rw [hMirror.left, hOutputZero, grqQnfMulZeroLeft scalarValue]
  · intro hBoth
    refine Exists.intro [qnfZero] (And.intro ?_ ?_)
    · refine (ihzScalarMirrorSpec scalarValue domVec [qnfZero]).mpr ?_
      refine Exists.intro qnfZero (And.intro ?_ rfl)
      rw [hBoth.left, grqQnfMulZeroLeft scalarValue]
    · exact (ihzCozeroStateSpec [qnfZero] codVec).mpr (And.intro rfl hBoth.right)

/-- A15 scalar-through-copy schema, sound at EVERY scalar:
`k ; copy  =  copy ; (k (x) k)` (1->2). -/
theorem ihzThroughCopySchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBox scalarValue], [IhsCell.blackComult]] }
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox scalarValue, IhsCell.scalarBox scalarValue]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 2 [[qnfOne, scalarValue]]
    [[qnfOne, qnfOne, qnfOne]] (ihzScalarRowsAllWidth scalarValue)
    ihzCopyRowsAllWidth domVec codVec) ?_
  refine Iff.trans ?_ (ihzPairTwoStageIff 1 2 2 [[qnfOne, qnfOne, qnfOne]]
    [[qnfOne, qnfZero, scalarValue, qnfZero], [qnfZero, qnfOne, qnfZero, scalarValue]]
    ihzCopyRowsAllWidth (ihzScalarPairRowsAllWidth scalarValue scalarValue)
    domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarGraphSpec scalarValue domVec midVec).mp hStages.left with
        | intro inputCoeff hScalar =>
            cases (ihzCopySpec midVec codVec).mp hStages.right with
            | intro throughCoeff hCopy =>
                have hMidHead : throughCoeff = qnfMul inputCoeff scalarValue :=
                  ihzHeadOfSingletonEq (hCopy.left.symm.trans hScalar.right)
                refine Exists.intro [inputCoeff, inputCoeff] (And.intro ?_ ?_)
                · exact (ihzCopySpec domVec [inputCoeff, inputCoeff]).mpr
                    (Exists.intro inputCoeff (And.intro hScalar.left rfl))
                · refine (ihzScalarPairLayerSpec scalarValue scalarValue
                    [inputCoeff, inputCoeff] codVec).mpr ?_
                  refine Exists.intro inputCoeff (Exists.intro inputCoeff
                    (And.intro rfl ?_))
                  rw [hCopy.right, hMidHead]
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzCopySpec domVec midVec).mp hStages.left with
        | intro inputCoeff hCopy =>
            cases (ihzScalarPairLayerSpec scalarValue scalarValue midVec codVec).mp
              hStages.right with
            | intro firstIn hPack =>
                cases hPack with
                | intro secondIn hPair =>
                    have hMidEq := hPair.left.symm.trans hCopy.right
                    have hFirstIs : firstIn = inputCoeff := ihzPairHeadEq hMidEq
                    have hSecondIs : secondIn = inputCoeff := ihzPairTailEq hMidEq
                    refine Exists.intro [qnfMul inputCoeff scalarValue]
                      (And.intro ?_ ?_)
                    · exact (ihzScalarGraphSpec scalarValue domVec
                        [qnfMul inputCoeff scalarValue]).mpr
                        (Exists.intro inputCoeff (And.intro hCopy.left rfl))
                    · refine (ihzCopySpec [qnfMul inputCoeff scalarValue]
                        codVec).mpr ?_
                      refine Exists.intro (qnfMul inputCoeff scalarValue)
                        (And.intro rfl ?_)
                      rw [hPair.right, hFirstIs, hSecondIs]

/-- A15op scalar-through-cocopy schema, sound at EVERY scalar:
`cocopy ; k-mirror  =  (k-mirror (x) k-mirror) ; cocopy` (2->1). -/
theorem ihzThroughCocopySchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 2
        layers := [[IhsCell.blackMult], [IhsCell.scalarBoxMirror scalarValue]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBoxMirror scalarValue,
          IhsCell.scalarBoxMirror scalarValue], [IhsCell.blackMult]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 2 1 1 [[qnfOne, qnfOne, qnfOne]]
    [[scalarValue, qnfOne]] ihzCopyRowsAllWidth
    (ihzScalarMirrorRowsAllWidth scalarValue) domVec codVec) ?_
  refine Iff.trans ?_ (ihzPairTwoStageIff 2 2 1
    [[scalarValue, qnfZero, qnfOne, qnfZero], [qnfZero, scalarValue, qnfZero, qnfOne]]
    [[qnfOne, qnfOne, qnfOne]]
    (ihzScalarMirrorPairRowsAllWidth scalarValue scalarValue) ihzCopyRowsAllWidth
    domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzCocopySpec domVec midVec).mp hStages.left with
        | intro throughCoeff hCocopy =>
            cases (ihzScalarMirrorSpec scalarValue midVec codVec).mp
              hStages.right with
            | intro outputCoeff hMirror =>
                have hMidHead : throughCoeff = qnfMul outputCoeff scalarValue :=
                  ihzHeadOfSingletonEq (hCocopy.right.symm.trans hMirror.left)
                refine Exists.intro [outputCoeff, outputCoeff] (And.intro ?_ ?_)
                · refine (ihzScalarMirrorPairLayerSpec scalarValue scalarValue
                    domVec [outputCoeff, outputCoeff]).mpr ?_
                  refine Exists.intro outputCoeff (Exists.intro outputCoeff
                    (And.intro ?_ rfl))
                  rw [hCocopy.left, hMidHead]
                · exact (ihzCocopySpec [outputCoeff, outputCoeff] codVec).mpr
                    (Exists.intro outputCoeff (And.intro rfl hMirror.right))
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarMirrorPairLayerSpec scalarValue scalarValue domVec
          midVec).mp hStages.left with
        | intro firstOut hPack =>
            cases hPack with
            | intro secondOut hPair =>
                cases (ihzCocopySpec midVec codVec).mp hStages.right with
                | intro throughCoeff hCocopy =>
                    have hMidEq := hCocopy.left.symm.trans hPair.right
                    have hFirstIs : throughCoeff = firstOut := ihzPairHeadEq hMidEq
                    have hSecondIs : throughCoeff = secondOut := ihzPairTailEq hMidEq
                    refine Exists.intro [qnfMul throughCoeff scalarValue]
                      (And.intro ?_ ?_)
                    · refine (ihzCocopySpec domVec
                        [qnfMul throughCoeff scalarValue]).mpr ?_
                      refine Exists.intro (qnfMul throughCoeff scalarValue)
                        (And.intro ?_ rfl)
                      rw [hPair.left, <- hFirstIs, <- hSecondIs]
                    · refine (ihzScalarMirrorSpec scalarValue
                        [qnfMul throughCoeff scalarValue] codVec).mpr ?_
                      refine Exists.intro throughCoeff (And.intro rfl ?_)
                      rw [hCocopy.right]

/-- A16 discard-absorption schema, sound at EVERY scalar:
`k ; discard  =  discard` (1->0). -/
theorem ihzDiscardAbsorbSchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBox scalarValue], [IhsCell.blackCounit]] }
      { sourceArity := 1, layers := [[IhsCell.blackCounit]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 0 [[qnfOne, scalarValue]] [[qnfOne]]
    (ihzScalarRowsAllWidth scalarValue) ihzUnitLineRowsAllWidth domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 0 [[qnfOne]] ihzUnitLineRowsAllWidth)
        domVec codVec)
      (ihzDiscardSpec domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarGraphSpec scalarValue domVec midVec).mp hStages.left with
        | intro inputCoeff hScalar =>
            cases (ihzDiscardSpec midVec codVec).mp hStages.right with
            | intro dropCoeff hDiscard =>
                exact Exists.intro inputCoeff
                  (And.intro hScalar.left hDiscard.right)
  · intro hExists
    cases hExists with
    | intro inputCoeff hBoth =>
        refine Exists.intro [qnfMul inputCoeff scalarValue] (And.intro ?_ ?_)
        · exact (ihzScalarGraphSpec scalarValue domVec
            [qnfMul inputCoeff scalarValue]).mpr
            (Exists.intro inputCoeff (And.intro hBoth.left rfl))
        · exact (ihzDiscardSpec [qnfMul inputCoeff scalarValue] codVec).mpr
            (Exists.intro (qnfMul inputCoeff scalarValue)
              (And.intro rfl hBoth.right))

/-- A16op unit-absorption schema, sound at EVERY scalar:
`blackunit ; k-mirror  =  blackunit` (0->1); holds for ALL k including 0
(the composite is the full line either way). -/
theorem ihzUnitAbsorbSchemaBundle (scalarValue : QnfRat) :
    IhsConvBundle
      { sourceArity := 0
        layers := [[IhsCell.blackUnit], [IhsCell.scalarBoxMirror scalarValue]] }
      { sourceArity := 0, layers := [[IhsCell.blackUnit]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 0 1 1 [[qnfOne]] [[scalarValue, qnfOne]]
    ihzUnitLineRowsAllWidth (ihzScalarMirrorRowsAllWidth scalarValue)
    domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 0 1 [[qnfOne]] ihzUnitLineRowsAllWidth)
        domVec codVec)
      (ihzBlackUnitSpec domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzBlackUnitSpec domVec midVec).mp hStages.left with
        | intro lineCoeff hUnit =>
            cases (ihzScalarMirrorSpec scalarValue midVec codVec).mp
              hStages.right with
            | intro outputCoeff hMirror =>
                exact Exists.intro outputCoeff
                  (And.intro hUnit.left hMirror.right)
  · intro hExists
    cases hExists with
    | intro outputCoeff hBoth =>
        refine Exists.intro [qnfMul outputCoeff scalarValue] (And.intro ?_ ?_)
        · exact (ihzBlackUnitSpec domVec [qnfMul outputCoeff scalarValue]).mpr
            (Exists.intro (qnfMul outputCoeff scalarValue)
              (And.intro hBoth.left rfl))
        · exact (ihzScalarMirrorSpec scalarValue
            [qnfMul outputCoeff scalarValue] codVec).mpr
            (Exists.intro outputCoeff (And.intro rfl hBoth.right))

/-- A18 sum schema, sound at EVERY scalar pair:
`copy ; (k1 (x) k2) ; add  =  scalarBox (k1 + k2)` (1->1). -/
theorem ihzSumSchemaBundle (firstScalar secondScalar : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox firstScalar, IhsCell.scalarBox secondScalar],
          [IhsCell.whiteMult]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox (qnfAdd firstScalar secondScalar)]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairThreeStageIff 1 2 2 1 [[qnfOne, qnfOne, qnfOne]]
    [[qnfOne, qnfZero, firstScalar, qnfZero], [qnfZero, qnfOne, qnfZero, secondScalar]]
    [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
    ihzCopyRowsAllWidth (ihzScalarPairRowsAllWidth firstScalar secondScalar)
    ihzAddRowsAllWidth domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 1 [[qnfOne, qnfAdd firstScalar secondScalar]]
        (ihzScalarRowsAllWidth (qnfAdd firstScalar secondScalar)))
        domVec codVec)
      (ihzScalarGraphSpec (qnfAdd firstScalar secondScalar) domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstMidVec hPack =>
        cases hPack with
        | intro secondMidVec hStages =>
            cases (ihzCopySpec domVec firstMidVec).mp hStages.left with
            | intro inputCoeff hCopy =>
                cases (ihzScalarPairLayerSpec firstScalar secondScalar
                  firstMidVec secondMidVec).mp hStages.right.left with
                | intro firstIn hPack2 =>
                    cases hPack2 with
                    | intro secondIn hPair =>
                        cases (ihzAddSpec secondMidVec codVec).mp
                          hStages.right.right with
                        | intro firstScaled hPack3 =>
                            cases hPack3 with
                            | intro secondScaled hAdd =>
                                have hMid1Eq := hPair.left.symm.trans hCopy.right
                                have hFirstIs : firstIn = inputCoeff :=
                                  ihzPairHeadEq hMid1Eq
                                have hSecondIs : secondIn = inputCoeff :=
                                  ihzPairTailEq hMid1Eq
                                have hMid2Eq := hAdd.left.symm.trans hPair.right
                                have hFirstScaled : firstScaled
                                    = qnfMul firstIn firstScalar :=
                                  ihzPairHeadEq hMid2Eq
                                have hSecondScaled : secondScaled
                                    = qnfMul secondIn secondScalar :=
                                  ihzPairTailEq hMid2Eq
                                refine Exists.intro inputCoeff
                                  (And.intro hCopy.left ?_)
                                rw [hAdd.right, hFirstScaled, hSecondScaled,
                                  hFirstIs, hSecondIs,
                                  qnfMulLeftDistrib inputCoeff firstScalar
                                    secondScalar]
  · intro hExists
    cases hExists with
    | intro inputCoeff hBoth =>
        refine Exists.intro [inputCoeff, inputCoeff]
          (Exists.intro [qnfMul inputCoeff firstScalar,
            qnfMul inputCoeff secondScalar] (And.intro ?_ (And.intro ?_ ?_)))
        · exact (ihzCopySpec domVec [inputCoeff, inputCoeff]).mpr
            (Exists.intro inputCoeff (And.intro hBoth.left rfl))
        · exact (ihzScalarPairLayerSpec firstScalar secondScalar
            [inputCoeff, inputCoeff]
            [qnfMul inputCoeff firstScalar, qnfMul inputCoeff secondScalar]).mpr
            (Exists.intro inputCoeff (Exists.intro inputCoeff
              (And.intro rfl rfl)))
        · refine (ihzAddSpec [qnfMul inputCoeff firstScalar,
            qnfMul inputCoeff secondScalar] codVec).mpr ?_
          refine Exists.intro (qnfMul inputCoeff firstScalar)
            (Exists.intro (qnfMul inputCoeff secondScalar) (And.intro rfl ?_))
          rw [hBoth.right, qnfMulLeftDistrib inputCoeff firstScalar secondScalar]

/-- A18op sum-mirror schema, sound at EVERY scalar pair:
`coadd ; (k1-mirror (x) k2-mirror) ; cocopy  =  (k1 + k2)-mirror` (1->1). -/
theorem ihzSumMirrorSchemaBundle (firstScalar secondScalar : QnfRat) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.whiteComult],
          [IhsCell.scalarBoxMirror firstScalar, IhsCell.scalarBoxMirror secondScalar],
          [IhsCell.blackMult]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror (qnfAdd firstScalar secondScalar)]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairThreeStageIff 1 2 2 1
    [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
    [[firstScalar, qnfZero, qnfOne, qnfZero], [qnfZero, secondScalar, qnfZero, qnfOne]]
    [[qnfOne, qnfOne, qnfOne]]
    ihzCoaddRowsAllWidth (ihzScalarMirrorPairRowsAllWidth firstScalar secondScalar)
    ihzCopyRowsAllWidth domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 1 [[qnfAdd firstScalar secondScalar, qnfOne]]
        (ihzScalarMirrorRowsAllWidth (qnfAdd firstScalar secondScalar)))
        domVec codVec)
      (ihzScalarMirrorSpec (qnfAdd firstScalar secondScalar) domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstMidVec hPack =>
        cases hPack with
        | intro secondMidVec hStages =>
            cases (ihzCoaddSpec domVec firstMidVec).mp hStages.left with
            | intro firstScaled hPack2 =>
                cases hPack2 with
                | intro secondScaled hCoadd =>
                    cases (ihzScalarMirrorPairLayerSpec firstScalar secondScalar
                      firstMidVec secondMidVec).mp hStages.right.left with
                    | intro firstOut hPack3 =>
                        cases hPack3 with
                        | intro secondOut hMirrorPair =>
                            cases (ihzCocopySpec secondMidVec codVec).mp
                              hStages.right.right with
                            | intro throughCoeff hCocopy =>
                                have hMid1Eq :=
                                  hMirrorPair.left.symm.trans hCoadd.right
                                have hFirstScaled : qnfMul firstOut firstScalar
                                    = firstScaled := ihzPairHeadEq hMid1Eq
                                have hSecondScaled : qnfMul secondOut secondScalar
                                    = secondScaled := ihzPairTailEq hMid1Eq
                                have hMid2Eq :=
                                  hCocopy.left.symm.trans hMirrorPair.right
                                have hFirstIs : throughCoeff = firstOut :=
                                  ihzPairHeadEq hMid2Eq
                                have hSecondIs : throughCoeff = secondOut :=
                                  ihzPairTailEq hMid2Eq
                                refine Exists.intro throughCoeff
                                  (And.intro ?_ hCocopy.right)
                                rw [hCoadd.left, <- hFirstScaled, <- hSecondScaled,
                                  <- hFirstIs, <- hSecondIs,
                                  qnfMulLeftDistrib throughCoeff firstScalar
                                    secondScalar]
  · intro hExists
    cases hExists with
    | intro outputCoeff hBoth =>
        refine Exists.intro [qnfMul outputCoeff firstScalar,
          qnfMul outputCoeff secondScalar]
          (Exists.intro [outputCoeff, outputCoeff] (And.intro ?_ (And.intro ?_ ?_)))
        · refine (ihzCoaddSpec domVec [qnfMul outputCoeff firstScalar,
            qnfMul outputCoeff secondScalar]).mpr ?_
          refine Exists.intro (qnfMul outputCoeff firstScalar)
            (Exists.intro (qnfMul outputCoeff secondScalar) (And.intro ?_ rfl))
          rw [hBoth.left, qnfMulLeftDistrib outputCoeff firstScalar secondScalar]
        · exact (ihzScalarMirrorPairLayerSpec firstScalar secondScalar
            [qnfMul outputCoeff firstScalar, qnfMul outputCoeff secondScalar]
            [outputCoeff, outputCoeff]).mpr
            (Exists.intro outputCoeff (Exists.intro outputCoeff
              (And.intro rfl rfl)))
        · exact (ihzCocopySpec [outputCoeff, outputCoeff] codVec).mpr
            (Exists.intro outputCoeff (And.intro rfl hBoth.right))

/-- I1 forward-cancel schema, sound at EVERY NONZERO scalar:
`k ; k-mirror  =  id` (1->1).  The nonzero side condition is exactly the
census pitfall (b): at `k = 0` the composite is the total relation, NOT the
identity, so the hypothesis is load-bearing. -/
theorem ihzForwardCancelSchemaBundle (scalarValue : QnfRat)
    (hNonzero : scalarValue ≠ qnfZero) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBox scalarValue],
          [IhsCell.scalarBoxMirror scalarValue]] }
      { sourceArity := 1, layers := [[IhsCell.wire]] } := by
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 1 [[qnfOne, scalarValue]]
    [[scalarValue, qnfOne]] (ihzScalarRowsAllWidth scalarValue)
    (ihzScalarMirrorRowsAllWidth scalarValue) domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 1 [[qnfOne, qnfOne]] ihzWireRowsAllWidth)
        domVec codVec)
      (ihzWireSpec domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarGraphSpec scalarValue domVec midVec).mp hStages.left with
        | intro inputCoeff hScalar =>
            cases (ihzScalarMirrorSpec scalarValue midVec codVec).mp
              hStages.right with
            | intro outputCoeff hMirror =>
                have hProductsEq : qnfMul inputCoeff scalarValue
                    = qnfMul outputCoeff scalarValue :=
                  ihzHeadOfSingletonEq (hScalar.right.symm.trans hMirror.left)
                have hSame : inputCoeff = outputCoeff :=
                  ihzMulRightCancel hNonzero hProductsEq
                refine Exists.intro inputCoeff (And.intro hScalar.left ?_)
                rw [hMirror.right, hSame]
  · intro hExists
    cases hExists with
    | intro throughCoeff hBoth =>
        refine Exists.intro [qnfMul throughCoeff scalarValue] (And.intro ?_ ?_)
        · exact (ihzScalarGraphSpec scalarValue domVec
            [qnfMul throughCoeff scalarValue]).mpr
            (Exists.intro throughCoeff (And.intro hBoth.left rfl))
        · exact (ihzScalarMirrorSpec scalarValue
            [qnfMul throughCoeff scalarValue] codVec).mpr
            (Exists.intro throughCoeff (And.intro rfl hBoth.right))

/-- I2 backward-cancel schema, sound at EVERY NONZERO scalar:
`k-mirror ; k  =  id` (1->1).  The backward direction is where the FIELD
structure fires: recovering the witness needs `qnfInv` (over a mere PID this
instance family shrinks to the units). -/
theorem ihzBackwardCancelSchemaBundle (scalarValue : QnfRat)
    (hNonzero : scalarValue ≠ qnfZero) :
    IhsConvBundle
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror scalarValue],
          [IhsCell.scalarBox scalarValue]] }
      { sourceArity := 1, layers := [[IhsCell.wire]] } := by
  have hRecover : (throughCoeff : QnfRat) ->
      qnfMul (qnfMul throughCoeff (qnfInv scalarValue)) scalarValue
        = throughCoeff := by
    intro throughCoeff
    rw [qnfMulAssoc throughCoeff (qnfInv scalarValue) scalarValue,
      qnfInvMulCancels hNonzero, qnfMulOneRight throughCoeff]
  refine ihzBundleOfParts _ _ rfl rfl (ihsDiagramWFOfB _ rfl) (ihsDiagramWFOfB _ rfl) ?_
  intro domVec codVec
  refine Iff.trans (ihzPairTwoStageIff 1 1 1 [[scalarValue, qnfOne]]
    [[qnfOne, scalarValue]] (ihzScalarMirrorRowsAllWidth scalarValue)
    (ihzScalarRowsAllWidth scalarValue) domVec codVec) ?_
  refine Iff.trans ?_
    (Iff.trans ((ihsComposeIdRight 1 1 [[qnfOne, qnfOne]] ihzWireRowsAllWidth)
        domVec codVec)
      (ihzWireSpec domVec codVec)).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        cases (ihzScalarMirrorSpec scalarValue domVec midVec).mp hStages.left with
        | intro outputCoeff hMirror =>
            cases (ihzScalarGraphSpec scalarValue midVec codVec).mp
              hStages.right with
            | intro inputCoeff hScalar =>
                have hSame : inputCoeff = outputCoeff :=
                  ihzHeadOfSingletonEq (hScalar.left.symm.trans hMirror.right)
                refine Exists.intro (qnfMul outputCoeff scalarValue)
                  (And.intro hMirror.left ?_)
                rw [hScalar.right, hSame]
  · intro hExists
    cases hExists with
    | intro throughCoeff hBoth =>
        refine Exists.intro [qnfMul throughCoeff (qnfInv scalarValue)]
          (And.intro ?_ ?_)
        · refine (ihzScalarMirrorSpec scalarValue domVec
            [qnfMul throughCoeff (qnfInv scalarValue)]).mpr ?_
          refine Exists.intro (qnfMul throughCoeff (qnfInv scalarValue))
            (And.intro ?_ rfl)
          rw [hBoth.left, hRecover throughCoeff]
        · refine (ihzScalarGraphSpec scalarValue
            [qnfMul throughCoeff (qnfInv scalarValue)] codVec).mpr ?_
          refine Exists.intro (qnfMul throughCoeff (qnfInv scalarValue))
            (And.intro rfl ?_)
          rw [hBoth.right, hRecover throughCoeff]

/-! ## Stage 6 — THE SCHEMA ROW MOVES (T1)

SCHEMA CENSUS (verbatim against the seed census on
`ihsCompletenessStatement`, section 2; every scalar-indexed family of BSZ
Definition 6.1 whose committed row is an INSTANCE):

  constructor              census family  subsumed committed row(s)
  ------------------------------------------------------------------
  productSchema            A12            IhsRowTag.scalarProduct   (2;3=6)
  productMirrorSchema      A12op          IhsRowTag.scalarProductOp (2m;3m=6m)
  throughAddSchema         A13            IhsRowTag.scalarThroughAdd     (k=2)
  throughCoaddSchema       A13op          IhsRowTag.scalarThroughCoaddOp (k=2)
  zeroAbsorbSchema         A14            IhsRowTag.scalarAfterZero      (k=2)
  cozeroAbsorbSchema       A14op          IhsRowTag.scalarIntoCozeroOp   (k=2)
  throughCopySchema        A15            IhsRowTag.scalarThroughCopy    (k=2)
  throughCocopySchema      A15op          IhsRowTag.scalarThroughCocopyOp (k=2)
  discardAbsorbSchema      A16            IhsRowTag.scalarIntoDiscard    (k=2)
  unitAbsorbSchema         A16op          IhsRowTag.scalarAfterUnitOp    (k=2)
  sumSchema                A18            IhsRowTag.scalarSum       (2+3=5)
  sumMirrorSchema          A18op          IhsRowTag.scalarSumOp     (2+3=5)
  forwardCancelSchema      I1 (l /= 0)    IhsRowTag.forwardCancel   (l=2)
  backwardCancelSchema     I2 (l /= 0)    IhsRowTag.backwardCancel  (l=2)

NOT schemas (single-point members of the scalar family, committed rows cover
them exactly): A11/A11op (`scalar 1 = id`, k pinned to 1), A17/A17op
(`scalar 0 = discard;zero`, k pinned to 0).  Everything else of the census
(the scalar-free A1-A10 + ops + I3-I8 and the exchange move) rides in through
the `whiskerMove` embedding arm. -/

/-- A window move for the schema congruence: any committed whisker window move
(all 46 seed rows + the layer split), or one of the fourteen scalar SCHEMAS at
arbitrary `QnfRat` scalars (census table in the stage docstring). -/
inductive IhzRowMove : IhsDiagram -> IhsDiagram -> Prop where
  | whiskerMove {firstWindow secondWindow : IhsDiagram}
      (hMove : IhwWindowMove firstWindow secondWindow) :
      IhzRowMove firstWindow secondWindow
  | productSchema (firstScalar secondScalar : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBox firstScalar],
            [IhsCell.scalarBox secondScalar]] }
        { sourceArity := 1
          layers := [[IhsCell.scalarBox (qnfMul firstScalar secondScalar)]] }
  | productMirrorSchema (firstScalar secondScalar : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBoxMirror firstScalar],
            [IhsCell.scalarBoxMirror secondScalar]] }
        { sourceArity := 1
          layers := [[IhsCell.scalarBoxMirror (qnfMul firstScalar secondScalar)]] }
  | throughAddSchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 2
          layers := [[IhsCell.whiteMult], [IhsCell.scalarBox scalarValue]] }
        { sourceArity := 2
          layers := [[IhsCell.scalarBox scalarValue, IhsCell.scalarBox scalarValue],
            [IhsCell.whiteMult]] }
  | throughCoaddSchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBoxMirror scalarValue], [IhsCell.whiteComult]] }
        { sourceArity := 1
          layers := [[IhsCell.whiteComult],
            [IhsCell.scalarBoxMirror scalarValue,
              IhsCell.scalarBoxMirror scalarValue]] }
  | zeroAbsorbSchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 0
          layers := [[IhsCell.whiteUnit], [IhsCell.scalarBox scalarValue]] }
        { sourceArity := 0, layers := [[IhsCell.whiteUnit]] }
  | cozeroAbsorbSchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBoxMirror scalarValue], [IhsCell.whiteCounit]] }
        { sourceArity := 1, layers := [[IhsCell.whiteCounit]] }
  | throughCopySchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBox scalarValue], [IhsCell.blackComult]] }
        { sourceArity := 1
          layers := [[IhsCell.blackComult],
            [IhsCell.scalarBox scalarValue, IhsCell.scalarBox scalarValue]] }
  | throughCocopySchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 2
          layers := [[IhsCell.blackMult], [IhsCell.scalarBoxMirror scalarValue]] }
        { sourceArity := 2
          layers := [[IhsCell.scalarBoxMirror scalarValue,
            IhsCell.scalarBoxMirror scalarValue], [IhsCell.blackMult]] }
  | discardAbsorbSchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBox scalarValue], [IhsCell.blackCounit]] }
        { sourceArity := 1, layers := [[IhsCell.blackCounit]] }
  | unitAbsorbSchema (scalarValue : QnfRat) :
      IhzRowMove
        { sourceArity := 0
          layers := [[IhsCell.blackUnit], [IhsCell.scalarBoxMirror scalarValue]] }
        { sourceArity := 0, layers := [[IhsCell.blackUnit]] }
  | sumSchema (firstScalar secondScalar : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.blackComult],
            [IhsCell.scalarBox firstScalar, IhsCell.scalarBox secondScalar],
            [IhsCell.whiteMult]] }
        { sourceArity := 1
          layers := [[IhsCell.scalarBox (qnfAdd firstScalar secondScalar)]] }
  | sumMirrorSchema (firstScalar secondScalar : QnfRat) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.whiteComult],
            [IhsCell.scalarBoxMirror firstScalar,
              IhsCell.scalarBoxMirror secondScalar],
            [IhsCell.blackMult]] }
        { sourceArity := 1
          layers := [[IhsCell.scalarBoxMirror (qnfAdd firstScalar secondScalar)]] }
  | forwardCancelSchema (scalarValue : QnfRat) (hNonzero : scalarValue ≠ qnfZero) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBox scalarValue],
            [IhsCell.scalarBoxMirror scalarValue]] }
        { sourceArity := 1, layers := [[IhsCell.wire]] }
  | backwardCancelSchema (scalarValue : QnfRat) (hNonzero : scalarValue ≠ qnfZero) :
      IhzRowMove
        { sourceArity := 1
          layers := [[IhsCell.scalarBoxMirror scalarValue],
            [IhsCell.scalarBox scalarValue]] }
        { sourceArity := 1, layers := [[IhsCell.wire]] }

/-- Every committed seed row is a schema-layer row move (the embedding arm,
specialized). -/
theorem ihzRowMoveOfSeedRow (tag : IhsRowTag) :
    IhzRowMove (ihsRowLhs tag) (ihsRowRhs tag) :=
  IhzRowMove.whiskerMove (IhwWindowMove.row tag)

/-- SOUNDNESS OF EVERY SCHEMA ROW MOVE (bundle form): the committed arms by
the committed bundles, the fourteen schemas by their quantified theorems. -/
theorem ihzRowMoveBundle {firstWindow secondWindow : IhsDiagram}
    (hMove : IhzRowMove firstWindow secondWindow) :
    IhsConvBundle firstWindow secondWindow := by
  cases hMove with
  | whiskerMove hInner => exact ihwWindowMoveBundle hInner
  | productSchema firstScalar secondScalar =>
      exact ihzProductSchemaBundle firstScalar secondScalar
  | productMirrorSchema firstScalar secondScalar =>
      exact ihzProductMirrorSchemaBundle firstScalar secondScalar
  | throughAddSchema scalarValue => exact ihzThroughAddSchemaBundle scalarValue
  | throughCoaddSchema scalarValue => exact ihzThroughCoaddSchemaBundle scalarValue
  | zeroAbsorbSchema scalarValue => exact ihzZeroAbsorbSchemaBundle scalarValue
  | cozeroAbsorbSchema scalarValue => exact ihzCozeroAbsorbSchemaBundle scalarValue
  | throughCopySchema scalarValue => exact ihzThroughCopySchemaBundle scalarValue
  | throughCocopySchema scalarValue =>
      exact ihzThroughCocopySchemaBundle scalarValue
  | discardAbsorbSchema scalarValue =>
      exact ihzDiscardAbsorbSchemaBundle scalarValue
  | unitAbsorbSchema scalarValue => exact ihzUnitAbsorbSchemaBundle scalarValue
  | sumSchema firstScalar secondScalar =>
      exact ihzSumSchemaBundle firstScalar secondScalar
  | sumMirrorSchema firstScalar secondScalar =>
      exact ihzSumMirrorSchemaBundle firstScalar secondScalar
  | forwardCancelSchema scalarValue hNonzero =>
      exact ihzForwardCancelSchemaBundle scalarValue hNonzero
  | backwardCancelSchema scalarValue hNonzero =>
      exact ihzBackwardCancelSchemaBundle scalarValue hNonzero

/-! ## Stage 7 — the schema whisker congruence (T2)

The committed `IhwStep.pad` shape, re-run over `IhzRowMove` windows.  The pad
soundness engine is factored out as `ihzPadBundle` — the committed
`ihwStepBundle` body abstracted over the window bundle (so ANY sound window
relation pads soundly; `IhwStep`'s own soundness is the `ihwWindowMoveBundle`
instance of the same argument). -/

/-- Padding preserves the bundle: the `ihwStepBundle` engine, generic in the
window-move soundness witness. -/
theorem ihzPadBundle (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List IhsCell))
    {firstWindow secondWindow : IhsDiagram}
    (hWindowBundle : IhsConvBundle firstWindow secondWindow)
    (hBeforeWF : IhsLayersWF contextSource beforeLayers)
    (hBeforeCod : ihsLayersCodArity contextSource beforeLayers
      = leftWires + (firstWindow.sourceArity + rightWires))
    (hAfterWF : IhsLayersWF
      (leftWires + (ihsDiagramCodArity firstWindow + rightWires)) afterLayers) :
    IhsConvBundle
      (ihwPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        firstWindow)
      (ihwPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        secondWindow) := by
  have hSourceEq : firstWindow.sourceArity = secondWindow.sourceArity :=
    hWindowBundle.left
  have hCodEq : ihsDiagramCodArity firstWindow = ihsDiagramCodArity secondWindow :=
    hWindowBundle.right.left
  have hFirstWF : IhsDiagramWF firstWindow := hWindowBundle.right.right.left
  have hSecondWF : IhsDiagramWF secondWindow :=
    hWindowBundle.right.right.right.left
  have hEquiv := hWindowBundle.right.right.right.right
  have hBeforeCod2 : ihsLayersCodArity contextSource beforeLayers
      = leftWires + (secondWindow.sourceArity + rightWires) := by
    rw [hBeforeCod, hSourceEq]
  have hAfterWF2 : IhsLayersWF
      (leftWires + (ihsDiagramCodArity secondWindow + rightWires)) afterLayers := by
    rw [<- hCodEq]
    exact hAfterWF
  have hPadWF1 := ihwPadDiagramWF contextSource leftWires rightWires beforeLayers
    afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
  have hPadWF2 := ihwPadDiagramWF contextSource leftWires rightWires beforeLayers
    afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
  have hDecomp1 := ihwPadDiagramDenoteDecomp contextSource leftWires rightWires
    beforeLayers afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
  have hDecomp2 := ihwPadDiagramDenoteDecomp contextSource leftWires rightWires
    beforeLayers afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
  rw [<- hSourceEq, <- hCodEq] at hDecomp2
  have hBeforeAll : IhqAllWidth
      (contextSource + (leftWires + (firstWindow.sourceArity + rightWires)))
      (ihsLayersDenote contextSource beforeLayers) :=
    ihsAllWidthCast (by rw [hBeforeCod])
      (ihsLayersDenoteWidth beforeLayers hBeforeWF)
  have hAfterAll := ihsLayersDenoteWidth afterLayers hAfterWF
  have hFirstDenAll := ihsDiagramDenoteWidth firstWindow hFirstWF
  have hSecondDenAll : IhqAllWidth
      (firstWindow.sourceArity + ihsDiagramCodArity firstWindow)
      (ihsDiagramDenote secondWindow) :=
    ihsAllWidthCast (by rw [hSourceEq, hCodEq])
      (ihsDiagramDenoteWidth secondWindow hSecondWF)
  have hIdLeftAll := ihqIdRowsWidth leftWires
  have hIdRightAll := ihqIdRowsWidth rightWires
  have hInner1All := ihsTensorRowsWidth firstWindow.sourceArity
    (ihsDiagramCodArity firstWindow) rightWires rightWires
    (ihsDiagramDenote firstWindow) (ihqIdRows rightWires) hFirstDenAll hIdRightAll
  have hInner2All := ihsTensorRowsWidth firstWindow.sourceArity
    (ihsDiagramCodArity firstWindow) rightWires rightWires
    (ihsDiagramDenote secondWindow) (ihqIdRows rightWires) hSecondDenAll hIdRightAll
  have hTensor1All := ihsTensorRowsWidth leftWires leftWires
    (firstWindow.sourceArity + rightWires)
    (ihsDiagramCodArity firstWindow + rightWires) (ihqIdRows leftWires) _
    hIdLeftAll hInner1All
  have hTensor2All := ihsTensorRowsWidth leftWires leftWires
    (firstWindow.sourceArity + rightWires)
    (ihsDiagramCodArity firstWindow + rightWires) (ihqIdRows leftWires) _
    hIdLeftAll hInner2All
  have hMiddle : IhsRelEquiv (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      (ihsTensorRows leftWires leftWires
        (firstWindow.sourceArity + rightWires)
        (ihsDiagramCodArity firstWindow + rightWires)
        (ihqIdRows leftWires)
        (ihsTensorRows firstWindow.sourceArity (ihsDiagramCodArity firstWindow)
          rightWires rightWires (ihsDiagramDenote firstWindow)
          (ihqIdRows rightWires)))
      (ihsTensorRows leftWires leftWires
        (firstWindow.sourceArity + rightWires)
        (ihsDiagramCodArity firstWindow + rightWires)
        (ihqIdRows leftWires)
        (ihsTensorRows firstWindow.sourceArity (ihsDiagramCodArity firstWindow)
          rightWires rightWires (ihsDiagramDenote secondWindow)
          (ihqIdRows rightWires))) :=
    ihwTensorRowsCong leftWires leftWires (firstWindow.sourceArity + rightWires)
      (ihsDiagramCodArity firstWindow + rightWires)
      hIdLeftAll hIdLeftAll hInner1All hInner2All
      (ihsRelEquivRefl leftWires leftWires (ihqIdRows leftWires))
      (ihwTensorRowsCong firstWindow.sourceArity (ihsDiagramCodArity firstWindow)
        rightWires rightWires hFirstDenAll hSecondDenAll hIdRightAll hIdRightAll
        hEquiv
        (ihsRelEquivRefl rightWires rightWires (ihqIdRows rightWires)))
  have hCompose1All := ihqComposeRowsWidth
    (leftWires + (firstWindow.sourceArity + rightWires))
    (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
    (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      afterLayers) _
    (ihsLayersDenote (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      afterLayers)
    hTensor1All hAfterAll
  have hCompose2All := ihqComposeRowsWidth
    (leftWires + (firstWindow.sourceArity + rightWires))
    (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
    (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      afterLayers) _
    (ihsLayersDenote (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      afterLayers)
    hTensor2All hAfterAll
  have hMidCong := ihsComposeRowsCong contextSource
    (leftWires + (firstWindow.sourceArity + rightWires))
    (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      afterLayers)
    hBeforeAll hBeforeAll hCompose1All hCompose2All
    (ihsRelEquivRefl contextSource
      (leftWires + (firstWindow.sourceArity + rightWires))
      (ihsLayersDenote contextSource beforeLayers))
    (ihsComposeRowsCong (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
      (ihsLayersCodArity (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hTensor1All hTensor2All hAfterAll hAfterAll hMiddle
      (ihsRelEquivRefl (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
        (ihsLayersCodArity (leftWires
          + (ihsDiagramCodArity firstWindow + rightWires)) afterLayers)
        (ihsLayersDenote (leftWires + (ihsDiagramCodArity firstWindow + rightWires))
          afterLayers)))
  refine And.intro rfl (And.intro ?_ (And.intro hPadWF1 (And.intro hPadWF2 ?_)))
  · rw [ihwPadDiagramCodArity contextSource leftWires rightWires beforeLayers
      afterLayers firstWindow hBeforeCod,
      ihwPadDiagramCodArity contextSource leftWires rightWires beforeLayers
        afterLayers secondWindow hBeforeCod2, hCodEq]
  · refine ihsRelEquivCast rfl
      (ihwPadDiagramCodArity contextSource leftWires rightWires beforeLayers
        afterLayers firstWindow hBeforeCod).symm ?_
    exact ihsRelEquivTrans hDecomp1
      (ihsRelEquivTrans hMidCong (ihsRelEquivSymm hDecomp2))

/-- One schema whisker rewriting step: an `IhzRowMove` window fired inside the
committed padding context (the `IhwStep.pad` shape verbatim, wider windows). -/
inductive IhzStep : IhsDiagram -> IhsDiagram -> Prop where
  | pad (contextSource leftWires rightWires : Nat)
      (beforeLayers afterLayers : List (List IhsCell))
      {firstWindow secondWindow : IhsDiagram}
      (hMove : IhzRowMove firstWindow secondWindow)
      (hBeforeWF : IhsLayersWF contextSource beforeLayers)
      (hBeforeCod : ihsLayersCodArity contextSource beforeLayers
        = leftWires + (firstWindow.sourceArity + rightWires))
      (hAfterWF : IhsLayersWF
        (leftWires + (ihsDiagramCodArity firstWindow + rightWires)) afterLayers) :
      IhzStep
        (ihwPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow)
        (ihwPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow)

/-- Soundness of one padded schema step. -/
theorem ihzStepBundle {firstDiagram secondDiagram : IhsDiagram}
    (hStep : IhzStep firstDiagram secondDiagram) :
    IhsConvBundle firstDiagram secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove
      hBeforeWF hBeforeCod hAfterWF =>
      exact ihzPadBundle contextSource leftWires rightWires beforeLayers
        afterLayers (ihzRowMoveBundle hMove) hBeforeWF hBeforeCod hAfterWF

/-- **THE SCHEMA WHISKER CONGRUENCE**: padded `IhzRowMove` steps, reflexivity
on well-formed diagrams, symmetry, transitivity — `IhwConv` widened by the
fourteen scalar schemas. -/
inductive IhzConv : IhsDiagram -> IhsDiagram -> Prop where
  | step {firstDiagram secondDiagram : IhsDiagram}
      (hStep : IhzStep firstDiagram secondDiagram) :
      IhzConv firstDiagram secondDiagram
  | refl (diagram : IhsDiagram) (hWF : IhsDiagramWF diagram) : IhzConv diagram diagram
  | symm {firstDiagram secondDiagram : IhsDiagram}
      (hConv : IhzConv firstDiagram secondDiagram) :
      IhzConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : IhsDiagram}
      (hFirst : IhzConv firstDiagram secondDiagram)
      (hSecond : IhzConv secondDiagram thirdDiagram) :
      IhzConv firstDiagram thirdDiagram

/-- **SOUNDNESS of the schema congruence** (the full seed bundle). -/
theorem ihzConvSound {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhzConv firstDiagram secondDiagram) :
    IhsConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | step hStep => exact ihzStepBundle hStep
  | refl diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (ihsRelEquivRefl diagram.sourceArity (ihsDiagramCodArity diagram)
          (ihsDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact ihsConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact ihsConvBundleTrans firstBundle secondBundle

/-- THE REFUTATION BRIDGE at the schema level: convertibility forces the
executable span decision to fire `true` — a kernel `false` pin refutes. -/
theorem ihzConvSpanEqB {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhzConv firstDiagram secondDiagram) :
    ihqSpanEqB (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram)
      = true := by
  have hBundle := ihzConvSound hConv
  exact ihsSpanEqBOfRelEquiv
    (ihsDiagramDenoteWidth firstDiagram hBundle.right.right.left)
    (ihsAllWidthCast
      (Eq.trans
        (congrArg (fun boundaryArity =>
          boundaryArity + ihsDiagramCodArity secondDiagram) hBundle.left.symm)
        (congrArg (fun boundaryArity =>
          firstDiagram.sourceArity + boundaryArity) hBundle.right.left.symm))
      (ihsDiagramDenoteWidth secondDiagram hBundle.right.right.right.left))
    hBundle.right.right.right.right

/-- Every schema row move is one `IhzConv` step on the nose (the identity pad
dissolves — the `ihwRowConv` argument at the wider window relation). -/
theorem ihzMoveConv {firstWindow secondWindow : IhsDiagram}
    (hMove : IhzRowMove firstWindow secondWindow) :
    IhzConv firstWindow secondWindow := by
  have hStep := IhzStep.pad firstWindow.sourceArity 0 0 [] [] hMove
    (IhsLayersWF.nil firstWindow.sourceArity)
    (Nat.zero_add (firstWindow.sourceArity + 0)).symm
    (IhsLayersWF.nil (0 + (ihsDiagramCodArity firstWindow + 0)))
  rw [ihwPadDiagramIdentityAt firstWindow.sourceArity firstWindow rfl,
    ihwPadDiagramIdentityAt firstWindow.sourceArity secondWindow
      (ihzRowMoveBundle hMove).left.symm] at hStep
  exact IhzConv.step hStep

/-- **THE EMBEDDING** `IhwConv -> IhzConv`: every committed whisker derivation
is a schema derivation (pad steps map arm-for-arm through `whiskerMove`). -/
theorem ihzConvOfWhiskerConv {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhwConv firstDiagram secondDiagram) :
    IhzConv firstDiagram secondDiagram := by
  induction hConv with
  | step hStep =>
      cases hStep with
      | pad contextSource leftWires rightWires beforeLayers afterLayers hMove
          hBeforeWF hBeforeCod hAfterWF =>
          exact IhzConv.step (IhzStep.pad contextSource leftWires rightWires
            beforeLayers afterLayers (IhzRowMove.whiskerMove hMove)
            hBeforeWF hBeforeCod hAfterWF)
  | refl diagram hWF => exact IhzConv.refl diagram hWF
  | symm _hInner innerCarried => exact IhzConv.symm innerCarried
  | trans _hFirst _hSecond firstCarried secondCarried =>
      exact IhzConv.trans firstCarried secondCarried

/-- The committed SEQUENTIAL congruence embeds end-to-end
(`IhsConv -> IhwConv -> IhzConv`). -/
theorem ihzConvOfSeedConv {firstDiagram secondDiagram : IhsDiagram}
    (hConv : IhsConv firstDiagram secondDiagram) :
    IhzConv firstDiagram secondDiagram :=
  ihzConvOfWhiskerConv (ihwConvOfSeedConv hConv)

/-! ## Stage 8 — fresh-scalar fires (T3)

The pins that prove the scalar-schema GAP IS CLOSED: `IhzConv` fires scalar
rows at scalars NO committed row mentions (4, 1/2, 7 — the committed
instantiated set is {2, 3, 5, 6, -1, 0, 1}). -/

/-- The fresh scalar 4 (not in the committed instantiated row set). -/
def ihzScalarFour : QnfRat := qnfOfInt 4

/-- The fresh scalar 7 (not in the committed instantiated row set). -/
def ihzScalarSeven : QnfRat := qnfOfInt 7

/-- The fresh NON-INTEGER scalar 1/2, built through `qnfNormalize` — no
committed cell carries a non-integer scalar anywhere in the seed. -/
def ihzScalarHalf : QnfRat :=
  qnfNormalize { numerator := 1, denominatorPredecessor := 1 }

/-- Kernel pin: `4 * (1/2) = 2` on the canonical carrier. -/
theorem ihzFreshProductComputes :
    qnfMul ihzScalarFour ihzScalarHalf = ihsScalarTwo := rfl

/-- Kernel pin: 4 is apart from the canonical zero. -/
theorem ihzScalarFourIsNonzero : ihzScalarFour ≠ qnfZero :=
  ihqQnfNeZeroOfBeqZeroFalse rfl

/-- **THE GAP-CLOSED FIRE** (A12 at fresh scalars): `scalarBox 4 ; scalarBox
(1/2)` converts to `scalarBox 2`.  NO committed row mentions 4 or 1/2 — under
`IhwConv` the committed instantiated rows can never fire at these scalars
(the brick-4 route-note item (2) gap); the product SCHEMA fires directly. -/
theorem ihzFireFreshScalarProduct :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihzScalarFour],
          [IhsCell.scalarBox ihzScalarHalf]] }
      { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarTwo]] } := by
  have hMove := ihzMoveConv (IhzRowMove.productSchema ihzScalarFour ihzScalarHalf)
  rw [ihzFreshProductComputes] at hMove
  exact hMove

set_option maxHeartbeats 4000000 in
/-- Kernel span cross-check for the fresh product fire: at CLOSED scalars the
brick-1 decision procedure independently confirms the schema instance. -/
theorem ihzFireFreshScalarProductSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 1
          layers := [[IhsCell.scalarBox ihzScalarFour],
            [IhsCell.scalarBox ihzScalarHalf]] })
      (ihsDiagramDenote
        { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarTwo]] })
      = true := rfl

/-- THE ANTIPODE-FAMILY FIRE at a fresh scalar (I1 at l = 4):
`scalarBox 4 ; scalarBoxMirror 4` converts to the wire. -/
theorem ihzFireFreshForwardCancel :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihzScalarFour],
          [IhsCell.scalarBoxMirror ihzScalarFour]] }
      { sourceArity := 1, layers := [[IhsCell.wire]] } :=
  ihzMoveConv (IhzRowMove.forwardCancelSchema ihzScalarFour ihzScalarFourIsNonzero)

set_option maxHeartbeats 4000000 in
/-- Kernel span cross-check for the fresh cancel fire. -/
theorem ihzFireFreshForwardCancelSpanPin :
    ihqSpanEqB
      (ihsDiagramDenote
        { sourceArity := 1
          layers := [[IhsCell.scalarBox ihzScalarFour],
            [IhsCell.scalarBoxMirror ihzScalarFour]] })
      (ihsDiagramDenote { sourceArity := 1, layers := [[IhsCell.wire]] })
      = true := rfl

/-- The scalar-4 box as a diagram (fresh-scalar FALSE-control carrier). -/
def ihzScalarFourDiagram : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.scalarBox ihzScalarFour]] }

/-- The scalar-7 box as a diagram (fresh-scalar FALSE-control carrier). -/
def ihzScalarSevenDiagram : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.scalarBox ihzScalarSeven]] }

/-- FALSE CONTROL at fresh scalars: 4 and 7 denote different lines in Q^2. -/
theorem ihzFireFreshScalarsSpanDistinct :
    ihqSpanEqB (ihsDiagramDenote ihzScalarFourDiagram)
      (ihsDiagramDenote ihzScalarSevenDiagram) = false := rfl

/-- NEGATIVE DIRECTION at fresh scalars: even under the full schema
congruence, scalar 4 is NOT convertible to scalar 7. -/
theorem ihzFireFreshScalarsNotConv :
    Not (IhzConv ihzScalarFourDiagram ihzScalarSevenDiagram) :=
  fun hConv =>
    Bool.noConfusion ((ihzConvSpanEqB hConv).symm.trans ihzFireFreshScalarsSpanDistinct)

/-! ### Instance sanity pins: the schemas subsume the committed rows byte-for-byte -/

/-- At the committed instance (2, 3) the product schema's boundary diagrams ARE
the committed A12 row's diagrams (`qnfMul 2 3` computes to the committed 6). -/
theorem ihzProductSchemaInstanceIsSeedRow :
    ({ sourceArity := 1
       layers := [[IhsCell.scalarBox (qnfMul ihsScalarTwo ihsScalarThree)]] }
        : IhsDiagram)
      = ihsRowRhs IhsRowTag.scalarProduct := rfl

/-- At the committed instance (2, 3) the sum schema's right diagram IS the
committed A18 row's right diagram (`qnfAdd 2 3` computes to the committed 5). -/
theorem ihzSumSchemaInstanceIsSeedRow :
    ({ sourceArity := 1
       layers := [[IhsCell.scalarBox (qnfAdd ihsScalarTwo ihsScalarThree)]] }
        : IhsDiagram)
      = ihsRowRhs IhsRowTag.scalarSum := rfl

/-- At the committed instance the mirror-product schema's right diagram IS the
committed A12op row's right diagram. -/
theorem ihzProductMirrorSchemaInstanceIsSeedRow :
    ({ sourceArity := 1
       layers := [[IhsCell.scalarBoxMirror (qnfMul ihsScalarTwo ihsScalarThree)]] }
        : IhsDiagram)
      = ihsRowRhs IhsRowTag.scalarProductOp := rfl

/-! ## Stage 9 — the canonical NF chooser (HALF B, T4 matrix side)

The BSZ Theorem 6.4 normal form factors every relation through a SPAN of
matrices; the matrix-side representative must be CANONICAL.  The chooser:
`ihqRref` (brick 1) followed by pivot normalization through `qnfInv` —
leading-ONE reduced row echelon form, with span preservation both ways and
the kernel decision cross-check. -/

/-- Normalize one row to leading coefficient one (identity on the zero row). -/
def ihzLeadingOneRow (row : List QnfRat) : List QnfRat :=
  match ihqLead row with
  | Option.none => row
  | Option.some leadPosition =>
      ihqRowScale (qnfInv (ihqGetCoeff row leadPosition)) row

theorem ihzLeadingOneRowNone (row : List QnfRat)
    (hLead : ihqLead row = Option.none) : ihzLeadingOneRow row = row := by
  rw [show ihzLeadingOneRow row
      = (match ihqLead row with
         | Option.none => row
         | Option.some leadPosition =>
             ihqRowScale (qnfInv (ihqGetCoeff row leadPosition)) row) from rfl,
    hLead]

theorem ihzLeadingOneRowSome (row : List QnfRat) (leadPosition : Nat)
    (hLead : ihqLead row = Option.some leadPosition) :
    ihzLeadingOneRow row
      = ihqRowScale (qnfInv (ihqGetCoeff row leadPosition)) row := by
  rw [show ihzLeadingOneRow row
      = (match ihqLead row with
         | Option.none => row
         | Option.some leadPosition =>
             ihqRowScale (qnfInv (ihqGetCoeff row leadPosition)) row) from rfl,
    hLead]

theorem ihzLeadingOneRowLength (row : List QnfRat) :
    (ihzLeadingOneRow row).length = row.length := by
  cases hLead : ihqLead row with
  | none => rw [ihzLeadingOneRowNone row hLead]
  | some leadPosition =>
      rw [ihzLeadingOneRowSome row leadPosition hLead]
      exact ihqRowScaleLength (qnfInv (ihqGetCoeff row leadPosition)) row

/-- THE UNIT-PIVOT INVARIANT: after normalization the lead coefficient IS the
canonical one (the leading-one shape `zxpRrefUniquenessStatement`'s F2
precedent could not even express — over F2 every pivot is already 1). -/
theorem ihzLeadingOneRowUnitPivot (row : List QnfRat) (leadPosition : Nat)
    (hLead : ihqLead row = Option.some leadPosition) :
    ihqGetCoeff (ihzLeadingOneRow row) leadPosition = qnfOne := by
  have hNonzero : ihqGetCoeff row leadPosition ≠ qnfZero :=
    ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse row leadPosition hLead)
  rw [ihzLeadingOneRowSome row leadPosition hLead,
    ihqGetCoeffScale (qnfInv (ihqGetCoeff row leadPosition)) row leadPosition]
  exact qnfInvMulCancels hNonzero

/-- **THE CANONICAL CHOOSER**: leading-one reduced row echelon form. -/
def ihzCanonicalRows (rows : List (List QnfRat)) : List (List QnfRat) :=
  ihqMapRows ihzLeadingOneRow (ihqRref rows)

theorem ihzCanonicalRowsWidth {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) : IhqAllWidth width (ihzCanonicalRows rows) :=
  ihqMapRowsWidth ihzLeadingOneRow
    (fun row hLen => (ihzLeadingOneRowLength row).trans hLen)
    (ihqRref rows) (ihqRrefWidth rows hAll)

/-- A normalized row stays inside the span of the source list. -/
theorem ihzLeadingOneRowInSpan {width : Nat} {rows : List (List QnfRat)}
    (hAll : IhqAllWidth width rows) {row : List QnfRat}
    (hRow : IhqRowMem row rows) :
    IhqMemSpan width rows (ihzLeadingOneRow row) := by
  cases hLead : ihqLead row with
  | none =>
      rw [ihzLeadingOneRowNone row hLead]
      exact ihqMemSpanElem hAll hRow
  | some leadPosition =>
      rw [ihzLeadingOneRowSome row leadPosition hLead]
      exact ihqMemSpanScaleClosed (qnfInv (ihqGetCoeff row leadPosition))
        (ihqMemSpanElem hAll hRow)

/-- A source row is recovered from its normalization by the lead scale — THE
field step (needs `qnfInv`; the zero row recovers itself). -/
theorem ihzRowInLeadingOneSpan {width : Nat} {rows : List (List QnfRat)}
    (hMappedAll : IhqAllWidth width (ihqMapRows ihzLeadingOneRow rows))
    {row : List QnfRat} (hRow : IhqRowMem row rows) :
    IhqMemSpan width (ihqMapRows ihzLeadingOneRow rows) row := by
  cases hLead : ihqLead row with
  | none =>
      rw [<- ihzLeadingOneRowNone row hLead]
      exact ihqMemSpanElem hMappedAll
        (ihqMapRowsMemIntro ihzLeadingOneRow rows hRow)
  | some leadPosition =>
      have hNonzero : ihqGetCoeff row leadPosition ≠ qnfZero :=
        ihqQnfNeZeroOfBeqZeroFalse (ihqLeadCoeffBeqFalse row leadPosition hLead)
      have hScaleBack : ihqRowScale (ihqGetCoeff row leadPosition)
          (ihzLeadingOneRow row) = row := by
        rw [ihzLeadingOneRowSome row leadPosition hLead,
          ihqRowScaleScale (ihqGetCoeff row leadPosition)
            (qnfInv (ihqGetCoeff row leadPosition)) row,
          qnfMulInvCancels hNonzero, ihqRowScaleOne row]
      rw [<- hScaleBack]
      exact ihqMemSpanScaleClosed (ihqGetCoeff row leadPosition)
        (ihqMemSpanElem hMappedAll
          (ihqMapRowsMemIntro ihzLeadingOneRow rows hRow))

/-- **SPAN PRESERVATION of the canonical chooser**, both directions. -/
theorem ihzCanonicalRowsSpanIff {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) (vector : List QnfRat) :
    IhqMemSpan width (ihzCanonicalRows rows) vector
      <-> IhqMemSpan width rows vector := by
  have hRrefAll := ihqRrefWidth rows hAll
  have hCanonAll := ihzCanonicalRowsWidth rows hAll
  refine Iff.intro ?_ ?_
  · intro hMem
    refine (ihqRrefSpansSame rows hAll vector).mp ?_
    refine ihqMemSpanSub hRrefAll ?_ hMem
    intro mappedRow hMapped
    cases ihqMapRowsMemInv ihzLeadingOneRow (ihqRref rows) hMapped with
    | intro sourceRow hBoth =>
        rw [hBoth.right]
        exact ihzLeadingOneRowInSpan hRrefAll hBoth.left
  · intro hMem
    refine ihqMemSpanSub hCanonAll ?_ ((ihqRrefSpansSame rows hAll vector).mpr hMem)
    intro sourceRow hSource
    exact ihzRowInLeadingOneSpan hCanonAll hSource

/-- The kernel decision cross-check: the chooser's output span-equals its
input, as an `ihqSpanEqB` fire (via completeness — NOT `rfl`; the chooser is
symbolic here). -/
theorem ihzCanonicalRowsSpanEqB {width : Nat} (rows : List (List QnfRat))
    (hAll : IhqAllWidth width rows) :
    ihqSpanEqB (ihzCanonicalRows rows) rows = true :=
  ihqSpanEqBComplete (ihzCanonicalRowsWidth rows hAll) hAll
    (fun vector => ihzCanonicalRowsSpanIff rows hAll vector)

set_option maxHeartbeats 4000000 in
/-- Kernel `rfl` fire: the chooser normalizes `[[2, 6]]` to the leading-one
representative `[[1, 3]]`. -/
theorem ihzFireCanonicalRowsExample :
    ihzCanonicalRows [[ihsScalarTwo, ihsScalarSix]] = [[qnfOne, ihsScalarThree]] := rfl

/-! ## Stage 10 — the zero-relation normal form (HALF B, the diagram base case)

The `rows = []` (zero-subspace) corner of the BSZ factorized shape as an
actual diagram: a cozero fan pinning every input at 0 followed by a zero fan
pinning every output at 0 — proven to denote the EMPTY generator matrix at
THEOREM level for ARBITRARY boundaries. -/

/-- One `whiteCounit` per input strand. -/
def ihzCozeroFanCells : Nat -> List IhsCell
  | 0 => []
  | strandPred + 1 => IhsCell.whiteCounit :: ihzCozeroFanCells strandPred

/-- One `whiteUnit` per output strand. -/
def ihzZeroFanCells : Nat -> List IhsCell
  | 0 => []
  | strandPred + 1 => IhsCell.whiteUnit :: ihzZeroFanCells strandPred

theorem ihzCozeroFanDomArity : (strandCount : Nat) ->
    ihsLayerDomArity (ihzCozeroFanCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + ihsLayerDomArity (ihzCozeroFanCells strandPred) = strandPred + 1
      rw [ihzCozeroFanDomArity strandPred]
      exact Nat.add_comm 1 strandPred

theorem ihzCozeroFanCodArityZero : (strandCount : Nat) ->
    ihsLayerCodArity (ihzCozeroFanCells strandCount) = 0
  | 0 => rfl
  | strandPred + 1 => by
      show 0 + ihsLayerCodArity (ihzCozeroFanCells strandPred) = 0
      rw [ihzCozeroFanCodArityZero strandPred]

theorem ihzZeroFanDomArityZero : (strandCount : Nat) ->
    ihsLayerDomArity (ihzZeroFanCells strandCount) = 0
  | 0 => rfl
  | strandPred + 1 => by
      show 0 + ihsLayerDomArity (ihzZeroFanCells strandPred) = 0
      rw [ihzZeroFanDomArityZero strandPred]

theorem ihzZeroFanCodArity : (strandCount : Nat) ->
    ihsLayerCodArity (ihzZeroFanCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + ihsLayerCodArity (ihzZeroFanCells strandPred) = strandPred + 1
      rw [ihzZeroFanCodArity strandPred]
      exact Nat.add_comm 1 strandPred

/-- The cozero fan's generator matrix is EMPTY (each cell contributes no rows). -/
theorem ihzCozeroFanDenoteNil : (strandCount : Nat) ->
    ihsLayerDenote (ihzCozeroFanCells strandCount) = []
  | 0 => rfl
  | strandPred + 1 => by
      show ihsTensorRows 1 0 (ihsLayerDomArity (ihzCozeroFanCells strandPred))
          (ihsLayerCodArity (ihzCozeroFanCells strandPred))
          [] (ihsLayerDenote (ihzCozeroFanCells strandPred)) = []
      rw [ihzCozeroFanDenoteNil strandPred]
      exact rfl

/-- The zero fan's generator matrix is EMPTY. -/
theorem ihzZeroFanDenoteNil : (strandCount : Nat) ->
    ihsLayerDenote (ihzZeroFanCells strandCount) = []
  | 0 => rfl
  | strandPred + 1 => by
      show ihsTensorRows 0 1 (ihsLayerDomArity (ihzZeroFanCells strandPred))
          (ihsLayerCodArity (ihzZeroFanCells strandPred))
          [] (ihsLayerDenote (ihzZeroFanCells strandPred)) = []
      rw [ihzZeroFanDenoteNil strandPred]
      exact rfl

/-- The zero-relation normal form diagram at boundary `m -> n`. -/
def ihzZeroRelationDiagram (domWidth codWidth : Nat) : IhsDiagram :=
  { sourceArity := domWidth
    layers := [ihzCozeroFanCells domWidth, ihzZeroFanCells codWidth] }

theorem ihzZeroRelationDiagramWF (domWidth codWidth : Nat) :
    IhsDiagramWF (ihzZeroRelationDiagram domWidth codWidth) :=
  IhsLayersWF.cons (ihzCozeroFanDomArity domWidth)
    (IhsLayersWF.cons
      ((ihzZeroFanDomArityZero codWidth).trans
        (ihzCozeroFanCodArityZero domWidth).symm)
      (IhsLayersWF.nil (ihsLayerCodArity (ihzZeroFanCells codWidth))))

theorem ihzZeroRelationDiagramCodArity (domWidth codWidth : Nat) :
    ihsDiagramCodArity (ihzZeroRelationDiagram domWidth codWidth) = codWidth :=
  ihzZeroFanCodArity codWidth

/-- The zero NF diagram's denotation, reshaped onto closed generator data. -/
theorem ihzZeroRelationDiagramDenoteShape (domWidth codWidth : Nat) :
    ihsDiagramDenote (ihzZeroRelationDiagram domWidth codWidth)
      = ihqComposeRows domWidth 0 codWidth []
          (ihqComposeRows 0 codWidth codWidth [] (ihqIdRows codWidth)) := by
  have hInnerShape : ihsLayersDenote 0 [ihzZeroFanCells codWidth]
      = ihqComposeRows 0 codWidth codWidth [] (ihqIdRows codWidth) := by
    rw [show ihsLayersDenote 0 [ihzZeroFanCells codWidth]
        = ihqComposeRows 0 (ihsLayerCodArity (ihzZeroFanCells codWidth))
            (ihsLayersCodArity (ihsLayerCodArity (ihzZeroFanCells codWidth)) [])
            (ihsLayerDenote (ihzZeroFanCells codWidth))
            (ihsLayersDenote (ihsLayerCodArity (ihzZeroFanCells codWidth)) [])
        from rfl,
      ihzZeroFanDenoteNil codWidth, ihzZeroFanCodArity codWidth]
    exact rfl
  rw [show ihsDiagramDenote (ihzZeroRelationDiagram domWidth codWidth)
      = ihqComposeRows domWidth (ihsLayerCodArity (ihzCozeroFanCells domWidth))
          (ihsLayersCodArity (ihsLayerCodArity (ihzCozeroFanCells domWidth))
            [ihzZeroFanCells codWidth])
          (ihsLayerDenote (ihzCozeroFanCells domWidth))
          (ihsLayersDenote (ihsLayerCodArity (ihzCozeroFanCells domWidth))
            [ihzZeroFanCells codWidth])
      from rfl,
    ihzCozeroFanDenoteNil domWidth, ihzCozeroFanCodArityZero domWidth,
    hInnerShape,
    show ihsLayersCodArity 0 [ihzZeroFanCells codWidth]
      = ihsLayerCodArity (ihzZeroFanCells codWidth) from rfl,
    ihzZeroFanCodArity codWidth]

/-- **THE BASE-CASE DENOTATION THEOREM** (arbitrary boundaries): the zero NF
diagram denotes exactly the empty generator matrix's relation. -/
theorem ihzZeroRelationDiagramDenotesNil (domWidth codWidth : Nat) :
    IhsRelEquiv domWidth codWidth
      (ihsDiagramDenote (ihzZeroRelationDiagram domWidth codWidth)) [] := by
  intro domVec codVec
  rw [ihzZeroRelationDiagramDenoteShape domWidth codWidth]
  refine Iff.trans (ihzPairTwoStageIff domWidth 0 codWidth [] []
    IhqAllWidth.nil IhqAllWidth.nil domVec codVec) ?_
  refine Iff.trans ?_ (ihzNilRelationSpec domWidth codWidth domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hStages =>
        have hFront := (ihzNilRelationSpec domWidth 0 domVec midVec).mp hStages.left
        have hBack := (ihzNilRelationSpec 0 codWidth midVec codVec).mp hStages.right
        exact And.intro hFront.left hBack.right
  · intro hBoth
    refine Exists.intro [] (And.intro ?_ ?_)
    · exact (ihzNilRelationSpec domWidth 0 domVec []).mpr
        (And.intro hBoth.left rfl)
    · exact (ihzNilRelationSpec 0 codWidth [] codVec).mpr
        (And.intro rfl hBoth.right)

set_option maxHeartbeats 4000000 in
/-- Kernel cross-check at a closed boundary: the `2 -> 1` zero NF diagram's
denotation span-equals the empty matrix by `rfl`. -/
theorem ihzFireZeroRelationDiagramSpanPin :
    ihqSpanEqB (ihsDiagramDenote (ihzZeroRelationDiagram 2 1)) [] = true := rfl

/-! ## Stage 11 — statements, walls, markers (T5) -/

/-- THE NORMAL-FORM CARRIER STATEMENT (BSZ Theorem 6.4 span-of-matrices
factorization, diagram side): every generator matrix at every boundary is
denoted by SOME well-formed diagram.

OWNER FALSE — NOT PROVEN, NOT COMMISSIONED THIS BRICK.  What IS shipped:
(i) the zero-relation base case `ihzZeroRelationDiagram` +
`ihzZeroRelationDiagramDenotesNil` (rows = [], arbitrary boundaries);
(ii) the canonical matrix-side chooser `ihzCanonicalRows` with span
preservation and the unit-pivot invariant.  THE RESIDUAL (the honest wall):
the TOTAL matrix -> diagram compiler in the factorized shape — a copy fan
(`blackComult` tree) per input, a `scalarBox`-entry grid wired by A18-style
sums, an add fan (`whiteMult` tree) per output — plus its denotation
induction through `ihwTensorSpec`/`ihqComposeSpec` over rows and columns;
this is the ZX-arc's matrix-reification analogue and is a BUILD, not a wall
of principle.  Brick 5 should synthesize the compiler by recursion on the
row list, reusing the Stage-1 specs as the per-entry atoms. -/
def ihzNormalFormStatement : Prop :=
  (domWidth codWidth : Nat) -> (rows : List (List QnfRat)) ->
  IhqAllWidth (domWidth + codWidth) rows ->
  Exists fun nfDiagram =>
    nfDiagram.sourceArity = domWidth
      /\ ihsDiagramCodArity nfDiagram = codWidth
      /\ IhsDiagramWF nfDiagram
      /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote nfDiagram) rows

/-- THE REACHABILITY / COMPLETENESS STATEMENT at the schema congruence:
span-equal well-formed diagrams on matching boundaries are `IhzConv`-related
(equivalently: every WF diagram reaches the NF of its denotation).

OWNER FALSE — NOT PROVEN, NOT COMMISSIONED THIS BRICK.  What changed since
the seed's `ihsCompletenessStatement`: blockers (1) [no whisker congruence]
and (2) [instantiated-scalar-only rows] are now BOTH discharged —
`ihwHasWhiskerCongruence` (brick 3) and `ihzHasScalarSchemas` (this brick)
— so this statement is the FIRST version whose congruence is plausibly
complete.  THE RESIDUAL for brick 5: (a) the NF carrier
(`ihzNormalFormStatement` above); (b) the REACHABILITY INDUCTION — every WF
diagram `IhzConv`-reduces to the factorized shape: an absorption-style
induction over layers (the ZX-arc analogue) that pushes each generator
through the accumulated span form via the A8/I3/I4 Frobenius-bimonoid moves
and the fourteen schemas, exactly the census order the seed docstring
prescribes: census -> gate-refutation -> induction.  The committed
owner-false seed markers (`ihsCompletenessIsProven`,
`ihsCompletenessStatement`) stay byte-intact; this statement SUPERSEDES them
by extension. -/
def ihzReachabilityStatement : Prop :=
  (firstDiagram secondDiagram : IhsDiagram) ->
    IhsDiagramWF firstDiagram -> IhsDiagramWF secondDiagram ->
    firstDiagram.sourceArity = secondDiagram.sourceArity ->
    ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram ->
    IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
      (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram) ->
    IhzConv firstDiagram secondDiagram

/-- DECIDED — THE SCALAR-SCHEMA ADJUDICATION EXECUTED (supersedes the
brick-4 route-note item (2) on the committed `ihwHasWhiskerCongruence`,
which stays byte-intact): all fourteen scalar-indexed census families ship
as PARAMETERIZED row moves (`IhzRowMove`) with THEOREM-level span soundness
quantified over the scalars, the pad congruence `IhzConv` fires them in
whisker context, `IhwConv` embeds (`ihzConvOfWhiskerConv`), and the
fresh-scalar fires (`ihzFireFreshScalarProduct` at 4 and 1/2,
`ihzFireFreshForwardCancel` at 4, the 4-vs-7 FALSE control) pin that the
committed instantiated-scalar gap is CLOSED. -/
def ihzHasScalarSchemas : Bool := true

/-- DECIDED: the canonical matrix-side NF chooser (`ihzCanonicalRows` —
leading-one RREF via `ihqRref` + `qnfInv` pivots) ships with width
preservation, span preservation both ways, the unit-pivot invariant, the
`ihqSpanEqB` cross-check, and a kernel `rfl` fire. -/
def ihzHasCanonicalChooser : Bool := true

/-- OWNER FALSE — the full BSZ span-of-matrices DIAGRAM carrier is NOT
shipped; only the zero-relation base case is (see `ihzNormalFormStatement`
for the precise residual: the total matrix -> diagram compiler). -/
def ihzHasNormalFormCarrier : Bool := false

/-- OWNER FALSE — reachability/completeness of `IhzConv` is NOT proven (see
`ihzReachabilityStatement` for the residual: NF carrier + absorption-style
reachability induction). -/
def ihzReachabilityIsProven : Bool := false

end FX1Poly.ComputerAlgebra
