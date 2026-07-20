import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfCompiler

/-! # LinearAlgebra/InteractingHopfRowGadget — the single-row IH_Q gadget
(WP-PROP-3 brick 6)

Executing the brick-5 Stage-7 route residual on `ihzNormalFormStatement`: the
`R = 1` matrix -> diagram reifier for a single generator row over `IH_Q`.

* THE SCALAR LAYER (T1, `ihgScalarLayer` / `ihgScalarMirrorLayer`): a horizontal
  tensor of `scalarBox`/`scalarBoxMirror` cells over a coefficient list, with the
  arbitrary-width per-strand denotation theorems (`ihgScalarLayerDenote`,
  `ihgScalarMirrorLayerDenote`): the layer relates its input vector to the
  pointwise `qnfMul` by the coefficients, proven by structural recursion on the
  coefficient list via `ihwTensorSpec` + `ihzScalarGraphSpec`/`ihzScalarMirrorSpec`.

* THE SINGLE-ROW GADGET (T2, `ihgGadgetDiagram`): the four-stage
  `Collapse ; Expand` pipeline of the Stage-7 route —
  `scalarBoxMirror`-layer ; mult fan ; copy fan ; `scalarBox`-layer — with THE
  DENOTATION THEOREM (`ihgGadgetDenote`): the gadget spans the line
  `{ (scale c inputs, scale c outputs) }`, assembled via `ihqComposeSpec` /
  `ihwLayersDenoteCat` / `ihsLayersDenoteSnoc` through the committed fan kit.

* THE SINGLE-ROW NF CARRIER (T3, `ihgSingleRowNormalForm`): the single-row
  instance of `ihzNormalFormStatement` — the gadget is a WF diagram span-equal
  to the single-row matrix `[inputs ++ outputs]`.

* THE MULTI-ROW WALL (T4, `ihgTwoRowSpatialSumStatement`, owner-false): the
  `R >= 2` spatial sum needs the generator-transpose RIFFLE permutation layer.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfRowGadget.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the scalar layer constructors (T1) -/

/-- The parallel scalar layer: one `scalarBox k_i` cell per coefficient. -/
def ihgScalarLayer : List QnfRat -> List IhsCell
  | [] => []
  | headCoeff :: restCoeffs => IhsCell.scalarBox headCoeff :: ihgScalarLayer restCoeffs

/-- The parallel mirror scalar layer: one `scalarBoxMirror k_i` per coefficient. -/
def ihgScalarMirrorLayer : List QnfRat -> List IhsCell
  | [] => []
  | headCoeff :: restCoeffs =>
      IhsCell.scalarBoxMirror headCoeff :: ihgScalarMirrorLayer restCoeffs

theorem ihgScalarLayerDomArity : (coefficients : List QnfRat) ->
    ihsLayerDomArity (ihgScalarLayer coefficients) = coefficients.length
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show 1 + ihsLayerDomArity (ihgScalarLayer restCoeffs) = restCoeffs.length + 1
      rw [ihgScalarLayerDomArity restCoeffs, Nat.add_comm 1 restCoeffs.length]

theorem ihgScalarLayerCodArity : (coefficients : List QnfRat) ->
    ihsLayerCodArity (ihgScalarLayer coefficients) = coefficients.length
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show 1 + ihsLayerCodArity (ihgScalarLayer restCoeffs) = restCoeffs.length + 1
      rw [ihgScalarLayerCodArity restCoeffs, Nat.add_comm 1 restCoeffs.length]

theorem ihgScalarMirrorLayerDomArity : (coefficients : List QnfRat) ->
    ihsLayerDomArity (ihgScalarMirrorLayer coefficients) = coefficients.length
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show 1 + ihsLayerDomArity (ihgScalarMirrorLayer restCoeffs) = restCoeffs.length + 1
      rw [ihgScalarMirrorLayerDomArity restCoeffs, Nat.add_comm 1 restCoeffs.length]

theorem ihgScalarMirrorLayerCodArity : (coefficients : List QnfRat) ->
    ihsLayerCodArity (ihgScalarMirrorLayer coefficients) = coefficients.length
  | [] => rfl
  | headCoeff :: restCoeffs => by
      show 1 + ihsLayerCodArity (ihgScalarMirrorLayer restCoeffs) = restCoeffs.length + 1
      rw [ihgScalarMirrorLayerCodArity restCoeffs, Nat.add_comm 1 restCoeffs.length]

theorem ihgScalarLayerAllWidth (coefficients : List QnfRat) :
    IhqAllWidth (coefficients.length + coefficients.length)
      (ihsLayerDenote (ihgScalarLayer coefficients)) :=
  ihsAllWidthCast
    (by rw [ihgScalarLayerDomArity coefficients, ihgScalarLayerCodArity coefficients])
    (ihsLayerDenoteWidth (ihgScalarLayer coefficients))

theorem ihgScalarMirrorLayerAllWidth (coefficients : List QnfRat) :
    IhqAllWidth (coefficients.length + coefficients.length)
      (ihsLayerDenote (ihgScalarMirrorLayer coefficients)) :=
  ihsAllWidthCast
    (by rw [ihgScalarMirrorLayerDomArity coefficients,
      ihgScalarMirrorLayerCodArity coefficients])
    (ihsLayerDenoteWidth (ihgScalarMirrorLayer coefficients))

/-- Pointwise product of an input vector with the coefficient list (the diagonal
scaling denotation of the scalar layer). -/
def ihgPointwiseScale : List QnfRat -> List QnfRat -> List QnfRat
  | [], [] => []
  | [], _headCoeff :: _restCoeffs => []
  | _headInput :: _restInputs, [] => []
  | headInput :: restInputs, headCoeff :: restCoeffs =>
      qnfMul headInput headCoeff :: ihgPointwiseScale restInputs restCoeffs

/-! ## Stage 1 — the per-strand scalar-layer denotations (T1) -/

theorem ihgScalarLayerDenote : (coefficients : List QnfRat) ->
    (domVec codVec : List QnfRat) ->
    (IhqPairMem coefficients.length coefficients.length
        (ihsLayerDenote (ihgScalarLayer coefficients)) domVec codVec
      <-> domVec.length = coefficients.length
          /\ codVec = ihgPointwiseScale domVec coefficients)
  | [], domVec, codVec => by
      refine Iff.trans (ihzNilRelationSpec 0 0 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hBoth
        refine And.intro ?_ ?_
        · rw [hBoth.left]
          rfl
        · rw [hBoth.left, hBoth.right]
          rfl
      · intro hBoth
        have hDomNil : domVec = [] := ihsLengthZeroNil domVec hBoth.left
        refine And.intro ?_ ?_
        · rw [hDomNil]
          rfl
        · rw [hBoth.right, hDomNil]
          rfl
  | headCoeff :: restCoeffs, domVec, codVec => by
      have hDenote : ihsLayerDenote (ihgScalarLayer (headCoeff :: restCoeffs))
          = ihsTensorRows 1 1 restCoeffs.length restCoeffs.length
              [[qnfOne, headCoeff]] (ihsLayerDenote (ihgScalarLayer restCoeffs)) := by
        show ihsTensorRows 1 1 (ihsLayerDomArity (ihgScalarLayer restCoeffs))
            (ihsLayerCodArity (ihgScalarLayer restCoeffs)) [[qnfOne, headCoeff]]
            (ihsLayerDenote (ihgScalarLayer restCoeffs)) = _
        rw [ihgScalarLayerDomArity restCoeffs, ihgScalarLayerCodArity restCoeffs]
      rw [hDenote]
      refine Iff.trans (ihwPairMemCast
        (rows := ihsTensorRows 1 1 restCoeffs.length restCoeffs.length
          [[qnfOne, headCoeff]] (ihsLayerDenote (ihgScalarLayer restCoeffs)))
        (Nat.add_comm 1 restCoeffs.length).symm
        (Nat.add_comm 1 restCoeffs.length).symm) ?_
      refine Iff.trans (ihwTensorSpec 1 1 restCoeffs.length restCoeffs.length
        [[qnfOne, headCoeff]] (ihsLayerDenote (ihgScalarLayer restCoeffs))
        (ihzScalarRowsAllWidth headCoeff)
        (ihsAllWidthCast (by rw [ihgScalarLayerDomArity restCoeffs,
          ihgScalarLayerCodArity restCoeffs])
          (ihsLayerDenoteWidth (ihgScalarLayer restCoeffs)))
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro firstDomVec hPack1 =>
            cases hPack1 with
            | intro secondDomVec hPack2 =>
                cases hPack2 with
                | intro firstCodVec hPack3 =>
                    cases hPack3 with
                    | intro secondCodVec hFacts =>
                        cases (ihzScalarGraphSpec headCoeff firstDomVec firstCodVec).mp
                          hFacts.right.right.left with
                        | intro inputCoeff hScalar =>
                            have hTail := (ihgScalarLayerDenote restCoeffs
                              secondDomVec secondCodVec).mp hFacts.right.right.right
                            refine And.intro ?_ ?_
                            · rw [hFacts.left, ihqCatLength, hScalar.left]
                              show 1 + secondDomVec.length = restCoeffs.length + 1
                              rw [hTail.left, Nat.add_comm 1 restCoeffs.length]
                            · rw [hFacts.right.left, hFacts.left, hScalar.left,
                                hScalar.right, hTail.right]
                              show qnfMul inputCoeff headCoeff
                                  :: ihgPointwiseScale secondDomVec restCoeffs
                                = ihgPointwiseScale (ihqCat [inputCoeff] secondDomVec)
                                    (headCoeff :: restCoeffs)
                              rfl
      · intro hBoth
        cases domVec with
        | nil => exact nomatch hBoth.left
        | cons headInput restInputs =>
            have hRestLen : restInputs.length = restCoeffs.length :=
              Nat.succ.inj hBoth.left
            refine Exists.intro [headInput] (Exists.intro restInputs
              (Exists.intro [qnfMul headInput headCoeff]
                (Exists.intro (ihgPointwiseScale restInputs restCoeffs)
                  (And.intro rfl (And.intro ?_ (And.intro ?_ ?_))))))
            · rw [hBoth.right]
              rfl
            · exact (ihzScalarGraphSpec headCoeff [headInput]
                [qnfMul headInput headCoeff]).mpr
                (Exists.intro headInput (And.intro rfl rfl))
            · exact (ihgScalarLayerDenote restCoeffs restInputs
                (ihgPointwiseScale restInputs restCoeffs)).mpr
                (And.intro hRestLen rfl)

theorem ihgScalarMirrorLayerDenote : (coefficients : List QnfRat) ->
    (domVec codVec : List QnfRat) ->
    (IhqPairMem coefficients.length coefficients.length
        (ihsLayerDenote (ihgScalarMirrorLayer coefficients)) domVec codVec
      <-> codVec.length = coefficients.length
          /\ domVec = ihgPointwiseScale codVec coefficients)
  | [], domVec, codVec => by
      refine Iff.trans (ihzNilRelationSpec 0 0 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hBoth
        refine And.intro ?_ ?_
        · rw [hBoth.right]
          rfl
        · rw [hBoth.left, hBoth.right]
          rfl
      · intro hBoth
        have hCodNil : codVec = [] := ihsLengthZeroNil codVec hBoth.left
        refine And.intro ?_ ?_
        · rw [hBoth.right, hCodNil]
          rfl
        · rw [hCodNil]
          rfl
  | headCoeff :: restCoeffs, domVec, codVec => by
      have hDenote : ihsLayerDenote (ihgScalarMirrorLayer (headCoeff :: restCoeffs))
          = ihsTensorRows 1 1 restCoeffs.length restCoeffs.length
              [[headCoeff, qnfOne]]
              (ihsLayerDenote (ihgScalarMirrorLayer restCoeffs)) := by
        show ihsTensorRows 1 1 (ihsLayerDomArity (ihgScalarMirrorLayer restCoeffs))
            (ihsLayerCodArity (ihgScalarMirrorLayer restCoeffs)) [[headCoeff, qnfOne]]
            (ihsLayerDenote (ihgScalarMirrorLayer restCoeffs)) = _
        rw [ihgScalarMirrorLayerDomArity restCoeffs,
          ihgScalarMirrorLayerCodArity restCoeffs]
      rw [hDenote]
      refine Iff.trans (ihwPairMemCast
        (rows := ihsTensorRows 1 1 restCoeffs.length restCoeffs.length
          [[headCoeff, qnfOne]] (ihsLayerDenote (ihgScalarMirrorLayer restCoeffs)))
        (Nat.add_comm 1 restCoeffs.length).symm
        (Nat.add_comm 1 restCoeffs.length).symm) ?_
      refine Iff.trans (ihwTensorSpec 1 1 restCoeffs.length restCoeffs.length
        [[headCoeff, qnfOne]] (ihsLayerDenote (ihgScalarMirrorLayer restCoeffs))
        (ihzScalarMirrorRowsAllWidth headCoeff)
        (ihsAllWidthCast (by rw [ihgScalarMirrorLayerDomArity restCoeffs,
          ihgScalarMirrorLayerCodArity restCoeffs])
          (ihsLayerDenoteWidth (ihgScalarMirrorLayer restCoeffs)))
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro firstDomVec hPack1 =>
            cases hPack1 with
            | intro secondDomVec hPack2 =>
                cases hPack2 with
                | intro firstCodVec hPack3 =>
                    cases hPack3 with
                    | intro secondCodVec hFacts =>
                        cases (ihzScalarMirrorSpec headCoeff firstDomVec firstCodVec).mp
                          hFacts.right.right.left with
                        | intro outputCoeff hScalar =>
                            have hTail := (ihgScalarMirrorLayerDenote restCoeffs
                              secondDomVec secondCodVec).mp hFacts.right.right.right
                            refine And.intro ?_ ?_
                            · rw [hFacts.right.left, ihqCatLength, hScalar.right]
                              show 1 + secondCodVec.length = restCoeffs.length + 1
                              rw [hTail.left, Nat.add_comm 1 restCoeffs.length]
                            · rw [hFacts.left, hFacts.right.left, hScalar.left,
                                hScalar.right, hTail.right]
                              show qnfMul outputCoeff headCoeff
                                  :: ihgPointwiseScale secondCodVec restCoeffs
                                = ihgPointwiseScale (ihqCat [outputCoeff] secondCodVec)
                                    (headCoeff :: restCoeffs)
                              rfl
      · intro hBoth
        cases codVec with
        | nil => exact nomatch hBoth.left
        | cons headOutput restOutputs =>
            have hRestLen : restOutputs.length = restCoeffs.length :=
              Nat.succ.inj hBoth.left
            refine Exists.intro [qnfMul headOutput headCoeff]
              (Exists.intro (ihgPointwiseScale restOutputs restCoeffs)
                (Exists.intro [headOutput] (Exists.intro restOutputs
                  (And.intro ?_ (And.intro rfl (And.intro ?_ ?_))))))
            · rw [hBoth.right]
              rfl
            · exact (ihzScalarMirrorSpec headCoeff [qnfMul headOutput headCoeff]
                [headOutput]).mpr
                (Exists.intro headOutput (And.intro rfl rfl))
            · exact (ihgScalarMirrorLayerDenote restCoeffs
                (ihgPointwiseScale restOutputs restCoeffs) restOutputs).mpr
                (And.intro hRestLen rfl)

/-- DECIDED (T1): the scalar-layer tensor constructor ships with the
arbitrary-width per-strand denotation theorems for both the `scalarBox` layer
(`ihgScalarLayerDenote`) and its mirror (`ihgScalarMirrorLayerDenote`). -/
def ihgHasScalarLayerTensor : Bool := true

/-! ## Stage 2 — the replicate/scale bridge and the two half-gadgets (T2) -/

theorem ihgPointwiseScaleReplicate (value : QnfRat) : (coefficients : List QnfRat) ->
    ihgPointwiseScale (ihcReplicate coefficients.length value) coefficients
      = ihqRowScale value coefficients
  | [] => rfl
  | headCoeff :: restCoeffs =>
      congrArg (fun tailPart => qnfMul value headCoeff :: tailPart)
        (ihgPointwiseScaleReplicate value restCoeffs)

/-- The `Collapse` half: per-input `scalarBoxMirror` layer then the mult fan,
`m -> 1`, forcing all mid strands equal to a single collapsed value. -/
def ihgCollapseDiagram (inputCoefficients : List QnfRat) : IhsDiagram :=
  { sourceArity := inputCoefficients.length,
    layers := ihgScalarMirrorLayer inputCoefficients
      :: ihcMultFanLayers inputCoefficients.length }

/-- The `Expand` half: the copy fan then a per-output `scalarBox` layer,
`1 -> n`, broadcasting a single value scaled per output strand. -/
def ihgExpandDiagram (outputCoefficients : List QnfRat) : IhsDiagram :=
  { sourceArity := 1,
    layers := ihsSnocLayers (ihcCopyFanLayers outputCoefficients.length)
      (ihgScalarLayer outputCoefficients) }

theorem ihgCollapseCodArity (inputCoefficients : List QnfRat) :
    ihsLayersCodArity inputCoefficients.length
        (ihgCollapseDiagram inputCoefficients).layers = 1 := by
  show ihsLayersCodArity (ihsLayerCodArity (ihgScalarMirrorLayer inputCoefficients))
      (ihcMultFanLayers inputCoefficients.length) = 1
  rw [ihgScalarMirrorLayerCodArity inputCoefficients,
    ihcMultFanCodArity inputCoefficients.length]

theorem ihgCollapseWF (inputCoefficients : List QnfRat) :
    IhsDiagramWF (ihgCollapseDiagram inputCoefficients) := by
  refine IhsLayersWF.cons (ihgScalarMirrorLayerDomArity inputCoefficients) ?_
  rw [ihgScalarMirrorLayerCodArity inputCoefficients]
  exact ihcMultFanWF inputCoefficients.length

theorem ihgCollapseCodArityDiagram (inputCoefficients : List QnfRat) :
    ihsDiagramCodArity (ihgCollapseDiagram inputCoefficients) = 1 :=
  ihgCollapseCodArity inputCoefficients

theorem ihgExpandCodArity (outputCoefficients : List QnfRat) :
    ihsLayersCodArity 1 (ihgExpandDiagram outputCoefficients).layers
      = outputCoefficients.length := by
  show ihsLayersCodArity 1
      (ihsSnocLayers (ihcCopyFanLayers outputCoefficients.length)
        (ihgScalarLayer outputCoefficients)) = outputCoefficients.length
  rw [ihsLayersCodAritySnoc (ihcCopyFanLayers outputCoefficients.length)
    (ihgScalarLayer outputCoefficients) 1, ihgScalarLayerCodArity outputCoefficients]

theorem ihgExpandWF (outputCoefficients : List QnfRat) :
    IhsDiagramWF (ihgExpandDiagram outputCoefficients) := by
  show IhsLayersWF 1 (ihsSnocLayers (ihcCopyFanLayers outputCoefficients.length)
    (ihgScalarLayer outputCoefficients))
  refine ihsLayersWFSnoc (ihcCopyFanLayers outputCoefficients.length)
    (ihgScalarLayer outputCoefficients) (ihcCopyFanWF outputCoefficients.length) ?_
  rw [ihgScalarLayerDomArity outputCoefficients,
    ihcCopyFanCodArity outputCoefficients.length]

theorem ihgExpandCodArityDiagram (outputCoefficients : List QnfRat) :
    ihsDiagramCodArity (ihgExpandDiagram outputCoefficients)
      = outputCoefficients.length :=
  ihgExpandCodArity outputCoefficients

theorem ihgCollapseAllWidth (inputCoefficients : List QnfRat) :
    IhqAllWidth (inputCoefficients.length + 1)
      (ihsDiagramDenote (ihgCollapseDiagram inputCoefficients)) :=
  ihsAllWidthCast
    (congrArg (fun boundaryArity => inputCoefficients.length + boundaryArity)
      (ihgCollapseCodArityDiagram inputCoefficients))
    (ihsDiagramDenoteWidth (ihgCollapseDiagram inputCoefficients)
      (ihgCollapseWF inputCoefficients))

theorem ihgExpandAllWidth (outputCoefficients : List QnfRat) :
    IhqAllWidth (1 + outputCoefficients.length)
      (ihsDiagramDenote (ihgExpandDiagram outputCoefficients)) :=
  ihsAllWidthCast
    (congrArg (fun boundaryArity => 1 + boundaryArity)
      (ihgExpandCodArityDiagram outputCoefficients))
    (ihsDiagramDenoteWidth (ihgExpandDiagram outputCoefficients)
      (ihgExpandWF outputCoefficients))

theorem ihgCollapseDenote (inputCoefficients : List QnfRat)
    (domVec midVec : List QnfRat) :
    IhqPairMem inputCoefficients.length 1
        (ihsDiagramDenote (ihgCollapseDiagram inputCoefficients)) domVec midVec
      <-> Exists fun through =>
            domVec = ihqRowScale through inputCoefficients /\ midVec = [through] := by
  have hMirrorAll : IhqAllWidth (inputCoefficients.length + inputCoefficients.length)
      (ihsLayerDenote (ihgScalarMirrorLayer inputCoefficients)) :=
    ihgScalarMirrorLayerAllWidth inputCoefficients
  have hMultAll : IhqAllWidth (inputCoefficients.length + 1)
      (ihsDiagramDenote (ihcMultFanDiagram inputCoefficients.length)) :=
    ihsAllWidthCast
      (congrArg (fun boundaryArity => inputCoefficients.length + boundaryArity)
        (ihcMultFanDiagramCodArity inputCoefficients.length))
      (ihsDiagramDenoteWidth (ihcMultFanDiagram inputCoefficients.length)
        (ihcMultFanDiagramWF inputCoefficients.length))
  have hDenoteEq : ihsDiagramDenote (ihgCollapseDiagram inputCoefficients)
      = ihqComposeRows inputCoefficients.length inputCoefficients.length 1
          (ihsLayerDenote (ihgScalarMirrorLayer inputCoefficients))
          (ihsDiagramDenote (ihcMultFanDiagram inputCoefficients.length)) := by
    show ihqComposeRows inputCoefficients.length
        (ihsLayerCodArity (ihgScalarMirrorLayer inputCoefficients))
        (ihsLayersCodArity (ihsLayerCodArity (ihgScalarMirrorLayer inputCoefficients))
          (ihcMultFanLayers inputCoefficients.length))
        (ihsLayerDenote (ihgScalarMirrorLayer inputCoefficients))
        (ihsLayersDenote (ihsLayerCodArity (ihgScalarMirrorLayer inputCoefficients))
          (ihcMultFanLayers inputCoefficients.length)) = _
    rw [ihgScalarMirrorLayerCodArity inputCoefficients,
      ihcMultFanCodArity inputCoefficients.length]
    rfl
  rw [hDenoteEq]
  refine Iff.trans (ihqComposeSpec inputCoefficients.length inputCoefficients.length 1
    (ihsLayerDenote (ihgScalarMirrorLayer inputCoefficients))
    (ihsDiagramDenote (ihcMultFanDiagram inputCoefficients.length))
    hMirrorAll hMultAll domVec midVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro innerMid hParts =>
        have hMirror := (ihgScalarMirrorLayerDenote inputCoefficients domVec innerMid).mp
          hParts.left
        cases (ihcMultFanDenote inputCoefficients.length innerMid midVec).mp
          hParts.right with
        | intro through hMult =>
            refine Exists.intro through (And.intro ?_ hMult.right)
            rw [hMirror.right, hMult.left]
            exact ihgPointwiseScaleReplicate through inputCoefficients
  · intro hExists
    cases hExists with
    | intro through hBoth =>
        refine Exists.intro (ihcReplicate inputCoefficients.length through)
          (And.intro ?_ ?_)
        · refine (ihgScalarMirrorLayerDenote inputCoefficients domVec
            (ihcReplicate inputCoefficients.length through)).mpr
            (And.intro (ihcReplicateLength through inputCoefficients.length) ?_)
          rw [hBoth.left]
          exact (ihgPointwiseScaleReplicate through inputCoefficients).symm
        · exact (ihcMultFanDenote inputCoefficients.length
            (ihcReplicate inputCoefficients.length through) midVec).mpr
            (Exists.intro through (And.intro rfl hBoth.right))

theorem ihgExpandDenote (outputCoefficients : List QnfRat)
    (midVec codVec : List QnfRat) :
    IhqPairMem 1 outputCoefficients.length
        (ihsDiagramDenote (ihgExpandDiagram outputCoefficients)) midVec codVec
      <-> Exists fun through =>
            midVec = [through] /\ codVec = ihqRowScale through outputCoefficients := by
  have hCopyAll : IhqAllWidth (1 + outputCoefficients.length)
      (ihsDiagramDenote (ihcCopyFanDiagram outputCoefficients.length)) :=
    ihsAllWidthCast
      (congrArg (fun boundaryArity => 1 + boundaryArity)
        (ihcCopyFanDiagramCodArity outputCoefficients.length))
      (ihsDiagramDenoteWidth (ihcCopyFanDiagram outputCoefficients.length)
        (ihcCopyFanDiagramWF outputCoefficients.length))
  have hScalarAll : IhqAllWidth (outputCoefficients.length + outputCoefficients.length)
      (ihsLayerDenote (ihgScalarLayer outputCoefficients)) :=
    ihgScalarLayerAllWidth outputCoefficients
  have hFit : ihsLayerDomArity (ihgScalarLayer outputCoefficients)
      = ihsLayersCodArity 1 (ihcCopyFanLayers outputCoefficients.length) := by
    rw [ihgScalarLayerDomArity outputCoefficients,
      ihcCopyFanCodArity outputCoefficients.length]
  have hSnoc := ihsLayersDenoteSnoc (ihcCopyFanLayers outputCoefficients.length)
    (ihgScalarLayer outputCoefficients) 1 (ihcCopyFanWF outputCoefficients.length) hFit
  rw [ihgScalarLayerCodArity outputCoefficients,
    ihcCopyFanCodArity outputCoefficients.length] at hSnoc
  refine Iff.trans (hSnoc midVec codVec) ?_
  refine Iff.trans (ihqComposeSpec 1 outputCoefficients.length
    outputCoefficients.length
    (ihsDiagramDenote (ihcCopyFanDiagram outputCoefficients.length))
    (ihsLayerDenote (ihgScalarLayer outputCoefficients))
    hCopyAll hScalarAll midVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro copyMid hParts =>
        cases (ihcCopyFanDenote outputCoefficients.length midVec copyMid).mp
          hParts.left with
        | intro through hCopy =>
            have hScalar := (ihgScalarLayerDenote outputCoefficients copyMid codVec).mp
              hParts.right
            refine Exists.intro through (And.intro hCopy.left ?_)
            rw [hScalar.right, hCopy.right]
            exact ihgPointwiseScaleReplicate through outputCoefficients
  · intro hExists
    cases hExists with
    | intro through hBoth =>
        refine Exists.intro (ihcReplicate outputCoefficients.length through)
          (And.intro ?_ ?_)
        · exact (ihcCopyFanDenote outputCoefficients.length midVec
            (ihcReplicate outputCoefficients.length through)).mpr
            (Exists.intro through (And.intro hBoth.left rfl))
        · refine (ihgScalarLayerDenote outputCoefficients
            (ihcReplicate outputCoefficients.length through) codVec).mpr
            (And.intro (ihcReplicateLength through outputCoefficients.length) ?_)
          rw [hBoth.right]
          exact (ihgPointwiseScaleReplicate through outputCoefficients).symm

/-! ## Stage 3 — the four-stage gadget and its denotation (T2) -/

/-- THE SINGLE-ROW GADGET: `Collapse ; Expand` of the Stage-7 route, a `m -> n`
diagram for one generator row `(inputs | outputs)`. -/
def ihgGadgetDiagram (inputCoefficients outputCoefficients : List QnfRat) :
    IhsDiagram :=
  { sourceArity := inputCoefficients.length,
    layers := ihwCatLayers (ihgCollapseDiagram inputCoefficients).layers
      (ihgExpandDiagram outputCoefficients).layers }

theorem ihgGadgetCodArity (inputCoefficients outputCoefficients : List QnfRat) :
    ihsDiagramCodArity (ihgGadgetDiagram inputCoefficients outputCoefficients)
      = outputCoefficients.length := by
  show ihsLayersCodArity inputCoefficients.length
      (ihwCatLayers (ihgCollapseDiagram inputCoefficients).layers
        (ihgExpandDiagram outputCoefficients).layers) = outputCoefficients.length
  rw [ihwLayersCodArityCat inputCoefficients.length
    (ihgCollapseDiagram inputCoefficients).layers
    (ihgExpandDiagram outputCoefficients).layers,
    ihgCollapseCodArity inputCoefficients, ihgExpandCodArity outputCoefficients]

theorem ihgGadgetWF (inputCoefficients outputCoefficients : List QnfRat) :
    IhsDiagramWF (ihgGadgetDiagram inputCoefficients outputCoefficients) := by
  refine ihwLayersWFCat (ihgCollapseDiagram inputCoefficients).layers
    (ihgExpandDiagram outputCoefficients).layers (ihgCollapseWF inputCoefficients) ?_
  exact ihsLayersWFCast (ihgCollapseCodArity inputCoefficients).symm
    (ihgExpandWF outputCoefficients)

/-- THE GADGET DENOTATION: the gadget for `(inputs | outputs)` spans the line
`{ (scale c inputs, scale c outputs) }`. -/
theorem ihgGadgetDenote (inputCoefficients outputCoefficients : List QnfRat)
    (domVec codVec : List QnfRat) :
    IhqPairMem inputCoefficients.length outputCoefficients.length
        (ihsDiagramDenote (ihgGadgetDiagram inputCoefficients outputCoefficients))
        domVec codVec
      <-> Exists fun scale =>
            domVec = ihqRowScale scale inputCoefficients
              /\ codVec = ihqRowScale scale outputCoefficients := by
  have hCat := @ihwLayersDenoteCat inputCoefficients.length
    (ihgCollapseDiagram inputCoefficients).layers
    (ihgExpandDiagram outputCoefficients).layers (ihgCollapseWF inputCoefficients)
    (ihsLayersWFCast (ihgCollapseCodArity inputCoefficients).symm
      (ihgExpandWF outputCoefficients))
  rw [ihgCollapseCodArity inputCoefficients, ihgExpandCodArity outputCoefficients]
    at hCat
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec inputCoefficients.length 1
    outputCoefficients.length
    (ihsDiagramDenote (ihgCollapseDiagram inputCoefficients))
    (ihsDiagramDenote (ihgExpandDiagram outputCoefficients))
    (ihgCollapseAllWidth inputCoefficients) (ihgExpandAllWidth outputCoefficients)
    domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (ihgCollapseDenote inputCoefficients domVec midVec).mp hParts.left with
        | intro firstScale hCollapse =>
            cases (ihgExpandDenote outputCoefficients midVec codVec).mp
              hParts.right with
            | intro secondScale hExpand =>
                have hScaleEq : firstScale = secondScale :=
                  ihzHeadOfSingletonEq (hCollapse.right.symm.trans hExpand.left)
                refine Exists.intro firstScale (And.intro hCollapse.left ?_)
                rw [hExpand.right, hScaleEq]
  · intro hExists
    cases hExists with
    | intro scale hBoth =>
        refine Exists.intro [scale] (And.intro ?_ ?_)
        · exact (ihgCollapseDenote inputCoefficients domVec [scale]).mpr
            (Exists.intro scale (And.intro hBoth.left rfl))
        · exact (ihgExpandDenote outputCoefficients [scale] codVec).mpr
            (Exists.intro scale (And.intro rfl hBoth.right))

/-- DECIDED (T2): the single-row `Collapse ; Expand` gadget ships with its
line-span denotation theorem `ihgGadgetDenote`, assembled zero-axiom through the
committed fan kit + `ihqComposeSpec`. -/
def ihgHasSingleRowGadget : Bool := true

/-! ## Stage 4 — the single-row NF carrier instance (T3) -/

/-- THE SINGLE-ROW NF CARRIER: the `rows = [row]` instance of
`ihzNormalFormStatement` — the gadget is a WF diagram at the row's boundary,
span-equal to the single-row matrix `[inputs ++ outputs]`. -/
theorem ihgSingleRowNormalForm (inputCoefficients outputCoefficients : List QnfRat) :
    Exists fun nfDiagram =>
      nfDiagram.sourceArity = inputCoefficients.length
        /\ ihsDiagramCodArity nfDiagram = outputCoefficients.length
        /\ IhsDiagramWF nfDiagram
        /\ IhsRelEquiv inputCoefficients.length outputCoefficients.length
            (ihsDiagramDenote nfDiagram)
            [ihqCat inputCoefficients outputCoefficients] := by
  refine Exists.intro (ihgGadgetDiagram inputCoefficients outputCoefficients)
    (And.intro rfl (And.intro (ihgGadgetCodArity inputCoefficients outputCoefficients)
      (And.intro (ihgGadgetWF inputCoefficients outputCoefficients) ?_)))
  intro domVec codVec
  have hRowLen : (ihqCat inputCoefficients outputCoefficients).length
      = inputCoefficients.length + outputCoefficients.length :=
    ihqCatLength inputCoefficients outputCoefficients
  refine Iff.trans (ihgGadgetDenote inputCoefficients outputCoefficients
    domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro scale hBoth =>
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [hBoth.left, ihqRowScaleLength]
        · rw [hBoth.right, ihqRowScaleLength]
        · rw [hBoth.left, hBoth.right,
            (ihqRowScaleCat scale inputCoefficients outputCoefficients).symm]
          exact ihzMemSpanSingleIntro (ihqCat inputCoefficients outputCoefficients)
            scale hRowLen
  · intro hPair
    cases ihzMemSpanSingleInv hRowLen hPair.right.right with
    | intro scale hVecEq =>
        rw [ihqRowScaleCat scale inputCoefficients outputCoefficients] at hVecEq
        have hSplit := ihqCatInj domVec codVec
          (ihqRowScale scale inputCoefficients)
          (ihqRowScale scale outputCoefficients)
          (by rw [hPair.left, (ihqRowScaleLength scale inputCoefficients).symm])
          hVecEq
        exact Exists.intro scale (And.intro hSplit.left hSplit.right)

/-! ## Stage 5 — kernel-decided span fires (the gadget at fresh rows) -/

set_option maxHeartbeats 4000000 in
/-- T1 fire: the width-2 scalar layer `[scalarBox 2, scalarBox (1/2)]` denotes
the componentwise-scaling matrix `[[1,0,2,0],[0,1,0,1/2]]`. -/
theorem ihgFireScalarLayerTwoHalf :
    ihqSpanEqB (ihsLayerDenote (ihgScalarLayer [ihsScalarTwo, ihzScalarHalf]))
      [[qnfOne, qnfZero, ihsScalarTwo, qnfZero],
        [qnfZero, qnfOne, qnfZero, ihzScalarHalf]] = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 fire (degenerate boundary `(1,1)`): the gadget for the row `[2, 1/2]`
span-equals the single-row matrix `[[2, 1/2]]`. -/
theorem ihgFireGadgetOneOne :
    ihqSpanEqB (ihsDiagramDenote (ihgGadgetDiagram [ihsScalarTwo] [ihzScalarHalf]))
      [[ihsScalarTwo, ihzScalarHalf]] = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 fire (`m = 2`, exercises the mult fan): the gadget for the row
`[2, 1/2 | 1]` span-equals `[[2, 1/2, 1]]`. -/
theorem ihgFireGadgetTwoOne :
    ihqSpanEqB (ihsDiagramDenote
        (ihgGadgetDiagram [ihsScalarTwo, ihzScalarHalf] [qnfOne]))
      [[ihsScalarTwo, ihzScalarHalf, qnfOne]] = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 fire (`n = 2`, exercises the copy fan): the gadget for the row
`[2 | 1, 3]` span-equals `[[2, 1, 3]]`. -/
theorem ihgFireGadgetOneTwo :
    ihqSpanEqB (ihsDiagramDenote
        (ihgGadgetDiagram [ihsScalarTwo] [qnfOne, ihsScalarThree]))
      [[ihsScalarTwo, qnfOne, ihsScalarThree]] = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 FALSE control: the gadget for `[2, 1/2]` is NOT the different line
`[[2, 1]]` (span decision refutes). -/
theorem ihgFireGadgetOneOneWrong :
    ihqSpanEqB (ihsDiagramDenote (ihgGadgetDiagram [ihsScalarTwo] [ihzScalarHalf]))
      [[ihsScalarTwo, qnfOne]] = false := rfl

/-! ## Stage 6 — the multi-row wall (T4) and markers -/

/-- WALL (T4) — OWNER FALSE, NOT PROVEN THIS BRICK.  The `R >= 2` NF carrier: a
two-row matrix `[in1 ++ out1, in2 ++ out2]` at a shared boundary is denoted by
SOME WF diagram.

BURNED ATTACK / precise residual: the single-row gadget factors through ONE
shared middle strand (`Collapse ; Expand`), so `span (row :: rest)` cannot reuse
it directly — the spatial sum `span (row :: rest) = span [row] + span rest`
reifies as `coadd-split ; (rowGadget X restDiagram) ; add-merge`, and routing the
copy-fan grid into the per-column add fans needs the GENERATOR-TRANSPOSE RIFFLE
permutation layer (built from `crossing` cells) plus its interleave denotation.
That riffle layer + denotation is the genuine remaining BUILD (the ZX-arc's
matrix-reification analogue); it is not shipped this brick.  Attacked twice: (a)
direct tensor of two single-row gadgets fails — the two `Collapse` middles are
disjoint, so the tensor denotes the direct SUM of two lines, not their span join;
(b) sharing a single copy fan across both rows needs the crossing riffle to
regroup outputs, which is the named obstruction. -/
def ihgTwoRowSpatialSumStatement : Prop :=
  (firstInputCoefficients firstOutputCoefficients
    secondInputCoefficients secondOutputCoefficients : List QnfRat) ->
    firstInputCoefficients.length = secondInputCoefficients.length ->
    firstOutputCoefficients.length = secondOutputCoefficients.length ->
    Exists fun sumDiagram =>
      sumDiagram.sourceArity = firstInputCoefficients.length
        /\ ihsDiagramCodArity sumDiagram = firstOutputCoefficients.length
        /\ IhsDiagramWF sumDiagram
        /\ IhsRelEquiv firstInputCoefficients.length firstOutputCoefficients.length
            (ihsDiagramDenote sumDiagram)
            [ihqCat firstInputCoefficients firstOutputCoefficients,
              ihqCat secondInputCoefficients secondOutputCoefficients]

/-- OWNER FALSE — the multi-row (`R >= 2`) generator-transpose riffle layer and
its denotation are NOT built this brick; `ihgTwoRowSpatialSumStatement` names the
precise residual.  The single-row gadget (`ihgHasSingleRowGadget`) and its NF
carrier instance (`ihgSingleRowNormalForm`) ARE shipped. -/
def ihgHasMultiRowRiffle : Bool := false

end FX1Poly.ComputerAlgebra
