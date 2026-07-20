import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfSchema

/-! # LinearAlgebra/InteractingHopfCompiler — the matrix -> diagram fan kit
(WP-PROP-3 brick 5)

Executing the brick-4 route note residual on `ihzNormalFormStatement`: the
copy/add fan kit that reifies generator rows into IH_Q diagrams.

* THE COPY FAN (`ihcCopyFan`, `1 -> copies`, a `blackComult` cascade): denotes
  the diagonal relation `[c] |-> replicate copies c`, proven at arbitrary width
  by structural recursion on the copy count (snoc one wire-padded `blackComult`
  per step).
* THE ADD FAN (`ihcAddFan`, `inputs -> 1`, a `whiteMult` cascade): denotes the
  sum relation `xs |-> [sum xs]`, proven at arbitrary width by structural
  recursion on the input count.

Each fan ships arity/WF lemmas, the arbitrary-width pair-membership denotation
theorem, and kernel `rfl` span fires at small widths.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfCompiler.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the diagonal and sum targets -/

/-- `copies`-fold repetition of one coefficient (the diagonal codomain vector). -/
def ihcReplicate : Nat -> QnfRat -> List QnfRat
  | 0, _value => []
  | count + 1, value => value :: ihcReplicate count value

theorem ihcReplicateLength (value : QnfRat) : (count : Nat) ->
    (ihcReplicate count value).length = count
  | 0 => rfl
  | count + 1 => congrArg (fun predLen => predLen + 1) (ihcReplicateLength value count)

/-- Left-folded sum of a coefficient list (the add-fan codomain scalar). -/
def ihcSum : List QnfRat -> QnfRat
  | [] => qnfZero
  | value :: rest => qnfAdd value (ihcSum rest)

/-! ## Stage 1 — the copy fan cell cascade -/

/-- The copy fan layer cascade `1 -> copies` (a `blackComult` tree, growing one
copy per snoc'd wire-padded `blackComult`). -/
def ihcCopyFanLayers : Nat -> List (List IhsCell)
  | 0 => [[IhsCell.blackCounit]]
  | 1 => []
  | copies + 2 =>
      ihsSnocLayers (ihcCopyFanLayers (copies + 1))
        (ihwCatCells (ihwWireCells copies) [IhsCell.blackComult])

/-- The copy fan diagram at output width `copies`. -/
def ihcCopyFanDiagram (copies : Nat) : IhsDiagram :=
  { sourceArity := 1, layers := ihcCopyFanLayers copies }

/-- The wire-padded `blackComult` that grows a copy fan by one strand. -/
def ihcCopyGrowLayer (keptWires : Nat) : List IhsCell :=
  ihwCatCells (ihwWireCells keptWires) [IhsCell.blackComult]

theorem ihcCopyGrowLayerDomArity (keptWires : Nat) :
    ihsLayerDomArity (ihcCopyGrowLayer keptWires) = keptWires + 1 := by
  show ihsLayerDomArity (ihwCatCells (ihwWireCells keptWires) [IhsCell.blackComult])
    = keptWires + 1
  rw [ihwCatCellsDomArity, ihwWireCellsDomArity]
  rfl

theorem ihcCopyGrowLayerCodArity (keptWires : Nat) :
    ihsLayerCodArity (ihcCopyGrowLayer keptWires) = keptWires + 2 := by
  show ihsLayerCodArity (ihwCatCells (ihwWireCells keptWires) [IhsCell.blackComult])
    = keptWires + 2
  rw [ihwCatCellsCodArity, ihwWireCellsCodArity]
  rfl

theorem ihcCopyFanCodArity : (copies : Nat) ->
    ihsLayersCodArity 1 (ihcCopyFanLayers copies) = copies
  | 0 => rfl
  | 1 => rfl
  | copies + 2 => by
      show ihsLayersCodArity 1
          (ihsSnocLayers (ihcCopyFanLayers (copies + 1)) (ihcCopyGrowLayer copies))
        = copies + 2
      rw [ihsLayersCodAritySnoc (ihcCopyFanLayers (copies + 1))
        (ihcCopyGrowLayer copies) 1, ihcCopyGrowLayerCodArity copies]

theorem ihcCopyFanWF : (copies : Nat) -> IhsLayersWF 1 (ihcCopyFanLayers copies)
  | 0 => IhsLayersWF.cons rfl (IhsLayersWF.nil 0)
  | 1 => IhsLayersWF.nil 1
  | copies + 2 => by
      show IhsLayersWF 1
        (ihsSnocLayers (ihcCopyFanLayers (copies + 1)) (ihcCopyGrowLayer copies))
      refine ihsLayersWFSnoc (ihcCopyFanLayers (copies + 1)) (ihcCopyGrowLayer copies)
        (ihcCopyFanWF (copies + 1)) ?_
      rw [ihcCopyGrowLayerDomArity copies, ihcCopyFanCodArity (copies + 1)]

theorem ihcCopyFanDiagramCodArity (copies : Nat) :
    ihsDiagramCodArity (ihcCopyFanDiagram copies) = copies :=
  ihcCopyFanCodArity copies

theorem ihcCopyFanDiagramWF (copies : Nat) : IhsDiagramWF (ihcCopyFanDiagram copies) :=
  ihcCopyFanWF copies

/-! ## Stage 2 — the add fan cell cascade -/

/-- The add fan layer cascade `inputs -> 1` (a `whiteMult` tree). -/
def ihcAddFanLayers : Nat -> List (List IhsCell)
  | 0 => [[IhsCell.whiteUnit]]
  | 1 => []
  | inputs + 2 =>
      ihwCatCells (ihwWireCells inputs) [IhsCell.whiteMult]
        :: ihcAddFanLayers (inputs + 1)

/-- The add fan diagram at input width `inputs`. -/
def ihcAddFanDiagram (inputs : Nat) : IhsDiagram :=
  { sourceArity := inputs, layers := ihcAddFanLayers inputs }

/-- The wire-padded `whiteMult` that shrinks an add fan by one strand. -/
def ihcAddShrinkLayer (keptWires : Nat) : List IhsCell :=
  ihwCatCells (ihwWireCells keptWires) [IhsCell.whiteMult]

theorem ihcAddShrinkLayerDomArity (keptWires : Nat) :
    ihsLayerDomArity (ihcAddShrinkLayer keptWires) = keptWires + 2 := by
  show ihsLayerDomArity (ihwCatCells (ihwWireCells keptWires) [IhsCell.whiteMult])
    = keptWires + 2
  rw [ihwCatCellsDomArity, ihwWireCellsDomArity]
  rfl

theorem ihcAddShrinkLayerCodArity (keptWires : Nat) :
    ihsLayerCodArity (ihcAddShrinkLayer keptWires) = keptWires + 1 := by
  show ihsLayerCodArity (ihwCatCells (ihwWireCells keptWires) [IhsCell.whiteMult])
    = keptWires + 1
  rw [ihwCatCellsCodArity, ihwWireCellsCodArity]
  rfl

theorem ihcAddFanCodArity : (inputs : Nat) ->
    ihsLayersCodArity inputs (ihcAddFanLayers inputs) = 1
  | 0 => rfl
  | 1 => rfl
  | inputs + 2 => by
      show ihsLayersCodArity (ihsLayerCodArity (ihcAddShrinkLayer inputs))
          (ihcAddFanLayers (inputs + 1))
        = 1
      rw [ihcAddShrinkLayerCodArity inputs, ihcAddFanCodArity (inputs + 1)]

theorem ihcAddFanWF : (inputs : Nat) -> IhsLayersWF inputs (ihcAddFanLayers inputs)
  | 0 => IhsLayersWF.cons rfl (IhsLayersWF.nil 1)
  | 1 => IhsLayersWF.nil 1
  | inputs + 2 => by
      show IhsLayersWF (inputs + 2)
        (ihcAddShrinkLayer inputs :: ihcAddFanLayers (inputs + 1))
      refine IhsLayersWF.cons (ihcAddShrinkLayerDomArity inputs) ?_
      rw [ihcAddShrinkLayerCodArity inputs]
      exact ihcAddFanWF (inputs + 1)

theorem ihcAddFanDiagramCodArity (inputs : Nat) :
    ihsDiagramCodArity (ihcAddFanDiagram inputs) = 1 :=
  ihcAddFanCodArity inputs

theorem ihcAddFanDiagramWF (inputs : Nat) : IhsDiagramWF (ihcAddFanDiagram inputs) :=
  ihcAddFanWF inputs

/-! ## Stage 3 — kernel `rfl` span fires validating the fan semantics

Each fan's denotation span-equals its target matrix by kernel decision at a
concrete width (the all-ones diagonal row for the copy fan; the `[I | ones]`
sum matrix for the add fan) — the semantic validation the general denotation
theorems below discharge at arbitrary width. -/

set_option maxHeartbeats 4000000 in
theorem ihcFireCopyFanDiscard :
    ihqSpanEqB (ihsDiagramDenote (ihcCopyFanDiagram 0)) [[qnfOne]] = true := rfl

set_option maxHeartbeats 4000000 in
theorem ihcFireCopyFanWire :
    ihqSpanEqB (ihsDiagramDenote (ihcCopyFanDiagram 1)) [[qnfOne, qnfOne]] = true := rfl

set_option maxHeartbeats 4000000 in
theorem ihcFireCopyFanTwo :
    ihqSpanEqB (ihsDiagramDenote (ihcCopyFanDiagram 2)) [[qnfOne, qnfOne, qnfOne]]
      = true := rfl

set_option maxHeartbeats 4000000 in
theorem ihcFireCopyFanThree :
    ihqSpanEqB (ihsDiagramDenote (ihcCopyFanDiagram 3))
      [[qnfOne, qnfOne, qnfOne, qnfOne]] = true := rfl

set_option maxHeartbeats 4000000 in
theorem ihcFireAddFanWire :
    ihqSpanEqB (ihsDiagramDenote (ihcAddFanDiagram 1)) [[qnfOne, qnfOne]] = true := rfl

set_option maxHeartbeats 4000000 in
theorem ihcFireAddFanTwo :
    ihqSpanEqB (ihsDiagramDenote (ihcAddFanDiagram 2))
      [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]] = true := rfl

/-! ## Stage 4 — the copy fan denotation (the diagonal, at arbitrary width)

`ihcCopyFanDenote`: the copy fan `1 -> copies` relates `[through]` to
`replicate copies through` (the diagonal), by structural recursion on the copy
count.  `ihcCopyGrowRel`/`ihcCopyGrowReplicate` characterize the wire-padded
`blackComult` growth layer via `ihwLayerDenoteCatSplit` + `ihwTensorSpec`. -/

theorem ihcReplicateSnoc (value : QnfRat) : (count : Nat) ->
    ihcReplicate (count + 1) value = ihqCat (ihcReplicate count value) [value]
  | 0 => rfl
  | count + 1 =>
      congrArg (fun tailPart => value :: tailPart) (ihcReplicateSnoc value count)

theorem ihcReplicateSnocTwo (value : QnfRat) : (count : Nat) ->
    ihcReplicate (count + 2) value = ihqCat (ihcReplicate count value) [value, value]
  | 0 => rfl
  | count + 1 =>
      congrArg (fun tailPart => value :: tailPart) (ihcReplicateSnocTwo value count)

-- copied from growprobe (already verified)
theorem ihcCopyGrowRel (keptWires : Nat) (domVec codVec : List QnfRat) :
    IhqPairMem (keptWires + 1) (keptWires + 2)
      (ihsLayerDenote (ihcCopyGrowLayer keptWires)) domVec codVec
    <-> Exists fun prefixVec => Exists fun through =>
          prefixVec.length = keptWires
            /\ domVec = ihqCat prefixVec [through]
            /\ codVec = ihqCat prefixVec [through, through] := by
  have hWireAll : IhqAllWidth (keptWires + keptWires)
      (ihsLayerDenote (ihwWireCells keptWires)) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells keptWires))
  have hCopyAll : IhqAllWidth (1 + 2) (ihsLayerDenote [IhsCell.blackComult]) :=
    ihsLayerDenoteWidth [IhsCell.blackComult]
  have hSplit := ihwLayerDenoteCatSplit (ihwWireCells keptWires) [IhsCell.blackComult]
  rw [ihwWireCellsDomArity keptWires, ihwWireCellsCodArity keptWires] at hSplit
  have hCong := ihwTensorRowsCong keptWires keptWires 1 2
    hWireAll (ihqIdRowsWidth keptWires) hCopyAll hCopyAll
    (ihwWireCellsDenoteId keptWires)
    (ihsRelEquivRefl 1 2 (ihsLayerDenote [IhsCell.blackComult]))
  have hEquiv := ihsRelEquivTrans hSplit hCong
  refine Iff.trans (hEquiv domVec codVec) ?_
  refine Iff.trans (ihwTensorSpec keptWires keptWires 1 2 (ihqIdRows keptWires)
    (ihsLayerDenote [IhsCell.blackComult]) (ihqIdRowsWidth keptWires) hCopyAll
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
                    have hIdSame := (ihsIdSpec keptWires firstDomVec firstCodVec).mp
                      hFacts.right.right.left
                    have hCopyMem : IhqPairMem 1 2 [[qnfOne, qnfOne, qnfOne]]
                        secondDomVec secondCodVec := hFacts.right.right.right
                    cases (ihzCopySpec secondDomVec secondCodVec).mp hCopyMem with
                    | intro through hCopyBoth =>
                        refine Exists.intro firstDomVec (Exists.intro through
                          (And.intro hIdSame.right (And.intro ?_ ?_)))
                        · rw [hFacts.left, hCopyBoth.left]
                        · rw [hFacts.right.left, hCopyBoth.right, hIdSame.left]
  · intro hExists
    cases hExists with
    | intro prefixVec hPack =>
        cases hPack with
        | intro through hFacts =>
            refine Exists.intro prefixVec (Exists.intro [through]
              (Exists.intro prefixVec (Exists.intro [through, through]
                (And.intro hFacts.right.left (And.intro hFacts.right.right
                  (And.intro ((ihsIdSpec keptWires prefixVec prefixVec).mpr
                    (And.intro rfl hFacts.left))
                    ((ihzCopySpec [through] [through, through]).mpr
                      (Exists.intro through (And.intro rfl rfl)))))))))

theorem ihcCopyGrowReplicate (keptWires : Nat) (value : QnfRat) (codVec : List QnfRat) :
    IhqPairMem (keptWires + 1) (keptWires + 2)
      (ihsLayerDenote (ihcCopyGrowLayer keptWires))
      (ihcReplicate (keptWires + 1) value) codVec
    <-> codVec = ihcReplicate (keptWires + 2) value := by
  refine Iff.trans (ihcCopyGrowRel keptWires (ihcReplicate (keptWires + 1) value) codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro prefixVec hPack =>
        cases hPack with
        | intro through hFacts =>
            have hSplit := ihqCatInj prefixVec [through] (ihcReplicate keptWires value)
              [value] (by rw [hFacts.left, ihcReplicateLength value keptWires])
              (by rw [<- hFacts.right.left, ihcReplicateSnoc value keptWires])
            have hThrough : through = value := ihzHeadOfSingletonEq hSplit.right
            rw [hFacts.right.right, hSplit.left, hThrough,
              <- ihcReplicateSnocTwo value keptWires]
  · intro hCod
    refine Exists.intro (ihcReplicate keptWires value) (Exists.intro value
      (And.intro (ihcReplicateLength value keptWires) (And.intro
        (ihcReplicateSnoc value keptWires) ?_)))
    rw [hCod, ihcReplicateSnocTwo value keptWires]

theorem ihcCopyFanDenote : (copies : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem 1 copies (ihsDiagramDenote (ihcCopyFanDiagram copies)) domVec codVec
    <-> Exists fun through =>
          domVec = [through] /\ codVec = ihcReplicate copies through)
  | 0, domVec, codVec => by
      have hAll0 : IhqAllWidth (1 + 0) (ihsLayerDenote [IhsCell.blackCounit]) :=
        ihsLayerDenoteWidth [IhsCell.blackCounit]
      have hEquiv0 : IhsRelEquiv 1 0 (ihsDiagramDenote (ihcCopyFanDiagram 0)) [[qnfOne]] :=
        ihsComposeIdRight 1 0 (ihsLayerDenote [IhsCell.blackCounit]) hAll0
      refine Iff.trans (hEquiv0 domVec codVec) ?_
      refine Iff.trans (ihzDiscardSpec domVec codVec) ?_
      exact Iff.rfl
  | 1, domVec, codVec => by
      refine Iff.trans (ihsIdSpec 1 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        cases ihzLengthOneShape domVec hSame.right with
        | intro through hDomEq =>
            refine Exists.intro through (And.intro hDomEq ?_)
            show codVec = [through]
            rw [<- hSame.left]
            exact hDomEq
      · intro hExists
        cases hExists with
        | intro through hBoth =>
            have hCodEq : codVec = [through] := hBoth.right
            have hDomEq : domVec = [through] := hBoth.left
            refine And.intro ?_ ?_
            · rw [hDomEq, hCodEq]
            · rw [hDomEq]
              rfl
  | copies + 2, domVec, codVec => by
      have hFit : ihsLayerDomArity (ihcCopyGrowLayer copies)
          = ihsLayersCodArity 1 (ihcCopyFanLayers (copies + 1)) := by
        rw [ihcCopyGrowLayerDomArity copies, ihcCopyFanCodArity (copies + 1)]
      have hSnoc := ihsLayersDenoteSnoc (ihcCopyFanLayers (copies + 1))
        (ihcCopyGrowLayer copies) 1 (ihcCopyFanWF (copies + 1)) hFit
      rw [ihcCopyGrowLayerCodArity copies, ihcCopyFanCodArity (copies + 1)] at hSnoc
      have hFanAll : IhqAllWidth (1 + (copies + 1))
          (ihsLayersDenote 1 (ihcCopyFanLayers (copies + 1))) :=
        ihsAllWidthCast (congrArg (fun boundaryArity => 1 + boundaryArity)
          (ihcCopyFanCodArity (copies + 1)))
          (ihsLayersDenoteWidth (ihcCopyFanLayers (copies + 1)) (ihcCopyFanWF (copies + 1)))
      have hGrowAll : IhqAllWidth ((copies + 1) + (copies + 2))
          (ihsLayerDenote (ihcCopyGrowLayer copies)) :=
        ihsAllWidthCast (by rw [ihcCopyGrowLayerDomArity copies,
          ihcCopyGrowLayerCodArity copies])
          (ihsLayerDenoteWidth (ihcCopyGrowLayer copies))
      refine Iff.trans (hSnoc domVec codVec) ?_
      refine Iff.trans (ihqComposeSpec 1 (copies + 1) (copies + 2)
        (ihsLayersDenote 1 (ihcCopyFanLayers (copies + 1)))
        (ihsLayerDenote (ihcCopyGrowLayer copies)) hFanAll hGrowAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro midVec hParts =>
            cases (ihcCopyFanDenote (copies + 1) domVec midVec).mp hParts.left with
            | intro through hFanBoth =>
                refine Exists.intro through (And.intro hFanBoth.left ?_)
                have hGrow : IhqPairMem (copies + 1) (copies + 2)
                    (ihsLayerDenote (ihcCopyGrowLayer copies))
                    (ihcReplicate (copies + 1) through) codVec := by
                  rw [<- hFanBoth.right]; exact hParts.right
                exact (ihcCopyGrowReplicate copies through codVec).mp hGrow
      · intro hExists
        cases hExists with
        | intro through hBoth =>
            refine Exists.intro (ihcReplicate (copies + 1) through) (And.intro ?_ ?_)
            · exact (ihcCopyFanDenote (copies + 1) domVec
                (ihcReplicate (copies + 1) through)).mpr
                (Exists.intro through (And.intro hBoth.left rfl))
            · have hGrow := (ihcCopyGrowReplicate copies through codVec).mpr hBoth.right
              exact hGrow

/-! ## Stage 5 — the add fan denotation (the sum, at arbitrary width)

`ihcAddFanDenote`: the add fan `inputs -> 1` relates `xs` to `[sum xs]`, by
structural recursion on the input count.  `ihcAddShrinkRel` characterizes the
wire-padded `whiteMult` shrink layer; `ihcSumCat` distributes `ihcSum` over
`ihqCat`; `ihcAddFanUncons` splits the trailing pair off the input vector. -/

theorem ihcSumCat : (firstVec secondVec : List QnfRat) ->
    ihcSum (ihqCat firstVec secondVec) = qnfAdd (ihcSum firstVec) (ihcSum secondVec)
  | [], secondVec => (qnfAddZeroLeft (ihcSum secondVec)).symm
  | headCoeff :: restCoeffs, secondVec => by
      show qnfAdd headCoeff (ihcSum (ihqCat restCoeffs secondVec))
        = qnfAdd (qnfAdd headCoeff (ihcSum restCoeffs)) (ihcSum secondVec)
      rw [ihcSumCat restCoeffs secondVec,
        qnfAddAssoc headCoeff (ihcSum restCoeffs) (ihcSum secondVec)]

theorem ihcAddShrinkRel (keptWires : Nat) (domVec midVec : List QnfRat) :
    IhqPairMem (keptWires + 2) (keptWires + 1)
      (ihsLayerDenote (ihcAddShrinkLayer keptWires)) domVec midVec
    <-> Exists fun prefixVec => Exists fun firstIn => Exists fun secondIn =>
          prefixVec.length = keptWires
            /\ domVec = ihqCat prefixVec [firstIn, secondIn]
            /\ midVec = ihqCat prefixVec [qnfAdd firstIn secondIn] := by
  have hWireAll : IhqAllWidth (keptWires + keptWires)
      (ihsLayerDenote (ihwWireCells keptWires)) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells keptWires))
  have hAddAll : IhqAllWidth (2 + 1) (ihsLayerDenote [IhsCell.whiteMult]) :=
    ihsLayerDenoteWidth [IhsCell.whiteMult]
  have hSplit := ihwLayerDenoteCatSplit (ihwWireCells keptWires) [IhsCell.whiteMult]
  rw [ihwWireCellsDomArity keptWires, ihwWireCellsCodArity keptWires] at hSplit
  have hCong := ihwTensorRowsCong keptWires keptWires 2 1
    hWireAll (ihqIdRowsWidth keptWires) hAddAll hAddAll
    (ihwWireCellsDenoteId keptWires)
    (ihsRelEquivRefl 2 1 (ihsLayerDenote [IhsCell.whiteMult]))
  have hEquiv := ihsRelEquivTrans hSplit hCong
  refine Iff.trans (hEquiv domVec midVec) ?_
  refine Iff.trans (ihwTensorSpec keptWires keptWires 2 1 (ihqIdRows keptWires)
    (ihsLayerDenote [IhsCell.whiteMult]) (ihqIdRowsWidth keptWires) hAddAll
    domVec midVec) ?_
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
                    have hIdSame := (ihsIdSpec keptWires firstDomVec firstCodVec).mp
                      hFacts.right.right.left
                    have hAddMem : IhqPairMem 2 1
                        [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
                        secondDomVec secondCodVec := hFacts.right.right.right
                    cases (ihzAddSpec secondDomVec secondCodVec).mp hAddMem with
                    | intro firstIn hRest =>
                        cases hRest with
                        | intro secondIn hAddBoth =>
                            refine Exists.intro firstDomVec (Exists.intro firstIn
                              (Exists.intro secondIn (And.intro hIdSame.right
                                (And.intro ?_ ?_))))
                            · rw [hFacts.left, hAddBoth.left]
                            · rw [hFacts.right.left, hAddBoth.right, hIdSame.left]
  · intro hExists
    cases hExists with
    | intro prefixVec hPack =>
        cases hPack with
        | intro firstIn hPack2 =>
            cases hPack2 with
            | intro secondIn hFacts =>
                refine Exists.intro prefixVec (Exists.intro [firstIn, secondIn]
                  (Exists.intro prefixVec (Exists.intro [qnfAdd firstIn secondIn]
                    (And.intro hFacts.right.left (And.intro hFacts.right.right
                      (And.intro ((ihsIdSpec keptWires prefixVec prefixVec).mpr
                        (And.intro rfl hFacts.left))
                        ((ihzAddSpec [firstIn, secondIn] [qnfAdd firstIn secondIn]).mpr
                          (Exists.intro firstIn (Exists.intro secondIn
                            (And.intro rfl rfl))))))))))

theorem ihcAddFanUncons (inputs : Nat) (domVec : List QnfRat)
    (hLen : domVec.length = inputs + 2) :
    Exists fun prefixVec => Exists fun firstIn => Exists fun secondIn =>
      prefixVec.length = inputs
        /\ domVec = ihqCat prefixVec [firstIn, secondIn] := by
  have hReassemble : ihqCat (ihqTakeN inputs domVec) (ihqDropN inputs domVec) = domVec :=
    ihqCatTakeDrop domVec inputs 2 hLen
  have hTakeLen : (ihqTakeN inputs domVec).length = inputs :=
    ihqTakeNLength domVec inputs 2 hLen
  have hDropLen : (ihqDropN inputs domVec).length = 2 :=
    ihqDropNLength domVec inputs 2 hLen
  cases ihzLengthTwoShape (ihqDropN inputs domVec) hDropLen with
  | intro firstIn hRest =>
      cases hRest with
      | intro secondIn hDropEq =>
          refine Exists.intro (ihqTakeN inputs domVec) (Exists.intro firstIn
            (Exists.intro secondIn (And.intro hTakeLen ?_)))
          exact hReassemble.symm.trans
            (congrArg (fun tailPart => ihqCat (ihqTakeN inputs domVec) tailPart) hDropEq)

theorem ihcAddFanDenote : (inputs : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem inputs 1 (ihsDiagramDenote (ihcAddFanDiagram inputs)) domVec codVec
    <-> domVec.length = inputs /\ codVec = [ihcSum domVec])
  | 0, domVec, codVec => by
      have hAll : IhqAllWidth (0 + 1) (ihsLayerDenote [IhsCell.whiteUnit]) :=
        ihsLayerDenoteWidth [IhsCell.whiteUnit]
      have hEquiv : IhsRelEquiv 0 1 (ihsDiagramDenote (ihcAddFanDiagram 0))
          (ihsLayerDenote [IhsCell.whiteUnit]) :=
        ihsComposeIdRight 0 1 (ihsLayerDenote [IhsCell.whiteUnit]) hAll
      refine Iff.trans (hEquiv domVec codVec) ?_
      refine Iff.trans (ihzNilRelationSpec 0 1 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hBoth
        have hDomNil : domVec = [] := hBoth.left
        refine And.intro ?_ ?_
        · rw [hDomNil]
          rfl
        · rw [hBoth.right, hDomNil]
          rfl
      · intro hBoth
        have hDomNil : domVec = [] := ihsLengthZeroNil domVec hBoth.left
        refine And.intro hDomNil ?_
        rw [hBoth.right, hDomNil]
        rfl
  | 1, domVec, codVec => by
      refine Iff.trans (ihsIdSpec 1 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        cases ihzLengthOneShape domVec hSame.right with
        | intro headCoeff hDomEq =>
            refine And.intro hSame.right ?_
            rw [<- hSame.left, hDomEq]
            show [headCoeff] = [qnfAdd headCoeff qnfZero]
            rw [qnfAddZeroRight]
      · intro hBoth
        cases ihzLengthOneShape domVec hBoth.left with
        | intro headCoeff hDomEq =>
            refine And.intro ?_ hBoth.left
            rw [hBoth.right, hDomEq]
            show [headCoeff] = [qnfAdd headCoeff qnfZero]
            rw [qnfAddZeroRight]
  | inputs + 2, domVec, codVec => by
      have hDenoteEq : ihsDiagramDenote (ihcAddFanDiagram (inputs + 2))
          = ihqComposeRows (inputs + 2) (inputs + 1) 1
              (ihsLayerDenote (ihcAddShrinkLayer inputs))
              (ihsLayersDenote (inputs + 1) (ihcAddFanLayers (inputs + 1))) := by
        show ihqComposeRows (inputs + 2) (ihsLayerCodArity (ihcAddShrinkLayer inputs))
            (ihsLayersCodArity (ihsLayerCodArity (ihcAddShrinkLayer inputs))
              (ihcAddFanLayers (inputs + 1)))
            (ihsLayerDenote (ihcAddShrinkLayer inputs))
            (ihsLayersDenote (ihsLayerCodArity (ihcAddShrinkLayer inputs))
              (ihcAddFanLayers (inputs + 1)))
          = ihqComposeRows (inputs + 2) (inputs + 1) 1
              (ihsLayerDenote (ihcAddShrinkLayer inputs))
              (ihsLayersDenote (inputs + 1) (ihcAddFanLayers (inputs + 1)))
        rw [ihcAddShrinkLayerCodArity inputs, ihcAddFanCodArity (inputs + 1)]
      have hShrinkAll : IhqAllWidth ((inputs + 2) + (inputs + 1))
          (ihsLayerDenote (ihcAddShrinkLayer inputs)) :=
        ihsAllWidthCast (by rw [ihcAddShrinkLayerDomArity inputs,
          ihcAddShrinkLayerCodArity inputs])
          (ihsLayerDenoteWidth (ihcAddShrinkLayer inputs))
      have hAddAll : IhqAllWidth ((inputs + 1) + 1)
          (ihsLayersDenote (inputs + 1) (ihcAddFanLayers (inputs + 1))) :=
        ihsAllWidthCast (congrArg (fun boundaryArity => (inputs + 1) + boundaryArity)
          (ihcAddFanCodArity (inputs + 1)))
          (ihsLayersDenoteWidth (ihcAddFanLayers (inputs + 1)) (ihcAddFanWF (inputs + 1)))
      rw [hDenoteEq]
      refine Iff.trans (ihqComposeSpec (inputs + 2) (inputs + 1) 1
        (ihsLayerDenote (ihcAddShrinkLayer inputs))
        (ihsLayersDenote (inputs + 1) (ihcAddFanLayers (inputs + 1)))
        hShrinkAll hAddAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro midVec hParts =>
            cases (ihcAddShrinkRel inputs domVec midVec).mp hParts.left with
            | intro prefixVec hPack =>
                cases hPack with
                | intro firstIn hPack2 =>
                    cases hPack2 with
                    | intro secondIn hFacts =>
                        have hAddTail := (ihcAddFanDenote (inputs + 1) midVec codVec).mp
                          hParts.right
                        refine And.intro ?_ ?_
                        · rw [hFacts.right.left, ihqCatLength]
                          show prefixVec.length + 2 = inputs + 2
                          rw [hFacts.left]
                        · rw [hAddTail.right, hFacts.right.right, hFacts.right.left,
                            ihcSumCat prefixVec [qnfAdd firstIn secondIn],
                            ihcSumCat prefixVec [firstIn, secondIn]]
                          show [qnfAdd (ihcSum prefixVec) (qnfAdd (qnfAdd firstIn secondIn) qnfZero)]
                            = [qnfAdd (ihcSum prefixVec)
                                (qnfAdd firstIn (qnfAdd secondIn qnfZero))]
                          rw [qnfAddZeroRight (qnfAdd firstIn secondIn),
                            qnfAddZeroRight secondIn]
      · intro hBoth
        cases ihcAddFanUncons inputs domVec hBoth.left with
        | intro prefixVec hPack =>
            cases hPack with
            | intro firstIn hPack2 =>
                cases hPack2 with
                | intro secondIn hDomEq =>
                    refine Exists.intro (ihqCat prefixVec [qnfAdd firstIn secondIn])
                      (And.intro ?_ ?_)
                    · exact (ihcAddShrinkRel inputs domVec
                        (ihqCat prefixVec [qnfAdd firstIn secondIn])).mpr
                        (Exists.intro prefixVec (Exists.intro firstIn (Exists.intro secondIn
                          (And.intro hDomEq.left (And.intro hDomEq.right rfl)))))
                    · refine (ihcAddFanDenote (inputs + 1)
                        (ihqCat prefixVec [qnfAdd firstIn secondIn]) codVec).mpr
                        (And.intro ?_ ?_)
                      · rw [ihqCatLength]
                        show prefixVec.length + 1 = inputs + 1
                        rw [hDomEq.left]
                      · rw [hBoth.right, hDomEq.right,
                          ihcSumCat prefixVec [qnfAdd firstIn secondIn],
                          ihcSumCat prefixVec [firstIn, secondIn]]
                        show [qnfAdd (ihcSum prefixVec)
                              (qnfAdd firstIn (qnfAdd secondIn qnfZero))]
                          = [qnfAdd (ihcSum prefixVec) (qnfAdd (qnfAdd firstIn secondIn) qnfZero)]
                        rw [qnfAddZeroRight (qnfAdd firstIn secondIn), qnfAddZeroRight secondIn]

/-! ## Stage 6 — the mult fan (cocopy, the copy converse)

`ihcMultFanDenote`: the mult fan `inputs -> 1` (a `blackMult` cascade) relates
`replicate inputs through` to `[through]` (all-equal collapse — the relational
converse of the copy fan), by structural recursion on the input count.  It is
the input-side "collapse" fan the brick-6 single-row gadget composes with the
copy fan's output-side "expand". -/

def ihcMultFanLayers : Nat -> List (List IhsCell)
  | 0 => [[IhsCell.blackUnit]]
  | 1 => []
  | inputs + 2 =>
      ihwCatCells (ihwWireCells inputs) [IhsCell.blackMult]
        :: ihcMultFanLayers (inputs + 1)

def ihcMultFanDiagram (inputs : Nat) : IhsDiagram :=
  { sourceArity := inputs, layers := ihcMultFanLayers inputs }

def ihcMultShrinkLayer (keptWires : Nat) : List IhsCell :=
  ihwCatCells (ihwWireCells keptWires) [IhsCell.blackMult]

theorem ihcMultShrinkLayerDomArity (keptWires : Nat) :
    ihsLayerDomArity (ihcMultShrinkLayer keptWires) = keptWires + 2 := by
  show ihsLayerDomArity (ihwCatCells (ihwWireCells keptWires) [IhsCell.blackMult])
    = keptWires + 2
  rw [ihwCatCellsDomArity, ihwWireCellsDomArity]
  rfl

theorem ihcMultShrinkLayerCodArity (keptWires : Nat) :
    ihsLayerCodArity (ihcMultShrinkLayer keptWires) = keptWires + 1 := by
  show ihsLayerCodArity (ihwCatCells (ihwWireCells keptWires) [IhsCell.blackMult])
    = keptWires + 1
  rw [ihwCatCellsCodArity, ihwWireCellsCodArity]
  rfl

theorem ihcMultFanCodArity : (inputs : Nat) ->
    ihsLayersCodArity inputs (ihcMultFanLayers inputs) = 1
  | 0 => rfl
  | 1 => rfl
  | inputs + 2 => by
      show ihsLayersCodArity (ihsLayerCodArity (ihcMultShrinkLayer inputs))
          (ihcMultFanLayers (inputs + 1))
        = 1
      rw [ihcMultShrinkLayerCodArity inputs, ihcMultFanCodArity (inputs + 1)]

theorem ihcMultFanWF : (inputs : Nat) -> IhsLayersWF inputs (ihcMultFanLayers inputs)
  | 0 => IhsLayersWF.cons rfl (IhsLayersWF.nil 1)
  | 1 => IhsLayersWF.nil 1
  | inputs + 2 => by
      show IhsLayersWF (inputs + 2)
        (ihcMultShrinkLayer inputs :: ihcMultFanLayers (inputs + 1))
      refine IhsLayersWF.cons (ihcMultShrinkLayerDomArity inputs) ?_
      rw [ihcMultShrinkLayerCodArity inputs]
      exact ihcMultFanWF (inputs + 1)

theorem ihcMultFanDiagramCodArity (inputs : Nat) :
    ihsDiagramCodArity (ihcMultFanDiagram inputs) = 1 :=
  ihcMultFanCodArity inputs

theorem ihcMultFanDiagramWF (inputs : Nat) : IhsDiagramWF (ihcMultFanDiagram inputs) :=
  ihcMultFanWF inputs

theorem ihcMultShrinkRel (keptWires : Nat) (domVec midVec : List QnfRat) :
    IhqPairMem (keptWires + 2) (keptWires + 1)
      (ihsLayerDenote (ihcMultShrinkLayer keptWires)) domVec midVec
    <-> Exists fun prefixVec => Exists fun through =>
          prefixVec.length = keptWires
            /\ domVec = ihqCat prefixVec [through, through]
            /\ midVec = ihqCat prefixVec [through] := by
  have hWireAll : IhqAllWidth (keptWires + keptWires)
      (ihsLayerDenote (ihwWireCells keptWires)) :=
    ihsAllWidthCast (by rw [ihwWireCellsDomArity, ihwWireCellsCodArity])
      (ihsLayerDenoteWidth (ihwWireCells keptWires))
  have hCocopyAll : IhqAllWidth (2 + 1) (ihsLayerDenote [IhsCell.blackMult]) :=
    ihsLayerDenoteWidth [IhsCell.blackMult]
  have hSplit := ihwLayerDenoteCatSplit (ihwWireCells keptWires) [IhsCell.blackMult]
  rw [ihwWireCellsDomArity keptWires, ihwWireCellsCodArity keptWires] at hSplit
  have hCong := ihwTensorRowsCong keptWires keptWires 2 1
    hWireAll (ihqIdRowsWidth keptWires) hCocopyAll hCocopyAll
    (ihwWireCellsDenoteId keptWires)
    (ihsRelEquivRefl 2 1 (ihsLayerDenote [IhsCell.blackMult]))
  have hEquiv := ihsRelEquivTrans hSplit hCong
  refine Iff.trans (hEquiv domVec midVec) ?_
  refine Iff.trans (ihwTensorSpec keptWires keptWires 2 1 (ihqIdRows keptWires)
    (ihsLayerDenote [IhsCell.blackMult]) (ihqIdRowsWidth keptWires) hCocopyAll
    domVec midVec) ?_
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
                    have hIdSame := (ihsIdSpec keptWires firstDomVec firstCodVec).mp
                      hFacts.right.right.left
                    have hCocopyMem : IhqPairMem 2 1 [[qnfOne, qnfOne, qnfOne]]
                        secondDomVec secondCodVec := hFacts.right.right.right
                    cases (ihzCocopySpec secondDomVec secondCodVec).mp hCocopyMem with
                    | intro through hCocopyBoth =>
                        refine Exists.intro firstDomVec (Exists.intro through
                          (And.intro hIdSame.right (And.intro ?_ ?_)))
                        · rw [hFacts.left, hCocopyBoth.left]
                        · rw [hFacts.right.left, hCocopyBoth.right, hIdSame.left]
  · intro hExists
    cases hExists with
    | intro prefixVec hPack =>
        cases hPack with
        | intro through hFacts =>
            refine Exists.intro prefixVec (Exists.intro [through, through]
              (Exists.intro prefixVec (Exists.intro [through]
                (And.intro hFacts.right.left (And.intro hFacts.right.right
                  (And.intro ((ihsIdSpec keptWires prefixVec prefixVec).mpr
                    (And.intro rfl hFacts.left))
                    ((ihzCocopySpec [through, through] [through]).mpr
                      (Exists.intro through (And.intro rfl rfl)))))))))

theorem ihcMultFanDenote : (inputs : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem inputs 1 (ihsDiagramDenote (ihcMultFanDiagram inputs)) domVec codVec
    <-> Exists fun through =>
          domVec = ihcReplicate inputs through /\ codVec = [through])
  | 0, domVec, codVec => by
      have hAll : IhqAllWidth (0 + 1) (ihsLayerDenote [IhsCell.blackUnit]) :=
        ihsLayerDenoteWidth [IhsCell.blackUnit]
      have hEquiv : IhsRelEquiv 0 1 (ihsDiagramDenote (ihcMultFanDiagram 0))
          (ihsLayerDenote [IhsCell.blackUnit]) :=
        ihsComposeIdRight 0 1 (ihsLayerDenote [IhsCell.blackUnit]) hAll
      refine Iff.trans (hEquiv domVec codVec) ?_
      refine Iff.trans (ihzBlackUnitSpec domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro outputCoeff hBoth =>
            exact Exists.intro outputCoeff (And.intro hBoth.left hBoth.right)
      · intro hExists
        cases hExists with
        | intro through hBoth =>
            exact Exists.intro through (And.intro hBoth.left hBoth.right)
  | 1, domVec, codVec => by
      refine Iff.trans (ihsIdSpec 1 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        cases ihzLengthOneShape domVec hSame.right with
        | intro through hDomEq =>
            refine Exists.intro through (And.intro hDomEq ?_)
            rw [<- hSame.left, hDomEq]
      · intro hExists
        cases hExists with
        | intro through hBoth =>
            have hDomEq : domVec = [through] := hBoth.left
            refine And.intro ?_ ?_
            · rw [hDomEq, hBoth.right]
            · rw [hDomEq]
              rfl
  | inputs + 2, domVec, codVec => by
      have hDenoteEq : ihsDiagramDenote (ihcMultFanDiagram (inputs + 2))
          = ihqComposeRows (inputs + 2) (inputs + 1) 1
              (ihsLayerDenote (ihcMultShrinkLayer inputs))
              (ihsLayersDenote (inputs + 1) (ihcMultFanLayers (inputs + 1))) := by
        show ihqComposeRows (inputs + 2) (ihsLayerCodArity (ihcMultShrinkLayer inputs))
            (ihsLayersCodArity (ihsLayerCodArity (ihcMultShrinkLayer inputs))
              (ihcMultFanLayers (inputs + 1)))
            (ihsLayerDenote (ihcMultShrinkLayer inputs))
            (ihsLayersDenote (ihsLayerCodArity (ihcMultShrinkLayer inputs))
              (ihcMultFanLayers (inputs + 1)))
          = ihqComposeRows (inputs + 2) (inputs + 1) 1
              (ihsLayerDenote (ihcMultShrinkLayer inputs))
              (ihsLayersDenote (inputs + 1) (ihcMultFanLayers (inputs + 1)))
        rw [ihcMultShrinkLayerCodArity inputs, ihcMultFanCodArity (inputs + 1)]
      have hShrinkAll : IhqAllWidth ((inputs + 2) + (inputs + 1))
          (ihsLayerDenote (ihcMultShrinkLayer inputs)) :=
        ihsAllWidthCast (by rw [ihcMultShrinkLayerDomArity inputs,
          ihcMultShrinkLayerCodArity inputs])
          (ihsLayerDenoteWidth (ihcMultShrinkLayer inputs))
      have hMultAll : IhqAllWidth ((inputs + 1) + 1)
          (ihsLayersDenote (inputs + 1) (ihcMultFanLayers (inputs + 1))) :=
        ihsAllWidthCast (congrArg (fun boundaryArity => (inputs + 1) + boundaryArity)
          (ihcMultFanCodArity (inputs + 1)))
          (ihsLayersDenoteWidth (ihcMultFanLayers (inputs + 1)) (ihcMultFanWF (inputs + 1)))
      rw [hDenoteEq]
      refine Iff.trans (ihqComposeSpec (inputs + 2) (inputs + 1) 1
        (ihsLayerDenote (ihcMultShrinkLayer inputs))
        (ihsLayersDenote (inputs + 1) (ihcMultFanLayers (inputs + 1)))
        hShrinkAll hMultAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro midVec hParts =>
            cases (ihcMultShrinkRel inputs domVec midVec).mp hParts.left with
            | intro prefixVec hPack =>
                cases hPack with
                | intro through hFacts =>
                    cases (ihcMultFanDenote (inputs + 1) midVec codVec).mp hParts.right with
                    | intro tailThrough hTailBoth =>
                        have hMidEq : ihqCat prefixVec [through]
                            = ihcReplicate (inputs + 1) tailThrough := by
                          rw [<- hFacts.right.right, hTailBoth.left]
                        have hSplit := ihqCatInj prefixVec [through]
                          (ihcReplicate inputs tailThrough) [tailThrough]
                          (by rw [hFacts.left, ihcReplicateLength tailThrough inputs])
                          (by rw [hMidEq, ihcReplicateSnoc tailThrough inputs])
                        have hThroughEq : through = tailThrough :=
                          ihzHeadOfSingletonEq hSplit.right
                        refine Exists.intro tailThrough (And.intro ?_ hTailBoth.right)
                        rw [hFacts.right.left, hSplit.left, hThroughEq,
                          <- ihcReplicateSnocTwo tailThrough inputs]
      · intro hExists
        cases hExists with
        | intro through hBoth =>
            refine Exists.intro (ihcReplicate (inputs + 1) through) (And.intro ?_ ?_)
            · exact (ihcMultShrinkRel inputs domVec
                (ihcReplicate (inputs + 1) through)).mpr
                (Exists.intro (ihcReplicate inputs through) (Exists.intro through
                  (And.intro (ihcReplicateLength through inputs)
                    (And.intro (by rw [hBoth.left, ihcReplicateSnocTwo through inputs])
                      (ihcReplicateSnoc through inputs)))))
            · exact (ihcMultFanDenote (inputs + 1)
                (ihcReplicate (inputs + 1) through) codVec).mpr
                (Exists.intro through (And.intro rfl hBoth.right))

set_option maxHeartbeats 4000000 in
theorem ihcFireMultFanUnit :
    ihqSpanEqB (ihsDiagramDenote (ihcMultFanDiagram 0)) [[qnfOne]] = true := rfl
set_option maxHeartbeats 4000000 in
theorem ihcFireMultFanTwo :
    ihqSpanEqB (ihsDiagramDenote (ihcMultFanDiagram 2)) [[qnfOne, qnfOne, qnfOne]] = true := rfl

/-! ## Stage 7 — the fan-kit marker and the brick-6 route to the NF compiler

`ihcHasFanKit := true` records the landed T1 deliverable: three fans (copy /
diagonal, add / sum, mult / cocopy) with arbitrary-width denotation theorems
and kernel fires, all zero-axiom.

THE HONEST WALL on `ihzNormalFormStatement` (owner-false in
`InteractingHopfSchema`, byte-intact): the full matrix -> diagram compiler is
NOT shipped this brick.  Precise residual for brick 6:

* THE ROW GADGET (single generator, `R = 1`).  A row `(a | b)` at boundary
  `(m, n)` spans the line `{(c * a, c * b)}`, reified as the pipeline
  `Collapse ; Expand` with a SINGLE shared middle strand and NO interleaving:
  `Collapse : m -> 1` = per-input `scalarBoxMirror a_j` layer then the mult fan
  (`ihcMultFanDiagram m`, forcing all `o_j` equal to `c`, so `x_j = c * a_j`);
  `Expand : 1 -> n` = the copy fan (`ihcCopyFanDiagram n`) then per-output
  `scalarBox b_k` layer (so `y_k = c * b_k`).  The two missing pieces are the
  scalar LAYER constructor (a horizontal tensor of `scalarBox`/`scalarBoxMirror`
  cells with its per-strand scaling denotation by induction, via
  `ihwLayerDenoteCatSplit` + `ihzScalarGraphSpec`/`ihzScalarMirrorSpec`) and the
  four-stage assembly denotation `= span [row]` (a `Collapse ; Expand`
  `ihqComposeSpec` chain).  All fan pieces this needs are shipped here.

* THE MULTI-ROW ASSEMBLY (`R >= 2`).  `span (row :: rest) = span [row] + rest`
  is the spatial sum of relations, which reifies as
  `coadd-split ; (rowGadget (X) restDiagram) ; add-merge` — the tensor of two
  sub-diagrams plus a GENERATOR-TRANSPOSE (riffle) permutation layer routing the
  copy-fan grid into the per-column add fans.  The riffle layer (built from
  `crossing` cells) and its denotation is the genuine remaining obstruction
  (the ZX-arc's matrix-reification analogue); it is a BUILD, not a wall of
  principle.  Census -> row gadget -> spatial sum is the brick-6 order. -/

/-- DECIDED (T1): the copy/add/mult fan kit ships with arbitrary-width
denotation theorems (`ihcCopyFanDenote`, `ihcAddFanDenote`, `ihcMultFanDenote`)
and kernel span fires, all zero-axiom. -/
def ihcHasFanKit : Bool := true

/-- OWNER FALSE — the full BSZ span-of-matrices matrix -> diagram compiler
(`ihzNormalFormStatement`) is NOT shipped this brick; only the fan kit is (see
the Stage-7 residual: single-row `Collapse ; Expand` scalar-layer assembly, then
the multi-row spatial sum with the generator-transpose riffle layer).  The
committed `ihzHasNormalFormCarrier := false` stays byte-intact. -/
def ihcHasNormalFormCompiler : Bool := false

end FX1Poly.ComputerAlgebra
