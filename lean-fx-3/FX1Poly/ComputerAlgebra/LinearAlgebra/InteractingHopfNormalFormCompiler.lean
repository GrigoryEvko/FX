import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfTwoRowSum

/-! # LinearAlgebra/InteractingHopfNormalFormCompiler — the general row-list normal
form compiler and the IH_Q word-problem decision (WP-PROP-3 brick 11)

Discharging the committed owner-false `ihzNormalFormStatement` (the full
span-of-matrices carrier) and closing the IH_Q word problem.  The brick-10 wall
`ihtHasNormalFormCompiler` named the precise residual: the general spatial sum of
a single-row gadget with an ARBITRARY well-formed sub-diagram, then the
`split ; unshuffle ; (gadget TENSOR subDiagram) ; shuffle ; merge` assembly and
the row-at-a-time accumulation.  This brick builds exactly that.

* THE GADGET-SUB-DIAGRAM TENSOR (T1, `ihxGadgetSubTensorDenote`): the brick-10
  `ihtGadgetTensorDenote` with the SECOND factor abstracted from a gadget line to
  an arbitrary well-formed window `subLayers`.  The block tensor
  `(gadget[inputs,outputs] TENSOR subLayers)` relates a domain `cat (a*inputs) subDom`
  to a codomain `cat (a*outputs) subCod` where `(subDom, subCod)` runs the
  sub-window's own relation.  Assembled through `ihtWhiskerRightSpec` +
  `ihgGadgetDenote` (first factor) and `ihuWhiskerLeftSpec` (second factor,
  abstract), tied by `ihqComposeSpec`.

* THE GENERAL ASSEMBLY (T2, `ihxGeneralAssemblyDenote`): mirror of `ihtAssemblyDenote`
  with the abstract second factor — `split ; unshuffle ; (gadget TENSOR subLayers) ;
  shuffle ; merge` denotes the MINKOWSKI SUM of the single row's line-span and the
  sub-window's relation: `dom = (a*inputs) + subDom`, `cod = (a*outputs) + subCod`.
  Threaded through the committed generic `ihtSplitLayerDenote`, `ihuUnshuffleDenote`,
  and `ihtShuffleMergeDenote` around the T1 middle.

* THE ROW-LIST RECURSION (T3, `ihxNormalFormCompiler`): structural recursion over
  the row list — base `ihzZeroRelationDiagram` (rows = []) / step T2 (row prepended
  to the recursively-built rest-diagram), routed by the cons Minkowski decomposition
  `ihxConsPairMem` (`span (row :: rest) = line[row] + span rest`).  INHABITS the
  committed owner-false `ihzNormalFormStatement`, superseding the
  `ihg`/`ihr`/`ihu`/`iht`/`ihz` owner-false markers (all left byte-intact).

* THE IH_Q DECISION (T4, `ihxDiagramWordProblem` / `ihxNormalFormWordProblem`):
  compose the NF compiler with the committed `ihqSpanEqB` span decision — two IH_Q
  diagrams present the same relation iff the executable span decision fires; and
  every relation reaches a normal-form diagram, so the diagram word problem is
  decidable.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfNormalFormCompiler.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the gadget-sub-diagram tensor layer list, its WF and cod arity -/

/-- THE GADGET-SUB-DIAGRAM TENSOR: the parallel composite of a single-row gadget
`(inputs -> outputs)` with an ARBITRARY window `subLayers`, whiskered into the
shared `(inputs.length + subDomWidth)` boundary.  The generalization of
`ihrGadgetTensorLayers` whose second factor is any well-formed sub-diagram. -/
def ihxGadgetSubLayers (inputs outputs : List QnfRat) (subDomWidth : Nat)
    (subLayers : List (List IhsCell)) : List (List IhsCell) :=
  ihwCatLayers
    (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
    (ihwWhiskerLayers outputs.length 0 subLayers)

/-- The right-whiskered gadget's cod arity at the clean boundary. -/
theorem ihxStageACodArity (inputs outputs : List QnfRat) (subDomWidth : Nat) :
    ihsLayersCodArity (inputs.length + subDomWidth)
        (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
      = outputs.length + subDomWidth := by
  have hGadgetCod : ihsLayersCodArity inputs.length
      (ihgGadgetDiagram inputs outputs).layers = outputs.length :=
    ihgGadgetCodArity inputs outputs
  have hRaw := ihwWhiskerLayersCodArity 0 subDomWidth
    (ihgGadgetDiagram inputs outputs).layers inputs.length
  rw [hGadgetCod, Nat.zero_add (inputs.length + subDomWidth),
    Nat.zero_add (outputs.length + subDomWidth)] at hRaw
  exact hRaw

/-- The gadget-sub-diagram tensor cod arity: `outputs.length + (sub cod)`. -/
theorem ihxGadgetSubTensorCodArity (inputs outputs : List QnfRat) (subDomWidth : Nat)
    (subLayers : List (List IhsCell)) :
    ihsLayersCodArity (inputs.length + subDomWidth)
        (ihxGadgetSubLayers inputs outputs subDomWidth subLayers)
      = outputs.length + ihsLayersCodArity subDomWidth subLayers := by
  show ihsLayersCodArity (inputs.length + subDomWidth)
      (ihwCatLayers
        (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
        (ihwWhiskerLayers outputs.length 0 subLayers))
    = outputs.length + ihsLayersCodArity subDomWidth subLayers
  rw [ihwLayersCodArityCat, ihxStageACodArity inputs outputs subDomWidth]
  exact ihwWhiskerLayersCodArity outputs.length 0 subLayers subDomWidth

/-- The gadget-sub-diagram tensor is well-formed at its natural boundary. -/
theorem ihxGadgetSubTensorWF (inputs outputs : List QnfRat) (subDomWidth : Nat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF subDomWidth subLayers) :
    IhsLayersWF (inputs.length + subDomWidth)
      (ihxGadgetSubLayers inputs outputs subDomWidth subLayers) := by
  show IhsLayersWF (inputs.length + subDomWidth)
    (ihwCatLayers
      (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
      (ihwWhiskerLayers outputs.length 0 subLayers))
  refine ihwLayersWFCat
    (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
    (ihwWhiskerLayers outputs.length 0 subLayers) ?_ ?_
  · exact ihsLayersWFCast (Nat.zero_add _) (ihwWhiskerLayersWF 0 subDomWidth
      (ihgGadgetDiagram inputs outputs).layers (ihgGadgetWF inputs outputs))
  · exact ihsLayersWFCast (ihxStageACodArity inputs outputs subDomWidth).symm
      (ihwWhiskerLayersWF outputs.length 0 subLayers hSubWF)

/-! ## Stage 1 — the gadget-sub-diagram tensor denotation (T1) -/

/-- THE GADGET-SUB-DIAGRAM TENSOR DENOTATION (T1): the block tensor of the single-row
gadget with the arbitrary window `subLayers` spans, per block, the gadget's line on
the front and the sub-window's relation on the back — the domain splits as
`(scale*inputs) ++ subDom` and the codomain as `(scale*outputs) ++ subCod`. -/
theorem ihxGadgetSubTensorDenote (inputs outputs : List QnfRat) (subDomWidth : Nat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF subDomWidth subLayers)
    (domVec codVec : List QnfRat) :
    IhqPairMem (inputs.length + subDomWidth)
        (outputs.length + ihsLayersCodArity subDomWidth subLayers)
        (ihsLayersDenote (inputs.length + subDomWidth)
          (ihxGadgetSubLayers inputs outputs subDomWidth subLayers))
        domVec codVec
      <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
            domVec = ihqCat (ihqRowScale scale inputs) subDom
              /\ codVec = ihqCat (ihqRowScale scale outputs) subCod
              /\ IhqPairMem subDomWidth (ihsLayersCodArity subDomWidth subLayers)
                  (ihsLayersDenote subDomWidth subLayers) subDom subCod := by
  have hGadget1WF : IhsLayersWF inputs.length (ihgGadgetDiagram inputs outputs).layers :=
    ihgGadgetWF inputs outputs
  have hGadget1Cod : ihsLayersCodArity inputs.length (ihgGadgetDiagram inputs outputs).layers
      = outputs.length := ihgGadgetCodArity inputs outputs
  have hStageAWF : IhsLayersWF (inputs.length + subDomWidth)
      (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers) :=
    ihsLayersWFCast (Nat.zero_add _) (ihwWhiskerLayersWF 0 subDomWidth
      (ihgGadgetDiagram inputs outputs).layers hGadget1WF)
  have hStageACod : ihsLayersCodArity (inputs.length + subDomWidth)
      (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
      = outputs.length + subDomWidth := ihxStageACodArity inputs outputs subDomWidth
  have hStageBWF : IhsLayersWF (ihsLayersCodArity (inputs.length + subDomWidth)
      (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
      (ihwWhiskerLayers outputs.length 0 subLayers) :=
    ihsLayersWFCast hStageACod.symm (ihwWhiskerLayersWF outputs.length 0 subLayers hSubWF)
  have hStageAAll := ihsLayersDenoteWidth
    (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers) hStageAWF
  have hStageBAll := ihsLayersDenoteWidth
    (ihwWhiskerLayers outputs.length 0 subLayers) hStageBWF
  have hCat := ihwLayersDenoteCat
    (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
    (ihwWhiskerLayers outputs.length 0 subLayers) hStageAWF hStageBWF
  -- stage A per-strand characterization (gadget on the front block)
  have hAEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (inputs.length + subDomWidth)
          (ihsLayersCodArity (inputs.length + subDomWidth)
            (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
          (ihsLayersDenote (inputs.length + subDomWidth)
            (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
          domVec midVec
        <-> Exists fun scale => Exists fun rightPart =>
              domVec = ihqCat (ihqRowScale scale inputs) rightPart
                /\ midVec = ihqCat (ihqRowScale scale outputs) rightPart
                /\ rightPart.length = subDomWidth) := by
    intro midVec
    have hMidEq : ihsLayersCodArity (inputs.length + subDomWidth)
        (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers)
        = ihsLayersCodArity inputs.length (ihgGadgetDiagram inputs outputs).layers
            + subDomWidth := by
      rw [hStageACod, hGadget1Cod]
    refine Iff.trans (ihwPairMemCast rfl hMidEq) ?_
    refine Iff.trans (ihtWhiskerRightSpec subDomWidth inputs.length
      (ihgGadgetDiagram inputs outputs).layers hGadget1WF domVec midVec) ?_
    refine Iff.intro ?_ ?_
    · intro hW
      cases hW with
      | intro innerDom hP1 =>
          cases hP1 with
          | intro innerCod hP2 =>
              cases hP2 with
              | intro rightPart hFacts =>
                  cases (ihgGadgetDenote inputs outputs innerDom innerCod).mp
                    ((ihwPairMemCast rfl hGadget1Cod).mp hFacts.right.right.right) with
                  | intro scale hGad =>
                      refine Exists.intro scale (Exists.intro rightPart
                        (And.intro ?_ (And.intro ?_ hFacts.right.right.left)))
                      · rw [hFacts.left, hGad.left]
                      · rw [hFacts.right.left, hGad.right]
    · intro hR
      cases hR with
      | intro scale hP1 =>
          cases hP1 with
          | intro rightPart hFacts =>
              refine Exists.intro (ihqRowScale scale inputs)
                (Exists.intro (ihqRowScale scale outputs) (Exists.intro rightPart
                  (And.intro hFacts.left (And.intro hFacts.right.left
                    (And.intro hFacts.right.right ?_)))))
              exact (ihwPairMemCast rfl hGadget1Cod.symm).mp
                ((ihgGadgetDenote inputs outputs (ihqRowScale scale inputs)
                    (ihqRowScale scale outputs)).mpr
                  (Exists.intro scale (And.intro rfl rfl)))
  -- stage B per-strand characterization (the abstract window on the back block)
  have hBEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (inputs.length + subDomWidth)
            (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
          (ihsLayersCodArity (ihsLayersCodArity (inputs.length + subDomWidth)
              (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
            (ihwWhiskerLayers outputs.length 0 subLayers))
          (ihsLayersDenote (ihsLayersCodArity (inputs.length + subDomWidth)
              (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
            (ihwWhiskerLayers outputs.length 0 subLayers))
          midVec codVec
        <-> Exists fun leftPart => Exists fun subDom => Exists fun subCod =>
              midVec = ihqCat leftPart subDom /\ codVec = ihqCat leftPart subCod
                /\ leftPart.length = outputs.length
                /\ IhqPairMem subDomWidth (ihsLayersCodArity subDomWidth subLayers)
                    (ihsLayersDenote subDomWidth subLayers) subDom subCod) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwWhiskerLayers outputs.length 0 subLayers)) hStageACod]
    have hBCodEq : ihsLayersCodArity (ihsLayersCodArity (inputs.length + subDomWidth)
          (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
        (ihwWhiskerLayers outputs.length 0 subLayers)
        = outputs.length + ihsLayersCodArity subDomWidth subLayers := by
      rw [hStageACod]
      exact ihwWhiskerLayersCodArity outputs.length 0 subLayers subDomWidth
    refine Iff.trans (ihwPairMemCast hStageACod hBCodEq) ?_
    exact ihuWhiskerLeftSpec outputs.length subDomWidth subLayers hSubWF midVec codVec
  -- assemble the two stages through the compose
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (inputs.length + subDomWidth)
        (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
      (ihwWhiskerLayers outputs.length 0 subLayers)
      = outputs.length + ihsLayersCodArity subDomWidth subLayers := by
    rw [hStageACod]
    exact ihwWhiskerLayersCodArity outputs.length 0 subLayers subDomWidth
  refine Iff.trans (ihwPairMemCast (domWidth2 := inputs.length + subDomWidth)
    rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (inputs.length + subDomWidth)
    (ihsLayersCodArity (inputs.length + subDomWidth)
      (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
    (ihsLayersCodArity (ihsLayersCodArity (inputs.length + subDomWidth)
        (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
      (ihwWhiskerLayers outputs.length 0 subLayers))
    (ihsLayersDenote (inputs.length + subDomWidth)
      (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
    (ihsLayersDenote (ihsLayersCodArity (inputs.length + subDomWidth)
        (ihwWhiskerLayers 0 subDomWidth (ihgGadgetDiagram inputs outputs).layers))
      (ihwWhiskerLayers outputs.length 0 subLayers))
    hStageAAll hStageBAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hAEquiv midVec).mp hParts.left with
        | intro scale hA1 =>
            cases hA1 with
            | intro rightPart hAFacts =>
                cases (hBEquiv midVec).mp hParts.right with
                | intro leftPart hB1 =>
                    cases hB1 with
                    | intro subDom hB2 =>
                        cases hB2 with
                        | intro subCod hBFacts =>
                            have hLen : (ihqRowScale scale outputs).length
                                = leftPart.length := by
                              rw [ihqRowScaleLength, hBFacts.right.right.left]
                            have hSplit := ihqCatInj (ihqRowScale scale outputs)
                              rightPart leftPart subDom hLen
                              (hAFacts.right.left.symm.trans hBFacts.left)
                            refine Exists.intro scale (Exists.intro subDom
                              (Exists.intro subCod (And.intro ?_ (And.intro ?_
                                hBFacts.right.right.right))))
                            · rw [hAFacts.left, hSplit.right]
                            · rw [hBFacts.right.left, hSplit.left]
  · intro hExists
    cases hExists with
    | intro scale hP1 =>
        cases hP1 with
        | intro subDom hP2 =>
            cases hP2 with
            | intro subCod hFacts =>
                refine Exists.intro (ihqCat (ihqRowScale scale outputs) subDom)
                  (And.intro ?_ ?_)
                · exact (hAEquiv (ihqCat (ihqRowScale scale outputs) subDom)).mpr
                    (Exists.intro scale (Exists.intro subDom
                      (And.intro hFacts.left (And.intro rfl hFacts.right.right.left))))
                · exact (hBEquiv (ihqCat (ihqRowScale scale outputs) subDom)).mpr
                    (Exists.intro (ihqRowScale scale outputs) (Exists.intro subDom
                      (Exists.intro subCod (And.intro rfl (And.intro hFacts.right.left
                        (And.intro (ihqRowScaleLength scale outputs) hFacts.right.right))))))

/-- DECIDED (T1): the gadget-sub-diagram tensor ships its blockwise line-and-relation
denotation, generalizing `ihtGadgetTensorDenote` in the second factor. -/
def ihxHasGadgetSubTensor : Bool := true

/-! ## Stage 2 — the general assembly denotation (T2)

The three-stage threading `(gadget-sub-tensor ; shuffle ; merge)`,
`(unshuffle ; that)`, `(split ; that)`, each folded at `subDomWidth = inputs.length`
and `sub cod = outputs.length`, mirroring `ihtGadgetShuffleMergeDenote` /
`ihtUnshuffleRestDenote` / `ihtAssemblyDenote` with the abstract second factor. -/

/-- The `(gadget-sub-tensor ; shuffle ; merge)` middle is well-formed at `2m`. -/
theorem ihxGadgetSubShuffleMergeWF (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF inputs.length subLayers)
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length) :
    IhsLayersWF (inputs.length + inputs.length)
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])) := by
  refine ihwLayersWFCat (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
    (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])
    (ihxGadgetSubTensorWF inputs outputs inputs.length subLayers hSubWF) ?_
  rw [ihxGadgetSubTensorCodArity inputs outputs inputs.length subLayers,
    (show outputs.length + ihsLayersCodArity inputs.length subLayers
      = outputs.length + outputs.length by rw [hSubCod])]
  exact ihtShuffleMergeWF outputs.length

/-- The `(gadget-sub-tensor ; shuffle ; merge)` middle cod arity: `2m -> n`. -/
theorem ihxGadgetSubShuffleMergeCodArity (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell))
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length) :
    ihsLayersCodArity (inputs.length + inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
      = outputs.length := by
  rw [ihwLayersCodArityCat,
    ihxGadgetSubTensorCodArity inputs outputs inputs.length subLayers,
    (show outputs.length + ihsLayersCodArity inputs.length subLayers
      = outputs.length + outputs.length by rw [hSubCod])]
  exact ihtShuffleMergeCodArity outputs.length

/-- The `(gadget-sub-tensor ; shuffle ; merge)` middle (`2m -> n`): block input
`cat (a*inputs) subDom` mapped to the pointwise sum `(a*outputs) + subCod`. -/
theorem ihxGadgetSubShuffleMergeDenote (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF inputs.length subLayers)
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length)
    (domVec codVec : List QnfRat) :
    IhqPairMem (inputs.length + inputs.length) outputs.length
        (ihsLayersDenote (inputs.length + inputs.length)
          (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
            (ihwCatLayers (ihrShuffle outputs.length)
              [ihrMergeLayer outputs.length]))) domVec codVec
      <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
            domVec = ihqCat (ihqRowScale scale inputs) subDom
              /\ codVec = ihqRowAdd (ihqRowScale scale outputs) subCod
              /\ IhqPairMem inputs.length outputs.length
                  (ihsLayersDenote inputs.length subLayers) subDom subCod := by
  have hGadgetWF : IhsLayersWF (inputs.length + inputs.length)
      (ihxGadgetSubLayers inputs outputs inputs.length subLayers) :=
    ihxGadgetSubTensorWF inputs outputs inputs.length subLayers hSubWF
  have hGadgetCod : ihsLayersCodArity (inputs.length + inputs.length)
      (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
      = outputs.length + ihsLayersCodArity inputs.length subLayers :=
    ihxGadgetSubTensorCodArity inputs outputs inputs.length subLayers
  have hTailArity : outputs.length + ihsLayersCodArity inputs.length subLayers
      = outputs.length + outputs.length := by rw [hSubCod]
  have hRest4WF : IhsLayersWF (ihsLayersCodArity (inputs.length + inputs.length)
      (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]) := by
    rw [hGadgetCod, hTailArity]
    exact ihtShuffleMergeWF outputs.length
  have hGadgetAll := ihsLayersDenoteWidth
    (ihxGadgetSubLayers inputs outputs inputs.length subLayers) hGadgetWF
  have hRest4All := ihsLayersDenoteWidth
    (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]) hRest4WF
  have hCat := ihwLayersDenoteCat
    (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
    (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])
    hGadgetWF hRest4WF
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (inputs.length + inputs.length)
        (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])
      = outputs.length := by
    rw [hGadgetCod, hTailArity]
    exact ihtShuffleMergeCodArity outputs.length
  -- gadget-sub-tensor factor (cod folded to n1+sub)
  have hGadgetEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (inputs.length + inputs.length)
          (ihsLayersCodArity (inputs.length + inputs.length)
            (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
          (ihsLayersDenote (inputs.length + inputs.length)
            (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
          domVec midVec
        <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
              domVec = ihqCat (ihqRowScale scale inputs) subDom
                /\ midVec = ihqCat (ihqRowScale scale outputs) subCod
                /\ IhqPairMem inputs.length outputs.length
                    (ihsLayersDenote inputs.length subLayers) subDom subCod) := by
    intro midVec
    refine Iff.trans (ihwPairMemCast rfl hGadgetCod) ?_
    refine Iff.trans (ihxGadgetSubTensorDenote inputs outputs inputs.length subLayers
      hSubWF domVec midVec) ?_
    refine Iff.intro ?_ ?_
    · intro hG
      cases hG with
      | intro scale hP1 =>
          cases hP1 with
          | intro subDom hP2 =>
              cases hP2 with
              | intro subCod hFacts =>
                  exact Exists.intro scale (Exists.intro subDom (Exists.intro subCod
                    (And.intro hFacts.left (And.intro hFacts.right.left
                      ((ihwPairMemCast rfl hSubCod).mp hFacts.right.right)))))
    · intro hG
      cases hG with
      | intro scale hP1 =>
          cases hP1 with
          | intro subDom hP2 =>
              cases hP2 with
              | intro subCod hFacts =>
                  exact Exists.intro scale (Exists.intro subDom (Exists.intro subCod
                    (And.intro hFacts.left (And.intro hFacts.right.left
                      ((ihwPairMemCast rfl hSubCod).mpr hFacts.right.right)))))
  -- shuffle;merge factor (dom folded to n1+n1, cod folded to n1)
  have hTailEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (inputs.length + inputs.length)
            (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
          (ihsLayersCodArity (ihsLayersCodArity (inputs.length + inputs.length)
              (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
            (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
          (ihsLayersDenote (ihsLayersCodArity (inputs.length + inputs.length)
              (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
            (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
          midVec codVec
        <-> Exists fun firstList => Exists fun secondList =>
              midVec = ihqCat firstList secondList
                /\ codVec = ihqRowAdd firstList secondList
                /\ firstList.length = outputs.length
                /\ secondList.length = outputs.length) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
      (hGadgetCod.trans hTailArity)]
    refine Iff.trans (ihwPairMemCast (hGadgetCod.trans hTailArity) hFinalCod) ?_
    exact ihtShuffleMergeDenote outputs.length midVec codVec
  refine Iff.trans (ihwPairMemCast (domWidth2 := inputs.length + inputs.length)
    rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (inputs.length + inputs.length)
    (ihsLayersCodArity (inputs.length + inputs.length)
      (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
    (ihsLayersCodArity (ihsLayersCodArity (inputs.length + inputs.length)
        (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
    (ihsLayersDenote (inputs.length + inputs.length)
      (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
    (ihsLayersDenote (ihsLayersCodArity (inputs.length + inputs.length)
        (ihxGadgetSubLayers inputs outputs inputs.length subLayers))
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
    hGadgetAll hRest4All domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hGadgetEquiv midVec).mp hParts.left with
        | intro scale hG1 =>
            cases hG1 with
            | intro subDom hG2 =>
                cases hG2 with
                | intro subCod hGFacts =>
                    cases (hTailEquiv midVec).mp hParts.right with
                    | intro firstList hT1 =>
                        cases hT1 with
                        | intro secondList hTFacts =>
                            have hLen : (ihqRowScale scale outputs).length
                                = firstList.length := by
                              rw [ihqRowScaleLength, hTFacts.right.right.left]
                            have hSplit := ihqCatInj (ihqRowScale scale outputs)
                              subCod firstList secondList hLen
                              (hGFacts.right.left.symm.trans hTFacts.left)
                            refine Exists.intro scale (Exists.intro subDom
                              (Exists.intro subCod (And.intro hGFacts.left
                                (And.intro ?_ hGFacts.right.right))))
                            rw [hTFacts.right.left, hSplit.left, hSplit.right]
  · intro hExists
    cases hExists with
    | intro scale hP1 =>
        cases hP1 with
        | intro subDom hP2 =>
            cases hP2 with
            | intro subCod hFacts =>
                refine Exists.intro (ihqCat (ihqRowScale scale outputs) subCod)
                  (And.intro ?_ ?_)
                · exact (hGadgetEquiv (ihqCat (ihqRowScale scale outputs) subCod)).mpr
                    (Exists.intro scale (Exists.intro subDom (Exists.intro subCod
                      (And.intro hFacts.left (And.intro rfl hFacts.right.right)))))
                · exact (hTailEquiv (ihqCat (ihqRowScale scale outputs) subCod)).mpr
                    (Exists.intro (ihqRowScale scale outputs) (Exists.intro subCod
                      (And.intro rfl (And.intro hFacts.right.left
                        (And.intro (ihqRowScaleLength scale outputs)
                          hFacts.right.right.right.left)))))

/-- The `(unshuffle ; gadget-sub-tensor ; shuffle ; merge)` prefix is WF at `2m`. -/
theorem ihxUnshuffleGadgetSubWF (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF inputs.length subLayers)
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length) :
    IhsLayersWF (inputs.length + inputs.length)
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length)
            [ihrMergeLayer outputs.length]))) := by
  refine ihwLayersWFCat (ihrUnshuffle inputs.length) _ (ihuUnshuffleWF inputs.length) ?_
  rw [ihuUnshuffleCodArity inputs.length]
  exact ihxGadgetSubShuffleMergeWF inputs outputs subLayers hSubWF hSubCod

/-- The `(unshuffle ; gadget-sub-tensor ; shuffle ; merge)` prefix cod: `2m -> n`. -/
theorem ihxUnshuffleGadgetSubCodArity (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell))
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length) :
    ihsLayersCodArity (inputs.length + inputs.length)
        (ihwCatLayers (ihrUnshuffle inputs.length)
          (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
            (ihwCatLayers (ihrShuffle outputs.length)
              [ihrMergeLayer outputs.length]))) = outputs.length := by
  rw [ihwLayersCodArityCat, ihuUnshuffleCodArity inputs.length]
  exact ihxGadgetSubShuffleMergeCodArity inputs outputs subLayers hSubCod

/-- The `(unshuffle ; gadget-sub-tensor ; shuffle ; merge)` prefix (`2m -> n`):
interleaved input `interleave (a*inputs) subDom` merged to `(a*outputs) + subCod`. -/
theorem ihxUnshuffleGadgetSubDenote (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF inputs.length subLayers)
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length)
    (domVec codVec : List QnfRat) :
    IhqPairMem (inputs.length + inputs.length) outputs.length
        (ihsLayersDenote (inputs.length + inputs.length)
          (ihwCatLayers (ihrUnshuffle inputs.length)
            (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
              (ihwCatLayers (ihrShuffle outputs.length)
                [ihrMergeLayer outputs.length])))) domVec codVec
      <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
            domVec = ihnInterleave (ihqRowScale scale inputs) subDom
              /\ codVec = ihqRowAdd (ihqRowScale scale outputs) subCod
              /\ IhqPairMem inputs.length outputs.length
                  (ihsLayersDenote inputs.length subLayers) subDom subCod := by
  have hUnshuffleWF : IhsLayersWF (inputs.length + inputs.length)
      (ihrUnshuffle inputs.length) := ihuUnshuffleWF inputs.length
  have hUnshuffleCod : ihsLayersCodArity (inputs.length + inputs.length)
      (ihrUnshuffle inputs.length) = inputs.length + inputs.length :=
    ihuUnshuffleCodArity inputs.length
  have hRest3WF : IhsLayersWF (ihsLayersCodArity (inputs.length + inputs.length)
      (ihrUnshuffle inputs.length))
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length)
          [ihrMergeLayer outputs.length])) := by
    rw [hUnshuffleCod]
    exact ihxGadgetSubShuffleMergeWF inputs outputs subLayers hSubWF hSubCod
  have hUnshuffleAll := ihsLayersDenoteWidth (ihrUnshuffle inputs.length) hUnshuffleWF
  have hRest3All := ihsLayersDenoteWidth
    (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
    hRest3WF
  have hCat := ihwLayersDenoteCat (ihrUnshuffle inputs.length)
    (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
      (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
    hUnshuffleWF hRest3WF
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (inputs.length + inputs.length)
        (ihrUnshuffle inputs.length))
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))
      = outputs.length := by
    rw [hUnshuffleCod]
    exact ihxGadgetSubShuffleMergeCodArity inputs outputs subLayers hSubCod
  have hUnshuffleEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (inputs.length + inputs.length)
          (ihsLayersCodArity (inputs.length + inputs.length) (ihrUnshuffle inputs.length))
          (ihsLayersDenote (inputs.length + inputs.length) (ihrUnshuffle inputs.length))
          domVec midVec
        <-> Exists fun pList => Exists fun qList =>
              domVec = ihnInterleave pList qList /\ midVec = ihqCat pList qList
                /\ pList.length = inputs.length /\ qList.length = inputs.length) := by
    intro midVec
    refine Iff.trans (ihwPairMemCast rfl hUnshuffleCod) ?_
    exact ihuUnshuffleDenote inputs.length domVec midVec
  have hRest3Equiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (inputs.length + inputs.length)
            (ihrUnshuffle inputs.length))
          (ihsLayersCodArity (ihsLayersCodArity (inputs.length + inputs.length)
              (ihrUnshuffle inputs.length))
            (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
              (ihwCatLayers (ihrShuffle outputs.length)
                [ihrMergeLayer outputs.length])))
          (ihsLayersDenote (ihsLayersCodArity (inputs.length + inputs.length)
              (ihrUnshuffle inputs.length))
            (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
              (ihwCatLayers (ihrShuffle outputs.length)
                [ihrMergeLayer outputs.length])))
          midVec codVec
        <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
              midVec = ihqCat (ihqRowScale scale inputs) subDom
                /\ codVec = ihqRowAdd (ihqRowScale scale outputs) subCod
                /\ IhqPairMem inputs.length outputs.length
                    (ihsLayersDenote inputs.length subLayers) subDom subCod) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])))
      hUnshuffleCod]
    refine Iff.trans (ihwPairMemCast hUnshuffleCod hFinalCod) ?_
    exact ihxGadgetSubShuffleMergeDenote inputs outputs subLayers hSubWF hSubCod midVec codVec
  refine Iff.trans (ihwPairMemCast (domWidth2 := inputs.length + inputs.length)
    rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (inputs.length + inputs.length)
    (ihsLayersCodArity (inputs.length + inputs.length) (ihrUnshuffle inputs.length))
    (ihsLayersCodArity (ihsLayersCodArity (inputs.length + inputs.length)
        (ihrUnshuffle inputs.length))
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])))
    (ihsLayersDenote (inputs.length + inputs.length) (ihrUnshuffle inputs.length))
    (ihsLayersDenote (ihsLayersCodArity (inputs.length + inputs.length)
        (ihrUnshuffle inputs.length))
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])))
    hUnshuffleAll hRest3All domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hUnshuffleEquiv midVec).mp hParts.left with
        | intro pList hU1 =>
            cases hU1 with
            | intro qList hUFacts =>
                cases (hRest3Equiv midVec).mp hParts.right with
                | intro scale hR1 =>
                    cases hR1 with
                    | intro subDom hR2 =>
                        cases hR2 with
                        | intro subCod hRFacts =>
                            have hLen : pList.length
                                = (ihqRowScale scale inputs).length := by
                              rw [ihqRowScaleLength]; exact hUFacts.right.right.left
                            have hSplit := ihqCatInj pList qList
                              (ihqRowScale scale inputs) subDom hLen
                              (hUFacts.right.left.symm.trans hRFacts.left)
                            refine Exists.intro scale (Exists.intro subDom
                              (Exists.intro subCod (And.intro ?_
                                (And.intro hRFacts.right.left hRFacts.right.right))))
                            rw [hUFacts.left, hSplit.left, hSplit.right]
  · intro hExists
    cases hExists with
    | intro scale hP1 =>
        cases hP1 with
        | intro subDom hP2 =>
            cases hP2 with
            | intro subCod hFacts =>
                refine Exists.intro (ihqCat (ihqRowScale scale inputs) subDom)
                  (And.intro ?_ ?_)
                · exact (hUnshuffleEquiv (ihqCat (ihqRowScale scale inputs) subDom)).mpr
                    (Exists.intro (ihqRowScale scale inputs) (Exists.intro subDom
                      (And.intro hFacts.left (And.intro rfl
                        (And.intro (ihqRowScaleLength scale inputs)
                          hFacts.right.right.left)))))
                · exact (hRest3Equiv (ihqCat (ihqRowScale scale inputs) subDom)).mpr
                    (Exists.intro scale (Exists.intro subDom (Exists.intro subCod
                      (And.intro rfl (And.intro hFacts.right.left hFacts.right.right)))))

/-- THE GENERAL ASSEMBLY DENOTATION (T2): `split ; unshuffle ;
(gadget TENSOR subLayers) ; shuffle ; merge` denotes the MINKOWSKI SUM of the
single row's line and the sub-window's relation — `dom = (a*inputs) + subDom`,
`cod = (a*outputs) + subCod`, with `(subDom, subCod)` running `subLayers`. -/
theorem ihxGeneralAssemblyDenote (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF inputs.length subLayers)
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length)
    (domVec codVec : List QnfRat) :
    IhqPairMem inputs.length outputs.length
        (ihsLayersDenote inputs.length
          (ihwCatLayers [ihrSplitLayer inputs.length]
            (ihwCatLayers (ihrUnshuffle inputs.length)
              (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
                (ihwCatLayers (ihrShuffle outputs.length)
                  [ihrMergeLayer outputs.length]))))) domVec codVec
      <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
            domVec = ihqRowAdd (ihqRowScale scale inputs) subDom
              /\ codVec = ihqRowAdd (ihqRowScale scale outputs) subCod
              /\ IhqPairMem inputs.length outputs.length
                  (ihsLayersDenote inputs.length subLayers) subDom subCod := by
  have hSplitWF : IhsLayersWF inputs.length [ihrSplitLayer inputs.length] :=
    IhsLayersWF.cons (ihtSplitLayerDomArity inputs.length) (IhsLayersWF.nil _)
  have hSplitCod : ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length]
      = inputs.length + inputs.length := ihtSplitLayerCodArity inputs.length
  have hRest2WF : IhsLayersWF (ihsLayersCodArity inputs.length
      [ihrSplitLayer inputs.length])
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length)
            [ihrMergeLayer outputs.length]))) := by
    rw [hSplitCod]
    exact ihxUnshuffleGadgetSubWF inputs outputs subLayers hSubWF hSubCod
  have hSplitAll := ihsLayersDenoteWidth [ihrSplitLayer inputs.length] hSplitWF
  have hRest2All := ihsLayersDenoteWidth
    (ihwCatLayers (ihrUnshuffle inputs.length)
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])))
    hRest2WF
  have hCat := ihwLayersDenoteCat [ihrSplitLayer inputs.length]
    (ihwCatLayers (ihrUnshuffle inputs.length)
      (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
        (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length])))
    hSplitWF hRest2WF
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity inputs.length
        [ihrSplitLayer inputs.length])
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length)
            [ihrMergeLayer outputs.length]))) = outputs.length := by
    rw [hSplitCod]
    exact ihxUnshuffleGadgetSubCodArity inputs outputs subLayers hSubCod
  have hSplitEquiv : (midVec : List QnfRat) ->
      (IhqPairMem inputs.length (ihsLayersCodArity inputs.length
          [ihrSplitLayer inputs.length])
          (ihsLayersDenote inputs.length [ihrSplitLayer inputs.length]) domVec midVec
        <-> Exists fun pList => Exists fun qList =>
              domVec = ihqRowAdd pList qList /\ midVec = ihnInterleave pList qList
                /\ pList.length = inputs.length /\ qList.length = inputs.length) := by
    intro midVec
    refine Iff.trans (ihuSingletonDenote (ihrSplitLayer inputs.length) inputs.length
      (ihtSplitLayerDomArity inputs.length) domVec midVec) ?_
    refine Iff.trans (ihwPairMemCast rfl (ihtSplitLayerCodArity inputs.length)) ?_
    exact ihtSplitLayerDenote inputs.length domVec midVec
  have hRest2Equiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length])
          (ihsLayersCodArity (ihsLayersCodArity inputs.length
              [ihrSplitLayer inputs.length])
            (ihwCatLayers (ihrUnshuffle inputs.length)
              (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
                (ihwCatLayers (ihrShuffle outputs.length)
                  [ihrMergeLayer outputs.length]))))
          (ihsLayersDenote (ihsLayersCodArity inputs.length
              [ihrSplitLayer inputs.length])
            (ihwCatLayers (ihrUnshuffle inputs.length)
              (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
                (ihwCatLayers (ihrShuffle outputs.length)
                  [ihrMergeLayer outputs.length]))))
          midVec codVec
        <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
              midVec = ihnInterleave (ihqRowScale scale inputs) subDom
                /\ codVec = ihqRowAdd (ihqRowScale scale outputs) subCod
                /\ IhqPairMem inputs.length outputs.length
                    (ihsLayersDenote inputs.length subLayers) subDom subCod) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))))
      hSplitCod]
    refine Iff.trans (ihwPairMemCast hSplitCod hFinalCod) ?_
    exact ihxUnshuffleGadgetSubDenote inputs outputs subLayers hSubWF hSubCod midVec codVec
  refine Iff.trans (ihwPairMemCast (domWidth2 := inputs.length) rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec inputs.length
    (ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length])
    (ihsLayersCodArity (ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length])
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))))
    (ihsLayersDenote inputs.length [ihrSplitLayer inputs.length])
    (ihsLayersDenote (ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length])
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length) [ihrMergeLayer outputs.length]))))
    hSplitAll hRest2All domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hSplitEquiv midVec).mp hParts.left with
        | intro pList hS1 =>
            cases hS1 with
            | intro qList hSFacts =>
                cases (hRest2Equiv midVec).mp hParts.right with
                | intro scale hR1 =>
                    cases hR1 with
                    | intro subDom hR2 =>
                        cases hR2 with
                        | intro subCod hRFacts =>
                            have hRec := ihtInterleaveInj inputs.length pList qList
                              (ihqRowScale scale inputs) subDom
                              hSFacts.right.right.left hSFacts.right.right.right
                              (ihqRowScaleLength scale inputs)
                              hRFacts.right.right.left
                              (hSFacts.right.left.symm.trans hRFacts.left)
                            refine Exists.intro scale (Exists.intro subDom
                              (Exists.intro subCod (And.intro ?_
                                (And.intro hRFacts.right.left hRFacts.right.right))))
                            rw [hSFacts.left, hRec.left, hRec.right]
  · intro hExists
    cases hExists with
    | intro scale hP1 =>
        cases hP1 with
        | intro subDom hP2 =>
            cases hP2 with
            | intro subCod hFacts =>
                refine Exists.intro (ihnInterleave (ihqRowScale scale inputs) subDom)
                  (And.intro ?_ ?_)
                · exact (hSplitEquiv (ihnInterleave (ihqRowScale scale inputs) subDom)).mpr
                    (Exists.intro (ihqRowScale scale inputs) (Exists.intro subDom
                      (And.intro hFacts.left (And.intro rfl
                        (And.intro (ihqRowScaleLength scale inputs)
                          hFacts.right.right.left)))))
                · exact (hRest2Equiv (ihnInterleave (ihqRowScale scale inputs) subDom)).mpr
                    (Exists.intro scale (Exists.intro subDom (Exists.intro subCod
                      (And.intro rfl (And.intro hFacts.right.left hFacts.right.right)))))

/-- DECIDED (T2): the general assembly ships the Minkowski sum of a single row's
line with an arbitrary sub-window relation. -/
def ihxHasGeneralAssembly : Bool := true

/-! ## Stage 3 — the row-list recursion and the NF compiler (T3) -/

/-- THE ROW-CONS DIAGRAM: `split ; unshuffle ; (gadget TENSOR subLayers) ;
shuffle ; merge` at boundary `(inputs.length, outputs.length)`, prepending the
head row's line onto the sub-diagram's relation. -/
def ihxRowConsDiagram (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) : IhsDiagram :=
  { sourceArity := inputs.length,
    layers :=
      ihwCatLayers [ihrSplitLayer inputs.length]
        (ihwCatLayers (ihrUnshuffle inputs.length)
          (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
            (ihwCatLayers (ihrShuffle outputs.length)
              [ihrMergeLayer outputs.length]))) }

/-- The row-cons diagram is well-formed at the shared boundary. -/
theorem ihxRowConsDiagramWF (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell)) (hSubWF : IhsLayersWF inputs.length subLayers)
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length) :
    IhsDiagramWF (ihxRowConsDiagram inputs outputs subLayers) := by
  show IhsLayersWF inputs.length
    (ihwCatLayers [ihrSplitLayer inputs.length]
      (ihwCatLayers (ihrUnshuffle inputs.length)
        (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
          (ihwCatLayers (ihrShuffle outputs.length)
            [ihrMergeLayer outputs.length]))))
  refine ihwLayersWFCat [ihrSplitLayer inputs.length] _ ?_ ?_
  · exact IhsLayersWF.cons (ihtSplitLayerDomArity inputs.length) (IhsLayersWF.nil _)
  · rw [(show ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length]
        = inputs.length + inputs.length from ihtSplitLayerCodArity inputs.length)]
    exact ihxUnshuffleGadgetSubWF inputs outputs subLayers hSubWF hSubCod

/-- The row-cons diagram maps `m -> n` at the shared boundary. -/
theorem ihxRowConsDiagramCodArity (inputs outputs : List QnfRat)
    (subLayers : List (List IhsCell))
    (hSubCod : ihsLayersCodArity inputs.length subLayers = outputs.length) :
    ihsDiagramCodArity (ihxRowConsDiagram inputs outputs subLayers) = outputs.length := by
  show ihsLayersCodArity inputs.length
      (ihwCatLayers [ihrSplitLayer inputs.length]
        (ihwCatLayers (ihrUnshuffle inputs.length)
          (ihwCatLayers (ihxGadgetSubLayers inputs outputs inputs.length subLayers)
            (ihwCatLayers (ihrShuffle outputs.length)
              [ihrMergeLayer outputs.length])))) = outputs.length
  rw [ihwLayersCodArityCat,
    (show ihsLayersCodArity inputs.length [ihrSplitLayer inputs.length]
      = inputs.length + inputs.length from ihtSplitLayerCodArity inputs.length)]
  exact ihxUnshuffleGadgetSubCodArity inputs outputs subLayers hSubCod

/-- THE CONS MINKOWSKI DECOMPOSITION: membership in `span (row :: rest)` splits as
one scalar multiple of the head row's line plus a point of `span rest`. -/
theorem ihxConsPairMem (domWidth codWidth : Nat) (inputs outputs row : List QnfRat)
    (rest : List (List QnfRat))
    (hInLen : inputs.length = domWidth) (hOutLen : outputs.length = codWidth)
    (hRowCat : ihqCat inputs outputs = row)
    (hRestAll : IhqAllWidth (domWidth + codWidth) rest)
    (domVec codVec : List QnfRat) :
    IhqPairMem domWidth codWidth (row :: rest) domVec codVec
      <-> Exists fun scale => Exists fun subDom => Exists fun subCod =>
            domVec = ihqRowAdd (ihqRowScale scale inputs) subDom
              /\ codVec = ihqRowAdd (ihqRowScale scale outputs) subCod
              /\ IhqPairMem domWidth codWidth rest subDom subCod := by
  subst hRowCat
  refine Iff.intro ?_ ?_
  · intro hPair
    cases ihqMemSpanConsInv hPair.right.right with
    | inl hInRest =>
        refine Exists.intro qnfZero (Exists.intro domVec (Exists.intro codVec
          (And.intro ?_ (And.intro ?_ ?_))))
        · rw [ihqRowScaleZeroScalar inputs, hInLen,
            ihqRowAddZeroLeft domVec domWidth hPair.left]
        · rw [ihqRowScaleZeroScalar outputs, hOutLen,
            ihqRowAddZeroLeft codVec codWidth hPair.right.left]
        · exact And.intro hPair.left (And.intro hPair.right.left hInRest)
    | inr hSplit =>
        cases hSplit with
        | intro scale hPack =>
            cases hPack with
            | intro partner hBoth =>
                have hPartnerLen : partner.length = domWidth + codWidth :=
                  ihqMemSpanWidth hRestAll hBoth.left
                have hSubDomLen : (ihqTakeN domWidth partner).length = domWidth :=
                  ihqTakeNLength partner domWidth codWidth hPartnerLen
                have hSubCodLen : (ihqDropN domWidth partner).length = codWidth :=
                  ihqDropNLength partner domWidth codWidth hPartnerLen
                have hPartnerCat : ihqCat (ihqTakeN domWidth partner)
                    (ihqDropN domWidth partner) = partner :=
                  ihqCatTakeDrop partner domWidth codWidth hPartnerLen
                have hCombined : ihqCat domVec codVec
                    = ihqCat (ihqRowAdd (ihqRowScale scale inputs)
                        (ihqTakeN domWidth partner))
                      (ihqRowAdd (ihqRowScale scale outputs)
                        (ihqDropN domWidth partner)) := by
                  rw [<- ihqRowAddCat (ihqRowScale scale inputs)
                      (ihqRowScale scale outputs) (ihqTakeN domWidth partner)
                      (ihqDropN domWidth partner)
                      (by rw [ihqRowScaleLength scale inputs, hInLen]; exact hSubDomLen.symm),
                    <- ihqRowScaleCat scale inputs outputs, hPartnerCat, hBoth.right]
                have hSplitVec := ihqCatInj domVec codVec
                  (ihqRowAdd (ihqRowScale scale inputs) (ihqTakeN domWidth partner))
                  (ihqRowAdd (ihqRowScale scale outputs) (ihqDropN domWidth partner))
                  (by rw [hPair.left]
                      exact (ihqRowAddLength (ihqRowScale scale inputs)
                        (ihqTakeN domWidth partner) domWidth
                        ((ihqRowScaleLength scale inputs).trans hInLen) hSubDomLen).symm)
                  hCombined
                refine Exists.intro scale (Exists.intro (ihqTakeN domWidth partner)
                  (Exists.intro (ihqDropN domWidth partner) (And.intro hSplitVec.left
                    (And.intro hSplitVec.right (And.intro hSubDomLen
                      (And.intro hSubCodLen ?_))))))
                rw [hPartnerCat]
                exact hBoth.left
  · intro hExists
    cases hExists with
    | intro scale hP1 =>
        cases hP1 with
        | intro subDom hP2 =>
            cases hP2 with
            | intro subCod hFacts =>
                have hSubDomLen : subDom.length = domWidth := hFacts.right.right.left
                have hSubCodLen : subCod.length = codWidth := hFacts.right.right.right.left
                have hPartnerMem := hFacts.right.right.right.right
                have hCatVec : ihqCat domVec codVec
                    = ihqRowAdd (ihqRowScale scale (ihqCat inputs outputs))
                        (ihqCat subDom subCod) := by
                  rw [hFacts.left, hFacts.right.left, ihqRowScaleCat scale inputs outputs,
                    ihqRowAddCat (ihqRowScale scale inputs) (ihqRowScale scale outputs)
                      subDom subCod
                      (by rw [ihqRowScaleLength scale inputs, hInLen]; exact hSubDomLen.symm)]
                refine And.intro ?_ (And.intro ?_ ?_)
                · rw [hFacts.left]
                  exact ihqRowAddLength (ihqRowScale scale inputs) subDom domWidth
                    ((ihqRowScaleLength scale inputs).trans hInLen) hSubDomLen
                · rw [hFacts.right.left]
                  exact ihqRowAddLength (ihqRowScale scale outputs) subCod codWidth
                    ((ihqRowScaleLength scale outputs).trans hOutLen) hSubCodLen
                · rw [hCatVec]
                  exact IhqMemSpan.pick scale (ihqCat inputs outputs)
                    (IhqRowMem.head (ihqCat inputs outputs) rest)
                    (ihqMemSpanWeaken (ihqCat inputs outputs) hPartnerMem)

/-- THE NORMAL-FORM CARRIER (the recursion): every generator matrix at every
boundary is denoted by SOME well-formed diagram — base `ihzZeroRelationDiagram`,
step the row-cons diagram over the recursively-built sub-diagram. -/
theorem ihxNormalFormCarrier (domWidth codWidth : Nat) :
    (rows : List (List QnfRat)) -> IhqAllWidth (domWidth + codWidth) rows ->
    Exists fun nfDiagram =>
      nfDiagram.sourceArity = domWidth
        /\ ihsDiagramCodArity nfDiagram = codWidth
        /\ IhsDiagramWF nfDiagram
        /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote nfDiagram) rows
  | [], _hAll =>
      Exists.intro (ihzZeroRelationDiagram domWidth codWidth)
        (And.intro rfl (And.intro (ihzZeroRelationDiagramCodArity domWidth codWidth)
          (And.intro (ihzZeroRelationDiagramWF domWidth codWidth)
            (ihzZeroRelationDiagramDenotesNil domWidth codWidth))))
  | row :: rest, hAll => by
      cases hAll with
      | cons hRowLen hRestAll =>
          have hInLen : (ihqTakeN domWidth row).length = domWidth :=
            ihqTakeNLength row domWidth codWidth hRowLen
          have hOutLen : (ihqDropN domWidth row).length = codWidth :=
            ihqDropNLength row domWidth codWidth hRowLen
          have hRowCat : ihqCat (ihqTakeN domWidth row) (ihqDropN domWidth row) = row :=
            ihqCatTakeDrop row domWidth codWidth hRowLen
          cases ihxNormalFormCarrier domWidth codWidth rest hRestAll with
          | intro restDiagram hRestProps =>
              have hArityEq : restDiagram.sourceArity = (ihqTakeN domWidth row).length :=
                hRestProps.left.trans hInLen.symm
              have hSubWF : IhsLayersWF (ihqTakeN domWidth row).length restDiagram.layers :=
                ihsLayersWFCast hArityEq hRestProps.right.right.left
              have hSubCod : ihsLayersCodArity (ihqTakeN domWidth row).length
                  restDiagram.layers = (ihqDropN domWidth row).length := by
                rw [<- hArityEq]
                show ihsDiagramCodArity restDiagram = (ihqDropN domWidth row).length
                rw [hRestProps.right.left]
                exact hOutLen.symm
              have hSubBridge : (sd sc : List QnfRat) ->
                  (IhqPairMem (ihqTakeN domWidth row).length (ihqDropN domWidth row).length
                      (ihsLayersDenote (ihqTakeN domWidth row).length restDiagram.layers)
                      sd sc
                    <-> IhqPairMem domWidth codWidth rest sd sc) := by
                intro sd sc
                refine Iff.trans (ihwPairMemCast hInLen hOutLen) ?_
                rw [show ihsLayersDenote (ihqTakeN domWidth row).length restDiagram.layers
                    = ihsDiagramDenote restDiagram from
                  congrArg (fun startArity => ihsLayersDenote startArity restDiagram.layers)
                    (hInLen.trans hRestProps.left.symm)]
                exact hRestProps.right.right.right sd sc
              refine Exists.intro (ihxRowConsDiagram (ihqTakeN domWidth row)
                (ihqDropN domWidth row) restDiagram.layers)
                (And.intro hInLen (And.intro ?_ (And.intro ?_ ?_)))
              · exact (ihxRowConsDiagramCodArity (ihqTakeN domWidth row)
                  (ihqDropN domWidth row) restDiagram.layers hSubCod).trans hOutLen
              · exact ihxRowConsDiagramWF (ihqTakeN domWidth row)
                  (ihqDropN domWidth row) restDiagram.layers hSubWF hSubCod
              · intro domVec codVec
                refine Iff.trans (ihwPairMemCast hInLen.symm hOutLen.symm) ?_
                refine Iff.trans (ihxGeneralAssemblyDenote (ihqTakeN domWidth row)
                  (ihqDropN domWidth row) restDiagram.layers hSubWF hSubCod
                  domVec codVec) ?_
                refine Iff.trans ?_ (ihxConsPairMem domWidth codWidth
                  (ihqTakeN domWidth row) (ihqDropN domWidth row) row rest
                  hInLen hOutLen hRowCat hRestAll domVec codVec).symm
                refine Iff.intro ?_ ?_
                · intro hM
                  cases hM with
                  | intro scale hP1 =>
                      cases hP1 with
                      | intro subDom hP2 =>
                          cases hP2 with
                          | intro subCod hFacts =>
                              exact Exists.intro scale (Exists.intro subDom
                                (Exists.intro subCod (And.intro hFacts.left
                                  (And.intro hFacts.right.left
                                    ((hSubBridge subDom subCod).mp hFacts.right.right)))))
                · intro hM
                  cases hM with
                  | intro scale hP1 =>
                      cases hP1 with
                      | intro subDom hP2 =>
                          cases hP2 with
                          | intro subCod hFacts =>
                              exact Exists.intro scale (Exists.intro subDom
                                (Exists.intro subCod (And.intro hFacts.left
                                  (And.intro hFacts.right.left
                                    ((hSubBridge subDom subCod).mpr hFacts.right.right)))))

/-- DECIDED (T3): the committed owner-false `ihzNormalFormStatement` is INHABITED —
every generator matrix at every boundary is denoted by SOME well-formed diagram,
by structural recursion over the row list.  Supersedes the owner-false markers
`ihtHasNormalFormCompiler`, `ihgHasMultiRowRiffle`, `ihzHasNormalFormCarrier`
(all left byte-intact). -/
theorem ihxNormalFormCompiler : ihzNormalFormStatement := ihxNormalFormCarrier

/-- DECIDED (T3): the general `R`-row normal-form compiler ships. -/
def ihxHasNormalFormCompiler : Bool := true

/-! ## Stage 4 — the IH_Q word-problem decision (T4) -/

/-- THE SPAN DECISION (matrix side): two relations at the same boundary present
the same relation iff the executable `ihqSpanEqB` decision fires. -/
theorem ihxSpanDecision (domWidth codWidth : Nat) (rowsA rowsB : List (List QnfRat))
    (hRowsA : IhqAllWidth (domWidth + codWidth) rowsA)
    (hRowsB : IhqAllWidth (domWidth + codWidth) rowsB) :
    IhsRelEquiv domWidth codWidth rowsA rowsB <-> ihqSpanEqB rowsA rowsB = true :=
  Iff.intro
    (fun hEquiv => ihsSpanEqBOfRelEquiv hRowsA hRowsB hEquiv)
    (fun hDecide => ihsRelEquivOfSpanEqB hRowsA hRowsB hDecide)

/-- THE DIAGRAM WORD PROBLEM: two well-formed diagrams at matching boundary present
the same relation iff `ihqSpanEqB` on their denotation matrices fires. -/
theorem ihxDiagramWordProblem (firstDiagram secondDiagram : IhsDiagram)
    (hFirstWF : IhsDiagramWF firstDiagram) (hSecondWF : IhsDiagramWF secondDiagram)
    (hSource : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCod : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram) :
    IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
        (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram)
      <-> ihqSpanEqB (ihsDiagramDenote firstDiagram)
            (ihsDiagramDenote secondDiagram) = true := by
  have hFirstAll := ihsDiagramDenoteWidth firstDiagram hFirstWF
  have hSecondAll : IhqAllWidth
      (firstDiagram.sourceArity + ihsDiagramCodArity firstDiagram)
      (ihsDiagramDenote secondDiagram) := by
    rw [hSource, hCod]
    exact ihsDiagramDenoteWidth secondDiagram hSecondWF
  exact Iff.intro
    (fun hEquiv => ihsSpanEqBOfRelEquiv hFirstAll hSecondAll hEquiv)
    (fun hDecide => ihsRelEquivOfSpanEqB hFirstAll hSecondAll hDecide)

/-- THE IH_Q WORD-PROBLEM DECISION (headline, composing the NF compiler with
`ihqSpanEqB`): every pair of relations compiles to normal-form diagrams, and the
two NF diagrams present the same relation iff the span decision fires on the
original matrices. -/
theorem ihxNormalFormWordProblem (domWidth codWidth : Nat)
    (rowsA rowsB : List (List QnfRat))
    (hRowsA : IhqAllWidth (domWidth + codWidth) rowsA)
    (hRowsB : IhqAllWidth (domWidth + codWidth) rowsB) :
    Exists fun firstNf => Exists fun secondNf =>
      (firstNf.sourceArity = domWidth /\ ihsDiagramCodArity firstNf = codWidth
        /\ IhsDiagramWF firstNf
        /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote firstNf) rowsA)
      /\ (secondNf.sourceArity = domWidth /\ ihsDiagramCodArity secondNf = codWidth
        /\ IhsDiagramWF secondNf
        /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote secondNf) rowsB)
      /\ (IhsRelEquiv domWidth codWidth (ihsDiagramDenote firstNf)
            (ihsDiagramDenote secondNf) <-> ihqSpanEqB rowsA rowsB = true) := by
  cases ihxNormalFormCompiler domWidth codWidth rowsA hRowsA with
  | intro firstNf hFirst =>
      cases ihxNormalFormCompiler domWidth codWidth rowsB hRowsB with
      | intro secondNf hSecond =>
          refine Exists.intro firstNf (Exists.intro secondNf
            (And.intro hFirst (And.intro hSecond ?_)))
          refine Iff.intro ?_ ?_
          · intro hEquiv
            have hRowsEquiv : IhsRelEquiv domWidth codWidth rowsA rowsB :=
              ihsRelEquivTrans (ihsRelEquivSymm hFirst.right.right.right)
                (ihsRelEquivTrans hEquiv hSecond.right.right.right)
            exact (ihxSpanDecision domWidth codWidth rowsA rowsB hRowsA hRowsB).mp
              hRowsEquiv
          · intro hDecide
            have hRowsEquiv : IhsRelEquiv domWidth codWidth rowsA rowsB :=
              (ihxSpanDecision domWidth codWidth rowsA rowsB hRowsA hRowsB).mpr hDecide
            exact ihsRelEquivTrans hFirst.right.right.right
              (ihsRelEquivTrans hRowsEquiv (ihsRelEquivSymm hSecond.right.right.right))

/-- DECIDED (T4): the IH_Q word problem is decided — the NF compiler composed with
`ihqSpanEqB` closes span-equality of diagrams. -/
def ihxHasWordProblemDecision : Bool := true

/-! ## Stage 5 — the committed statement inhabited VERBATIM and kernel fires -/

/-- VERBATIM: the committed owner-false `ihzNormalFormStatement` is inhabited. -/
theorem ihxNormalFormStatementVerbatim : ihzNormalFormStatement := ihxNormalFormCompiler

/-- T3 fire (existence): the NF compiler RUNS on a fresh 3-row matrix
`[[1,2],[1,1],[3,1]]` (boundary `(1,1)`), producing a WF diagram span-equal to it. -/
theorem ihxFireNFCompilerRunsThreeRow :
    Exists fun nfDiagram =>
      nfDiagram.sourceArity = 1
        /\ ihsDiagramCodArity nfDiagram = 1
        /\ IhsDiagramWF nfDiagram
        /\ IhsRelEquiv 1 1 (ihsDiagramDenote nfDiagram)
            [[qnfOne, ihsScalarTwo], [qnfOne, qnfOne], [ihsScalarThree, qnfOne]] :=
  ihxNormalFormCompiler 1 1
    [[qnfOne, ihsScalarTwo], [qnfOne, qnfOne], [ihsScalarThree, qnfOne]]
    (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)))

/-- The concrete two-row normal-form diagram for `[[1,2],[3,1]]` (boundary `(1,1)`):
the row-cons of `[1|2]` onto the row-cons of `[3|1]` onto the zero diagram. -/
def ihxFireNFTwoRowDiagram : IhsDiagram :=
  ihxRowConsDiagram [qnfOne] [ihsScalarTwo]
    (ihxRowConsDiagram [ihsScalarThree] [qnfOne]
      (ihzZeroRelationDiagram 1 1).layers).layers

set_option maxHeartbeats 8000000 in
/-- T3 fire (kernel span decide): the two-row NF diagram span-equals `[[1,2],[3,1]]`. -/
theorem ihxFireNFTwoRowSpan :
    ihqSpanEqB (ihsDiagramDenote ihxFireNFTwoRowDiagram)
      [[qnfOne, ihsScalarTwo], [ihsScalarThree, qnfOne]] = true := rfl

set_option maxHeartbeats 8000000 in
/-- T3 FALSE control: the two-row NF diagram (full rank, all of `Q^2`) is NOT the
rank-deficient single line `[[1,0]]` (span decision refutes). -/
theorem ihxFireNFTwoRowSpanWrong :
    ihqSpanEqB (ihsDiagramDenote ihxFireNFTwoRowDiagram)
      [[qnfOne, qnfZero]] = false := rfl

/-- T4 fire (fresh EQUAL pair, boundary `(1,1)`): `[[1,1],[1,2]]` and the identity
`[[1,0],[0,1]]` span the same relation (both are all of `Q^2`). -/
theorem ihxFireDecisionEqual :
    ihqSpanEqB [[qnfOne, qnfOne], [qnfOne, ihsScalarTwo]]
      [[qnfOne, qnfZero], [qnfZero, qnfOne]] = true := rfl

/-- T4 fire (fresh UNEQUAL pair, FALSE control): the line `[[1,1]]` is NOT the line
`[[1,0]]` (span decision refutes). -/
theorem ihxFireDecisionUnequal :
    ihqSpanEqB [[qnfOne, qnfOne]] [[qnfOne, qnfZero]] = false := rfl

/-- T4 CONTENT fire (routes through `ihxSpanDecision.mpr`, not a span `rfl`): the
fresh equal pair yields an honest `IhsRelEquiv` at boundary `(1,1)`. -/
theorem ihxFireDecisionContent :
    IhsRelEquiv 1 1 [[qnfOne, qnfOne], [qnfOne, ihsScalarTwo]]
      [[qnfOne, qnfZero], [qnfZero, qnfOne]] :=
  (ihxSpanDecision 1 1 [[qnfOne, qnfOne], [qnfOne, ihsScalarTwo]]
      [[qnfOne, qnfZero], [qnfZero, qnfOne]]
      (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil))
      (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil))).mpr rfl

end FX1Poly.ComputerAlgebra
