import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfShuffleDenote

/-! # LinearAlgebra/InteractingHopfTwoRowSum — the split/merge fan denotations, the
gadget tensor, and the two-row spatial sum (WP-PROP-3 brick 10)

Discharging the committed owner-false `ihgTwoRowSpatialSumStatement` by assembling
the five-stage Minkowski sum `split ; unshuffle ; (gadget TENSOR gadget) ; shuffle
; merge`.  The brick-9 residual named exactly what remained: (1) the two per-strand
fan denotations, (2) the gadget-tensor denotation, (3) the five-stage compose.

* THE SPLIT FAN (T1, `ihtSplitLayerDenote`): the per-strand `whiteComult` coadd
  layer `m -> 2m` relates a domain vector `pList + qList` (pointwise) to the
  interleaved codomain layout `ihnInterleave pList qList`, by structural recursion
  on the strand count in the shape of `ihgScalarLayerDenote` via `ihwTensorSpec` +
  `ihzCoaddSpec`.

* THE MERGE FAN (T1, `ihtMergeLayerDenote`): the per-strand `whiteMult` add layer
  `2n -> n` relates the interleaved domain layout `ihnInterleave` to the pointwise
  sum, mirror of the split via `ihzAddSpec`.

* THE GADGET TENSOR (T2, `ihtGadgetTensorDenote`): the blockwise parallel composite
  `(gadget1 TENSOR gadget2)` spans, per block, each single-row gadget's line —
  `(dom, cod) <-> exists a b, dom = a*in1 ++ b*in2 / cod = a*out1 ++ b*out2`,
  assembled through `ihwWhiskerLayersDenote` + `ihgGadgetDenote` + `ihqComposeSpec`.

* THE FIVE-STAGE COMPOSE (T3, `ihtTwoRowSpatialSum`): the committed
  `ihgTwoRowSpatialSumStatement`, inhabited VERBATIM.  The Minkowski
  characterization `(dom, cod) <-> exists a b, dom = a*in1 + b*in2 /
  cod = a*out1 + b*out2` routed to `IhqPairMem` of the two-row matrix.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfTwoRowSum.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the split / merge fan arities -/

theorem ihtSplitLayerDomArity : (strandCount : Nat) ->
    ihsLayerDomArity (ihrSplitLayer strandCount) = strandCount
  | 0 => rfl
  | strandCount + 1 => by
      show 1 + ihsLayerDomArity (ihrSplitLayer strandCount) = strandCount + 1
      rw [ihtSplitLayerDomArity strandCount, Nat.add_comm 1 strandCount]

theorem ihtSplitLayerCodArity : (strandCount : Nat) ->
    ihsLayerCodArity (ihrSplitLayer strandCount) = strandCount + strandCount
  | 0 => rfl
  | strandCount + 1 => by
      show 2 + ihsLayerCodArity (ihrSplitLayer strandCount)
        = (strandCount + 1) + (strandCount + 1)
      rw [ihtSplitLayerCodArity strandCount]
      exact (ihuWidthCanon strandCount).symm

theorem ihtMergeLayerDomArity : (strandCount : Nat) ->
    ihsLayerDomArity (ihrMergeLayer strandCount) = strandCount + strandCount
  | 0 => rfl
  | strandCount + 1 => by
      show 2 + ihsLayerDomArity (ihrMergeLayer strandCount)
        = (strandCount + 1) + (strandCount + 1)
      rw [ihtMergeLayerDomArity strandCount]
      exact (ihuWidthCanon strandCount).symm

theorem ihtMergeLayerCodArity : (strandCount : Nat) ->
    ihsLayerCodArity (ihrMergeLayer strandCount) = strandCount
  | 0 => rfl
  | strandCount + 1 => by
      show 1 + ihsLayerCodArity (ihrMergeLayer strandCount) = strandCount + 1
      rw [ihtMergeLayerCodArity strandCount, Nat.add_comm 1 strandCount]

/-! ## Stage 1 — the per-strand split / merge fan denotations (T1) -/

/-- THE SPLIT FAN DENOTATION: `ihrSplitLayer m` (per-strand `whiteComult`, `m -> 2m`)
relates the pointwise sum `pList + qList` to the interleaved layout
`ihnInterleave pList qList`. -/
theorem ihtSplitLayerDenote : (strandCount : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem strandCount (strandCount + strandCount)
        (ihsLayerDenote (ihrSplitLayer strandCount)) domVec codVec
      <-> Exists fun pList => Exists fun qList =>
            domVec = ihqRowAdd pList qList
              /\ codVec = ihnInterleave pList qList
              /\ pList.length = strandCount
              /\ qList.length = strandCount)
  | 0, domVec, codVec => by
      refine Iff.trans (ihzNilRelationSpec 0 0 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hBoth
        refine Exists.intro [] (Exists.intro []
          (And.intro ?_ (And.intro ?_ (And.intro rfl rfl))))
        · rw [hBoth.left]
          rfl
        · rw [hBoth.right]
          rfl
      · intro hSpec
        cases hSpec with
        | intro pList hRest =>
            cases hRest with
            | intro qList hFacts =>
                have hPnil : pList = [] := ihsLengthZeroNil pList hFacts.right.right.left
                have hQnil : qList = [] := ihsLengthZeroNil qList hFacts.right.right.right
                refine And.intro ?_ ?_
                · rw [hFacts.left, hPnil, hQnil]
                  rfl
                · rw [hFacts.right.left, hPnil, hQnil]
                  rfl
  | strandCount + 1, domVec, codVec => by
      have hDenote : ihsLayerDenote (ihrSplitLayer (strandCount + 1))
          = ihsTensorRows 1 2 strandCount (strandCount + strandCount)
              [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
              (ihsLayerDenote (ihrSplitLayer strandCount)) := by
        show ihsTensorRows 1 2 (ihsLayerDomArity (ihrSplitLayer strandCount))
            (ihsLayerCodArity (ihrSplitLayer strandCount))
            [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
            (ihsLayerDenote (ihrSplitLayer strandCount)) = _
        rw [ihtSplitLayerDomArity strandCount, ihtSplitLayerCodArity strandCount]
      rw [hDenote]
      refine Iff.trans (ihwPairMemCast
        (rows := ihsTensorRows 1 2 strandCount (strandCount + strandCount)
          [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
          (ihsLayerDenote (ihrSplitLayer strandCount)))
        (Nat.add_comm strandCount 1) (ihuWidthCanon strandCount)) ?_
      refine Iff.trans (ihwTensorSpec 1 2 strandCount (strandCount + strandCount)
        [[qnfOne, qnfOne, qnfZero], [qnfOne, qnfZero, qnfOne]]
        (ihsLayerDenote (ihrSplitLayer strandCount))
        (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil))
        (ihsAllWidthCast (by rw [ihtSplitLayerDomArity strandCount,
          ihtSplitLayerCodArity strandCount])
          (ihsLayerDenoteWidth (ihrSplitLayer strandCount)))
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
                        cases (ihzCoaddSpec firstDomVec firstCodVec).mp
                          hFacts.right.right.left with
                        | intro headP hCoaddPack =>
                            cases hCoaddPack with
                            | intro headQ hCoadd =>
                                cases (ihtSplitLayerDenote strandCount secondDomVec
                                  secondCodVec).mp hFacts.right.right.right with
                                | intro pRest hTailPack =>
                                    cases hTailPack with
                                    | intro qRest hTail =>
                                        refine Exists.intro (headP :: pRest)
                                          (Exists.intro (headQ :: qRest)
                                            (And.intro ?_ (And.intro ?_
                                              (And.intro ?_ ?_))))
                                        · rw [hFacts.left, hCoadd.left, hTail.left]
                                          rfl
                                        · rw [hFacts.right.left, hCoadd.right,
                                            hTail.right.left]
                                          rfl
                                        · exact congrArg (fun count => count + 1)
                                            hTail.right.right.left
                                        · exact congrArg (fun count => count + 1)
                                            hTail.right.right.right
      · intro hSpec
        cases hSpec with
        | intro pList hRest =>
            cases hRest with
            | intro qList hFacts =>
                cases pList with
                | nil => exact nomatch hFacts.right.right.left
                | cons headP pRest =>
                    cases qList with
                    | nil => exact nomatch hFacts.right.right.right
                    | cons headQ qRest =>
                        have hPRestLen : pRest.length = strandCount :=
                          Nat.succ.inj hFacts.right.right.left
                        have hQRestLen : qRest.length = strandCount :=
                          Nat.succ.inj hFacts.right.right.right
                        refine Exists.intro [qnfAdd headP headQ]
                          (Exists.intro (ihqRowAdd pRest qRest)
                            (Exists.intro [headP, headQ]
                              (Exists.intro (ihnInterleave pRest qRest)
                                (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))
                        · rw [hFacts.left]
                          rfl
                        · rw [hFacts.right.left]
                          rfl
                        · exact (ihzCoaddSpec [qnfAdd headP headQ] [headP, headQ]).mpr
                            (Exists.intro headP (Exists.intro headQ
                              (And.intro rfl rfl)))
                        · exact (ihtSplitLayerDenote strandCount
                            (ihqRowAdd pRest qRest) (ihnInterleave pRest qRest)).mpr
                            (Exists.intro pRest (Exists.intro qRest
                              (And.intro rfl (And.intro rfl
                                (And.intro hPRestLen hQRestLen)))))

/-- THE MERGE FAN DENOTATION: `ihrMergeLayer n` (per-strand `whiteMult`, `2n -> n`)
relates the interleaved layout `ihnInterleave firstList secondList` to the
pointwise sum `firstList + secondList`. -/
theorem ihtMergeLayerDenote : (strandCount : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem (strandCount + strandCount) strandCount
        (ihsLayerDenote (ihrMergeLayer strandCount)) domVec codVec
      <-> Exists fun firstList => Exists fun secondList =>
            domVec = ihnInterleave firstList secondList
              /\ codVec = ihqRowAdd firstList secondList
              /\ firstList.length = strandCount
              /\ secondList.length = strandCount)
  | 0, domVec, codVec => by
      refine Iff.trans (ihzNilRelationSpec 0 0 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hBoth
        refine Exists.intro [] (Exists.intro []
          (And.intro ?_ (And.intro ?_ (And.intro rfl rfl))))
        · rw [hBoth.left]
          rfl
        · rw [hBoth.right]
          rfl
      · intro hSpec
        cases hSpec with
        | intro firstList hRest =>
            cases hRest with
            | intro secondList hFacts =>
                have hFnil : firstList = [] :=
                  ihsLengthZeroNil firstList hFacts.right.right.left
                have hSnil : secondList = [] :=
                  ihsLengthZeroNil secondList hFacts.right.right.right
                refine And.intro ?_ ?_
                · rw [hFacts.left, hFnil, hSnil]
                  rfl
                · rw [hFacts.right.left, hFnil, hSnil]
                  rfl
  | strandCount + 1, domVec, codVec => by
      have hDenote : ihsLayerDenote (ihrMergeLayer (strandCount + 1))
          = ihsTensorRows 2 1 (strandCount + strandCount) strandCount
              [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
              (ihsLayerDenote (ihrMergeLayer strandCount)) := by
        show ihsTensorRows 2 1 (ihsLayerDomArity (ihrMergeLayer strandCount))
            (ihsLayerCodArity (ihrMergeLayer strandCount))
            [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
            (ihsLayerDenote (ihrMergeLayer strandCount)) = _
        rw [ihtMergeLayerDomArity strandCount, ihtMergeLayerCodArity strandCount]
      rw [hDenote]
      refine Iff.trans (ihwPairMemCast
        (rows := ihsTensorRows 2 1 (strandCount + strandCount) strandCount
          [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
          (ihsLayerDenote (ihrMergeLayer strandCount)))
        (ihuWidthCanon strandCount) (Nat.add_comm strandCount 1)) ?_
      refine Iff.trans (ihwTensorSpec 2 1 (strandCount + strandCount) strandCount
        [[qnfOne, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne]]
        (ihsLayerDenote (ihrMergeLayer strandCount))
        (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil))
        (ihsAllWidthCast (by rw [ihtMergeLayerDomArity strandCount,
          ihtMergeLayerCodArity strandCount])
          (ihsLayerDenoteWidth (ihrMergeLayer strandCount)))
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
                        cases (ihzAddSpec firstDomVec firstCodVec).mp
                          hFacts.right.right.left with
                        | intro headA hAddPack =>
                            cases hAddPack with
                            | intro headB hAdd =>
                                cases (ihtMergeLayerDenote strandCount secondDomVec
                                  secondCodVec).mp hFacts.right.right.right with
                                | intro firstRest hTailPack =>
                                    cases hTailPack with
                                    | intro secondRest hTail =>
                                        refine Exists.intro (headA :: firstRest)
                                          (Exists.intro (headB :: secondRest)
                                            (And.intro ?_ (And.intro ?_
                                              (And.intro ?_ ?_))))
                                        · rw [hFacts.left, hAdd.left, hTail.left]
                                          rfl
                                        · rw [hFacts.right.left, hAdd.right,
                                            hTail.right.left]
                                          rfl
                                        · exact congrArg (fun count => count + 1)
                                            hTail.right.right.left
                                        · exact congrArg (fun count => count + 1)
                                            hTail.right.right.right
      · intro hSpec
        cases hSpec with
        | intro firstList hRest =>
            cases hRest with
            | intro secondList hFacts =>
                cases firstList with
                | nil => exact nomatch hFacts.right.right.left
                | cons headA firstRest =>
                    cases secondList with
                    | nil => exact nomatch hFacts.right.right.right
                    | cons headB secondRest =>
                        have hFRestLen : firstRest.length = strandCount :=
                          Nat.succ.inj hFacts.right.right.left
                        have hSRestLen : secondRest.length = strandCount :=
                          Nat.succ.inj hFacts.right.right.right
                        refine Exists.intro [headA, headB]
                          (Exists.intro (ihnInterleave firstRest secondRest)
                            (Exists.intro [qnfAdd headA headB]
                              (Exists.intro (ihqRowAdd firstRest secondRest)
                                (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))
                        · rw [hFacts.left]
                          rfl
                        · rw [hFacts.right.left]
                          rfl
                        · exact (ihzAddSpec [headA, headB] [qnfAdd headA headB]).mpr
                            (Exists.intro headA (Exists.intro headB
                              (And.intro rfl rfl)))
                        · exact (ihtMergeLayerDenote strandCount
                            (ihnInterleave firstRest secondRest)
                            (ihqRowAdd firstRest secondRest)).mpr
                            (Exists.intro firstRest (Exists.intro secondRest
                              (And.intro rfl (And.intro rfl
                                (And.intro hFRestLen hSRestLen)))))

/-- DECIDED (T1): the split and merge per-strand fan layers ship their faithful
coadd / add denotations. -/
def ihtHasFanDenotations : Bool := true

/-! ## Stage 2 — interleave injectivity (the shared-middle reconciliation) -/

/-- The interleave layout is injective at equal block widths: two `(p, q)` pairs
producing the same interleaved vector are equal componentwise. -/
theorem ihtInterleaveInj : (blockWidth : Nat) ->
    (firstP firstQ secondP secondQ : List QnfRat) ->
    firstP.length = blockWidth -> firstQ.length = blockWidth ->
    secondP.length = blockWidth -> secondQ.length = blockWidth ->
    ihnInterleave firstP firstQ = ihnInterleave secondP secondQ ->
    firstP = secondP /\ firstQ = secondQ
  | 0, firstP, firstQ, secondP, secondQ, hFP, hFQ, hSP, hSQ, _hEq =>
      And.intro
        ((ihsLengthZeroNil firstP hFP).trans (ihsLengthZeroNil secondP hSP).symm)
        ((ihsLengthZeroNil firstQ hFQ).trans (ihsLengthZeroNil secondQ hSQ).symm)
  | blockWidth + 1, firstP, firstQ, secondP, secondQ, hFP, hFQ, hSP, hSQ, hEq => by
      cases firstP with
      | nil => exact nomatch hFP
      | cons headFP restFP =>
          cases firstQ with
          | nil => exact nomatch hFQ
          | cons headFQ restFQ =>
              cases secondP with
              | nil => exact nomatch hSP
              | cons headSP restSP =>
                  cases secondQ with
                  | nil => exact nomatch hSQ
                  | cons headSQ restSQ =>
                      have hHeadP : headFP = headSP :=
                        congrArg (fun row => ihqGetCoeff row 0) hEq
                      have hHeadQ : headFQ = headSQ :=
                        congrArg (fun row => ihqGetCoeff row 1) hEq
                      have hTailEq : ihnInterleave restFP restFQ
                          = ihnInterleave restSP restSQ :=
                        congrArg (fun row => ihqDropN 2 row) hEq
                      have hRec := ihtInterleaveInj blockWidth restFP restFQ restSP restSQ
                        (Nat.succ.inj hFP) (Nat.succ.inj hFQ)
                        (Nat.succ.inj hSP) (Nat.succ.inj hSQ) hTailEq
                      refine And.intro ?_ ?_
                      · rw [hHeadP, hRec.left]
                      · rw [hHeadQ, hRec.right]

/-! ## Stage 3 — the gadget tensor (T2) -/

/-- Right-whisker spec: a window whiskered by `rightWires` identity wires on the
right (none on the left) keeps the last `rightWires` strands fixed and runs the
window on the front block.  The mirror of `ihuWhiskerLeftSpec`. -/
theorem ihtWhiskerRightSpec (rightWires currentArity : Nat) (window : List (List IhsCell))
    (hWindowWF : IhsLayersWF currentArity window) (domVec codVec : List QnfRat) :
    IhqPairMem (currentArity + rightWires)
        (ihsLayersCodArity currentArity window + rightWires)
        (ihsLayersDenote (currentArity + rightWires)
          (ihwWhiskerLayers 0 rightWires window)) domVec codVec
      <-> Exists fun innerDom => Exists fun innerCod => Exists fun rightPart =>
            domVec = ihqCat innerDom rightPart
              /\ codVec = ihqCat innerCod rightPart
              /\ rightPart.length = rightWires
              /\ IhqPairMem currentArity (ihsLayersCodArity currentArity window)
                  (ihsLayersDenote currentArity window) innerDom innerCod := by
  have hWindowAll : IhqAllWidth (currentArity + ihsLayersCodArity currentArity window)
      (ihsLayersDenote currentArity window) := ihsLayersDenoteWidth window hWindowWF
  have hInnerAll : IhqAllWidth
      ((currentArity + rightWires) + (ihsLayersCodArity currentArity window + rightWires))
      (ihsTensorRows currentArity (ihsLayersCodArity currentArity window) rightWires rightWires
        (ihsLayersDenote currentArity window) (ihqIdRows rightWires)) :=
    ihsTensorRowsWidth currentArity (ihsLayersCodArity currentArity window) rightWires rightWires
      (ihsLayersDenote currentArity window) (ihqIdRows rightWires) hWindowAll
      (ihqIdRowsWidth rightWires)
  rw [congrArg (fun startArity => ihsLayersDenote startArity (ihwWhiskerLayers 0 rightWires window))
    (Nat.zero_add (currentArity + rightWires)).symm]
  refine Iff.trans (ihwPairMemCast (Nat.zero_add (currentArity + rightWires)).symm
    (Nat.zero_add (ihsLayersCodArity currentArity window + rightWires)).symm) ?_
  refine Iff.trans ((ihwWhiskerLayersDenote 0 rightWires window hWindowWF) domVec codVec) ?_
  refine Iff.trans (ihwPairMemCast (Nat.zero_add (currentArity + rightWires))
    (Nat.zero_add (ihsLayersCodArity currentArity window + rightWires))) ?_
  refine Iff.trans ((ihwTensorUnitLeft (currentArity + rightWires)
    (ihsLayersCodArity currentArity window + rightWires)
    (ihsTensorRows currentArity (ihsLayersCodArity currentArity window) rightWires rightWires
      (ihsLayersDenote currentArity window) (ihqIdRows rightWires)) hInnerAll) domVec codVec) ?_
  refine Iff.trans (ihwTensorSpec currentArity (ihsLayersCodArity currentArity window)
    rightWires rightWires (ihsLayersDenote currentArity window) (ihqIdRows rightWires)
    hWindowAll (ihqIdRowsWidth rightWires) domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro innerDom hP1 =>
        cases hP1 with
        | intro rightDom hP2 =>
            cases hP2 with
            | intro innerCod hP3 =>
                cases hP3 with
                | intro rightCod hFacts =>
                    have hRightSame := (ihsIdSpec rightWires rightDom rightCod).mp
                      hFacts.right.right.right
                    refine Exists.intro innerDom (Exists.intro innerCod (Exists.intro rightDom
                      (And.intro hFacts.left (And.intro ?_ (And.intro hRightSame.right
                        hFacts.right.right.left)))))
                    rw [hFacts.right.left, hRightSame.left]
  · intro hExists
    cases hExists with
    | intro innerDom hP1 =>
        cases hP1 with
        | intro innerCod hP2 =>
            cases hP2 with
            | intro rightPart hFacts =>
                refine Exists.intro innerDom (Exists.intro rightPart (Exists.intro innerCod
                  (Exists.intro rightPart (And.intro hFacts.left (And.intro hFacts.right.left
                    (And.intro hFacts.right.right.right ?_))))))
                exact (ihsIdSpec rightWires rightPart rightPart).mpr
                  (And.intro rfl hFacts.right.right.left)

/-- THE GADGET TENSOR DENOTATION (T2): the blockwise parallel composite of the two
single-row gadgets spans, per block, each gadget's line — the domain splits as
`firstScale * firstInputs ++ secondScale * secondInputs` and the codomain as
`firstScale * firstOutputs ++ secondScale * secondOutputs`. -/
theorem ihtGadgetTensorDenote (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (domVec codVec : List QnfRat) :
    IhqPairMem (firstInputs.length + secondInputs.length)
        (firstOutputs.length + secondOutputs.length)
        (ihsLayersDenote (firstInputs.length + secondInputs.length)
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
        domVec codVec
      <-> Exists fun firstScale => Exists fun secondScale =>
            domVec = ihqCat (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs)
              /\ codVec = ihqCat (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs) := by
  have hGadget1WF : IhsLayersWF firstInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers := ihgGadgetWF firstInputs firstOutputs
  have hGadget2WF : IhsLayersWF secondInputs.length
      (ihgGadgetDiagram secondInputs secondOutputs).layers := ihgGadgetWF secondInputs secondOutputs
  have hGadget1Cod : ihsLayersCodArity firstInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers = firstOutputs.length :=
    ihgGadgetCodArity firstInputs firstOutputs
  have hGadget2Cod : ihsLayersCodArity secondInputs.length
      (ihgGadgetDiagram secondInputs secondOutputs).layers = secondOutputs.length :=
    ihgGadgetCodArity secondInputs secondOutputs
  have hStageAWF : IhsLayersWF (firstInputs.length + secondInputs.length)
      (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers) :=
    ihsLayersWFCast (Nat.zero_add _) (ihwWhiskerLayersWF 0 secondInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers hGadget1WF)
  have hStageACod : ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
      = firstOutputs.length + secondInputs.length := by
    have hRaw := ihwWhiskerLayersCodArity 0 secondInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers firstInputs.length
    rw [hGadget1Cod, Nat.zero_add (firstInputs.length + secondInputs.length),
      Nat.zero_add (firstOutputs.length + secondInputs.length)] at hRaw
    exact hRaw
  have hStageBWF : IhsLayersWF (ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
      (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers) :=
    ihsLayersWFCast hStageACod.symm (ihwWhiskerLayersWF firstOutputs.length 0
      (ihgGadgetDiagram secondInputs secondOutputs).layers hGadget2WF)
  have hStageAAll := ihsLayersDenoteWidth
    (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
    hStageAWF
  have hStageBAll := ihsLayersDenoteWidth
    (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers)
    hStageBWF
  have hCat := ihwLayersDenoteCat
    (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
    (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers)
    hStageAWF hStageBWF
  -- stage A per-strand characterization (gadget1 on the front block)
  have hAEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (firstInputs.length + secondInputs.length)
          (ihsLayersCodArity (firstInputs.length + secondInputs.length)
            (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
          (ihsLayersDenote (firstInputs.length + secondInputs.length)
            (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
          domVec midVec
        <-> Exists fun firstScale => Exists fun rightPart =>
              domVec = ihqCat (ihqRowScale firstScale firstInputs) rightPart
                /\ midVec = ihqCat (ihqRowScale firstScale firstOutputs) rightPart
                /\ rightPart.length = secondInputs.length) := by
    intro midVec
    have hMidEq : ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
        = ihsLayersCodArity firstInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers
            + secondInputs.length := by
      rw [hStageACod, hGadget1Cod]
    refine Iff.trans (ihwPairMemCast rfl hMidEq) ?_
    refine Iff.trans (ihtWhiskerRightSpec secondInputs.length firstInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers hGadget1WF domVec midVec) ?_
    refine Iff.intro ?_ ?_
    · intro hW
      cases hW with
      | intro innerDom hP1 =>
          cases hP1 with
          | intro innerCod hP2 =>
              cases hP2 with
              | intro rightPart hFacts =>
                  cases (ihgGadgetDenote firstInputs firstOutputs innerDom innerCod).mp
                    ((ihwPairMemCast rfl hGadget1Cod).mp hFacts.right.right.right) with
                  | intro firstScale hGad =>
                      refine Exists.intro firstScale (Exists.intro rightPart
                        (And.intro ?_ (And.intro ?_ hFacts.right.right.left)))
                      · rw [hFacts.left, hGad.left]
                      · rw [hFacts.right.left, hGad.right]
    · intro hR
      cases hR with
      | intro firstScale hP1 =>
          cases hP1 with
          | intro rightPart hFacts =>
              refine Exists.intro (ihqRowScale firstScale firstInputs)
                (Exists.intro (ihqRowScale firstScale firstOutputs) (Exists.intro rightPart
                  (And.intro hFacts.left (And.intro hFacts.right.left
                    (And.intro hFacts.right.right ?_)))))
              exact (ihwPairMemCast rfl hGadget1Cod.symm).mp
                ((ihgGadgetDenote firstInputs firstOutputs (ihqRowScale firstScale firstInputs)
                    (ihqRowScale firstScale firstOutputs)).mpr
                  (Exists.intro firstScale (And.intro rfl rfl)))
  -- stage B per-strand characterization (gadget2 on the back block)
  have hBEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (firstInputs.length + secondInputs.length)
            (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
          (ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
              (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
            (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
          (ihsLayersDenote (ihsLayersCodArity (firstInputs.length + secondInputs.length)
              (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
            (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
          midVec codVec
        <-> Exists fun leftPart => Exists fun secondScale =>
              midVec = ihqCat leftPart (ihqRowScale secondScale secondInputs)
                /\ codVec = ihqCat leftPart (ihqRowScale secondScale secondOutputs)
                /\ leftPart.length = firstOutputs.length) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
      hStageACod]
    have hBCodEq : ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
          (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
        (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers)
        = firstOutputs.length + ihsLayersCodArity secondInputs.length
            (ihgGadgetDiagram secondInputs secondOutputs).layers := by
      rw [hStageACod]
      have hRaw := ihwWhiskerLayersCodArity firstOutputs.length 0
        (ihgGadgetDiagram secondInputs secondOutputs).layers secondInputs.length
      exact hRaw
    refine Iff.trans (ihwPairMemCast hStageACod hBCodEq) ?_
    refine Iff.trans (ihuWhiskerLeftSpec firstOutputs.length secondInputs.length
      (ihgGadgetDiagram secondInputs secondOutputs).layers hGadget2WF midVec codVec) ?_
    refine Iff.intro ?_ ?_
    · intro hW
      cases hW with
      | intro leftPart hP1 =>
          cases hP1 with
          | intro innerDom hP2 =>
              cases hP2 with
              | intro innerCod hFacts =>
                  cases (ihgGadgetDenote secondInputs secondOutputs innerDom innerCod).mp
                    ((ihwPairMemCast rfl hGadget2Cod).mp hFacts.right.right.right) with
                  | intro secondScale hGad =>
                      refine Exists.intro leftPart (Exists.intro secondScale
                        (And.intro ?_ (And.intro ?_ hFacts.right.right.left)))
                      · rw [hFacts.left, hGad.left]
                      · rw [hFacts.right.left, hGad.right]
    · intro hR
      cases hR with
      | intro leftPart hP1 =>
          cases hP1 with
          | intro secondScale hFacts =>
              refine Exists.intro leftPart (Exists.intro (ihqRowScale secondScale secondInputs)
                (Exists.intro (ihqRowScale secondScale secondOutputs)
                  (And.intro hFacts.left (And.intro hFacts.right.left
                    (And.intro hFacts.right.right ?_)))))
              exact (ihwPairMemCast rfl hGadget2Cod.symm).mp
                ((ihgGadgetDenote secondInputs secondOutputs (ihqRowScale secondScale secondInputs)
                    (ihqRowScale secondScale secondOutputs)).mpr
                  (Exists.intro secondScale (And.intro rfl rfl)))
  -- assemble the two stages through the compose
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
      (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers)
      = firstOutputs.length + secondOutputs.length := by
    rw [hStageACod]
    have hRaw := ihwWhiskerLayersCodArity firstOutputs.length 0
      (ihgGadgetDiagram secondInputs secondOutputs).layers secondInputs.length
    rw [hGadget2Cod] at hRaw
    exact hRaw
  refine Iff.trans (ihwPairMemCast (domWidth2 := firstInputs.length + secondInputs.length)
    rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (firstInputs.length + secondInputs.length)
    (ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
    (ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
      (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
    (ihsLayersDenote (firstInputs.length + secondInputs.length)
      (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
    (ihsLayersDenote (ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers))
      (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
    hStageAAll hStageBAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hAEquiv midVec).mp hParts.left with
        | intro firstScale hA1 =>
            cases hA1 with
            | intro rightPart hAFacts =>
                cases (hBEquiv midVec).mp hParts.right with
                | intro leftPart hB1 =>
                    cases hB1 with
                    | intro secondScale hBFacts =>
                        have hLen : (ihqRowScale firstScale firstOutputs).length
                            = leftPart.length := by
                          rw [ihqRowScaleLength, hBFacts.right.right]
                        have hSplit := ihqCatInj (ihqRowScale firstScale firstOutputs)
                          rightPart leftPart (ihqRowScale secondScale secondInputs)
                          hLen (hAFacts.right.left.symm.trans hBFacts.left)
                        refine Exists.intro firstScale (Exists.intro secondScale
                          (And.intro ?_ ?_))
                        · rw [hAFacts.left, hSplit.right]
                        · rw [hBFacts.right.left, hSplit.left]
  · intro hExists
    cases hExists with
    | intro firstScale hP1 =>
        cases hP1 with
        | intro secondScale hFacts =>
            refine Exists.intro (ihqCat (ihqRowScale firstScale firstOutputs)
              (ihqRowScale secondScale secondInputs)) (And.intro ?_ ?_)
            · exact (hAEquiv (ihqCat (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondInputs))).mpr
                (Exists.intro firstScale (Exists.intro (ihqRowScale secondScale secondInputs)
                  (And.intro hFacts.left (And.intro rfl (ihqRowScaleLength secondScale secondInputs)))))
            · exact (hBEquiv (ihqCat (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondInputs))).mpr
                (Exists.intro (ihqRowScale firstScale firstOutputs) (Exists.intro secondScale
                  (And.intro rfl (And.intro hFacts.right (ihqRowScaleLength firstScale firstOutputs)))))

/-- The stage-A (right-whiskered gadget1) cod arity at the clean boundary. -/
theorem ihtStageACodArity (firstInputs firstOutputs secondInputs : List QnfRat) :
    ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
      = firstOutputs.length + secondInputs.length := by
  have hGadget1Cod : ihsLayersCodArity firstInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers = firstOutputs.length :=
    ihgGadgetCodArity firstInputs firstOutputs
  have hRaw := ihwWhiskerLayersCodArity 0 secondInputs.length
    (ihgGadgetDiagram firstInputs firstOutputs).layers firstInputs.length
  rw [hGadget1Cod, Nat.zero_add (firstInputs.length + secondInputs.length),
    Nat.zero_add (firstOutputs.length + secondInputs.length)] at hRaw
  exact hRaw

/-- The gadget tensor is well-formed at its natural boundary. -/
theorem ihtGadgetTensorWF (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) :
    IhsLayersWF (firstInputs.length + secondInputs.length)
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs) := by
  show IhsLayersWF (firstInputs.length + secondInputs.length)
    (ihwCatLayers
      (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
      (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
  refine ihwLayersWFCat
    (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
    (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers)
    ?_ ?_
  · exact ihsLayersWFCast (Nat.zero_add _) (ihwWhiskerLayersWF 0 secondInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers (ihgGadgetWF firstInputs firstOutputs))
  · exact ihsLayersWFCast (ihtStageACodArity firstInputs firstOutputs secondInputs).symm
      (ihwWhiskerLayersWF firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers
        (ihgGadgetWF secondInputs secondOutputs))

/-- The gadget tensor cod arity at its natural boundary. -/
theorem ihtGadgetTensorCodArity (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) :
    ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
      = firstOutputs.length + secondOutputs.length := by
  show ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihwCatLayers
        (ihwWhiskerLayers 0 secondInputs.length (ihgGadgetDiagram firstInputs firstOutputs).layers)
        (ihwWhiskerLayers firstOutputs.length 0 (ihgGadgetDiagram secondInputs secondOutputs).layers))
    = firstOutputs.length + secondOutputs.length
  rw [ihwLayersCodArityCat, ihtStageACodArity firstInputs firstOutputs secondInputs]
  have hGadget2Cod : ihsLayersCodArity secondInputs.length
      (ihgGadgetDiagram secondInputs secondOutputs).layers = secondOutputs.length :=
    ihgGadgetCodArity secondInputs secondOutputs
  have hRaw := ihwWhiskerLayersCodArity firstOutputs.length 0
    (ihgGadgetDiagram secondInputs secondOutputs).layers secondInputs.length
  rw [hGadget2Cod] at hRaw
  exact hRaw

/-- DECIDED (T2): the gadget tensor ships its blockwise line-span denotation. -/
def ihtHasGadgetTensor : Bool := true

/-! ## Stage 4 — the Minkowski / two-row-matrix membership routing -/

/-- The Minkowski-sum characterization is exactly membership in the span of the
two-row matrix `[in1 ++ out1, in2 ++ out2]`: `(dom, cod)` lies in the sum of the
two lines iff `dom = a*in1 + b*in2` and `cod = a*out1 + b*out2`. -/
theorem ihtMinkowskiPairMem (firstInputs firstOutputs secondInputs secondOutputs
    domVec codVec : List QnfRat)
    (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length) :
    (Exists fun firstScale => Exists fun secondScale =>
        domVec = ihqRowAdd (ihqRowScale firstScale firstInputs)
            (ihqRowScale secondScale secondInputs)
          /\ codVec = ihqRowAdd (ihqRowScale firstScale firstOutputs)
            (ihqRowScale secondScale secondOutputs))
      <-> IhqPairMem firstInputs.length firstOutputs.length
          [ihqCat firstInputs firstOutputs, ihqCat secondInputs secondOutputs]
          domVec codVec := by
  have hRow1Len : (ihqCat firstInputs firstOutputs).length
      = firstInputs.length + firstOutputs.length :=
    ihqCatLength firstInputs firstOutputs
  have hRow2Len : (ihqCat secondInputs secondOutputs).length
      = firstInputs.length + firstOutputs.length := by
    rw [ihqCatLength secondInputs secondOutputs, hInLen, hOutLen]
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro firstScale hP1 =>
        cases hP1 with
        | intro secondScale hFacts =>
            have hDomLen : domVec.length = firstInputs.length := by
              rw [hFacts.left]
              exact ihqRowAddLength (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs) firstInputs.length
                (ihqRowScaleLength firstScale firstInputs)
                ((ihqRowScaleLength secondScale secondInputs).trans hInLen.symm)
            have hCodLen : codVec.length = firstOutputs.length := by
              rw [hFacts.right]
              exact ihqRowAddLength (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs) firstOutputs.length
                (ihqRowScaleLength firstScale firstOutputs)
                ((ihqRowScaleLength secondScale secondOutputs).trans hOutLen.symm)
            refine And.intro hDomLen (And.intro hCodLen ?_)
            have hCatEq : ihqCat domVec codVec
                = ihqRowAdd
                    (ihqRowScale firstScale (ihqCat firstInputs firstOutputs))
                    (ihqRowScale secondScale (ihqCat secondInputs secondOutputs)) := by
              rw [hFacts.left, hFacts.right,
                ihqRowScaleCat firstScale firstInputs firstOutputs,
                ihqRowScaleCat secondScale secondInputs secondOutputs,
                ihqRowAddCat (ihqRowScale firstScale firstInputs)
                  (ihqRowScale firstScale firstOutputs)
                  (ihqRowScale secondScale secondInputs)
                  (ihqRowScale secondScale secondOutputs)
                  (by rw [ihqRowScaleLength firstScale firstInputs,
                    ihqRowScaleLength secondScale secondInputs, hInLen])]
            rw [hCatEq]
            exact ihzMemSpanPairIntro (ihqCat firstInputs firstOutputs)
              (ihqCat secondInputs secondOutputs) firstScale secondScale hRow1Len hRow2Len
  · intro hPair
    cases ihzMemSpanPairInv hRow1Len hRow2Len hPair.right.right with
    | intro firstScale hP1 =>
        cases hP1 with
        | intro secondScale hVecEq =>
            rw [ihqRowScaleCat firstScale firstInputs firstOutputs,
              ihqRowScaleCat secondScale secondInputs secondOutputs,
              ihqRowAddCat (ihqRowScale firstScale firstInputs)
                (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondInputs)
                (ihqRowScale secondScale secondOutputs)
                (by rw [ihqRowScaleLength firstScale firstInputs,
                  ihqRowScaleLength secondScale secondInputs, hInLen])] at hVecEq
            have hSplit := ihqCatInj domVec codVec
              (ihqRowAdd (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs))
              (ihqRowAdd (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs))
              (by rw [hPair.left, (ihqRowAddLength (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs) firstInputs.length
                (ihqRowScaleLength firstScale firstInputs)
                ((ihqRowScaleLength secondScale secondInputs).trans hInLen.symm))])
              hVecEq
            exact Exists.intro firstScale (Exists.intro secondScale
              (And.intro hSplit.left hSplit.right))

/-! ## Stage 5 — the five-stage assembly denotation (T3) -/

/-- The `shuffle ; merge` tail (`2n -> n`): block input `cat p q` mapped to the
pointwise sum `p + q`. -/
theorem ihtShuffleMergeDenote (blockWidth : Nat) (domVec codVec : List QnfRat) :
    IhqPairMem (blockWidth + blockWidth) blockWidth
        (ihsLayersDenote (blockWidth + blockWidth)
          (ihwCatLayers (ihrShuffle blockWidth) [ihrMergeLayer blockWidth])) domVec codVec
      <-> Exists fun firstList => Exists fun secondList =>
            domVec = ihqCat firstList secondList
              /\ codVec = ihqRowAdd firstList secondList
              /\ firstList.length = blockWidth
              /\ secondList.length = blockWidth := by
  have hShuffleWF : IhsLayersWF (blockWidth + blockWidth) (ihrShuffle blockWidth) :=
    ihuReversibleWF (ihuReversibleReverse (ihuReversibleUnshuffle blockWidth))
  have hShuffleCod : ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth)
      = blockWidth + blockWidth :=
    ihuReversibleCodArity (ihuReversibleReverse (ihuReversibleUnshuffle blockWidth))
  have hMergeWF : IhsLayersWF (blockWidth + blockWidth) [ihrMergeLayer blockWidth] :=
    IhsLayersWF.cons (ihtMergeLayerDomArity blockWidth) (IhsLayersWF.nil _)
  have hMergeWFatCod : IhsLayersWF (ihsLayersCodArity (blockWidth + blockWidth)
      (ihrShuffle blockWidth)) [ihrMergeLayer blockWidth] :=
    ihsLayersWFCast hShuffleCod.symm hMergeWF
  have hShuffleAll := ihsLayersDenoteWidth (ihrShuffle blockWidth) hShuffleWF
  have hMergeAll := ihsLayersDenoteWidth [ihrMergeLayer blockWidth] hMergeWFatCod
  have hCat := ihwLayersDenoteCat (ihrShuffle blockWidth) [ihrMergeLayer blockWidth]
    hShuffleWF hMergeWFatCod
  have hMergeCod : ihsLayerCodArity (ihrMergeLayer blockWidth) = blockWidth :=
    ihtMergeLayerCodArity blockWidth
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (blockWidth + blockWidth)
      (ihrShuffle blockWidth)) [ihrMergeLayer blockWidth] = blockWidth := by
    rw [hShuffleCod]
    exact hMergeCod
  -- shuffle factor characterization (cod folded)
  have hShuffleEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (blockWidth + blockWidth) (ihsLayersCodArity (blockWidth + blockWidth)
          (ihrShuffle blockWidth)) (ihsLayersDenote (blockWidth + blockWidth)
            (ihrShuffle blockWidth)) domVec midVec
        <-> Exists fun pList => Exists fun qList =>
              domVec = ihqCat pList qList /\ midVec = ihnInterleave pList qList
                /\ pList.length = blockWidth /\ qList.length = blockWidth) := by
    intro midVec
    refine Iff.trans (ihwPairMemCast rfl hShuffleCod) ?_
    exact ihuShuffleDenote blockWidth domVec midVec
  -- merge factor characterization (single-layer bridge + fold)
  have hMergeEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth))
          (ihsLayersCodArity (ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth))
            [ihrMergeLayer blockWidth])
          (ihsLayersDenote (ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth))
            [ihrMergeLayer blockWidth]) midVec codVec
        <-> Exists fun firstList => Exists fun secondList =>
              midVec = ihnInterleave firstList secondList
                /\ codVec = ihqRowAdd firstList secondList
                /\ firstList.length = blockWidth /\ secondList.length = blockWidth) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity [ihrMergeLayer blockWidth])
      hShuffleCod]
    refine Iff.trans (ihwPairMemCast hShuffleCod rfl) ?_
    refine Iff.trans (ihuSingletonDenote (ihrMergeLayer blockWidth) (blockWidth + blockWidth)
      (ihtMergeLayerDomArity blockWidth) midVec codVec) ?_
    refine Iff.trans (ihwPairMemCast rfl hMergeCod) ?_
    exact ihtMergeLayerDenote blockWidth midVec codVec
  refine Iff.trans (ihwPairMemCast (domWidth2 := blockWidth + blockWidth) rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (blockWidth + blockWidth)
    (ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth))
    (ihsLayersCodArity (ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth))
      [ihrMergeLayer blockWidth])
    (ihsLayersDenote (blockWidth + blockWidth) (ihrShuffle blockWidth))
    (ihsLayersDenote (ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth))
      [ihrMergeLayer blockWidth])
    hShuffleAll hMergeAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hShuffleEquiv midVec).mp hParts.left with
        | intro pList hS1 =>
            cases hS1 with
            | intro qList hSFacts =>
                cases (hMergeEquiv midVec).mp hParts.right with
                | intro firstList hM1 =>
                    cases hM1 with
                    | intro secondList hMFacts =>
                        have hRec := ihtInterleaveInj blockWidth pList qList firstList secondList
                          hSFacts.right.right.left hSFacts.right.right.right
                          hMFacts.right.right.left hMFacts.right.right.right
                          (hSFacts.right.left.symm.trans hMFacts.left)
                        refine Exists.intro pList (Exists.intro qList
                          (And.intro hSFacts.left (And.intro ?_ (And.intro
                            hSFacts.right.right.left hSFacts.right.right.right))))
                        rw [hMFacts.right.left, hRec.left, hRec.right]
  · intro hExists
    cases hExists with
    | intro firstList hP1 =>
        cases hP1 with
        | intro secondList hFacts =>
            refine Exists.intro (ihnInterleave firstList secondList) (And.intro ?_ ?_)
            · exact (hShuffleEquiv (ihnInterleave firstList secondList)).mpr
                (Exists.intro firstList (Exists.intro secondList
                  (And.intro hFacts.left (And.intro rfl
                    (And.intro hFacts.right.right.left hFacts.right.right.right)))))
            · exact (hMergeEquiv (ihnInterleave firstList secondList)).mpr
                (Exists.intro firstList (Exists.intro secondList
                  (And.intro rfl (And.intro hFacts.right.left
                    (And.intro hFacts.right.right.left hFacts.right.right.right)))))

/-- The `shuffle ; merge` tail is well-formed at `2n`. -/
theorem ihtShuffleMergeWF (blockWidth : Nat) :
    IhsLayersWF (blockWidth + blockWidth)
      (ihwCatLayers (ihrShuffle blockWidth) [ihrMergeLayer blockWidth]) := by
  have hShuffleWF : IhsLayersWF (blockWidth + blockWidth) (ihrShuffle blockWidth) :=
    ihuReversibleWF (ihuReversibleReverse (ihuReversibleUnshuffle blockWidth))
  have hShuffleCod : ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth)
      = blockWidth + blockWidth :=
    ihuReversibleCodArity (ihuReversibleReverse (ihuReversibleUnshuffle blockWidth))
  refine ihwLayersWFCat (ihrShuffle blockWidth) [ihrMergeLayer blockWidth] hShuffleWF ?_
  exact ihsLayersWFCast hShuffleCod.symm
    (IhsLayersWF.cons (ihtMergeLayerDomArity blockWidth) (IhsLayersWF.nil _))

/-- The `shuffle ; merge` tail cod arity: `2n -> n`. -/
theorem ihtShuffleMergeCodArity (blockWidth : Nat) :
    ihsLayersCodArity (blockWidth + blockWidth)
        (ihwCatLayers (ihrShuffle blockWidth) [ihrMergeLayer blockWidth]) = blockWidth := by
  have hShuffleCod : ihsLayersCodArity (blockWidth + blockWidth) (ihrShuffle blockWidth)
      = blockWidth + blockWidth :=
    ihuReversibleCodArity (ihuReversibleReverse (ihuReversibleUnshuffle blockWidth))
  rw [ihwLayersCodArityCat, hShuffleCod]
  exact ihtMergeLayerCodArity blockWidth

/-- The `gadget-tensor ; shuffle ; merge` middle (`2m -> n`): block-pairs run
each gadget's line then merge, so the domain splits blockwise and the codomain
is the pointwise sum of the two output lines. -/
theorem ihtGadgetShuffleMergeDenote (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hOutLen : firstOutputs.length = secondOutputs.length)
    (domVec codVec : List QnfRat) :
    IhqPairMem (firstInputs.length + secondInputs.length) firstOutputs.length
        (ihsLayersDenote (firstInputs.length + secondInputs.length)
          (ihwCatLayers
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
            (ihwCatLayers (ihrShuffle firstOutputs.length)
              [ihrMergeLayer firstOutputs.length]))) domVec codVec
      <-> Exists fun firstScale => Exists fun secondScale =>
            domVec = ihqCat (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs)
              /\ codVec = ihqRowAdd (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs) := by
  have hGadgetWF : IhsLayersWF (firstInputs.length + secondInputs.length)
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs) :=
    ihtGadgetTensorWF firstInputs firstOutputs secondInputs secondOutputs
  have hGadgetCod : ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
      = firstOutputs.length + secondOutputs.length :=
    ihtGadgetTensorCodArity firstInputs firstOutputs secondInputs secondOutputs
  -- the shuffle;merge tail runs at the gadget cod arity (n1+n2), folded to n1+n1
  have hTailArity : firstOutputs.length + secondOutputs.length
      = firstOutputs.length + firstOutputs.length := by rw [hOutLen]
  have hRest4WF : IhsLayersWF (ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]) := by
    rw [hGadgetCod, hTailArity]
    exact ihtShuffleMergeWF firstOutputs.length
  have hGadgetAll := ihsLayersDenoteWidth
    (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs) hGadgetWF
  have hRest4All := ihsLayersDenoteWidth
    (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]) hRest4WF
  have hCat := ihwLayersDenoteCat
    (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
    (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])
    hGadgetWF hRest4WF
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])
      = firstOutputs.length := by
    rw [hGadgetCod, hTailArity]
    exact ihtShuffleMergeCodArity firstOutputs.length
  -- gadget factor (cod folded to n1+n2)
  have hGadgetEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (firstInputs.length + secondInputs.length)
          (ihsLayersCodArity (firstInputs.length + secondInputs.length)
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
          (ihsLayersDenote (firstInputs.length + secondInputs.length)
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
          domVec midVec
        <-> Exists fun firstScale => Exists fun secondScale =>
              midVec = ihqCat (ihqRowScale firstScale firstOutputs)
                  (ihqRowScale secondScale secondOutputs)
                /\ domVec = ihqCat (ihqRowScale firstScale firstInputs)
                  (ihqRowScale secondScale secondInputs)) := by
    intro midVec
    refine Iff.trans (ihwPairMemCast rfl hGadgetCod) ?_
    refine Iff.trans (ihtGadgetTensorDenote firstInputs firstOutputs secondInputs secondOutputs
      domVec midVec) ?_
    refine Iff.intro ?_ ?_
    · intro hG
      cases hG with
      | intro firstScale hP1 =>
          cases hP1 with
          | intro secondScale hFacts =>
              exact Exists.intro firstScale (Exists.intro secondScale
                (And.intro hFacts.right hFacts.left))
    · intro hG
      cases hG with
      | intro firstScale hP1 =>
          cases hP1 with
          | intro secondScale hFacts =>
              exact Exists.intro firstScale (Exists.intro secondScale
                (And.intro hFacts.right hFacts.left))
  -- shuffle;merge factor (dom arity folded to n1+n1, cod folded to n1)
  have hTailEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (firstInputs.length + secondInputs.length)
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
          (ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
              (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
            (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
          (ihsLayersDenote (ihsLayersCodArity (firstInputs.length + secondInputs.length)
              (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
            (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
          midVec codVec
        <-> Exists fun firstList => Exists fun secondList =>
              midVec = ihqCat firstList secondList
                /\ codVec = ihqRowAdd firstList secondList
                /\ firstList.length = firstOutputs.length
                /\ secondList.length = firstOutputs.length) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
      (hGadgetCod.trans hTailArity)]
    refine Iff.trans (ihwPairMemCast (hGadgetCod.trans hTailArity) hFinalCod) ?_
    exact ihtShuffleMergeDenote firstOutputs.length midVec codVec
  refine Iff.trans (ihwPairMemCast (domWidth2 := firstInputs.length + secondInputs.length)
    rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (firstInputs.length + secondInputs.length)
    (ihsLayersCodArity (firstInputs.length + secondInputs.length)
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
    (ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
    (ihsLayersDenote (firstInputs.length + secondInputs.length)
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
    (ihsLayersDenote (ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs))
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
    hGadgetAll hRest4All domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro midVec hParts =>
        cases (hGadgetEquiv midVec).mp hParts.left with
        | intro firstScale hG1 =>
            cases hG1 with
            | intro secondScale hGFacts =>
                cases (hTailEquiv midVec).mp hParts.right with
                | intro firstList hT1 =>
                    cases hT1 with
                    | intro secondList hTFacts =>
                        have hLen : (ihqRowScale firstScale firstOutputs).length
                            = firstList.length := by
                          rw [ihqRowScaleLength, hTFacts.right.right.left]
                        have hSplit := ihqCatInj (ihqRowScale firstScale firstOutputs)
                          (ihqRowScale secondScale secondOutputs) firstList secondList
                          hLen (hGFacts.left.symm.trans hTFacts.left)
                        refine Exists.intro firstScale (Exists.intro secondScale
                          (And.intro hGFacts.right ?_))
                        rw [hTFacts.right.left, hSplit.left, hSplit.right]
  · intro hExists
    cases hExists with
    | intro firstScale hP1 =>
        cases hP1 with
        | intro secondScale hFacts =>
            refine Exists.intro (ihqCat (ihqRowScale firstScale firstOutputs)
              (ihqRowScale secondScale secondOutputs)) (And.intro ?_ ?_)
            · exact (hGadgetEquiv (ihqCat (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs))).mpr
                (Exists.intro firstScale (Exists.intro secondScale
                  (And.intro rfl hFacts.left)))
            · exact (hTailEquiv (ihqCat (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs))).mpr
                (Exists.intro (ihqRowScale firstScale firstOutputs)
                  (Exists.intro (ihqRowScale secondScale secondOutputs)
                    (And.intro rfl (And.intro hFacts.right
                      (And.intro (ihqRowScaleLength firstScale firstOutputs)
                        ((ihqRowScaleLength secondScale secondOutputs).trans hOutLen.symm))))))

/-- The `gadget-tensor ; shuffle ; merge` middle is well-formed at `2m`. -/
theorem ihtGadgetShuffleMergeWF (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hOutLen : firstOutputs.length = secondOutputs.length) :
    IhsLayersWF (firstInputs.length + secondInputs.length)
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length)
          [ihrMergeLayer firstOutputs.length])) := by
  refine ihwLayersWFCat
    (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
    (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])
    (ihtGadgetTensorWF firstInputs firstOutputs secondInputs secondOutputs) ?_
  rw [ihtGadgetTensorCodArity firstInputs firstOutputs secondInputs secondOutputs,
    (show firstOutputs.length + secondOutputs.length
      = firstOutputs.length + firstOutputs.length by rw [hOutLen])]
  exact ihtShuffleMergeWF firstOutputs.length

/-- The `gadget-tensor ; shuffle ; merge` middle cod arity: `2m -> n`. -/
theorem ihtGadgetShuffleMergeCodArity (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hOutLen : firstOutputs.length = secondOutputs.length) :
    ihsLayersCodArity (firstInputs.length + secondInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length)
            [ihrMergeLayer firstOutputs.length])) = firstOutputs.length := by
  rw [ihwLayersCodArityCat,
    ihtGadgetTensorCodArity firstInputs firstOutputs secondInputs secondOutputs,
    (show firstOutputs.length + secondOutputs.length
      = firstOutputs.length + firstOutputs.length by rw [hOutLen])]
  exact ihtShuffleMergeCodArity firstOutputs.length

/-- The `unshuffle ; gadget-tensor ; shuffle ; merge` prefix (`2m -> n`):
interleaved input woven into the block pairs, then run and merged. -/
theorem ihtUnshuffleRestDenote (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length)
    (domVec codVec : List QnfRat) :
    IhqPairMem (firstInputs.length + firstInputs.length) firstOutputs.length
        (ihsLayersDenote (firstInputs.length + firstInputs.length)
          (ihwCatLayers (ihrUnshuffle firstInputs.length)
            (ihwCatLayers
              (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
              (ihwCatLayers (ihrShuffle firstOutputs.length)
                [ihrMergeLayer firstOutputs.length])))) domVec codVec
      <-> Exists fun firstScale => Exists fun secondScale =>
            domVec = ihnInterleave (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs)
              /\ codVec = ihqRowAdd (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs) := by
  have hUnshuffleWF : IhsLayersWF (firstInputs.length + firstInputs.length)
      (ihrUnshuffle firstInputs.length) := ihuUnshuffleWF firstInputs.length
  have hUnshuffleCod : ihsLayersCodArity (firstInputs.length + firstInputs.length)
      (ihrUnshuffle firstInputs.length) = firstInputs.length + firstInputs.length :=
    ihuUnshuffleCodArity firstInputs.length
  have hArityFold : firstInputs.length + firstInputs.length
      = firstInputs.length + secondInputs.length := by rw [hInLen]
  have hRest3WF : IhsLayersWF (ihsLayersCodArity (firstInputs.length + firstInputs.length)
      (ihrUnshuffle firstInputs.length))
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length)
          [ihrMergeLayer firstOutputs.length])) := by
    rw [hUnshuffleCod, hArityFold]
    exact ihtGadgetShuffleMergeWF firstInputs firstOutputs secondInputs secondOutputs hOutLen
  have hUnshuffleAll := ihsLayersDenoteWidth (ihrUnshuffle firstInputs.length) hUnshuffleWF
  have hRest3All := ihsLayersDenoteWidth
    (ihwCatLayers
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
    hRest3WF
  have hCat := ihwLayersDenoteCat (ihrUnshuffle firstInputs.length)
    (ihwCatLayers
      (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
      (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))
    hUnshuffleWF hRest3WF
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + firstInputs.length)
        (ihrUnshuffle firstInputs.length))
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length)
          [ihrMergeLayer firstOutputs.length])) = firstOutputs.length := by
    rw [hUnshuffleCod, hArityFold]
    exact ihtGadgetShuffleMergeCodArity firstInputs firstOutputs secondInputs secondOutputs hOutLen
  -- unshuffle factor (cod folded to 2m)
  have hUnshuffleEquiv : (midVec : List QnfRat) ->
      (IhqPairMem (firstInputs.length + firstInputs.length)
          (ihsLayersCodArity (firstInputs.length + firstInputs.length)
            (ihrUnshuffle firstInputs.length))
          (ihsLayersDenote (firstInputs.length + firstInputs.length)
            (ihrUnshuffle firstInputs.length)) domVec midVec
        <-> Exists fun pList => Exists fun qList =>
              domVec = ihnInterleave pList qList /\ midVec = ihqCat pList qList
                /\ pList.length = firstInputs.length /\ qList.length = firstInputs.length) := by
    intro midVec
    refine Iff.trans (ihwPairMemCast rfl hUnshuffleCod) ?_
    exact ihuUnshuffleDenote firstInputs.length domVec midVec
  -- rest3 factor (dom arity folded to 2m2, cod folded to n)
  have hRest3Equiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity (firstInputs.length + firstInputs.length)
            (ihrUnshuffle firstInputs.length))
          (ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + firstInputs.length)
              (ihrUnshuffle firstInputs.length))
            (ihwCatLayers
              (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
              (ihwCatLayers (ihrShuffle firstOutputs.length)
                [ihrMergeLayer firstOutputs.length])))
          (ihsLayersDenote (ihsLayersCodArity (firstInputs.length + firstInputs.length)
              (ihrUnshuffle firstInputs.length))
            (ihwCatLayers
              (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
              (ihwCatLayers (ihrShuffle firstOutputs.length)
                [ihrMergeLayer firstOutputs.length])))
          midVec codVec
        <-> Exists fun firstScale => Exists fun secondScale =>
              midVec = ihqCat (ihqRowScale firstScale firstInputs)
                  (ihqRowScale secondScale secondInputs)
                /\ codVec = ihqRowAdd (ihqRowScale firstScale firstOutputs)
                  (ihqRowScale secondScale secondOutputs)) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])))
      (hUnshuffleCod.trans hArityFold)]
    refine Iff.trans (ihwPairMemCast (hUnshuffleCod.trans hArityFold) hFinalCod) ?_
    exact ihtGadgetShuffleMergeDenote firstInputs firstOutputs secondInputs secondOutputs
      hOutLen midVec codVec
  refine Iff.trans (ihwPairMemCast
    (domWidth2 := firstInputs.length + firstInputs.length) rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec (firstInputs.length + firstInputs.length)
    (ihsLayersCodArity (firstInputs.length + firstInputs.length)
      (ihrUnshuffle firstInputs.length))
    (ihsLayersCodArity (ihsLayersCodArity (firstInputs.length + firstInputs.length)
        (ihrUnshuffle firstInputs.length))
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])))
    (ihsLayersDenote (firstInputs.length + firstInputs.length)
      (ihrUnshuffle firstInputs.length))
    (ihsLayersDenote (ihsLayersCodArity (firstInputs.length + firstInputs.length)
        (ihrUnshuffle firstInputs.length))
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])))
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
                | intro firstScale hR1 =>
                    cases hR1 with
                    | intro secondScale hRFacts =>
                        have hLen : pList.length
                            = (ihqRowScale firstScale firstInputs).length := by
                          rw [ihqRowScaleLength, hUFacts.right.right.left]
                        have hSplit := ihqCatInj pList qList
                          (ihqRowScale firstScale firstInputs)
                          (ihqRowScale secondScale secondInputs)
                          hLen (hUFacts.right.left.symm.trans hRFacts.left)
                        refine Exists.intro firstScale (Exists.intro secondScale
                          (And.intro ?_ hRFacts.right))
                        rw [hUFacts.left, hSplit.left, hSplit.right]
  · intro hExists
    cases hExists with
    | intro firstScale hP1 =>
        cases hP1 with
        | intro secondScale hFacts =>
            refine Exists.intro (ihqCat (ihqRowScale firstScale firstInputs)
              (ihqRowScale secondScale secondInputs)) (And.intro ?_ ?_)
            · exact (hUnshuffleEquiv (ihqCat (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs))).mpr
                (Exists.intro (ihqRowScale firstScale firstInputs)
                  (Exists.intro (ihqRowScale secondScale secondInputs)
                    (And.intro hFacts.left (And.intro rfl
                      (And.intro (ihqRowScaleLength firstScale firstInputs)
                        ((ihqRowScaleLength secondScale secondInputs).trans hInLen.symm))))))
            · exact (hRest3Equiv (ihqCat (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs))).mpr
                (Exists.intro firstScale (Exists.intro secondScale
                  (And.intro rfl hFacts.right)))

/-- The `unshuffle ; gadget-tensor ; shuffle ; merge` prefix is well-formed at `2m`. -/
theorem ihtUnshuffleRestWF (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length) :
    IhsLayersWF (firstInputs.length + firstInputs.length)
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length)
            [ihrMergeLayer firstOutputs.length]))) := by
  refine ihwLayersWFCat (ihrUnshuffle firstInputs.length) _
    (ihuUnshuffleWF firstInputs.length) ?_
  rw [ihuUnshuffleCodArity firstInputs.length,
    (show firstInputs.length + firstInputs.length
      = firstInputs.length + secondInputs.length by rw [hInLen])]
  exact ihtGadgetShuffleMergeWF firstInputs firstOutputs secondInputs secondOutputs hOutLen

/-- The `unshuffle ; gadget-tensor ; shuffle ; merge` prefix cod arity: `2m -> n`. -/
theorem ihtUnshuffleRestCodArity (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length) :
    ihsLayersCodArity (firstInputs.length + firstInputs.length)
        (ihwCatLayers (ihrUnshuffle firstInputs.length)
          (ihwCatLayers
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
            (ihwCatLayers (ihrShuffle firstOutputs.length)
              [ihrMergeLayer firstOutputs.length]))) = firstOutputs.length := by
  rw [ihwLayersCodArityCat, ihuUnshuffleCodArity firstInputs.length,
    (show firstInputs.length + firstInputs.length
      = firstInputs.length + secondInputs.length by rw [hInLen])]
  exact ihtGadgetShuffleMergeCodArity firstInputs firstOutputs secondInputs secondOutputs hOutLen

/-- THE FULL ASSEMBLY DENOTATION: `split ; unshuffle ; (gadget TENSOR gadget) ;
shuffle ; merge` denotes the Minkowski sum of the two lines — the domain is
`a*in1 + b*in2`, the codomain is `a*out1 + b*out2`. -/
theorem ihtAssemblyDenote (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length)
    (domVec codVec : List QnfRat) :
    IhqPairMem firstInputs.length firstOutputs.length
        (ihsDiagramDenote
          (ihrTwoRowSumDiagram firstInputs firstOutputs secondInputs secondOutputs))
        domVec codVec
      <-> Exists fun firstScale => Exists fun secondScale =>
            domVec = ihqRowAdd (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs)
              /\ codVec = ihqRowAdd (ihqRowScale firstScale firstOutputs)
                (ihqRowScale secondScale secondOutputs) := by
  show IhqPairMem firstInputs.length firstOutputs.length
      (ihsLayersDenote firstInputs.length
        (ihwCatLayers [ihrSplitLayer firstInputs.length]
          (ihwCatLayers (ihrUnshuffle firstInputs.length)
            (ihwCatLayers
              (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
              (ihwCatLayers (ihrShuffle firstOutputs.length)
                [ihrMergeLayer firstOutputs.length]))))) domVec codVec
    <-> _
  have hSplitWF : IhsLayersWF firstInputs.length [ihrSplitLayer firstInputs.length] :=
    IhsLayersWF.cons (ihtSplitLayerDomArity firstInputs.length) (IhsLayersWF.nil _)
  have hSplitCod : ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length]
      = firstInputs.length + firstInputs.length := ihtSplitLayerCodArity firstInputs.length
  have hRest2WF : IhsLayersWF (ihsLayersCodArity firstInputs.length
      [ihrSplitLayer firstInputs.length])
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length)
            [ihrMergeLayer firstOutputs.length]))) := by
    rw [hSplitCod]
    exact ihtUnshuffleRestWF firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen
  have hSplitAll := ihsLayersDenoteWidth [ihrSplitLayer firstInputs.length] hSplitWF
  have hRest2All := ihsLayersDenoteWidth
    (ihwCatLayers (ihrUnshuffle firstInputs.length)
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])))
    hRest2WF
  have hCat := ihwLayersDenoteCat [ihrSplitLayer firstInputs.length]
    (ihwCatLayers (ihrUnshuffle firstInputs.length)
      (ihwCatLayers
        (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
        (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length])))
    hSplitWF hRest2WF
  have hFinalCod : ihsLayersCodArity (ihsLayersCodArity firstInputs.length
        [ihrSplitLayer firstInputs.length])
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length)
            [ihrMergeLayer firstOutputs.length]))) = firstOutputs.length := by
    rw [hSplitCod]
    exact ihtUnshuffleRestCodArity firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen
  -- split factor (single-layer bridge + fold to (m, 2m))
  have hSplitEquiv : (midVec : List QnfRat) ->
      (IhqPairMem firstInputs.length (ihsLayersCodArity firstInputs.length
          [ihrSplitLayer firstInputs.length])
          (ihsLayersDenote firstInputs.length [ihrSplitLayer firstInputs.length])
          domVec midVec
        <-> Exists fun pList => Exists fun qList =>
              domVec = ihqRowAdd pList qList /\ midVec = ihnInterleave pList qList
                /\ pList.length = firstInputs.length /\ qList.length = firstInputs.length) := by
    intro midVec
    refine Iff.trans (ihuSingletonDenote (ihrSplitLayer firstInputs.length) firstInputs.length
      (ihtSplitLayerDomArity firstInputs.length) domVec midVec) ?_
    refine Iff.trans (ihwPairMemCast rfl (ihtSplitLayerCodArity firstInputs.length)) ?_
    exact ihtSplitLayerDenote firstInputs.length domVec midVec
  -- rest2 factor (dom arity folded to 2m, cod folded to n)
  have hRest2Equiv : (midVec : List QnfRat) ->
      (IhqPairMem (ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length])
          (ihsLayersCodArity (ihsLayersCodArity firstInputs.length
              [ihrSplitLayer firstInputs.length])
            (ihwCatLayers (ihrUnshuffle firstInputs.length)
              (ihwCatLayers
                (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
                (ihwCatLayers (ihrShuffle firstOutputs.length)
                  [ihrMergeLayer firstOutputs.length]))))
          (ihsLayersDenote (ihsLayersCodArity firstInputs.length
              [ihrSplitLayer firstInputs.length])
            (ihwCatLayers (ihrUnshuffle firstInputs.length)
              (ihwCatLayers
                (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
                (ihwCatLayers (ihrShuffle firstOutputs.length)
                  [ihrMergeLayer firstOutputs.length]))))
          midVec codVec
        <-> Exists fun firstScale => Exists fun secondScale =>
              midVec = ihnInterleave (ihqRowScale firstScale firstInputs)
                  (ihqRowScale secondScale secondInputs)
                /\ codVec = ihqRowAdd (ihqRowScale firstScale firstOutputs)
                  (ihqRowScale secondScale secondOutputs)) := by
    intro midVec
    rw [congrArg (fun startArity => ihsLayersDenote startArity
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))))
      hSplitCod]
    refine Iff.trans (ihwPairMemCast hSplitCod hFinalCod) ?_
    exact ihtUnshuffleRestDenote firstInputs firstOutputs secondInputs secondOutputs
      hInLen hOutLen midVec codVec
  refine Iff.trans (ihwPairMemCast (domWidth2 := firstInputs.length) rfl hFinalCod.symm) ?_
  refine Iff.trans (hCat domVec codVec) ?_
  refine Iff.trans (ihqComposeSpec firstInputs.length
    (ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length])
    (ihsLayersCodArity (ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length])
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))))
    (ihsLayersDenote firstInputs.length [ihrSplitLayer firstInputs.length])
    (ihsLayersDenote (ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length])
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length) [ihrMergeLayer firstOutputs.length]))))
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
                | intro firstScale hR1 =>
                    cases hR1 with
                    | intro secondScale hRFacts =>
                        have hRec := ihtInterleaveInj firstInputs.length pList qList
                          (ihqRowScale firstScale firstInputs)
                          (ihqRowScale secondScale secondInputs)
                          hSFacts.right.right.left hSFacts.right.right.right
                          (ihqRowScaleLength firstScale firstInputs)
                          ((ihqRowScaleLength secondScale secondInputs).trans hInLen.symm)
                          (hSFacts.right.left.symm.trans hRFacts.left)
                        refine Exists.intro firstScale (Exists.intro secondScale
                          (And.intro ?_ hRFacts.right))
                        rw [hSFacts.left, hRec.left, hRec.right]
  · intro hExists
    cases hExists with
    | intro firstScale hP1 =>
        cases hP1 with
        | intro secondScale hFacts =>
            refine Exists.intro (ihnInterleave (ihqRowScale firstScale firstInputs)
              (ihqRowScale secondScale secondInputs)) (And.intro ?_ ?_)
            · exact (hSplitEquiv (ihnInterleave (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs))).mpr
                (Exists.intro (ihqRowScale firstScale firstInputs)
                  (Exists.intro (ihqRowScale secondScale secondInputs)
                    (And.intro hFacts.left (And.intro rfl
                      (And.intro (ihqRowScaleLength firstScale firstInputs)
                        ((ihqRowScaleLength secondScale secondInputs).trans hInLen.symm))))))
            · exact (hRest2Equiv (ihnInterleave (ihqRowScale firstScale firstInputs)
                (ihqRowScale secondScale secondInputs))).mpr
                (Exists.intro firstScale (Exists.intro secondScale
                  (And.intro rfl hFacts.right)))

/-! ## Stage 6 — the two-row spatial sum: WF, cod arity, and the committed
statement inhabited VERBATIM (T3) -/

/-- The two-row-sum diagram is well-formed at the shared boundary. -/
theorem ihtTwoRowSumWF (firstInputs firstOutputs secondInputs secondOutputs : List QnfRat)
    (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length) :
    IhsDiagramWF (ihrTwoRowSumDiagram firstInputs firstOutputs secondInputs secondOutputs) := by
  show IhsLayersWF firstInputs.length
    (ihwCatLayers [ihrSplitLayer firstInputs.length]
      (ihwCatLayers (ihrUnshuffle firstInputs.length)
        (ihwCatLayers
          (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
          (ihwCatLayers (ihrShuffle firstOutputs.length)
            [ihrMergeLayer firstOutputs.length]))))
  refine ihwLayersWFCat [ihrSplitLayer firstInputs.length] _ ?_ ?_
  · exact IhsLayersWF.cons (ihtSplitLayerDomArity firstInputs.length) (IhsLayersWF.nil _)
  · rw [(show ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length]
        = firstInputs.length + firstInputs.length from ihtSplitLayerCodArity firstInputs.length)]
    exact ihtUnshuffleRestWF firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen

/-- The two-row-sum diagram maps `m -> n` at the shared boundary. -/
theorem ihtTwoRowSumCodArity (firstInputs firstOutputs secondInputs secondOutputs : List QnfRat)
    (hInLen : firstInputs.length = secondInputs.length)
    (hOutLen : firstOutputs.length = secondOutputs.length) :
    ihsDiagramCodArity (ihrTwoRowSumDiagram firstInputs firstOutputs secondInputs secondOutputs)
      = firstOutputs.length := by
  show ihsLayersCodArity firstInputs.length
      (ihwCatLayers [ihrSplitLayer firstInputs.length]
        (ihwCatLayers (ihrUnshuffle firstInputs.length)
          (ihwCatLayers
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
            (ihwCatLayers (ihrShuffle firstOutputs.length)
              [ihrMergeLayer firstOutputs.length])))) = firstOutputs.length
  rw [ihwLayersCodArityCat,
    (show ihsLayersCodArity firstInputs.length [ihrSplitLayer firstInputs.length]
      = firstInputs.length + firstInputs.length from ihtSplitLayerCodArity firstInputs.length)]
  exact ihtUnshuffleRestCodArity firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen

/-- DECIDED (T3): the committed owner-false `ihgTwoRowSpatialSumStatement` is
inhabited VERBATIM — the two-row-sum diagram `split ; unshuffle ;
(gadget TENSOR gadget) ; shuffle ; merge` is a WF `m -> n` diagram whose
denotation is relation-equal to the two-row matrix `[in1 ++ out1, in2 ++ out2]`. -/
theorem ihtTwoRowSpatialSum : ihgTwoRowSpatialSumStatement := by
  intro firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen
  refine Exists.intro
    (ihrTwoRowSumDiagram firstInputs firstOutputs secondInputs secondOutputs)
    (And.intro rfl (And.intro
      (ihtTwoRowSumCodArity firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen)
      (And.intro
        (ihtTwoRowSumWF firstInputs firstOutputs secondInputs secondOutputs hInLen hOutLen) ?_)))
  intro domVec codVec
  exact Iff.trans
    (ihtAssemblyDenote firstInputs firstOutputs secondInputs secondOutputs
      hInLen hOutLen domVec codVec)
    (ihtMinkowskiPairMem firstInputs firstOutputs secondInputs secondOutputs
      domVec codVec hInLen hOutLen)

/-- DECIDED (T3): the general two-row Minkowski spatial sum ships, superseding the
committed owner-false markers `ihgHasMultiRowRiffle` / `ihrHasTwoRowSpatialSum` /
`ihuHasTwoRowSpatialSum`. -/
def ihtHasTwoRowSpatialSum : Bool := true

/-! ## Stage 7 — kernel-decided fires -/

set_option maxHeartbeats 4000000 in
/-- T3 fire (fresh config the `ihr` instances never used, `m = 2`, `n = 1`): the
two-row sum of `[3,1|2]` and `[1,2|3]` span-equals the two-row matrix
`[[3,1,2],[1,2,3]]`. -/
theorem ihtFireTwoRowSumFresh :
    ihqSpanEqB (ihsDiagramDenote
        (ihrTwoRowSumDiagram [ihsScalarThree, qnfOne] [ihsScalarTwo]
          [qnfOne, ihsScalarTwo] [ihsScalarThree]))
      [[ihsScalarThree, qnfOne, ihsScalarTwo],
        [qnfOne, ihsScalarTwo, ihsScalarThree]] = true := rfl

set_option maxHeartbeats 4000000 in
/-- T3 FALSE control: the same fresh two-row sum is NOT the matrix with a
perturbed second row (span decision refutes). -/
theorem ihtFireTwoRowSumFreshWrong :
    ihqSpanEqB (ihsDiagramDenote
        (ihrTwoRowSumDiagram [ihsScalarThree, qnfOne] [ihsScalarTwo]
          [qnfOne, ihsScalarTwo] [ihsScalarThree]))
      [[ihsScalarThree, qnfOne, ihsScalarTwo],
        [qnfOne, ihsScalarTwo, qnfOne]] = false := rfl

/-- T3 CONTENT fire (routes through `ihtAssemblyDenote.mpr`, not a span `rfl`):
the fresh diagram relates the Minkowski point `1*[3,1] + 2*[1,2]` to
`1*[2] + 2*[3]` — the combination `(a, b) = (1, 2)` of the two lines. -/
theorem ihtFireTwoRowSumContent :
    IhqPairMem 2 1 (ihsDiagramDenote
        (ihrTwoRowSumDiagram [ihsScalarThree, qnfOne] [ihsScalarTwo]
          [qnfOne, ihsScalarTwo] [ihsScalarThree]))
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarThree, qnfOne])
        (ihqRowScale ihsScalarTwo [qnfOne, ihsScalarTwo]))
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarTwo])
        (ihqRowScale ihsScalarTwo [ihsScalarThree])) :=
  (ihtAssemblyDenote [ihsScalarThree, qnfOne] [ihsScalarTwo] [qnfOne, ihsScalarTwo]
      [ihsScalarThree] rfl rfl
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarThree, qnfOne])
        (ihqRowScale ihsScalarTwo [qnfOne, ihsScalarTwo]))
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarTwo])
        (ihqRowScale ihsScalarTwo [ihsScalarThree]))).mpr
    (Exists.intro qnfOne (Exists.intro ihsScalarTwo (And.intro rfl rfl)))

/-- T3 CONTENT fire (routes through `ihtMinkowskiPairMem.mpr`): the same
Minkowski point lies in the span of the two-row matrix `[[3,1,2],[1,2,3]]`. -/
theorem ihtFireMinkowskiRouting :
    IhqPairMem 2 1
        [ihqCat [ihsScalarThree, qnfOne] [ihsScalarTwo],
          ihqCat [qnfOne, ihsScalarTwo] [ihsScalarThree]]
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarThree, qnfOne])
        (ihqRowScale ihsScalarTwo [qnfOne, ihsScalarTwo]))
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarTwo])
        (ihqRowScale ihsScalarTwo [ihsScalarThree])) :=
  (ihtMinkowskiPairMem [ihsScalarThree, qnfOne] [ihsScalarTwo] [qnfOne, ihsScalarTwo]
      [ihsScalarThree]
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarThree, qnfOne])
        (ihqRowScale ihsScalarTwo [qnfOne, ihsScalarTwo]))
      (ihqRowAdd (ihqRowScale qnfOne [ihsScalarTwo])
        (ihqRowScale ihsScalarTwo [ihsScalarThree])) rfl rfl).mp
    (Exists.intro qnfOne (Exists.intro ihsScalarTwo (And.intro rfl rfl)))

/-! ## Stage 8 — toward `ihzNormalFormStatement`: the two-row NF carrier (T4) -/

/-- T4 (started): the `R = 2` instance of the committed `ihzNormalFormStatement`.
Any two-row matrix `[firstRow, secondRow]` (rows of width `domWidth + codWidth`)
is denoted by SOME WF `domWidth -> codWidth` diagram — split each row into its
input / output halves and Minkowski-sum the two lines via `ihtTwoRowSpatialSum`. -/
theorem ihtTwoRowNormalFormCarrier (domWidth codWidth : Nat)
    (firstRow secondRow : List QnfRat)
    (hAll : IhqAllWidth (domWidth + codWidth) [firstRow, secondRow]) :
    Exists fun nfDiagram =>
      nfDiagram.sourceArity = domWidth
        /\ ihsDiagramCodArity nfDiagram = codWidth
        /\ IhsDiagramWF nfDiagram
        /\ IhsRelEquiv domWidth codWidth (ihsDiagramDenote nfDiagram)
            [firstRow, secondRow] := by
  have hRow1Len : firstRow.length = domWidth + codWidth := by
    cases hAll with
    | cons hHead1 _hRest => exact hHead1
  have hRow2Len : secondRow.length = domWidth + codWidth := by
    cases hAll with
    | cons _hHead1 hRest =>
        cases hRest with
        | cons hHead2 _hNil => exact hHead2
  have hIn1Len : (ihqTakeN domWidth firstRow).length = domWidth :=
    ihqTakeNLength firstRow domWidth codWidth hRow1Len
  have hOut1Len : (ihqDropN domWidth firstRow).length = codWidth :=
    ihqDropNLength firstRow domWidth codWidth hRow1Len
  have hIn2Len : (ihqTakeN domWidth secondRow).length = domWidth :=
    ihqTakeNLength secondRow domWidth codWidth hRow2Len
  have hOut2Len : (ihqDropN domWidth secondRow).length = codWidth :=
    ihqDropNLength secondRow domWidth codWidth hRow2Len
  have hCat1 : ihqCat (ihqTakeN domWidth firstRow) (ihqDropN domWidth firstRow) = firstRow :=
    ihqCatTakeDrop firstRow domWidth codWidth hRow1Len
  have hCat2 : ihqCat (ihqTakeN domWidth secondRow) (ihqDropN domWidth secondRow) = secondRow :=
    ihqCatTakeDrop secondRow domWidth codWidth hRow2Len
  cases ihtTwoRowSpatialSum (ihqTakeN domWidth firstRow) (ihqDropN domWidth firstRow)
    (ihqTakeN domWidth secondRow) (ihqDropN domWidth secondRow)
    (hIn1Len.trans hIn2Len.symm) (hOut1Len.trans hOut2Len.symm) with
  | intro nfDiagram hProps =>
      have hRelEquiv := hProps.right.right.right
      rw [hIn1Len, hOut1Len, hCat1, hCat2] at hRelEquiv
      refine Exists.intro nfDiagram (And.intro (hProps.left.trans hIn1Len)
        (And.intro (hProps.right.left.trans hOut1Len)
          (And.intro hProps.right.right.left hRelEquiv)))

/-- OWNER FALSE — the general `R`-row NF compiler (`ihzNormalFormStatement`) is
NOT proven this brick.  What IS shipped toward it: the single-row base
(`ihgSingleRowNormalForm`, committed) and the two-row carrier
(`ihtTwoRowNormalFormCarrier`).  THE RESIDUAL (the honest wall): the row-list
recursion `span (row :: rest) = span [row] + span rest` needs the GENERAL
spatial sum of a single-row gadget with an ARBITRARY sub-diagram — i.e. the
diagram tensor `(gadget TENSOR subDiagram)` denotation with the second factor
abstracted from a line span (`ihgGadgetDenote`) to an arbitrary WF relation, then
the `split ; unshuffle ; (gadget TENSOR subDiagram) ; shuffle ; merge` assembly
at the shared boundary and the row-at-a-time accumulation.  This is a distinct
BUILD (generalizing `ihtGadgetTensorDenote` / `ihtAssemblyDenote` in the second
factor), not a wall of principle. -/
def ihtHasNormalFormCompiler : Bool := false

end FX1Poly.ComputerAlgebra
