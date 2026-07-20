import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfNormalForm

/-! # LinearAlgebra/InteractingHopfShuffleDenote — the perfect (un)shuffle
denotation and the two-row spatial sum (WP-PROP-3 brick 9)

Discharging the brick-8 residuals `ihnUnshuffleDenoteStatement` /
`ihnShuffleDenoteStatement` (the faithful block-transpose denotations) and the
committed `ihgTwoRowSpatialSumStatement`.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfShuffleDenote.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — width arithmetic and the unshuffle arity/WF bookkeeping -/

/-- The unshuffle running width in canonical `2 + (·)` form. -/
theorem ihuWidthCanon (blockWidth : Nat) :
    (blockWidth + 1) + (blockWidth + 1) = 2 + (blockWidth + blockWidth) := by
  rw [Nat.add_comm 2 (blockWidth + blockWidth),
    Nat.add_assoc blockWidth blockWidth 2,
    Nat.add_assoc blockWidth 1 (blockWidth + 1),
    Nat.add_comm 1 (blockWidth + 1),
    Nat.add_assoc blockWidth 1 1]

/-- The unshuffle running width in the move-right `1 + (1 + (·))` form. -/
theorem ihuWidthMove (blockWidth : Nat) :
    (blockWidth + 1) + (blockWidth + 1) = 1 + (1 + (blockWidth + blockWidth)) := by
  rw [ihuWidthCanon blockWidth]
  exact Nat.add_assoc 1 1 (blockWidth + blockWidth)

/-- The perfect unshuffle preserves arity: `ihrUnshuffle m` runs `2m -> 2m`. -/
theorem ihuUnshuffleCodArity : (blockWidth : Nat) ->
    ihsLayersCodArity (blockWidth + blockWidth) (ihrUnshuffle blockWidth)
      = blockWidth + blockWidth
  | 0 => rfl
  | blockWidth + 1 => by
      show ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihwCatLayers (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
            (ihrMoveRight 1 blockWidth blockWidth))
        = (blockWidth + 1) + (blockWidth + 1)
      rw [ihwLayersCodArityCat ((blockWidth + 1) + (blockWidth + 1))
        (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
        (ihrMoveRight 1 blockWidth blockWidth)]
      have hWhiskerCod :
          ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
              (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
            = (blockWidth + 1) + (blockWidth + 1) := by
        have hCanon : (blockWidth + 1) + (blockWidth + 1)
            = 2 + ((blockWidth + blockWidth) + 0) := ihuWidthCanon blockWidth
        rw [hCanon, ihwWhiskerLayersCodArity 2 0 (ihrUnshuffle blockWidth)
          (blockWidth + blockWidth), ihuUnshuffleCodArity blockWidth]
      rw [hWhiskerCod]
      have hMoveCanon : (blockWidth + 1) + (blockWidth + 1)
          = 1 + (1 + (blockWidth + blockWidth)) := ihuWidthMove blockWidth
      rw [hMoveCanon]
      exact ihrMoveRightCodArity 1 blockWidth blockWidth

/-- The perfect unshuffle is well-formed at `2m`. -/
theorem ihuUnshuffleWF : (blockWidth : Nat) ->
    IhsLayersWF (blockWidth + blockWidth) (ihrUnshuffle blockWidth)
  | 0 => IhsLayersWF.nil (0 + 0)
  | blockWidth + 1 => by
      show IhsLayersWF ((blockWidth + 1) + (blockWidth + 1))
        (ihwCatLayers (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
          (ihrMoveRight 1 blockWidth blockWidth))
      refine ihwLayersWFCat (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
        (ihrMoveRight 1 blockWidth blockWidth) ?_ ?_
      · exact ihsLayersWFCast (ihuWidthCanon blockWidth).symm
          (ihwWhiskerLayersWF 2 0 (ihrUnshuffle blockWidth) (ihuUnshuffleWF blockWidth))
      · have hWhiskerCod :
            ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
                (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
              = (blockWidth + 1) + (blockWidth + 1) := by
          have hCanon : (blockWidth + 1) + (blockWidth + 1)
              = 2 + ((blockWidth + blockWidth) + 0) := ihuWidthCanon blockWidth
          rw [hCanon, ihwWhiskerLayersCodArity 2 0 (ihrUnshuffle blockWidth)
            (blockWidth + blockWidth), ihuUnshuffleCodArity blockWidth]
        rw [hWhiskerCod]
        exact ihsLayersWFCast (ihuWidthMove blockWidth).symm
          (ihrMoveRightWF 1 blockWidth blockWidth)

/-- Running cod arity of the whiskered smaller unshuffle at the full width. -/
theorem ihuWhiskerACod (blockWidth : Nat) :
    ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
        (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
      = (blockWidth + 1) + (blockWidth + 1) := by
  have hCanon : (blockWidth + 1) + (blockWidth + 1)
      = 2 + ((blockWidth + blockWidth) + 0) := ihuWidthCanon blockWidth
  rw [hCanon, ihwWhiskerLayersCodArity 2 0 (ihrUnshuffle blockWidth)
    (blockWidth + blockWidth), ihuUnshuffleCodArity blockWidth]

/-! ## Stage 1 — the whisker-left pair-membership spec -/

/-- Whiskering a window by `leftContext` wires on the left and none on the right
denotes: keep the first `leftContext` strands fixed, run the window on the rest. -/
theorem ihuWhiskerLeftSpec (leftContext currentArity : Nat)
    (window : List (List IhsCell)) (hWindowWF : IhsLayersWF currentArity window)
    (domVec codVec : List QnfRat) :
    IhqPairMem (leftContext + (currentArity + 0))
        (leftContext + (ihsLayersCodArity currentArity window + 0))
        (ihsLayersDenote (leftContext + (currentArity + 0))
          (ihwWhiskerLayers leftContext 0 window)) domVec codVec
      <-> Exists fun leftPart => Exists fun innerDom => Exists fun innerCod =>
            domVec = ihqCat leftPart innerDom
              /\ codVec = ihqCat leftPart innerCod
              /\ leftPart.length = leftContext
              /\ IhqPairMem currentArity (ihsLayersCodArity currentArity window)
                  (ihsLayersDenote currentArity window) innerDom innerCod := by
  have hWindowAll : IhqAllWidth
      (currentArity + ihsLayersCodArity currentArity window)
      (ihsLayersDenote currentArity window) :=
    ihsLayersDenoteWidth window hWindowWF
  have hInnerAll : IhqAllWidth
      ((currentArity + 0) + (ihsLayersCodArity currentArity window + 0))
      (ihsTensorRows currentArity (ihsLayersCodArity currentArity window) 0 0
        (ihsLayersDenote currentArity window) (ihqIdRows 0)) :=
    ihsTensorRowsWidth currentArity (ihsLayersCodArity currentArity window) 0 0
      (ihsLayersDenote currentArity window) (ihqIdRows 0)
      hWindowAll (ihqIdRowsWidth 0)
  refine Iff.trans (ihwWhiskerLayersDenote leftContext 0 window hWindowWF
    domVec codVec) ?_
  refine Iff.trans (ihwTensorSpec leftContext leftContext (currentArity + 0)
    (ihsLayersCodArity currentArity window + 0) (ihqIdRows leftContext)
    (ihsTensorRows currentArity (ihsLayersCodArity currentArity window) 0 0
      (ihsLayersDenote currentArity window) (ihqIdRows 0))
    (ihqIdRowsWidth leftContext) hInnerAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro leftDomVec hPack1 =>
        cases hPack1 with
        | intro innerDomVec hPack2 =>
            cases hPack2 with
            | intro leftCodVec hPack3 =>
                cases hPack3 with
                | intro innerCodVec hFacts =>
                    have hLeftSame := (ihsIdSpec leftContext leftDomVec leftCodVec).mp
                      hFacts.right.right.left
                    have hInnerWindow := (ihwTensorUnitRight currentArity
                      (ihsLayersCodArity currentArity window)
                      (ihsLayersDenote currentArity window) hWindowAll
                      innerDomVec innerCodVec).mp hFacts.right.right.right
                    refine Exists.intro leftDomVec (Exists.intro innerDomVec
                      (Exists.intro innerCodVec (And.intro hFacts.left (And.intro ?_
                        (And.intro hLeftSame.right hInnerWindow)))))
                    rw [hFacts.right.left, hLeftSame.left]
  · intro hExists
    cases hExists with
    | intro leftPart hPack1 =>
        cases hPack1 with
        | intro innerDom hPack2 =>
            cases hPack2 with
            | intro innerCod hFacts =>
                refine Exists.intro leftPart (Exists.intro innerDom
                  (Exists.intro leftPart (Exists.intro innerCod
                    (And.intro hFacts.left (And.intro hFacts.right.left
                      (And.intro ?_ ?_))))))
                · exact (ihsIdSpec leftContext leftPart leftPart).mpr
                    (And.intro rfl hFacts.right.right.left)
                · exact (ihwTensorUnitRight currentArity
                    (ihsLayersCodArity currentArity window)
                    (ihsLayersDenote currentArity window) hWindowAll
                    innerDom innerCod).mpr hFacts.right.right.right

/-- The whiskered smaller unshuffle at full width: keep the first two strands
fixed, run the smaller unshuffle on the rest — folded to the full-width boundary
and the smaller unshuffle's own boundary. -/
theorem ihuWhiskeredUnshuffleSpec (blockWidth : Nat) (domVec midVec : List QnfRat) :
    IhqPairMem ((blockWidth + 1) + (blockWidth + 1)) ((blockWidth + 1) + (blockWidth + 1))
        (ihsLayersDenote ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))) domVec midVec
      <-> Exists fun leftHead => Exists fun innerDom => Exists fun innerCod =>
            domVec = ihqCat leftHead innerDom
              /\ midVec = ihqCat leftHead innerCod
              /\ leftHead.length = 2
              /\ IhqPairMem (blockWidth + blockWidth) (blockWidth + blockWidth)
                  (ihsLayersDenote (blockWidth + blockWidth) (ihrUnshuffle blockWidth))
                  innerDom innerCod := by
  have hSpec := ihuWhiskerLeftSpec 2 (blockWidth + blockWidth) (ihrUnshuffle blockWidth)
    (ihuUnshuffleWF blockWidth) domVec midVec
  rw [ihuUnshuffleCodArity blockWidth] at hSpec
  rw [show (2 : Nat) + ((blockWidth + blockWidth) + 0) = (blockWidth + 1) + (blockWidth + 1)
      from (ihuWidthCanon blockWidth).symm] at hSpec
  exact hSpec

/-! ## Stage 2 — THE UNSHUFFLE DENOTATION (T1) -/

/-- THE FAITHFUL UNSHUFFLE DENOTATION: the perfect unshuffle `ihrUnshuffle m`
relates the interleaved layout `ihnInterleave pList qList` to the block layout
`ihqCat pList qList`, at every width, by structural recursion on `m`.  The step
splits the diagram into the whiskered smaller unshuffle (head pair fixed) followed
by the head-strand move-past-block cascade `ihrMoveRight 1 m m`. -/
theorem ihuUnshuffleDenote : (blockWidth : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem (blockWidth + blockWidth) (blockWidth + blockWidth)
        (ihsLayersDenote (blockWidth + blockWidth) (ihrUnshuffle blockWidth))
        domVec codVec
      <-> Exists fun pList => Exists fun qList =>
            domVec = ihnInterleave pList qList
              /\ codVec = ihqCat pList qList
              /\ pList.length = blockWidth
              /\ qList.length = blockWidth)
  | 0, domVec, codVec => by
      refine Iff.trans (ihsIdSpec 0 domVec codVec) (Iff.intro ?_ ?_)
      · intro hSame
        have hDomNil : domVec = [] := ihsLengthZeroNil domVec hSame.right
        refine Exists.intro [] (Exists.intro [] (And.intro hDomNil (And.intro ?_
          (And.intro rfl rfl))))
        rw [<- hSame.left]
        exact hDomNil
      · intro hSpec
        cases hSpec with
        | intro pList hRest =>
            cases hRest with
            | intro qList hFacts =>
                have hPnil : pList = [] := ihsLengthZeroNil pList hFacts.right.right.left
                have hQnil : qList = [] :=
                  ihsLengthZeroNil qList hFacts.right.right.right
                refine And.intro ?_ ?_
                · rw [hFacts.left, hFacts.right.left, hPnil, hQnil]
                  rfl
                · rw [hFacts.left, hPnil, hQnil]
                  rfl
  | blockWidth + 1, domVec, codVec => by
      have hACod : ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
          = (blockWidth + 1) + (blockWidth + 1) := ihuWhiskerACod blockWidth
      have hAWF : IhsLayersWF ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)) :=
        ihsLayersWFCast (ihuWidthCanon blockWidth).symm
          (ihwWhiskerLayersWF 2 0 (ihrUnshuffle blockWidth) (ihuUnshuffleWF blockWidth))
      have hBWF : IhsLayersWF (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
          (ihrMoveRight 1 blockWidth blockWidth) :=
        ihsLayersWFCast hACod.symm (ihsLayersWFCast (ihuWidthMove blockWidth).symm
          (ihrMoveRightWF 1 blockWidth blockWidth))
      have hBCod : ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihrMoveRight 1 blockWidth blockWidth) = (blockWidth + 1) + (blockWidth + 1) := by
        rw [ihuWidthMove blockWidth]
        exact ihrMoveRightCodArity 1 blockWidth blockWidth
      have hFinalCod : ihsLayersCodArity (ihsLayersCodArity
          ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
          (ihrMoveRight 1 blockWidth blockWidth) = (blockWidth + 1) + (blockWidth + 1) := by
        rw [hACod]
        exact hBCod
      have hAAll := ihsLayersDenoteWidth
        (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)) hAWF
      have hBAll := ihsLayersDenoteWidth (ihrMoveRight 1 blockWidth blockWidth) hBWF
      have hCat := ihwLayersDenoteCat
        (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
        (ihrMoveRight 1 blockWidth blockWidth) hAWF hBWF
      -- the whiskered-unshuffle factor characterization (via the IH)
      have hWhiskEquiv : (midVec : List QnfRat) ->
          (IhqPairMem ((blockWidth + 1) + (blockWidth + 1))
              (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
                (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
              (ihsLayersDenote ((blockWidth + 1) + (blockWidth + 1))
                (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))) domVec midVec
            <-> Exists fun leftHead => Exists fun pTail => Exists fun qTail =>
                  domVec = ihqCat leftHead (ihnInterleave pTail qTail)
                    /\ midVec = ihqCat leftHead (ihqCat pTail qTail)
                    /\ leftHead.length = 2
                    /\ pTail.length = blockWidth
                    /\ qTail.length = blockWidth) := by
        intro midVec
        refine Iff.trans (ihwPairMemCast rfl hACod) ?_
        refine Iff.trans (ihuWhiskeredUnshuffleSpec blockWidth domVec midVec) ?_
        refine Iff.intro ?_ ?_
        · intro hW
          cases hW with
          | intro leftHead hW1 =>
              cases hW1 with
              | intro innerDom hW2 =>
                  cases hW2 with
                  | intro innerCod hWF =>
                      cases (ihuUnshuffleDenote blockWidth innerDom innerCod).mp
                        hWF.right.right.right with
                      | intro pTail hP1 =>
                          cases hP1 with
                          | intro qTail hPF =>
                              refine Exists.intro leftHead (Exists.intro pTail
                                (Exists.intro qTail (And.intro ?_ (And.intro ?_
                                  (And.intro hWF.right.right.left
                                    (And.intro hPF.right.right.left
                                      hPF.right.right.right))))))
                              · rw [hWF.left, hPF.left]
                              · rw [hWF.right.left, hPF.right.left]
        · intro hR
          cases hR with
          | intro leftHead hR1 =>
              cases hR1 with
              | intro pTail hR2 =>
                  cases hR2 with
                  | intro qTail hRF =>
                      refine Exists.intro leftHead (Exists.intro (ihnInterleave pTail qTail)
                        (Exists.intro (ihqCat pTail qTail) (And.intro hRF.left
                          (And.intro hRF.right.left (And.intro hRF.right.right.left ?_)))))
                      exact (ihuUnshuffleDenote blockWidth (ihnInterleave pTail qTail)
                          (ihqCat pTail qTail)).mpr
                        (Exists.intro pTail (Exists.intro qTail (And.intro rfl (And.intro rfl
                          (And.intro hRF.right.right.right.left
                            hRF.right.right.right.right)))))
      -- the move-past-block factor characterization (via the T1 cascade denotation)
      have hMoveEquiv : (midVec : List QnfRat) ->
          (IhqPairMem (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
                (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
              (ihsLayersCodArity (ihsLayersCodArity
                ((blockWidth + 1) + (blockWidth + 1))
                (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
                (ihrMoveRight 1 blockWidth blockWidth))
              (ihsLayersDenote (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
                (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
                (ihrMoveRight 1 blockWidth blockWidth)) midVec codVec
            <-> ihnMovePairSpec 1 blockWidth blockWidth midVec codVec) := by
        intro midVec
        rw [congrArg (fun ar => ihsLayersDenote ar (ihrMoveRight 1 blockWidth blockWidth))
          (hACod.trans (ihuWidthMove blockWidth))]
        refine Iff.trans (ihwPairMemCast (hACod.trans (ihuWidthMove blockWidth))
          (hFinalCod.trans (ihuWidthMove blockWidth))) ?_
        exact ihnMoveRightDenote 1 blockWidth blockWidth midVec codVec
      -- split the cascade, characterize both factors, reconcile the shared middle
      refine Iff.trans (ihwPairMemCast rfl hFinalCod.symm) ?_
      refine Iff.trans (hCat domVec codVec) ?_
      refine Iff.trans (ihqComposeSpec ((blockWidth + 1) + (blockWidth + 1))
        (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
        (ihsLayersCodArity (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
          (ihrMoveRight 1 blockWidth blockWidth))
        (ihsLayersDenote ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
        (ihsLayersDenote (ihsLayersCodArity ((blockWidth + 1) + (blockWidth + 1))
          (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth)))
          (ihrMoveRight 1 blockWidth blockWidth))
        hAAll hBAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hExists
        cases hExists with
        | intro midVec hParts =>
            cases (hWhiskEquiv midVec).mp hParts.left with
            | intro leftHead hW1 =>
                cases hW1 with
                | intro pTail hW2 =>
                    cases hW2 with
                    | intro qTail hWFacts =>
                        cases ihzLengthTwoShape leftHead hWFacts.right.right.left with
                        | intro headP hLH1 =>
                            cases hLH1 with
                            | intro headQ hLHeq =>
                                cases (hMoveEquiv midVec).mp hParts.right with
                                | intro leftPart hM1 =>
                                    cases hM1 with
                                    | intro movingWire hM2 =>
                                        cases hM2 with
                                        | intro blockPart hM3 =>
                                            cases hM3 with
                                            | intro rightPart hMFacts =>
                                                cases ihzLengthOneShape leftPart
                                                  hMFacts.right.right.left with
                                                | intro pivot hLPeq =>
                                                    have hMidEq :
                                                        ihqCat leftHead
                                                            (ihqCat pTail qTail)
                                                          = ihqCat leftPart (ihqCat
                                                              [movingWire] (ihqCat
                                                                blockPart rightPart)) :=
                                                      hWFacts.right.left.symm.trans
                                                        hMFacts.left
                                                    rw [hLHeq, hLPeq] at hMidEq
                                                    have hHeadP : headP = pivot :=
                                                      congrArg (fun r => ihqGetCoeff r 0)
                                                        hMidEq
                                                    have hHeadQ : headQ = movingWire :=
                                                      congrArg (fun r => ihqGetCoeff r 1)
                                                        hMidEq
                                                    have hBlocks : ihqCat pTail qTail
                                                        = ihqCat blockPart rightPart :=
                                                      congrArg (fun r => ihqDropN 2 r)
                                                        hMidEq
                                                    have hSplit := ihqCatInj pTail qTail
                                                      blockPart rightPart
                                                      (by rw
                                                        [hWFacts.right.right.right.left,
                                                          hMFacts.right.right.right.left])
                                                      hBlocks
                                                    refine Exists.intro (headP :: pTail)
                                                      (Exists.intro (headQ :: qTail)
                                                        (And.intro ?_ (And.intro ?_
                                                          (And.intro ?_ ?_))))
                                                    · rw [hWFacts.left, hLHeq]
                                                      rfl
                                                    · rw [hMFacts.right.left, hLPeq,
                                                        <- hHeadP, <- hHeadQ,
                                                        <- hSplit.left, <- hSplit.right]
                                                      rfl
                                                    · exact congrArg (fun k => k + 1)
                                                        hWFacts.right.right.right.left
                                                    · exact congrArg (fun k => k + 1)
                                                        hWFacts.right.right.right.right
      · intro hSpec
        cases hSpec with
        | intro pList hS1 =>
            cases hS1 with
            | intro qList hSFacts =>
                cases pList with
                | nil => exact nomatch hSFacts.right.right.left
                | cons headP pRest =>
                    cases qList with
                    | nil => exact nomatch hSFacts.right.right.right
                    | cons headQ qRest =>
                        have hPRestLen : pRest.length = blockWidth :=
                          Nat.succ.inj hSFacts.right.right.left
                        have hQRestLen : qRest.length = blockWidth :=
                          Nat.succ.inj hSFacts.right.right.right
                        refine Exists.intro
                          (ihqCat [headP, headQ] (ihqCat pRest qRest)) (And.intro ?_ ?_)
                        · refine (hWhiskEquiv
                            (ihqCat [headP, headQ] (ihqCat pRest qRest))).mpr ?_
                          refine Exists.intro [headP, headQ] (Exists.intro pRest
                            (Exists.intro qRest (And.intro ?_ (And.intro rfl (And.intro rfl
                              (And.intro hPRestLen hQRestLen))))))
                          rw [hSFacts.left]
                          rfl
                        · refine (hMoveEquiv
                            (ihqCat [headP, headQ] (ihqCat pRest qRest))).mpr ?_
                          refine Exists.intro [headP] (Exists.intro headQ (Exists.intro pRest
                            (Exists.intro qRest (And.intro rfl (And.intro ?_ (And.intro rfl
                              (And.intro hPRestLen hQRestLen)))))))
                          rw [hSFacts.right.left]
                          rfl

/-- DECIDED (T1): the committed owner-false `ihnUnshuffleDenoteStatement` is
inhabited by the faithful unshuffle denotation. -/
theorem ihuUnshuffleDenoteHolds : ihnUnshuffleDenoteStatement :=
  ihuUnshuffleDenote

/-- DECIDED (T1): the perfect unshuffle ships its faithful block-transpose
denotation, superseding the committed owner-false `ihnHasUnshuffleDenote`. -/
def ihuHasUnshuffleDenote : Bool := true

set_option maxHeartbeats 4000000 in
/-- T1 CONTENT fire (routes through `ihuUnshuffleDenote`, not a span `rfl`): the
unshuffle `ihrUnshuffle 2` relates the interleaved input `[2, 3, 1, 1]` to the
block output `[2, 1, 3, 1]` — the pair `p = [2, 1]`, `q = [3, 1]` woven then
un-woven. -/
theorem ihuFireUnshuffleContent :
    IhqPairMem 4 4 (ihsLayersDenote 4 (ihrUnshuffle 2))
      [ihsScalarTwo, ihsScalarThree, qnfOne, qnfOne]
      [ihsScalarTwo, qnfOne, ihsScalarThree, qnfOne] :=
  (ihuUnshuffleDenote 2 [ihsScalarTwo, ihsScalarThree, qnfOne, qnfOne]
      [ihsScalarTwo, qnfOne, ihsScalarThree, qnfOne]).mpr
    (Exists.intro [ihsScalarTwo, qnfOne] (Exists.intro [ihsScalarThree, qnfOne]
      (And.intro rfl (And.intro rfl (And.intro rfl rfl)))))

/-! ## Stage 3 — the shuffle: propext-free reverse structure and the
crossing-self-inverse fact (T1 shuffle scaffolding) -/

/-- `ihwCatLayers` is associative (layer-list append). -/
theorem ihuCatLayersAssoc : (firstLayers secondLayers thirdLayers : List (List IhsCell)) ->
    ihwCatLayers (ihwCatLayers firstLayers secondLayers) thirdLayers
      = ihwCatLayers firstLayers (ihwCatLayers secondLayers thirdLayers)
  | [], _secondLayers, _thirdLayers => rfl
  | headLayer :: restLayers, secondLayers, thirdLayers =>
      congrArg (fun tailLayers => headLayer :: tailLayers)
        (ihuCatLayersAssoc restLayers secondLayers thirdLayers)

/-- `List.reverseAux` as a `ihwCatLayers` — the propext-free replacement for the
propext-leaking `List.reverseAux_eq`. -/
theorem ihuReverseAuxCat : (layers accumulator : List (List IhsCell)) ->
    List.reverseAux layers accumulator
      = ihwCatLayers (List.reverseAux layers []) accumulator
  | [], _accumulator => rfl
  | headLayer :: restLayers, accumulator => by
      show List.reverseAux restLayers (headLayer :: accumulator)
        = ihwCatLayers (List.reverseAux restLayers [headLayer]) accumulator
      rw [ihuReverseAuxCat restLayers (headLayer :: accumulator),
        ihuReverseAuxCat restLayers [headLayer], ihuCatLayersAssoc]
      rfl

/-- Reversing a cons layer list snocs the head — the propext-free replacement for
`List.reverse_cons`. -/
theorem ihuReverseConsCat (headLayer : List IhsCell) (restLayers : List (List IhsCell)) :
    List.reverse (headLayer :: restLayers)
      = ihwCatLayers (List.reverse restLayers) [headLayer] := by
  show List.reverseAux restLayers [headLayer]
    = ihwCatLayers (List.reverseAux restLayers []) [headLayer]
  exact ihuReverseAuxCat restLayers [headLayer]

/-- THE CROSSING IS SELF-INVERSE: the atomic swap layer relates a pair in one
order iff it relates it in the other — an adjacent transposition is its own
converse.  The base fact the layer-reverse-is-converse bridge rests on. -/
theorem ihuSwapSelfConverse (leftContext rightContext : Nat) (domVec codVec : List QnfRat) :
    IhqPairMem (leftContext + (2 + rightContext)) (leftContext + (2 + rightContext))
        (ihsLayerDenote (ihrSwapLayer leftContext rightContext)) domVec codVec
      <-> IhqPairMem (leftContext + (2 + rightContext)) (leftContext + (2 + rightContext))
        (ihsLayerDenote (ihrSwapLayer leftContext rightContext)) codVec domVec := by
  refine Iff.trans (ihrSwapLayerDenote leftContext rightContext domVec codVec) ?_
  refine Iff.trans ?_ (ihrSwapLayerDenote leftContext rightContext codVec domVec).symm
  refine Iff.intro ?_ ?_
  · intro hFwd
    cases hFwd with
    | intro leftPart hF1 =>
        cases hF1 with
        | intro firstMid hF2 =>
            cases hF2 with
            | intro secondMid hF3 =>
                cases hF3 with
                | intro rightPart hFacts =>
                    exact Exists.intro leftPart (Exists.intro secondMid
                      (Exists.intro firstMid (Exists.intro rightPart
                        (And.intro hFacts.right.left (And.intro hFacts.left
                          (And.intro hFacts.right.right.left
                            hFacts.right.right.right))))))
  · intro hBwd
    cases hBwd with
    | intro leftPart hB1 =>
        cases hB1 with
        | intro firstMid hB2 =>
            cases hB2 with
            | intro secondMid hB3 =>
                cases hB3 with
                | intro rightPart hFacts =>
                    exact Exists.intro leftPart (Exists.intro secondMid
                      (Exists.intro firstMid (Exists.intro rightPart
                        (And.intro hFacts.right.left (And.intro hFacts.left
                          (And.intro hFacts.right.right.left
                            hFacts.right.right.right))))))

/-! ## Stage 4 — reversibility: each layer square and self-converse -/

/-- Whiskering by `leftContext` wires left and none right: the single-layer
pair-membership spec (keep the first `leftContext` strands fixed). -/
theorem ihuWhiskerLayerLeftSpec (leftContext : Nat) (layer : List IhsCell)
    (domVec codVec : List QnfRat) :
    IhqPairMem (leftContext + (ihsLayerDomArity layer + 0))
        (leftContext + (ihsLayerCodArity layer + 0))
        (ihsLayerDenote (ihwWhiskerLayer leftContext 0 layer)) domVec codVec
      <-> Exists fun leftPart => Exists fun innerDom => Exists fun innerCod =>
            domVec = ihqCat leftPart innerDom
              /\ codVec = ihqCat leftPart innerCod
              /\ leftPart.length = leftContext
              /\ IhqPairMem (ihsLayerDomArity layer) (ihsLayerCodArity layer)
                  (ihsLayerDenote layer) innerDom innerCod := by
  have hLayerAll : IhqAllWidth (ihsLayerDomArity layer + ihsLayerCodArity layer)
      (ihsLayerDenote layer) := ihsLayerDenoteWidth layer
  have hInnerAll : IhqAllWidth
      ((ihsLayerDomArity layer + 0) + (ihsLayerCodArity layer + 0))
      (ihsTensorRows (ihsLayerDomArity layer) (ihsLayerCodArity layer) 0 0
        (ihsLayerDenote layer) (ihqIdRows 0)) :=
    ihsTensorRowsWidth (ihsLayerDomArity layer) (ihsLayerCodArity layer) 0 0
      (ihsLayerDenote layer) (ihqIdRows 0) hLayerAll (ihqIdRowsWidth 0)
  refine Iff.trans (ihwWhiskerLayerDenote leftContext 0 layer domVec codVec) ?_
  refine Iff.trans (ihwTensorSpec leftContext leftContext
    (ihsLayerDomArity layer + 0) (ihsLayerCodArity layer + 0) (ihqIdRows leftContext)
    (ihsTensorRows (ihsLayerDomArity layer) (ihsLayerCodArity layer) 0 0
      (ihsLayerDenote layer) (ihqIdRows 0))
    (ihqIdRowsWidth leftContext) hInnerAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hExists
    cases hExists with
    | intro leftDomVec hPack1 =>
        cases hPack1 with
        | intro innerDomVec hPack2 =>
            cases hPack2 with
            | intro leftCodVec hPack3 =>
                cases hPack3 with
                | intro innerCodVec hFacts =>
                    have hLeftSame := (ihsIdSpec leftContext leftDomVec leftCodVec).mp
                      hFacts.right.right.left
                    have hInner := (ihwTensorUnitRight (ihsLayerDomArity layer)
                      (ihsLayerCodArity layer) (ihsLayerDenote layer) hLayerAll
                      innerDomVec innerCodVec).mp hFacts.right.right.right
                    refine Exists.intro leftDomVec (Exists.intro innerDomVec
                      (Exists.intro innerCodVec (And.intro hFacts.left (And.intro ?_
                        (And.intro hLeftSame.right hInner)))))
                    rw [hFacts.right.left, hLeftSame.left]
  · intro hExists
    cases hExists with
    | intro leftPart hPack1 =>
        cases hPack1 with
        | intro innerDom hPack2 =>
            cases hPack2 with
            | intro innerCod hFacts =>
                refine Exists.intro leftPart (Exists.intro innerDom
                  (Exists.intro leftPart (Exists.intro innerCod
                    (And.intro hFacts.left (And.intro hFacts.right.left
                      (And.intro ?_ ?_))))))
                · exact (ihsIdSpec leftContext leftPart leftPart).mpr
                    (And.intro rfl hFacts.right.right.left)
                · exact (ihwTensorUnitRight (ihsLayerDomArity layer)
                    (ihsLayerCodArity layer) (ihsLayerDenote layer) hLayerAll
                    innerDom innerCod).mpr hFacts.right.right.right

/-- Whiskering preserves self-converse: if a square layer is its own converse,
so is that layer whiskered by wires on the left. -/
theorem ihuWhiskerLayerSelfConverse (leftContext innerWidth : Nat) (layer : List IhsCell)
    (hDom : ihsLayerDomArity layer = innerWidth)
    (hCod : ihsLayerCodArity layer = innerWidth)
    (hSelf : (firstVec secondVec : List QnfRat) ->
      (IhqPairMem innerWidth innerWidth (ihsLayerDenote layer) firstVec secondVec
        <-> IhqPairMem innerWidth innerWidth (ihsLayerDenote layer) secondVec firstVec))
    (domVec codVec : List QnfRat) :
    IhqPairMem (leftContext + (innerWidth + 0)) (leftContext + (innerWidth + 0))
        (ihsLayerDenote (ihwWhiskerLayer leftContext 0 layer)) domVec codVec
      <-> IhqPairMem (leftContext + (innerWidth + 0)) (leftContext + (innerWidth + 0))
        (ihsLayerDenote (ihwWhiskerLayer leftContext 0 layer)) codVec domVec := by
  have hLeft := ihuWhiskerLayerLeftSpec leftContext layer domVec codVec
  have hRight := ihuWhiskerLayerLeftSpec leftContext layer codVec domVec
  rw [hDom, hCod] at hLeft hRight
  refine Iff.trans hLeft (Iff.trans ?_ hRight.symm)
  refine Iff.intro ?_ ?_
  · intro hL
    cases hL with
    | intro leftPart hL1 =>
        cases hL1 with
        | intro innerDom hL2 =>
            cases hL2 with
            | intro innerCod hFacts =>
                exact Exists.intro leftPart (Exists.intro innerCod (Exists.intro innerDom
                  (And.intro hFacts.right.left (And.intro hFacts.left
                    (And.intro hFacts.right.right.left
                      ((hSelf innerDom innerCod).mp hFacts.right.right.right))))))
  · intro hR
    cases hR with
    | intro leftPart hR1 =>
        cases hR1 with
        | intro innerDom hR2 =>
            cases hR2 with
            | intro innerCod hFacts =>
                exact Exists.intro leftPart (Exists.intro innerCod (Exists.intro innerDom
                  (And.intro hFacts.right.left (And.intro hFacts.left
                    (And.intro hFacts.right.right.left
                      ((hSelf innerDom innerCod).mp hFacts.right.right.right))))))

/-- A reversible layer list: every layer is square at `width` and self-converse.
The layer-reverse of such a list denotes the converse relation. -/
inductive IhuReversible : Nat -> List (List IhsCell) -> Prop where
  | nil (width : Nat) : IhuReversible width []
  | cons {width : Nat} {layer : List IhsCell} {restLayers : List (List IhsCell)}
      (hDom : ihsLayerDomArity layer = width)
      (hCod : ihsLayerCodArity layer = width)
      (hSelfConverse : (firstVec secondVec : List QnfRat) ->
        (IhqPairMem width width (ihsLayerDenote layer) firstVec secondVec
          <-> IhqPairMem width width (ihsLayerDenote layer) secondVec firstVec))
      (hRest : IhuReversible width restLayers) :
      IhuReversible width (layer :: restLayers)

/-- Width transport for reversibility. -/
theorem ihuReversibleCast {firstWidth secondWidth : Nat} {layers : List (List IhsCell)}
    (hWidthEq : firstWidth = secondWidth) (hRev : IhuReversible firstWidth layers) :
    IhuReversible secondWidth layers := by
  rw [<- hWidthEq]
  exact hRev

/-- Reversible lists are well-formed. -/
theorem ihuReversibleWF {width : Nat} {layers : List (List IhsCell)}
    (hRev : IhuReversible width layers) : IhsLayersWF width layers := by
  induction hRev with
  | nil => exact IhsLayersWF.nil width
  | cons hDom hCod _hSelf _hRest ihRest =>
      exact IhsLayersWF.cons hDom (ihsLayersWFCast hCod.symm ihRest)

/-- Reversible lists preserve arity. -/
theorem ihuReversibleCodArity {width : Nat} {layers : List (List IhsCell)}
    (hRev : IhuReversible width layers) : ihsLayersCodArity width layers = width := by
  induction hRev with
  | nil => rfl
  | cons _hDom hCod _hSelf _hRest ihRest =>
      show ihsLayersCodArity (ihsLayerCodArity _) _ = _
      rw [hCod]
      exact ihRest

/-- Reversibility is closed under layer-list concatenation. -/
theorem ihuReversibleCat {width : Nat} {firstLayers secondLayers : List (List IhsCell)}
    (hFirst : IhuReversible width firstLayers) (hSecond : IhuReversible width secondLayers) :
    IhuReversible width (ihwCatLayers firstLayers secondLayers) := by
  induction hFirst with
  | nil => exact hSecond
  | cons hDom hCod hSelf _hRest ihRest =>
      exact IhuReversible.cons hDom hCod hSelf ihRest

/-- Reversibility is preserved by layer-list reversal. -/
theorem ihuReversibleReverse {width : Nat} {layers : List (List IhsCell)}
    (hRev : IhuReversible width layers) : IhuReversible width (List.reverse layers) := by
  induction hRev with
  | nil => exact IhuReversible.nil width
  | cons hDom hCod hSelf hRest ihRest =>
      rw [ihuReverseConsCat]
      exact ihuReversibleCat ihRest
        (IhuReversible.cons hDom hCod hSelf (IhuReversible.nil _))

/-- Reversibility is preserved by left-whiskering. -/
theorem ihuReversibleWhisker (leftContext : Nat) {innerWidth : Nat}
    {layers : List (List IhsCell)} (hRev : IhuReversible innerWidth layers) :
    IhuReversible (leftContext + (innerWidth + 0))
      (ihwWhiskerLayers leftContext 0 layers) := by
  induction hRev with
  | nil => exact IhuReversible.nil (leftContext + (innerWidth + 0))
  | cons hDom hCod hSelf _hRest ihRest =>
      refine IhuReversible.cons ?_ ?_ ?_ ihRest
      · rw [ihwWhiskerLayerDomArity leftContext 0, hDom]
      · rw [ihwWhiskerLayerCodArity leftContext 0, hCod]
      · exact ihuWhiskerLayerSelfConverse leftContext innerWidth _ hDom hCod hSelf

/-- The move-past-block cascade is reversible: every layer is an adjacent
transposition, square at the running width and self-converse. -/
theorem ihuReversibleMoveRight : (leftContext blockLen rightContext : Nat) ->
    IhuReversible (leftContext + (1 + (blockLen + rightContext)))
      (ihrMoveRight leftContext blockLen rightContext)
  | _leftContext, 0, _rightContext => IhuReversible.nil _
  | leftContext, blockLen + 1, rightContext => by
      have hStep : (leftContext + (1 + ((blockLen + 1) + rightContext)))
          = leftContext + (2 + (blockLen + rightContext)) :=
        ihrMoveWidthStep leftContext blockLen rightContext
      refine IhuReversible.cons ?_ ?_ ?_ ?_
      · exact (ihrSwapLayerDomArity leftContext (blockLen + rightContext)).trans hStep.symm
      · exact (ihrSwapLayerCodArity leftContext (blockLen + rightContext)).trans hStep.symm
      · exact fun firstVec secondVec =>
          Iff.trans (ihwPairMemCast hStep hStep)
            (Iff.trans (ihuSwapSelfConverse leftContext (blockLen + rightContext)
              firstVec secondVec) (ihwPairMemCast hStep.symm hStep.symm))
      · exact ihuReversibleCast
          (hStep.trans (ihrMoveWidthRec leftContext blockLen rightContext)).symm
          (ihuReversibleMoveRight (leftContext + 1) blockLen rightContext)

/-- The perfect unshuffle is reversible. -/
theorem ihuReversibleUnshuffle : (blockWidth : Nat) ->
    IhuReversible (blockWidth + blockWidth) (ihrUnshuffle blockWidth)
  | 0 => IhuReversible.nil _
  | blockWidth + 1 => by
      show IhuReversible ((blockWidth + 1) + (blockWidth + 1))
        (ihwCatLayers (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
          (ihrMoveRight 1 blockWidth blockWidth))
      refine ihuReversibleCat ?_ ?_
      · exact ihuReversibleCast (ihuWidthCanon blockWidth).symm
          (ihuReversibleWhisker 2 (ihuReversibleUnshuffle blockWidth))
      · exact ihuReversibleCast (ihuWidthMove blockWidth).symm
          (ihuReversibleMoveRight 1 blockWidth blockWidth)

/-! ## Stage 5 — the reverse-is-converse bridge and the shuffle denotation -/

/-- A one-layer window denotes exactly its layer (the trailing identity is a
right unit). -/
theorem ihuSingletonDenote (layer : List IhsCell) (arity : Nat)
    (hDomEq : ihsLayerDomArity layer = arity) (domVec codVec : List QnfRat) :
    IhqPairMem arity (ihsLayerCodArity layer) (ihsLayersDenote arity [layer]) domVec codVec
      <-> IhqPairMem arity (ihsLayerCodArity layer) (ihsLayerDenote layer) domVec codVec := by
  have hAll : IhqAllWidth (arity + ihsLayerCodArity layer) (ihsLayerDenote layer) :=
    ihsAllWidthCast (by rw [hDomEq]) (ihsLayerDenoteWidth layer)
  exact ihsComposeIdRight arity (ihsLayerCodArity layer) (ihsLayerDenote layer)
    hAll domVec codVec

/-- A one-layer window at a square boundary denotes its layer, boundary folded. -/
theorem ihuSingletonSquareDenote (layer : List IhsCell) (width : Nat)
    (hDom : ihsLayerDomArity layer = width) (hCod : ihsLayerCodArity layer = width)
    (domVec codVec : List QnfRat) :
    IhqPairMem width width (ihsLayersDenote width [layer]) domVec codVec
      <-> IhqPairMem width width (ihsLayerDenote layer) domVec codVec := by
  refine Iff.trans (ihwPairMemCast rfl hCod.symm) ?_
  refine Iff.trans (ihuSingletonDenote layer width hDom domVec codVec) ?_
  exact ihwPairMemCast rfl hCod

/-- THE LAYER-REVERSE IS THE CONVERSE: for a reversible layer list, the reversed
diagram relates `dom` to `cod` iff the original relates `cod` to `dom`. -/
theorem ihuReverseConverse {width : Nat} {layers : List (List IhsCell)}
    (hRev : IhuReversible width layers) (domVec codVec : List QnfRat) :
    IhqPairMem width width (ihsLayersDenote width (List.reverse layers)) domVec codVec
      <-> IhqPairMem width width (ihsLayersDenote width layers) codVec domVec := by
  induction hRev generalizing domVec codVec with
  | nil =>
      refine Iff.trans (ihsIdSpec width domVec codVec)
        (Iff.trans ?_ (ihsIdSpec width codVec domVec).symm)
      refine Iff.intro ?_ ?_
      · intro hEq
        exact And.intro hEq.left.symm (by rw [<- hEq.left]; exact hEq.right)
      · intro hEq
        exact And.intro hEq.left.symm (by rw [<- hEq.left]; exact hEq.right)
  | @cons layer restLayers hDom hCod hSelf hRest ihRest =>
      have hRevRest := ihuReversibleReverse hRest
      have hRevRestWF := ihuReversibleWF hRevRest
      have hRevRestCod : ihsLayersCodArity width (List.reverse restLayers) = width :=
        ihuReversibleCodArity hRevRest
      have hRestWF := ihuReversibleWF hRest
      have hRestCod : ihsLayersCodArity width restLayers = width :=
        ihuReversibleCodArity hRest
      have hFinalW : ihsLayersCodArity (ihsLayersCodArity width (List.reverse restLayers))
          [layer] = width := hCod
      have hFinalW2 : ihsLayersCodArity (ihsLayerCodArity layer) restLayers = width := by
        rw [hCod]; exact hRestCod
      have hLayerWF : IhsLayersWF (ihsLayersCodArity width (List.reverse restLayers)) [layer] :=
        ihsLayersWFCast hRevRestCod.symm
          (IhsLayersWF.cons hDom (IhsLayersWF.nil (ihsLayerCodArity layer)))
      have hRevRestAll : IhqAllWidth
          (width + ihsLayersCodArity width (List.reverse restLayers))
          (ihsLayersDenote width (List.reverse restLayers)) :=
        ihsLayersDenoteWidth (List.reverse restLayers) hRevRestWF
      have hLayerListAll : IhqAllWidth
          (ihsLayersCodArity width (List.reverse restLayers)
            + ihsLayersCodArity (ihsLayersCodArity width (List.reverse restLayers)) [layer])
          (ihsLayersDenote (ihsLayersCodArity width (List.reverse restLayers)) [layer]) :=
        ihsLayersDenoteWidth [layer] hLayerWF
      have hLayerAll : IhqAllWidth (width + ihsLayerCodArity layer) (ihsLayerDenote layer) :=
        ihsAllWidthCast (by rw [hDom]) (ihsLayerDenoteWidth layer)
      have hRestForCompose : IhqAllWidth
          (ihsLayerCodArity layer + ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
          (ihsLayersDenote (ihsLayerCodArity layer) restLayers) :=
        ihsLayersDenoteWidth restLayers (ihsLayersWFCast hCod.symm hRestWF)
      -- per-factor iffs (both folded to the square width)
      have hF1 : (midVec : List QnfRat) ->
          (IhqPairMem width (ihsLayersCodArity width (List.reverse restLayers))
              (ihsLayersDenote width (List.reverse restLayers)) domVec midVec
            <-> IhqPairMem width width (ihsLayersDenote width restLayers) midVec domVec) := by
        intro midVec
        refine Iff.trans (ihwPairMemCast rfl hRevRestCod) ?_
        exact ihRest domVec midVec
      have hF2 : (midVec : List QnfRat) ->
          (IhqPairMem (ihsLayersCodArity width (List.reverse restLayers))
              (ihsLayersCodArity (ihsLayersCodArity width (List.reverse restLayers)) [layer])
              (ihsLayersDenote (ihsLayersCodArity width (List.reverse restLayers)) [layer])
              midVec codVec
            <-> IhqPairMem width width (ihsLayerDenote layer) codVec midVec) := by
        intro midVec
        refine Iff.trans (ihwPairMemCast hRevRestCod hFinalW) ?_
        rw [congrArg (fun runningArity => ihsLayersDenote runningArity [layer]) hRevRestCod]
        refine Iff.trans (ihuSingletonSquareDenote layer width hDom hCod midVec codVec) ?_
        exact hSelf midVec codVec
      -- the RHS characterization (a fresh composeSpec, folded)
      have hRHS : IhqPairMem width width (ihsLayersDenote width (layer :: restLayers))
            codVec domVec
          <-> Exists fun midVec =>
              IhqPairMem width width (ihsLayerDenote layer) codVec midVec
                /\ IhqPairMem width width (ihsLayersDenote width restLayers) midVec domVec := by
        refine Iff.trans (ihwPairMemCast rfl hFinalW2.symm) ?_
        refine Iff.trans (ihqComposeSpec width (ihsLayerCodArity layer)
          (ihsLayersCodArity (ihsLayerCodArity layer) restLayers)
          (ihsLayerDenote layer) (ihsLayersDenote (ihsLayerCodArity layer) restLayers)
          hLayerAll hRestForCompose codVec domVec) ?_
        refine Iff.intro ?_ ?_
        · intro hR
          cases hR with
          | intro midVec hParts =>
              refine Exists.intro midVec (And.intro ((ihwPairMemCast rfl hCod).mp hParts.left)
                ?_)
              have hCast := (ihwPairMemCast hCod hFinalW2).mp hParts.right
              rw [congrArg (fun runningArity => ihsLayersDenote runningArity restLayers) hCod]
                at hCast
              exact hCast
        · intro hR
          cases hR with
          | intro midVec hParts =>
              refine Exists.intro midVec (And.intro ((ihwPairMemCast rfl hCod.symm).mp
                hParts.left) ?_)
              have hCast := hParts.right
              rw [<- congrArg (fun runningArity => ihsLayersDenote runningArity restLayers) hCod]
                at hCast
              exact (ihwPairMemCast hCod.symm hFinalW2.symm).mp hCast
      -- assemble: split the reversed cascade, characterize both factors, reorder
      rw [ihuReverseConsCat]
      refine Iff.trans (ihwPairMemCast rfl hFinalW.symm) ?_
      refine Iff.trans ((ihwLayersDenoteCat (List.reverse restLayers) [layer]
        hRevRestWF hLayerWF) domVec codVec) ?_
      refine Iff.trans (ihqComposeSpec width
        (ihsLayersCodArity width (List.reverse restLayers))
        (ihsLayersCodArity (ihsLayersCodArity width (List.reverse restLayers)) [layer])
        (ihsLayersDenote width (List.reverse restLayers))
        (ihsLayersDenote (ihsLayersCodArity width (List.reverse restLayers)) [layer])
        hRevRestAll hLayerListAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hL
        cases hL with
        | intro midVec hParts =>
            exact hRHS.mpr (Exists.intro midVec (And.intro ((hF2 midVec).mp hParts.right)
              ((hF1 midVec).mp hParts.left)))
      · intro hR
        cases hRHS.mp hR with
        | intro midVec hParts =>
            exact Exists.intro midVec (And.intro ((hF1 midVec).mpr hParts.right)
              ((hF2 midVec).mpr hParts.left))

/-- THE FAITHFUL SHUFFLE DENOTATION: the inverse block-transpose `ihrShuffle m`
relates the block layout `ihqCat pList qList` to the interleaved layout
`ihnInterleave pList qList` (dom/cod swapped from the unshuffle) — the layer
reverse of the unshuffle carries its denotation to the converse. -/
theorem ihuShuffleDenote (blockWidth : Nat) (domVec codVec : List QnfRat) :
    IhqPairMem (blockWidth + blockWidth) (blockWidth + blockWidth)
        (ihsLayersDenote (blockWidth + blockWidth) (ihrShuffle blockWidth)) domVec codVec
      <-> Exists fun pList => Exists fun qList =>
            domVec = ihqCat pList qList
              /\ codVec = ihnInterleave pList qList
              /\ pList.length = blockWidth
              /\ qList.length = blockWidth := by
  refine Iff.trans (ihuReverseConverse (ihuReversibleUnshuffle blockWidth) domVec codVec) ?_
  refine Iff.trans (ihuUnshuffleDenote blockWidth codVec domVec) ?_
  refine Iff.intro ?_ ?_
  · intro hSpec
    cases hSpec with
    | intro pList hRest =>
        cases hRest with
        | intro qList hFacts =>
            exact Exists.intro pList (Exists.intro qList (And.intro hFacts.right.left
              (And.intro hFacts.left (And.intro hFacts.right.right.left
                hFacts.right.right.right))))
  · intro hSpec
    cases hSpec with
    | intro pList hRest =>
        cases hRest with
        | intro qList hFacts =>
            exact Exists.intro pList (Exists.intro qList (And.intro hFacts.right.left
              (And.intro hFacts.left (And.intro hFacts.right.right.left
                hFacts.right.right.right))))

/-- DECIDED (T1): the committed owner-false `ihnShuffleDenoteStatement` is
inhabited by the faithful shuffle denotation. -/
theorem ihuShuffleDenoteHolds : ihnShuffleDenoteStatement :=
  ihuShuffleDenote

/-- DECIDED (T1): the perfect shuffle ships its faithful block-transpose
denotation. -/
def ihuHasShuffleDenote : Bool := true

set_option maxHeartbeats 4000000 in
/-- T1 CONTENT fire (routes through `ihuShuffleDenote`): the shuffle `ihrShuffle 2`
relates the block input `[2, 1, 3, 1]` to the interleaved output `[2, 3, 1, 1]` —
the exact inverse of `ihuFireUnshuffleContent`. -/
theorem ihuFireShuffleContent :
    IhqPairMem 4 4 (ihsLayersDenote 4 (ihrShuffle 2))
      [ihsScalarTwo, qnfOne, ihsScalarThree, qnfOne]
      [ihsScalarTwo, ihsScalarThree, qnfOne, qnfOne] :=
  (ihuShuffleDenote 2 [ihsScalarTwo, qnfOne, ihsScalarThree, qnfOne]
      [ihsScalarTwo, ihsScalarThree, qnfOne, qnfOne]).mpr
    (Exists.intro [ihsScalarTwo, qnfOne] (Exists.intro [ihsScalarThree, qnfOne]
      (And.intro rfl (And.intro rfl (And.intro rfl rfl)))))

/-! ## Stage 6 — the T2 / T3 walls (two-row spatial sum, multi-row NF compiler) -/

/-- WALL (T2) — OWNER FALSE, NOT PROVEN THIS BRICK.  The committed
`ihgTwoRowSpatialSumStatement`.

STATUS UPDATE: the blocker named by the r7/r8 walls (`ihrHasTwoRowSpatialSum`,
`ihnHasTwoRowSpatialSum`) was the faithful perfect (un)shuffle denotation
(`ihrUnshuffleDenoteResidual`).  That blocker is now DISCHARGED —
`ihuUnshuffleDenote` and `ihuShuffleDenote` (above) are the faithful bidirectional
block-transpose denotations, zero-axiom.  So T2 is no longer gated on an unbuilt
(un)shuffle denotation.

PRECISE REMAINING RESIDUAL: the assembly `ihrTwoRowSumDiagram`
(`split ; unshuffle ; (gadget (x) gadget) ; shuffle ; merge`) needs (1) the two
per-strand fan denotations — `ihrSplitLayer` (per-strand `whiteComult` coadd,
`m -> 2m`, relating `s_i` to an interleaved `(p_i, q_i)` with `p_i + q_i = s_i`)
and `ihrMergeLayer` (per-strand `whiteMult` add, `2n -> n`), each a fresh
per-strand tensor recursion in the shape of `ihgScalarLayerDenote`; (2) the
gadget-tensor denotation `(gadget1 (x) gadget2)` via `ihwTensorSpec` +
`ihgGadgetDenote`; (3) the five-stage `ihqComposeSpec` chain reconciling the
interleave/block layouts through `ihuUnshuffleDenote` / `ihuShuffleDenote`, landing
the Minkowski-sum characterization `(dom, cod) <-> exists a b,
dom = a*in1 + b*in2 /\ cod = a*out1 + b*out2` — i.e. `ihqCat dom cod` in the span
of `[in1 ++ out1, in2 ++ out2]`.  The construction is already kernel-validated at
concrete dimensions (`ihrTwoRowSumInstanceOneOut`, `ihrTwoRowSumInstanceTwoOut`);
only the arbitrary-width denotation induction remains — a distinct large build, not
shipped this round. -/
def ihuHasTwoRowSpatialSum : Bool := false

/-- WALL (T3) — OWNER FALSE, NOT PROVEN THIS BRICK.  The committed
`ihzNormalFormStatement`.  Gated on the general two-row spatial sum
(`ihuHasTwoRowSpatialSum`): the multi-row NF compiler is the row-list recursion
`span (row :: rest) = span [row] + span rest`, joining the single-row gadget
(`ihgSingleRowNormalForm`) for the head row with the recursively-built sub-diagram
via the general Minkowski spatial sum (of which the two-single-row case is
`ihgTwoRowSpatialSumStatement`).  Not shipped this round. -/
def ihuHasNormalFormCompiler : Bool := false

end FX1Poly.ComputerAlgebra
