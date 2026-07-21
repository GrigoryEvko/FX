import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfCompilerRiffle

/-! # LinearAlgebra/InteractingHopfNormalForm — the move-past-block cascade
denotation and its dependents

Discharges the residual `ihrMoveRightDenoteResidual`, the faithful bidirectional
denotation of the move-past-block cascade, together with its downstream
consequences.

The cascade denotation (T1, `ihnMoveRightDenote`): the faithful bidirectional
`IhqPairMem` characterization of `ihrMoveRight` — the cascade relates
`L ++ [x] ++ B ++ R` to `L ++ B ++ [x] ++ R` at every context.  Structural
recursion on `blockLen`: the base is the identity spec, the step composes the
head swap layer (`ihrSwapLayerDenote`) with the recursive cascade through
`ihqComposeSpec`, reconciling the two decompositions of the shared middle vector
via `ihqCatInj` + `ihwCatAssoc`, over the alternating `1 + (.)` / `2 + (.)`
running widths (`ihrMoveWidthStep` / `ihrMoveWidthRec`).  It inhabits
`ihrMoveRightDenoteResidual`.  The module also states the faithful interleave and
(un)shuffle denotation statements (`ihnInterleave`, `ihnUnshuffleDenoteStatement`,
`ihnShuffleDenoteStatement`).

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfNormalForm.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-- `ihqCat` with the empty first block is the identity (definitional, exposed
as a rewrite lemma). -/
theorem ihnCatNilLeft (row : List QnfRat) : ihqCat [] row = row := rfl

/-! ## Stage 0 — the move-pair structural predicate (the residual RHS) -/

/-- The move-pair spec: the structural relation the cascade denotes — a wire
`movingWire` moved rightward from position `leftContext` past a `blockLen`-wide
block, everything else fixed.  Matches the RHS of `ihrMoveRightDenoteResidual`. -/
def ihnMovePairSpec (leftContext blockLen rightContext : Nat)
    (domVec codVec : List QnfRat) : Prop :=
  Exists fun leftPart => Exists fun movingWire => Exists fun blockPart =>
    Exists fun rightPart =>
      domVec = ihqCat leftPart (ihqCat [movingWire] (ihqCat blockPart rightPart))
        /\ codVec = ihqCat leftPart (ihqCat blockPart (ihqCat [movingWire] rightPart))
        /\ leftPart.length = leftContext
        /\ blockPart.length = blockLen
        /\ rightPart.length = rightContext

/-! ## Stage 1 — the cascade denotation (T1) -/

/-- The cascade denotation: the move-past-block cascade `ihrMoveRight` relates a
vector `L ++ [x] ++ B ++ R` to `L ++ B ++ [x] ++ R`, at every context, by
structural recursion on `blockLen`. -/
theorem ihnMoveRightDenote : (leftContext blockLen rightContext : Nat) ->
    (domVec codVec : List QnfRat) ->
    (IhqPairMem (leftContext + (1 + (blockLen + rightContext)))
        (leftContext + (1 + (blockLen + rightContext)))
        (ihsLayersDenote (leftContext + (1 + (blockLen + rightContext)))
          (ihrMoveRight leftContext blockLen rightContext)) domVec codVec
      <-> ihnMovePairSpec leftContext blockLen rightContext domVec codVec)
  | leftContext, 0, rightContext, domVec, codVec => by
      refine Iff.trans (ihsIdSpec (leftContext + (1 + (0 + rightContext)))
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        have hDomLen : domVec.length = leftContext + (1 + (0 + rightContext)) :=
          hSame.right
        have hLeftLen : (ihqTakeN leftContext domVec).length = leftContext :=
          ihqTakeNLength domVec leftContext (1 + (0 + rightContext)) hDomLen
        have hRestLen : (ihqDropN leftContext domVec).length = 1 + (0 + rightContext) :=
          ihqDropNLength domVec leftContext (1 + (0 + rightContext)) hDomLen
        have hMoveLen : (ihqTakeN 1 (ihqDropN leftContext domVec)).length = 1 :=
          ihqTakeNLength (ihqDropN leftContext domVec) 1 (0 + rightContext) hRestLen
        have hRightLen : (ihqDropN 1 (ihqDropN leftContext domVec)).length
            = 0 + rightContext :=
          ihqDropNLength (ihqDropN leftContext domVec) 1 (0 + rightContext) hRestLen
        have hSplitOuter := ihqCatTakeDrop domVec leftContext
          (1 + (0 + rightContext)) hDomLen
        have hSplitInner := ihqCatTakeDrop (ihqDropN leftContext domVec) 1
          (0 + rightContext) hRestLen
        cases ihzLengthOneShape (ihqTakeN 1 (ihqDropN leftContext domVec)) hMoveLen with
        | intro movingWire hMoveEq =>
            refine Exists.intro (ihqTakeN leftContext domVec)
              (Exists.intro movingWire (Exists.intro []
                (Exists.intro (ihqDropN 1 (ihqDropN leftContext domVec))
                  (And.intro ?_ (And.intro ?_ (And.intro hLeftLen
                    (And.intro rfl (hRightLen.trans (Nat.zero_add rightContext)))))))))
            · show domVec = ihqCat (ihqTakeN leftContext domVec)
                  (ihqCat [movingWire] (ihqDropN 1 (ihqDropN leftContext domVec)))
              rw [<- hMoveEq, hSplitInner, hSplitOuter]
            · show codVec = ihqCat (ihqTakeN leftContext domVec)
                  (ihqCat [movingWire] (ihqDropN 1 (ihqDropN leftContext domVec)))
              rw [<- hSame.left, <- hMoveEq, hSplitInner, hSplitOuter]
      · intro hSpec
        cases hSpec with
        | intro leftPart hPack1 =>
            cases hPack1 with
            | intro movingWire hPack2 =>
                cases hPack2 with
                | intro blockPart hPack3 =>
                    cases hPack3 with
                    | intro rightPart hFacts =>
                        have hBlockNil : blockPart = [] :=
                          ihsLengthZeroNil blockPart hFacts.right.right.right.left
                        refine And.intro ?_ ?_
                        · have hCommon : ihqCat leftPart
                                (ihqCat [movingWire] (ihqCat blockPart rightPart))
                              = ihqCat leftPart
                                (ihqCat blockPart (ihqCat [movingWire] rightPart)) := by
                            rw [hBlockNil, ihnCatNilLeft, ihnCatNilLeft]
                          rw [hFacts.left, hFacts.right.left]
                          exact hCommon
                        · rw [hFacts.left, ihqCatLength, ihqCatLength, ihqCatLength,
                            hFacts.right.right.left, hFacts.right.right.right.left,
                            hFacts.right.right.right.right]
                          rfl
  | leftContext, blockLen + 1, rightContext, domVec, codVec => by
      have hStep : leftContext + (1 + ((blockLen + 1) + rightContext))
          = leftContext + (2 + (blockLen + rightContext)) :=
        ihrMoveWidthStep leftContext blockLen rightContext
      have hRec : leftContext + (2 + (blockLen + rightContext))
          = (leftContext + 1) + (1 + (blockLen + rightContext)) :=
        ihrMoveWidthRec leftContext blockLen rightContext
      have hTailCod : ihsLayersCodArity (leftContext + (2 + (blockLen + rightContext)))
          (ihrMoveRight (leftContext + 1) blockLen rightContext)
          = leftContext + (2 + (blockLen + rightContext)) := by
        rw [hRec]
        exact ihrMoveRightCodArity (leftContext + 1) blockLen rightContext
      have hDenoteEq : ihsLayersDenote (leftContext + (1 + ((blockLen + 1) + rightContext)))
          (ihrMoveRight leftContext (blockLen + 1) rightContext)
          = ihqComposeRows (leftContext + (1 + ((blockLen + 1) + rightContext)))
              (leftContext + (2 + (blockLen + rightContext)))
              (ihsLayersCodArity (leftContext + (2 + (blockLen + rightContext)))
                (ihrMoveRight (leftContext + 1) blockLen rightContext))
              (ihsLayerDenote (ihrSwapLayer leftContext (blockLen + rightContext)))
              (ihsLayersDenote (leftContext + (2 + (blockLen + rightContext)))
                (ihrMoveRight (leftContext + 1) blockLen rightContext)) := by
        show ihqComposeRows (leftContext + (1 + ((blockLen + 1) + rightContext)))
            (ihsLayerCodArity (ihrSwapLayer leftContext (blockLen + rightContext)))
            (ihsLayersCodArity
              (ihsLayerCodArity (ihrSwapLayer leftContext (blockLen + rightContext)))
              (ihrMoveRight (leftContext + 1) blockLen rightContext))
            (ihsLayerDenote (ihrSwapLayer leftContext (blockLen + rightContext)))
            (ihsLayersDenote
              (ihsLayerCodArity (ihrSwapLayer leftContext (blockLen + rightContext)))
              (ihrMoveRight (leftContext + 1) blockLen rightContext)) = _
        rw [ihrSwapLayerCodArity leftContext (blockLen + rightContext)]
      have hSwapAll : IhqAllWidth
          ((leftContext + (1 + ((blockLen + 1) + rightContext)))
            + (leftContext + (2 + (blockLen + rightContext))))
          (ihsLayerDenote (ihrSwapLayer leftContext (blockLen + rightContext))) :=
        ihsAllWidthCast
          (by rw [ihrSwapLayerDomArity leftContext (blockLen + rightContext),
            ihrSwapLayerCodArity leftContext (blockLen + rightContext), hStep])
          (ihsLayerDenoteWidth (ihrSwapLayer leftContext (blockLen + rightContext)))
      have hTailWF : IhsLayersWF (leftContext + (2 + (blockLen + rightContext)))
          (ihrMoveRight (leftContext + 1) blockLen rightContext) :=
        ihsLayersWFCast hRec.symm (ihrMoveRightWF (leftContext + 1) blockLen rightContext)
      have hTailAll : IhqAllWidth
          ((leftContext + (2 + (blockLen + rightContext)))
            + ihsLayersCodArity (leftContext + (2 + (blockLen + rightContext)))
                (ihrMoveRight (leftContext + 1) blockLen rightContext))
          (ihsLayersDenote (leftContext + (2 + (blockLen + rightContext)))
            (ihrMoveRight (leftContext + 1) blockLen rightContext)) :=
        ihsLayersDenoteWidth (ihrMoveRight (leftContext + 1) blockLen rightContext) hTailWF
      -- hLHS: the cascade denotation splits into head-swap + recursive-tail
      have hLHS : IhqPairMem (leftContext + (1 + ((blockLen + 1) + rightContext)))
          (leftContext + (1 + ((blockLen + 1) + rightContext)))
          (ihsLayersDenote (leftContext + (1 + ((blockLen + 1) + rightContext)))
            (ihrMoveRight leftContext (blockLen + 1) rightContext)) domVec codVec
          <-> Exists fun midVec =>
              IhqPairMem (leftContext + (1 + ((blockLen + 1) + rightContext)))
                  (leftContext + (2 + (blockLen + rightContext)))
                  (ihsLayerDenote (ihrSwapLayer leftContext (blockLen + rightContext)))
                  domVec midVec
                /\ IhqPairMem (leftContext + (2 + (blockLen + rightContext)))
                    (ihsLayersCodArity (leftContext + (2 + (blockLen + rightContext)))
                      (ihrMoveRight (leftContext + 1) blockLen rightContext))
                    (ihsLayersDenote (leftContext + (2 + (blockLen + rightContext)))
                      (ihrMoveRight (leftContext + 1) blockLen rightContext))
                    midVec codVec := by
        rw [hDenoteEq]
        refine Iff.trans (ihwPairMemCast rfl (hTailCod.trans hStep.symm).symm) ?_
        exact ihqComposeSpec (leftContext + (1 + ((blockLen + 1) + rightContext)))
          (leftContext + (2 + (blockLen + rightContext)))
          (ihsLayersCodArity (leftContext + (2 + (blockLen + rightContext)))
            (ihrMoveRight (leftContext + 1) blockLen rightContext))
          (ihsLayerDenote (ihrSwapLayer leftContext (blockLen + rightContext)))
          (ihsLayersDenote (leftContext + (2 + (blockLen + rightContext)))
            (ihrMoveRight (leftContext + 1) blockLen rightContext))
          hSwapAll hTailAll domVec codVec
      -- hSwapEquiv: the head swap layer's denotation at the shared boundary
      have hSwapEquiv : (midVec : List QnfRat) ->
          (IhqPairMem (leftContext + (1 + ((blockLen + 1) + rightContext)))
              (leftContext + (2 + (blockLen + rightContext)))
              (ihsLayerDenote (ihrSwapLayer leftContext (blockLen + rightContext)))
              domVec midVec
            <-> Exists fun leftPart => Exists fun firstMid => Exists fun secondMid =>
                  Exists fun rightPart =>
                    domVec = ihqCat leftPart (ihqCat [firstMid, secondMid] rightPart)
                      /\ midVec = ihqCat leftPart (ihqCat [secondMid, firstMid] rightPart)
                      /\ leftPart.length = leftContext
                      /\ rightPart.length = blockLen + rightContext) := by
        intro midVec
        refine Iff.trans (ihwPairMemCast hStep rfl) ?_
        exact ihrSwapLayerDenote leftContext (blockLen + rightContext) domVec midVec
      -- hTailEquiv: the recursive cascade's denotation (the IH)
      have hDenoteArity : ihsLayersDenote (leftContext + (2 + (blockLen + rightContext)))
          (ihrMoveRight (leftContext + 1) blockLen rightContext)
          = ihsLayersDenote ((leftContext + 1) + (1 + (blockLen + rightContext)))
            (ihrMoveRight (leftContext + 1) blockLen rightContext) :=
        congrArg (fun ar => ihsLayersDenote ar
          (ihrMoveRight (leftContext + 1) blockLen rightContext)) hRec
      have hTailEquiv : (midVec : List QnfRat) ->
          (IhqPairMem (leftContext + (2 + (blockLen + rightContext)))
              (ihsLayersCodArity (leftContext + (2 + (blockLen + rightContext)))
                (ihrMoveRight (leftContext + 1) blockLen rightContext))
              (ihsLayersDenote (leftContext + (2 + (blockLen + rightContext)))
                (ihrMoveRight (leftContext + 1) blockLen rightContext))
              midVec codVec
            <-> ihnMovePairSpec (leftContext + 1) blockLen rightContext midVec codVec) := by
        intro midVec
        rw [hDenoteArity]
        refine Iff.trans (ihwPairMemCast hRec (hTailCod.trans hRec)) ?_
        exact ihnMoveRightDenote (leftContext + 1) blockLen rightContext midVec codVec
      -- assemble: split via hLHS, characterize both factors, reconcile
      refine Iff.trans hLHS (Iff.intro ?_ ?_)
      · intro hExists
        cases hExists with
        | intro midVec hParts =>
            have hSwap := (hSwapEquiv midVec).mp hParts.left
            have hTail := (hTailEquiv midVec).mp hParts.right
            cases hSwap with
            | intro leftPart hS1 =>
                cases hS1 with
                | intro firstMid hS2 =>
                    cases hS2 with
                    | intro secondMid hS3 =>
                        cases hS3 with
                        | intro rightPart hSFacts =>
                            cases hTail with
                            | intro leftPart2 hT1 =>
                                cases hT1 with
                                | intro movingWire2 hT2 =>
                                    cases hT2 with
                                    | intro blockPart2 hT3 =>
                                        cases hT3 with
                                        | intro rightPart2 hTFacts =>
                                            -- reconcile midVec
                                            have hMidSwap : midVec
                                                = ihqCat (ihqCat leftPart [secondMid])
                                                    (ihqCat [firstMid] rightPart) :=
                                              Eq.trans hSFacts.right.left
                                                (ihwCatAssoc leftPart [secondMid]
                                                  (ihqCat [firstMid] rightPart)).symm
                                            have hLenEq : (ihqCat leftPart [secondMid]).length
                                                = leftPart2.length :=
                                              (ihqCatLength leftPart [secondMid]).trans
                                                (by rw [hSFacts.right.right.left,
                                                  hTFacts.right.right.left]; rfl)
                                            have hReconcile :
                                                ihqCat (ihqCat leftPart [secondMid])
                                                    (ihqCat [firstMid] rightPart)
                                                  = ihqCat leftPart2
                                                    (ihqCat [movingWire2]
                                                      (ihqCat blockPart2 rightPart2)) :=
                                              hMidSwap.symm.trans hTFacts.left
                                            have hSplit1 := ihqCatInj (ihqCat leftPart [secondMid])
                                              (ihqCat [firstMid] rightPart) leftPart2
                                              (ihqCat [movingWire2] (ihqCat blockPart2 rightPart2))
                                              hLenEq hReconcile
                                            have hSplit2 := ihqCatInj [firstMid] rightPart
                                              [movingWire2] (ihqCat blockPart2 rightPart2) rfl
                                              hSplit1.right
                                            have hFmEq : firstMid = movingWire2 :=
                                              congrArg (fun row => ihqGetCoeff row 0) hSplit2.left
                                            refine Exists.intro leftPart (Exists.intro firstMid
                                              (Exists.intro (secondMid :: blockPart2)
                                                (Exists.intro rightPart2
                                                  (And.intro ?_ (And.intro ?_
                                                    (And.intro hSFacts.right.right.left
                                                      (And.intro
                                                        (congrArg (fun k => k + 1)
                                                          hTFacts.right.right.right.left)
                                                        hTFacts.right.right.right.right)))))))
                                            · rw [hSFacts.left, hSplit2.right]
                                              rfl
                                            · rw [hTFacts.right.left, <- hSplit1.left, <- hFmEq]
                                              exact ihwCatAssoc leftPart [secondMid]
                                                (ihqCat blockPart2 (ihqCat [firstMid] rightPart2))
      · intro hSpec
        cases hSpec with
        | intro leftPart hP1 =>
            cases hP1 with
            | intro movingWire hP2 =>
                cases hP2 with
                | intro blockPart hP3 =>
                    cases hP3 with
                    | intro rightPart hFacts =>
                        cases blockPart with
                        | nil => exact nomatch hFacts.right.right.right.left
                        | cons blockHead blockRest =>
                            have hBlockRestLen : blockRest.length = blockLen :=
                              Nat.succ.inj hFacts.right.right.right.left
                            refine Exists.intro
                              (ihqCat leftPart (ihqCat [blockHead, movingWire]
                                (ihqCat blockRest rightPart)))
                              (And.intro ?_ ?_)
                            · exact (hSwapEquiv (ihqCat leftPart
                                (ihqCat [blockHead, movingWire]
                                  (ihqCat blockRest rightPart)))).mpr
                                ⟨leftPart, movingWire, blockHead, ihqCat blockRest rightPart,
                                  hFacts.left, rfl, hFacts.right.right.left,
                                  (ihqCatLength blockRest rightPart).trans
                                    (by rw [hBlockRestLen, hFacts.right.right.right.right])⟩
                            · refine (hTailEquiv (ihqCat leftPart
                                (ihqCat [blockHead, movingWire]
                                  (ihqCat blockRest rightPart)))).mpr
                                ⟨ihqCat leftPart [blockHead], movingWire, blockRest, rightPart,
                                  ?_, ?_,
                                  (ihqCatLength leftPart [blockHead]).trans
                                    (by rw [hFacts.right.right.left]; rfl),
                                  hBlockRestLen, hFacts.right.right.right.right⟩
                              · exact (ihwCatAssoc leftPart [blockHead]
                                  (ihqCat [movingWire] (ihqCat blockRest rightPart))).symm
                              · rw [hFacts.right.left]
                                exact (ihwCatAssoc leftPart [blockHead]
                                  (ihqCat blockRest (ihqCat [movingWire] rightPart))).symm

/-- The residual `ihrMoveRightDenoteResidual` is inhabited by the cascade
denotation `ihnMoveRightDenote`. -/
theorem ihnMoveRightDenoteResidualHolds : ihrMoveRightDenoteResidual :=
  ihnMoveRightDenote

/-- The move-past-block cascade ships its faithful bidirectional denotation,
discharging the riffle brick's move-right residual. -/
def ihnHasCascadeDenote : Bool := true

/-! ## Stage 2 — kernel-decided fires for the cascade denotation (T1) -/

set_option maxHeartbeats 4000000 in
/-- T1 fire (fresh dimension `ihrMoveRight 0 2 0`, width 3): moving the wire at
position 0 past a 2-wire block denotes the permutation `[x,b0,b1] -> [b0,b1,x]`. -/
theorem ihnFireMoveRightZeroTwoZero :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 3, layers := ihrMoveRight 0 2 0 })
      [[qnfOne, qnfZero, qnfZero, qnfZero, qnfZero, qnfOne],
        [qnfZero, qnfOne, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfOne, qnfZero]]
      = true := rfl

set_option maxHeartbeats 4000000 in
/-- T1 false control: the same cascade is not the identity permutation. -/
theorem ihnFireMoveRightZeroTwoZeroFalse :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 3, layers := ihrMoveRight 0 2 0 })
      [[qnfOne, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfOne, qnfZero, qnfZero, qnfOne, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfOne]]
      = false := rfl

set_option maxHeartbeats 4000000 in
/-- T1 content fire (routes through `ihnMoveRightDenote`, not merely a span
`rfl`): the cascade `ihrMoveRight 0 2 0` relates the concrete input
`[2, 1, 3]` to `[1, 3, 2]` — the whole wire moved past the whole block. -/
theorem ihnFireCascadeContent :
    IhqPairMem 3 3 (ihsDiagramDenote { sourceArity := 3, layers := ihrMoveRight 0 2 0 })
      [ihsScalarTwo, qnfOne, ihsScalarThree] [qnfOne, ihsScalarThree, ihsScalarTwo] :=
  (ihnMoveRightDenote 0 2 0 [ihsScalarTwo, qnfOne, ihsScalarThree]
      [qnfOne, ihsScalarThree, ihsScalarTwo]).mpr
    (Exists.intro [] (Exists.intro ihsScalarTwo (Exists.intro [qnfOne, ihsScalarThree]
      (Exists.intro [] (And.intro rfl (And.intro rfl (And.intro rfl
        (And.intro rfl rfl))))))))

/-! ## Stage 3 — the faithful (un)shuffle denotation statements (T2) -/

/-- The perfect interleave: `[p0, p1, ...]` and `[q0, q1, ...]` woven into
`[p0, q0, p1, q1, ...]` — the domain layout of the unshuffle. -/
def ihnInterleave : List QnfRat -> List QnfRat -> List QnfRat
  | [], _qList => []
  | _pList, [] => []
  | pHead :: pRest, qHead :: qRest =>
      pHead :: qHead :: ihnInterleave pRest qRest

/-- The faithful unshuffle denotation (the statement `ihrUnshuffleDenoteResidual`
under-specifies — that residual demands only a width consequence).  The
block-transpose `ihrUnshuffle blockWidth` relates the interleaved layout
`ihnInterleave pList qList` to the block layout `ihqCat pList qList`.

Not yet proven.  The residual is an induction on `blockWidth` chaining
`ihwWhiskerLayersDenote` (for the whiskered smaller unshuffle
`id_2 (x) (unshuffle m (x) id_0)`) with the T1 cascade denotation
`ihnMoveRightDenote` (for the head-strand move `ihrMoveRight 1 m m`) through
`ihwLayersDenoteCat` + `ihqComposeSpec`, reconciling the interleave/block
decompositions at each level (the same `ihqCatInj` + `ihwCatAssoc` bookkeeping
as T1, one dimension up).  Semantics `#eval`-validated (`ihnFireUnshuffleTwo`,
`ihrFireUnshuffleThree`). -/
def ihnUnshuffleDenoteStatement : Prop :=
  (blockWidth : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem (blockWidth + blockWidth) (blockWidth + blockWidth)
        (ihsDiagramDenote (IhsDiagram.mk (blockWidth + blockWidth)
          (ihrUnshuffle blockWidth))) domVec codVec
      <-> Exists fun pList => Exists fun qList =>
            domVec = ihnInterleave pList qList
              /\ codVec = ihqCat pList qList
              /\ pList.length = blockWidth
              /\ qList.length = blockWidth)

/-- The faithful shuffle denotation: the inverse block-transpose relates the
block layout `ihqCat pList qList` to the interleaved layout
`ihnInterleave pList qList` (dom/cod swapped from the unshuffle).

Not yet proven.  `ihrShuffle` is the layer-reverse of `ihrUnshuffle`; the
denotation follows from `ihnUnshuffleDenoteStatement` by the reverse-composite /
each-crossing-self-inverse argument, gated on the unshuffle denotation above. -/
def ihnShuffleDenoteStatement : Prop :=
  (blockWidth : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem (blockWidth + blockWidth) (blockWidth + blockWidth)
        (ihsDiagramDenote (IhsDiagram.mk (blockWidth + blockWidth)
          (ihrShuffle blockWidth))) domVec codVec
      <-> Exists fun pList => Exists fun qList =>
            domVec = ihqCat pList qList
              /\ codVec = ihnInterleave pList qList
              /\ pList.length = blockWidth
              /\ qList.length = blockWidth)

set_option maxHeartbeats 4000000 in
/-- T2 fire (fresh dimension `ihrUnshuffle 2`, `4 -> 4`): the block transpose
`[p0,q0,p1,q1] -> [p0,p1,q0,q1]`. -/
theorem ihnFireUnshuffleTwo :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 4, layers := ihrUnshuffle 2 })
      [[qnfOne, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfOne]]
      = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 false control: `ihrUnshuffle 2` is not the identity on `4` strands. -/
theorem ihnFireUnshuffleTwoFalse :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 4, layers := ihrUnshuffle 2 })
      [[qnfOne, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfOne]]
      = false := rfl

end FX1Poly.ComputerAlgebra
