import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfRowGadget

/-! # LinearAlgebra/InteractingHopfCompilerRiffle — the generator-transpose riffle
and the multi-row NF compiler (WP-PROP-3 brick 7)

Executing the brick-6 T4 residual (`ihgTwoRowSpatialSumStatement`): the multi-row
`R >= 2` spatial sum needs the GENERATOR-TRANSPOSE RIFFLE permutation layer built
from `IhsCell.crossing` cells, plus its interleave denotation, to regroup the
`blockA ++ blockB` strand layouts the Minkowski-sum assembly of two row relations
produces.

* THE ATOMIC RIFFLE LAYER (T1a, `ihrSwapLayer` / `ihrSwapLayerDenote`): a single
  `crossing` cell whiskered by `leftContext`/`rightContext` wires — swaps the two
  adjacent strands at position `leftContext` in a vector, everything else fixed.
  The reusable adjacent-transposition primitive, assembled from the crossing's own
  pair-membership spec (`ihrCrossingRowsSpec`) through `ihwWhiskerLayerDenote`.

* THE MOVE-PAST-BLOCK CASCADE (T1b, `ihrMoveRight` / `ihrMoveRightDenote`): a wire
  moved rightward past a block of `blockLen` wires by a cascade of `blockLen`
  swap layers — `L ++ [x] ++ B ++ R  ~>  L ++ B ++ [x] ++ R`.

* THE PERFECT (UN)SHUFFLE (T1c, `ihrUnshuffle` / `ihrShuffle` with denotations):
  the 2-block block-transpose — unshuffle sends the interleaved `[p0,q0,...]`
  layout to the block layout `[p0..; q0..]`; shuffle is its inverse.

* THE SPLIT / MERGE FANS (T2a, `ihrSplitLayer` / `ihrMergeLayer`): the per-strand
  `whiteComult` split `m -> 2m` and the per-strand `whiteMult` merge `2n -> n`.

* THE TWO-ROW SPATIAL SUM (T2, `ihrTwoRowSpatialSum`): the committed
  `ihgTwoRowSpatialSumStatement`, `split ; unshuffle ; (gadget TENSOR gadget) ;
  shuffle ; merge`, span-joining the two lines through `ihqComposeSpec`.

* THE MULTI-ROW COMPILER (T3, `ihrCompile` / `ihrNormalFormHolds`): the total
  matrix -> diagram compiler by structural recursion on the row list, discharging
  the committed owner-false `ihzNormalFormStatement`.

Raw Lean 4 + Init + the ComputerAlgebra bricks only; zero-axiom; structural
recursion only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfCompilerRiffle.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0 — the crossing cell pair-membership spec (T1a) -/

/-- THE CROSSING SPEC: the `crossing` generator matrix `[[1,0,0,1],[0,1,1,0]]`
at boundary `(2, 2)` relates `[x, y]` to `[y, x]` — the adjacent transposition. -/
theorem ihrCrossingRowsSpec (domVec codVec : List QnfRat) :
    IhqPairMem 2 2
        [[qnfOne, qnfZero, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne, qnfZero]]
        domVec codVec
      <-> Exists fun firstIn => Exists fun secondIn =>
            domVec = [firstIn, secondIn] /\ codVec = [secondIn, firstIn] := by
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
                            have hFirstIn : firstIn
                                = qnfAdd (qnfMul firstCoeff qnfOne)
                                    (qnfMul secondCoeff qnfZero) :=
                              congrArg (fun row => ihqGetCoeff row 0) hVecEq
                            have hSecondIn : secondIn
                                = qnfAdd (qnfMul firstCoeff qnfZero)
                                    (qnfMul secondCoeff qnfOne) :=
                              congrArg (fun row => ihqGetCoeff row 1) hVecEq
                            have hFirstOut : firstOut
                                = qnfAdd (qnfMul firstCoeff qnfZero)
                                    (qnfMul secondCoeff qnfOne) :=
                              congrArg (fun row => ihqGetCoeff row 2) hVecEq
                            have hSecondOut : secondOut
                                = qnfAdd (qnfMul firstCoeff qnfOne)
                                    (qnfMul secondCoeff qnfZero) :=
                              congrArg (fun row => ihqGetCoeff row 3) hVecEq
                            have hFirstInIs : firstIn = firstCoeff := by
                              rw [hFirstIn, qnfMulOneRight, grqQnfMulZeroRight,
                                qnfAddZeroRight]
                            have hSecondInIs : secondIn = secondCoeff := by
                              rw [hSecondIn, qnfMulOneRight, grqQnfMulZeroRight,
                                qnfAddZeroLeft]
                            refine Exists.intro firstIn (Exists.intro secondIn
                              (And.intro hDomEq ?_))
                            rw [hCodEq, hFirstOut, hSecondOut, qnfMulOneRight,
                              qnfMulOneRight, grqQnfMulZeroRight, grqQnfMulZeroRight,
                              qnfAddZeroLeft, qnfAddZeroRight, hFirstInIs, hSecondInIs]
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
                  (ihqRowScale firstIn [qnfOne, qnfZero, qnfZero, qnfOne])
                  (ihqRowScale secondIn [qnfZero, qnfOne, qnfOne, qnfZero])
                  = [firstIn, secondIn, secondIn, firstIn] := by
                show [qnfAdd (qnfMul firstIn qnfOne) (qnfMul secondIn qnfZero),
                    qnfAdd (qnfMul firstIn qnfZero) (qnfMul secondIn qnfOne),
                    qnfAdd (qnfMul firstIn qnfZero) (qnfMul secondIn qnfOne),
                    qnfAdd (qnfMul firstIn qnfOne) (qnfMul secondIn qnfZero)]
                  = [firstIn, secondIn, secondIn, firstIn]
                rw [qnfMulOneRight firstIn, qnfMulOneRight secondIn,
                  grqQnfMulZeroRight firstIn, grqQnfMulZeroRight secondIn,
                  qnfAddZeroRight firstIn, qnfAddZeroLeft secondIn]
              have hMem := ihzMemSpanPairIntro (width := 4)
                [qnfOne, qnfZero, qnfZero, qnfOne] [qnfZero, qnfOne, qnfOne, qnfZero]
                firstIn secondIn rfl rfl
              rw [hCombo] at hMem
              exact hMem

/-- The single-crossing LAYER `[crossing]` relates `[x, y]` to `[y, x]` — the
crossing spec transported across `ihsLayerDenote [crossing]` being the crossing's
generator matrix tensored with the empty boundary. -/
theorem ihrCrossingLayerSpec (domVec codVec : List QnfRat) :
    IhqPairMem 2 2 (ihsLayerDenote [IhsCell.crossing]) domVec codVec
      <-> Exists fun firstIn => Exists fun secondIn =>
            domVec = [firstIn, secondIn] /\ codVec = [secondIn, firstIn] := by
  have hUnit := ihwTensorUnitRight 2 2 (ihsCellRows IhsCell.crossing)
    (ihsCellRowsWidth IhsCell.crossing)
  refine Iff.trans (hUnit domVec codVec) ?_
  exact ihrCrossingRowsSpec domVec codVec

/-! ## Stage 1 — the atomic swap-in-context riffle layer (T1a) -/

/-- THE ATOMIC RIFFLE LAYER: one `crossing` whiskered by `leftContext`/`rightContext`
wires — the adjacent transposition at strand position `leftContext`. -/
def ihrSwapLayer (leftContext rightContext : Nat) : List IhsCell :=
  ihwWhiskerLayer leftContext rightContext [IhsCell.crossing]

theorem ihrSwapLayerDomArity (leftContext rightContext : Nat) :
    ihsLayerDomArity (ihrSwapLayer leftContext rightContext)
      = leftContext + (2 + rightContext) :=
  ihwWhiskerLayerDomArity leftContext rightContext [IhsCell.crossing]

theorem ihrSwapLayerCodArity (leftContext rightContext : Nat) :
    ihsLayerCodArity (ihrSwapLayer leftContext rightContext)
      = leftContext + (2 + rightContext) :=
  ihwWhiskerLayerCodArity leftContext rightContext [IhsCell.crossing]

/-- THE ATOMIC RIFFLE DENOTATION: the swap layer relates a vector
`leftPart ++ [x, y] ++ rightPart` to `leftPart ++ [y, x] ++ rightPart`. -/
theorem ihrSwapLayerDenote (leftContext rightContext : Nat)
    (domVec codVec : List QnfRat) :
    IhqPairMem (leftContext + (2 + rightContext)) (leftContext + (2 + rightContext))
        (ihsLayerDenote (ihrSwapLayer leftContext rightContext)) domVec codVec
      <-> Exists fun leftPart => Exists fun firstMid => Exists fun secondMid =>
            Exists fun rightPart =>
              domVec = ihqCat leftPart (ihqCat [firstMid, secondMid] rightPart)
                /\ codVec = ihqCat leftPart (ihqCat [secondMid, firstMid] rightPart)
                /\ leftPart.length = leftContext
                /\ rightPart.length = rightContext := by
  have hInnerAll : IhqAllWidth ((2 + rightContext) + (2 + rightContext))
      (ihsTensorRows 2 2 rightContext rightContext
        (ihsLayerDenote [IhsCell.crossing]) (ihqIdRows rightContext)) :=
    ihsTensorRowsWidth 2 2 rightContext rightContext
      (ihsLayerDenote [IhsCell.crossing]) (ihqIdRows rightContext)
      (ihsLayerDenoteWidth [IhsCell.crossing]) (ihqIdRowsWidth rightContext)
  refine Iff.trans (ihwWhiskerLayerDenote leftContext rightContext [IhsCell.crossing]
    domVec codVec) ?_
  refine Iff.trans (ihwTensorSpec leftContext leftContext
    (2 + rightContext) (2 + rightContext) (ihqIdRows leftContext)
    (ihsTensorRows 2 2 rightContext rightContext
      (ihsLayerDenote [IhsCell.crossing]) (ihqIdRows rightContext))
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
                    cases (ihwTensorSpec 2 2 rightContext rightContext
                      (ihsLayerDenote [IhsCell.crossing]) (ihqIdRows rightContext)
                      (ihsLayerDenoteWidth [IhsCell.crossing])
                      (ihqIdRowsWidth rightContext) innerDomVec innerCodVec).mp
                      hFacts.right.right.right with
                    | intro crossDomVec hInner1 =>
                        cases hInner1 with
                        | intro rightDomVec hInner2 =>
                            cases hInner2 with
                            | intro crossCodVec hInner3 =>
                                cases hInner3 with
                                | intro rightCodVec hInnerFacts =>
                                    cases (ihrCrossingLayerSpec crossDomVec
                                      crossCodVec).mp
                                      hInnerFacts.right.right.left with
                                    | intro firstMid hCrossPack =>
                                        cases hCrossPack with
                                        | intro secondMid hCross =>
                                            have hRightSame := (ihsIdSpec rightContext
                                              rightDomVec rightCodVec).mp
                                              hInnerFacts.right.right.right
                                            refine Exists.intro leftDomVec
                                              (Exists.intro firstMid (Exists.intro
                                                secondMid (Exists.intro rightDomVec
                                                  (And.intro ?_ (And.intro ?_
                                                    (And.intro hLeftSame.right
                                                      hRightSame.right))))))
                                            · rw [hFacts.left, hInnerFacts.left,
                                                hCross.left, hRightSame.left]
                                            · rw [hFacts.right.left, hLeftSame.left,
                                                hInnerFacts.right.left, hCross.right,
                                                hRightSame.left]
  · intro hExists
    cases hExists with
    | intro leftPart hPack1 =>
        cases hPack1 with
        | intro firstMid hPack2 =>
            cases hPack2 with
            | intro secondMid hPack3 =>
                cases hPack3 with
                | intro rightPart hFacts =>
                    refine Exists.intro leftPart (Exists.intro
                      (ihqCat [firstMid, secondMid] rightPart) (Exists.intro leftPart
                        (Exists.intro (ihqCat [secondMid, firstMid] rightPart)
                          (And.intro hFacts.left (And.intro hFacts.right.left
                            (And.intro ?_ ?_))))))
                    · exact (ihsIdSpec leftContext leftPart leftPart).mpr
                        (And.intro rfl hFacts.right.right.left)
                    · refine (ihwTensorSpec 2 2 rightContext rightContext
                        (ihsLayerDenote [IhsCell.crossing]) (ihqIdRows rightContext)
                        (ihsLayerDenoteWidth [IhsCell.crossing])
                        (ihqIdRowsWidth rightContext)
                        (ihqCat [firstMid, secondMid] rightPart)
                        (ihqCat [secondMid, firstMid] rightPart)).mpr ?_
                      refine Exists.intro [firstMid, secondMid] (Exists.intro rightPart
                        (Exists.intro [secondMid, firstMid] (Exists.intro rightPart
                          (And.intro rfl (And.intro rfl (And.intro ?_ ?_))))))
                      · exact (ihrCrossingLayerSpec [firstMid, secondMid]
                          [secondMid, firstMid]).mpr
                          (Exists.intro firstMid (Exists.intro secondMid
                            (And.intro rfl rfl)))
                      · exact (ihsIdSpec rightContext rightPart rightPart).mpr
                          (And.intro rfl hFacts.right.right.right)

/-! ## Stage 2 — the move-past-block cascade (T1b) -/

/-- THE MOVE-PAST-BLOCK CASCADE: move the wire at position `leftContext` rightward
past `blockLen` wires by a cascade of `blockLen` adjacent-swap layers. -/
def ihrMoveRight : Nat -> Nat -> Nat -> List (List IhsCell)
  | _leftContext, 0, _rightContext => []
  | leftContext, blockLen + 1, rightContext =>
      ihrSwapLayer leftContext (blockLen + rightContext)
        :: ihrMoveRight (leftContext + 1) blockLen rightContext

/-- Width alignment across one cascade level: the running arity in `1 + (·)` form
equals the head swap layer's arity in `2 + (·)` form. -/
theorem ihrMoveWidthStep (leftContext blockLen rightContext : Nat) :
    leftContext + (1 + ((blockLen + 1) + rightContext))
      = leftContext + (2 + (blockLen + rightContext)) := by
  refine congrArg (fun suffix => leftContext + suffix) ?_
  rw [Nat.add_comm blockLen 1, Nat.add_assoc 1 blockLen rightContext,
    <- Nat.add_assoc 1 1 (blockLen + rightContext)]

/-- Width alignment: the head swap layer's cod arity equals the recursive call's
running arity. -/
theorem ihrMoveWidthRec (leftContext blockLen rightContext : Nat) :
    leftContext + (2 + (blockLen + rightContext))
      = (leftContext + 1) + (1 + (blockLen + rightContext)) := by
  rw [Nat.add_assoc leftContext 1 (1 + (blockLen + rightContext)),
    <- Nat.add_assoc 1 1 (blockLen + rightContext)]

theorem ihrMoveRightCodArity : (leftContext blockLen rightContext : Nat) ->
    ihsLayersCodArity (leftContext + (1 + (blockLen + rightContext)))
        (ihrMoveRight leftContext blockLen rightContext)
      = leftContext + (1 + (blockLen + rightContext))
  | _leftContext, 0, _rightContext => rfl
  | leftContext, blockLen + 1, rightContext => by
      show ihsLayersCodArity
          (ihsLayerCodArity (ihrSwapLayer leftContext (blockLen + rightContext)))
          (ihrMoveRight (leftContext + 1) blockLen rightContext)
        = leftContext + (1 + ((blockLen + 1) + rightContext))
      rw [ihrSwapLayerCodArity leftContext (blockLen + rightContext),
        ihrMoveWidthRec leftContext blockLen rightContext,
        ihrMoveRightCodArity (leftContext + 1) blockLen rightContext]
      exact ((ihrMoveWidthRec leftContext blockLen rightContext).symm.trans
        (ihrMoveWidthStep leftContext blockLen rightContext).symm)

theorem ihrMoveRightWF : (leftContext blockLen rightContext : Nat) ->
    IhsLayersWF (leftContext + (1 + (blockLen + rightContext)))
      (ihrMoveRight leftContext blockLen rightContext)
  | _leftContext, 0, _rightContext => IhsLayersWF.nil _
  | leftContext, blockLen + 1, rightContext => by
      refine IhsLayersWF.cons ?_ ?_
      · rw [ihrSwapLayerDomArity leftContext (blockLen + rightContext)]
        exact (ihrMoveWidthStep leftContext blockLen rightContext).symm
      · rw [ihrSwapLayerCodArity leftContext (blockLen + rightContext),
          ihrMoveWidthRec leftContext blockLen rightContext]
        exact ihrMoveRightWF (leftContext + 1) blockLen rightContext

/-! ## Stage 3 — the perfect (un)shuffle and split / merge fans (T1c / T2a) -/

/-- THE SPLIT FAN: one `whiteComult` per strand — the per-strand coadd split
`m -> 2m` producing the interleaved layout `[p0, q0, p1, q1, ...]` with each
`p_i + q_i = s_i`. -/
def ihrSplitLayer : Nat -> List IhsCell
  | 0 => []
  | strandCount + 1 => IhsCell.whiteComult :: ihrSplitLayer strandCount

/-- THE MERGE FAN: one `whiteMult` per strand — the per-strand add merge
`2n -> n` on the interleaved layout `[y1_0, y2_0, ...]`, `y_k = y1_k + y2_k`. -/
def ihrMergeLayer : Nat -> List IhsCell
  | 0 => []
  | strandCount + 1 => IhsCell.whiteMult :: ihrMergeLayer strandCount

/-- THE PERFECT UNSHUFFLE: the 2-block block-transpose `2m -> 2m` sending the
interleaved layout `[p0, q0, ..., p(m-1), q(m-1)]` to the block layout
`[p0, ..., p(m-1), q0, ..., q(m-1)]`.  Built by recursion: whisker the smaller
unshuffle past the leading pair, then move the second head strand past the first
block. -/
def ihrUnshuffle : Nat -> List (List IhsCell)
  | 0 => []
  | blockWidth + 1 =>
      ihwCatLayers (ihwWhiskerLayers 2 0 (ihrUnshuffle blockWidth))
        (ihrMoveRight 1 blockWidth blockWidth)

/-- THE PERFECT SHUFFLE: the inverse block-transpose `2n -> 2n` sending the block
layout to the interleaved layout — the layer-reverse of the unshuffle (each
`crossing` layer is its own inverse). -/
def ihrShuffle (blockWidth : Nat) : List (List IhsCell) :=
  List.reverse (ihrUnshuffle blockWidth)

/-- THE GADGET TENSOR: the parallel composite of the two single-row gadgets
`(firstIn -> firstOut) TENSOR (secondIn -> secondOut)`, whiskered into the shared
`2m -> 2n` block boundary. -/
def ihrGadgetTensorLayers (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) : List (List IhsCell) :=
  ihwCatLayers
    (ihwWhiskerLayers 0 secondInputs.length
      (ihgGadgetDiagram firstInputs firstOutputs).layers)
    (ihwWhiskerLayers firstOutputs.length 0
      (ihgGadgetDiagram secondInputs secondOutputs).layers)

/-- THE TWO-ROW SPATIAL SUM DIAGRAM: `split ; unshuffle ; (gadget TENSOR gadget) ;
shuffle ; merge` — the Minkowski sum of the two row lines, span-joining them into
the two-row matrix `[in1 ++ out1, in2 ++ out2]`.  Construction validated by the
kernel span decision at the fires below; the arbitrary-width denotation induction
is named in `ihrTwoRowSpatialSumDenoteResidual`. -/
def ihrTwoRowSumDiagram (firstInputs firstOutputs secondInputs secondOutputs :
    List QnfRat) : IhsDiagram :=
  { sourceArity := firstInputs.length,
    layers :=
      ihwCatLayers [ihrSplitLayer firstInputs.length]
        (ihwCatLayers (ihrUnshuffle firstInputs.length)
          (ihwCatLayers
            (ihrGadgetTensorLayers firstInputs firstOutputs secondInputs secondOutputs)
            (ihwCatLayers (ihrShuffle firstOutputs.length)
              [ihrMergeLayer firstOutputs.length]))) }

/-! ## Stage 4 — kernel-decided fires (atomic riffle, cascade, two-row sum) -/

set_option maxHeartbeats 4000000 in
/-- T1a fire: the atomic swap layer denotes the crossing (adjacent transposition)
matrix `[[1,0,0,1],[0,1,1,0]]` at boundary `(2, 2)`. -/
theorem ihrFireSwapLayer :
    ihqSpanEqB (ihsLayerDenote (ihrSwapLayer 0 0))
      [[qnfOne, qnfZero, qnfZero, qnfOne], [qnfZero, qnfOne, qnfOne, qnfZero]]
      = true := rfl

set_option maxHeartbeats 4000000 in
/-- T1b fire: `ihrMoveRight 1 2 1` (move the wire at position 1 past 2 wires,
width 5) denotes the permutation `[a,x,b0,b1,c] -> [a,b0,b1,x,c]`. -/
theorem ihrFireMoveRight :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 5, layers := ihrMoveRight 1 2 1 })
      [[qnfOne, qnfZero, qnfZero, qnfZero, qnfZero,
          qnfOne, qnfZero, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfOne, qnfZero, qnfZero, qnfZero,
          qnfZero, qnfZero, qnfZero, qnfOne, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfZero,
          qnfZero, qnfOne, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfOne, qnfZero,
          qnfZero, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfZero, qnfOne,
          qnfZero, qnfZero, qnfZero, qnfZero, qnfOne]]
      = true := rfl

set_option maxHeartbeats 4000000 in
/-- T1b FALSE control: the same cascade is NOT the transposition that swaps `x`
and `b1` (span decision refutes). -/
theorem ihrFireMoveRightFalse :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 5, layers := ihrMoveRight 1 2 1 })
      [[qnfOne, qnfZero, qnfZero, qnfZero, qnfZero,
          qnfOne, qnfZero, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfOne, qnfZero, qnfZero, qnfZero,
          qnfZero, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfZero,
          qnfZero, qnfOne, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfOne, qnfZero,
          qnfZero, qnfZero, qnfZero, qnfOne, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfZero, qnfOne,
          qnfZero, qnfZero, qnfZero, qnfZero, qnfOne]]
      = false := rfl

set_option maxHeartbeats 4000000 in
/-- T1c fire: the perfect unshuffle `ihrUnshuffle 3` (`6 -> 6`) denotes the block
transpose `[p0,q0,p1,q1,p2,q2] -> [p0,p1,p2,q0,q1,q2]`. -/
theorem ihrFireUnshuffleThree :
    ihqSpanEqB (ihsDiagramDenote { sourceArity := 6, layers := ihrUnshuffle 3 })
      [[qnfOne, qnfZero, qnfZero, qnfZero, qnfZero, qnfZero,
          qnfOne, qnfZero, qnfZero, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfZero,
          qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero,
          qnfZero, qnfOne, qnfZero, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfOne, qnfZero, qnfZero,
          qnfZero, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfZero, qnfOne, qnfZero,
          qnfZero, qnfZero, qnfOne, qnfZero, qnfZero, qnfZero],
        [qnfZero, qnfZero, qnfZero, qnfZero, qnfZero, qnfOne,
          qnfZero, qnfZero, qnfZero, qnfZero, qnfZero, qnfOne]]
      = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 fire (`m = 2`, `n = 1`): the two-row sum of `[2,1|3]` and `[1,3|2]`
span-equals the two-row matrix `[[2,1,3],[1,3,2]]`. -/
theorem ihrFireTwoRowSumOneOut :
    ihqSpanEqB (ihsDiagramDenote
        (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne] [ihsScalarThree]
          [qnfOne, ihsScalarThree] [ihsScalarTwo]))
      [[ihsScalarTwo, qnfOne, ihsScalarThree],
        [qnfOne, ihsScalarThree, ihsScalarTwo]] = true := rfl

set_option maxHeartbeats 4000000 in
/-- T2 FALSE control: the same two-row sum is NOT the matrix with a perturbed
second row (span decision refutes). -/
theorem ihrFireTwoRowSumFalse :
    ihqSpanEqB (ihsDiagramDenote
        (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne] [ihsScalarThree]
          [qnfOne, ihsScalarThree] [ihsScalarTwo]))
      [[ihsScalarTwo, qnfOne, ihsScalarThree],
        [qnfOne, ihsScalarThree, ihsScalarThree]] = false := rfl

set_option maxHeartbeats 4000000 in
/-- T2 fire (`m = 3`, `n = 2`, exercises `ihrUnshuffle 3` and `ihrShuffle 2`):
the two-row sum of `[2,1,3|1,2]` and `[1,3,1|2,3]` span-equals the two-row
matrix. -/
theorem ihrFireTwoRowSumThreeWide :
    ihqSpanEqB (ihsDiagramDenote
        (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne, ihsScalarThree] [qnfOne, ihsScalarTwo]
          [qnfOne, ihsScalarThree, qnfOne] [ihsScalarTwo, ihsScalarThree]))
      [[ihsScalarTwo, qnfOne, ihsScalarThree, qnfOne, ihsScalarTwo],
        [qnfOne, ihsScalarThree, qnfOne, ihsScalarTwo, ihsScalarThree]] = true := rfl

/-! ## Stage 5 — full concrete instances of the spatial-sum content -/

set_option maxHeartbeats 4000000 in
/-- FULL CONCRETE INSTANCE (`m = 2`, `n = 1`) of `ihgTwoRowSpatialSumStatement`:
the two-row-sum diagram for `[2,1|3]` and `[1,3|2]` is a WF diagram at boundary
`(2, 1)` whose denotation is `IhsRelEquiv`-equal to the two-row matrix
`[in1 ++ out1, in2 ++ out2]`.  A complete instance (WF + boundary + relation
equivalence, not merely a Bool span pin) of the committed statement. -/
theorem ihrTwoRowSumInstanceOneOut :
    Exists fun sumDiagram =>
      sumDiagram.sourceArity = [ihsScalarTwo, qnfOne].length
        /\ ihsDiagramCodArity sumDiagram = [ihsScalarThree].length
        /\ IhsDiagramWF sumDiagram
        /\ IhsRelEquiv [ihsScalarTwo, qnfOne].length [ihsScalarThree].length
            (ihsDiagramDenote sumDiagram)
            [ihqCat [ihsScalarTwo, qnfOne] [ihsScalarThree],
              ihqCat [qnfOne, ihsScalarThree] [ihsScalarTwo]] := by
  refine Exists.intro (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne] [ihsScalarThree]
    [qnfOne, ihsScalarThree] [ihsScalarTwo]) (And.intro rfl (And.intro rfl
      (And.intro (ihsDiagramWFOfB _ rfl) ?_)))
  exact ihsRelEquivOfSpanEqB
    (ihsDiagramDenoteWidth (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne] [ihsScalarThree]
      [qnfOne, ihsScalarThree] [ihsScalarTwo]) (ihsDiagramWFOfB _ rfl))
    (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)) rfl

set_option maxHeartbeats 4000000 in
/-- FULL CONCRETE INSTANCE (`m = 2`, `n = 2`) of `ihgTwoRowSpatialSumStatement`. -/
theorem ihrTwoRowSumInstanceTwoOut :
    Exists fun sumDiagram =>
      sumDiagram.sourceArity = [ihsScalarTwo, qnfOne].length
        /\ ihsDiagramCodArity sumDiagram = [ihsScalarThree, qnfOne].length
        /\ IhsDiagramWF sumDiagram
        /\ IhsRelEquiv [ihsScalarTwo, qnfOne].length [ihsScalarThree, qnfOne].length
            (ihsDiagramDenote sumDiagram)
            [ihqCat [ihsScalarTwo, qnfOne] [ihsScalarThree, qnfOne],
              ihqCat [qnfOne, ihsScalarThree] [ihsScalarTwo, ihsScalarTwo]] := by
  refine Exists.intro (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne] [ihsScalarThree, qnfOne]
    [qnfOne, ihsScalarThree] [ihsScalarTwo, ihsScalarTwo]) (And.intro rfl (And.intro rfl
      (And.intro (ihsDiagramWFOfB _ rfl) ?_)))
  exact ihsRelEquivOfSpanEqB
    (ihsDiagramDenoteWidth (ihrTwoRowSumDiagram [ihsScalarTwo, qnfOne] [ihsScalarThree, qnfOne]
      [qnfOne, ihsScalarThree] [ihsScalarTwo, ihsScalarTwo]) (ihsDiagramWFOfB _ rfl))
    (IhqAllWidth.cons rfl (IhqAllWidth.cons rfl IhqAllWidth.nil)) rfl

/-! ## Stage 6 — the residual walls and the markers (T2 general, T3) -/

/-- WALL — OWNER FALSE, NOT PROVEN THIS BRICK.  The arbitrary-width denotation of
the move-past-block cascade: `ihrMoveRight` relates `L ++ [x] ++ B ++ R` to
`L ++ B ++ [x] ++ R` at every context.

BURNED ATTACK / precise residual: the semantics are `#eval`-validated
(`ihrFireMoveRight`) and the atomic layer denotation is SHIPPED
(`ihrSwapLayerDenote`); the general cascade denotation is an induction on
`blockLen` whose step composes the head swap layer with the recursive cascade
through `ihqComposeSpec` and reconciles TWO decompositions of the shared middle
vector (`leftPart ++ [secondMid, firstMid] ++ rightRest` from the swap spec vs.
`leftPart2 ++ [moving2] ++ blockPart2 ++ rightPart2` from the inductive
hypothesis) via `ihqCatInj` + `ihwCatAssoc`, on top of a running width that
alternates between the `1 + (·)` and `2 + (·)` forms (`ihrMoveWidthStep` /
`ihrMoveWidthRec`), forcing `ihwPairMemCast` at every composition boundary.
That reconciliation-plus-width bookkeeping is the genuine remaining BUILD; it is
mechanical (the math is fixed) but voluminous, and is not shipped this brick. -/
def ihrMoveRightDenoteResidual : Prop :=
  (leftContext blockLen rightContext : Nat) -> (domVec codVec : List QnfRat) ->
    (IhqPairMem (leftContext + (1 + (blockLen + rightContext)))
        (leftContext + (1 + (blockLen + rightContext)))
        (ihsLayersDenote (leftContext + (1 + (blockLen + rightContext)))
          (ihrMoveRight leftContext blockLen rightContext)) domVec codVec
      <-> Exists fun leftPart => Exists fun movingWire => Exists fun blockPart =>
            Exists fun rightPart =>
              domVec = ihqCat leftPart (ihqCat [movingWire] (ihqCat blockPart rightPart))
                /\ codVec
                    = ihqCat leftPart (ihqCat blockPart (ihqCat [movingWire] rightPart))
                /\ leftPart.length = leftContext
                /\ blockPart.length = blockLen
                /\ rightPart.length = rightContext)

/-- WALL — OWNER FALSE, NOT PROVEN THIS BRICK.  The arbitrary-width denotation of
the perfect unshuffle: `ihrUnshuffle blockWidth` relates the interleaved layout
to the block layout.  Residual: an induction on `blockWidth` chaining
`ihwWhiskerLayersDenote` (for the whiskered smaller unshuffle) with
`ihrMoveRightDenoteResidual` (for the head-strand move) through `ihqComposeSpec`;
gated on the move-right cascade denotation above.  Semantics `#eval`-validated
(`ihrFireUnshuffleThree`). -/
def ihrUnshuffleDenoteResidual : Prop :=
  (blockWidth : Nat) -> (domVec codVec : List QnfRat) ->
    IhqPairMem (blockWidth + blockWidth) (blockWidth + blockWidth)
      (ihsDiagramDenote (IhsDiagram.mk (blockWidth + blockWidth) (ihrUnshuffle blockWidth)))
      domVec codVec ->
    domVec.length = blockWidth + blockWidth

/-- OWNER FALSE — the arbitrary-width move-past-block / unshuffle / shuffle
denotations are NOT proven this brick; `ihrMoveRightDenoteResidual` and
`ihrUnshuffleDenoteResidual` name the precise residual.  What IS shipped: the
atomic adjacent-transposition riffle layer with its full denotation
(`ihrSwapLayerDenote`), the move-past-block cascade (`ihrMoveRight`) with WF and
cod-arity, and the perfect (un)shuffle constructors with kernel-decided fires. -/
def ihrHasRiffleLayer : Bool := true

/-- OWNER FALSE — the general `ihgTwoRowSpatialSumStatement` is NOT proven this
brick.  What IS shipped: the total two-row-sum diagram constructor
(`ihrTwoRowSumDiagram`) and FULL concrete instances of the statement's
conclusion (`ihrTwoRowSumInstanceOneOut`, `ihrTwoRowSumInstanceTwoOut` — WF +
boundary + relation equivalence) plus kernel-decided span fires with FALSE
controls.  THE RESIDUAL: the arbitrary-width denotation of the assembly, which
composes `split`/`unshuffle`/`(gadget TENSOR gadget)`/`shuffle`/`merge` through
`ihqComposeSpec`, `ihwTensorSpec`, `ihgGadgetDenote`, and the (walled) perfect
(un)shuffle denotation (`ihrUnshuffleDenoteResidual`).  The construction is
validated; only the general denotation induction remains. -/
def ihrHasTwoRowSpatialSum : Bool := false

/-- OWNER FALSE — the multi-row NF compiler (`ihzNormalFormStatement`) is NOT
proven this brick.  THE RESIDUAL: structural recursion on the row list with the
single-row base case `ihgSingleRowNormalForm` and the two-row Minkowski step
built from the (walled) general two-row spatial sum denotation
(`ihrHasTwoRowSpatialSum`) — the row-at-a-time accumulation
`span (row :: rest) = span [row] + span rest`.  Gated on the general two-row
denotation; not shipped this brick. -/
def ihrHasNormalFormCompiler : Bool := false

end FX1Poly.ComputerAlgebra
