import FX1Poly.Polygraph.Omega.ZXPhaseFree.FinalFlip

/-! # Polygraph/Omega/ZXPhaseFree/TransportRides — the comb-move rides

The FinalFlip round reduced `zxwGeneratorTransportStatement` to two named
adjacent-comb moves (`zxfCombSwapStatement`, `zxfCombXorAbsorbStatement`) and
walled the fourth crossing-ride window (`zxfCrossWindowTTStatement`) with a
documented on-paper derivation.  This round lands:

* (i)  THE TT CROSSING WINDOW (`zxtCrossWindowTTHolds`): the documented
  twenty-four-move chain, transcribed whole — three fork-extraction exchange
  pairs, the fork slide through the leading crossing, the inner fork slide,
  five more disjoint-block exchange pairs, two new derived merge-routing
  windows (`zxtCrossThenMergeRight`, `zxtMergeAfterCross`), Yang-Baxter twice,
  X-monoid commutativity twice and associativity once, the sigma involution
  twice, and two wire strips.  This COMPLETES the four-window layer of the
  swap ride (FF/FT/TF committed in FinalFlip).
* (ii) the merge-routing bricks: `zxtCrossThenMergeRight` (a crossing feeding
  the left leg of a merge re-routes to the right leg) and `zxtMergeAfterCross`
  (its mirror), each three moves from the slides, the involution and a strip.
* (iii) THE DOUBLE-COMB CARRIER (`zxtDoubleLayers`): the zipped two-carrier
  comb — per strand, the inner-carrier gadget then the outer-carrier gadget —
  with well-formedness and output-arity lemmas; the interleaving lemma
  (`zxtDoubleOfCombLayers`) converting two sequential solo combs into the
  zipped form by parking each outer gadget past the inner comb tail through
  the committed block-routing engine; and THE CROSSING RIDE
  (`zxtCrossRideDouble`): a crossing between the two carriers rides the whole
  zipped comb, swapping the carrier roles position by position through the
  four windows, and dies at the discard boundary.
* (iv) THE ADJACENT COMB SWAP (`zxtCombSwapHolds : zxfCombSwapStatement`):
  park the second creation behind the first comb (block-routing engine at the
  creation block), zip, insert the birth crossing
  (`zxfCreatesCrossInsert` backwards), ride, unzip, unpark.
* (v)  the four CNOT ride windows for the transvection ride, minted as named
  statements with kernel span pins; the FF window PROVEN
  (`zxtCnotWindowFFHolds`) — the CNOT gadget passes a double-skip position by
  two exchange pairs and two slides; TF/FT/TT walled owner-false with their
  exact configurations (TF = double-fork reassociation, FT = the bialgebra
  square, TT = bialgebra plus the Hopf cancellation).
* (vi) NOT LANDED (recorded on the markers, owners false): the transvection
  ride and therefore `zxfCombXorAbsorbStatement`;
  `zxwGeneratorTransportStatement` stays open — the committed FinalFlip and
  WiringFlip owners stay byte-intact and false; the residual is exactly the
  three cnot windows plus the cnot ride skeleton (which now has a proven
  template in the crossing ride).

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no
`List.append`, no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms
over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — exchange-pair plumbing

Two disjoint one-layer blocks commute; the committed primitives give the two
splits of the merged tensor layer.  Both composite directions are packaged
here once and reused throughout the rides. -/

/-- Left-first two-layer split converts to right-first: merge by the layer
split read backwards, re-split by the exchange read backwards. -/
theorem zxtLeftFirstToRightFirst (leftCells rightCells : List ZxpCell) :
    ZxwConv
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
          zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells] }
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells,
          zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))] } :=
  ZxwConv.trans
    (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
      (ZxrWindowMove.seed (ZxpWindowMove.splitLayer leftCells rightCells))))))
    (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
      (ZxeWindowMove.rightFirstExchange leftCells rightCells))))

/-- Right-first two-layer split converts to left-first: the exchange forward,
then the layer split forward. -/
theorem zxtRightFirstToLeftFirst (leftCells rightCells : List ZxpCell) :
    ZxwConv
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity leftCells)) rightCells,
          zxpCatCells leftCells (zxpWireCells (zxpLayerCodArity rightCells))] }
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
          zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells] } :=
  ZxwConv.trans
    (zxwMoveConv (ZxwWindowMove.base
      (ZxeWindowMove.rightFirstExchange leftCells rightCells)))
    (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
      (ZxrWindowMove.seed (ZxpWindowMove.splitLayer leftCells rightCells)))))

/-! ## Stage 1 — the merge-routing bricks

A crossing feeding the LEFT leg of an adjacent merge re-routes to the RIGHT
leg (and mirrored).  Three moves each: insert a crossing pair by the sigma
involution read backwards behind a fresh wire layer, then absorb three of the
four crossings into the staircase side of the merge slide. -/

/-- `[crossing, w] ; [w, x21]  ~  [w, crossing] ; [x21, w] ; [crossing]`:
the crossing entering the far merge leg trades for a crossing on the passive
pair plus one exiting crossing. -/
theorem zxtCrossThenMergeRight :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.crossing]] } := by
  -- step A: grow a leading wire layer (strip read backwards)
  have hStrip := zxwOfZxeConv
    (zxeStripLeadingWireLayer [ZxpCell.crossing, ZxpCell.wire])
  have hStripLift := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.xSpider 2 1]] (ZxwConv.symm hStrip)
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hStripLift
  refine ZxwConv.trans hStepA ?_
  -- step B: the wire pair at positions 1-2 becomes a crossing pair (involution
  -- read backwards, whisker (1,0))
  have hInvolution := ZxwConv.symm (zxwMoveConv ZxwWindowMove.sigmaInvolution)
  have hInvolutionLift := zxwConvLift 3 1 0 []
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]]
    hInvolution (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hInvolutionLift
  refine ZxwConv.trans hStepB ?_
  -- step C: the trailing three layers are the staircase side of the merge
  -- slide; collapse them to merge-then-crossing
  have hSlide := ZxwConv.symm (zxwSlideRightConv (ZxpCell.xSpider 2 1))
  have hSlideLift := zxwLiftConv 3 [[ZxpCell.wire, ZxpCell.crossing]] []
    hSlide (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hSlideLift
  exact hSlideLift

/-- `[w, crossing] ; [x21, w]  ~  [crossing, w] ; [w, x21] ; [crossing]`:
the mirror routing at the near merge leg. -/
theorem zxtMergeAfterCross :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1], [ZxpCell.crossing]] } := by
  have hStrip := zxwOfZxeConv
    (zxeStripLeadingWireLayer [ZxpCell.wire, ZxpCell.crossing])
  have hStripLift := zxwLiftConv 3 []
    [[ZxpCell.xSpider 2 1, ZxpCell.wire]] (ZxwConv.symm hStrip)
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hStripLift
  refine ZxwConv.trans hStepA ?_
  have hInvolution := ZxwConv.symm (zxwMoveConv ZxwWindowMove.sigmaInvolution)
  have hInvolutionLift := zxwConvLift 3 0 1 []
    [[ZxpCell.wire, ZxpCell.crossing], [ZxpCell.xSpider 2 1, ZxpCell.wire]]
    hInvolution (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hInvolutionLift
  refine ZxwConv.trans hStepB ?_
  have hSlide := ZxwConv.symm (zxwSlideLeftConv (ZxpCell.xSpider 2 1))
  have hSlideLift := zxwLiftConv 3 [[ZxpCell.crossing, ZxpCell.wire]] []
    hSlide (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hSlideLift
  exact hSlideLift

/-! ## Stage 2 — THE TT CROSSING WINDOW, WHOLE

The r10 wall (`zxfCrossWindowTTStatement`) falls to the documented chain: the
second-gadget fork extracts backward through three exchange pairs, the leading
crossing dissolves into both forks by the two slide orientations, the merge
chain reassociates by X-monoid associativity/commutativity, the merge-routing
bricks re-route both crossings feeding merges, Yang-Baxter fires twice, the
sigma involution kills both doubled crossing pairs, and the two fork/merge
blocks exit through five more exchange pairs. -/

/-- THE TT CROSSING WINDOW: the crossing rides past a double tap position. -/
theorem zxtCrossWindowTTHolds : zxfCrossWindowTTStatement := by
  show ZxwConv
    { sourceArity := 3
      layers := [[ZxpCell.crossing, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire]] }
    { sourceArity := 3
      layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.crossing]] }
  -- step 1: exchange pair — the second fork extracts past the ride crossing
  have hLift1 := zxwLiftConv 3
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift1
  refine ZxwConv.trans hStep1 ?_
  -- step 2: exchange pair — the fork extracts past the first merge
  have hLift2 := zxwLiftConv 3
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2]
      [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift2
  refine ZxwConv.trans hStep2 ?_
  -- step 3: exchange pair — the fork extracts past the first fork
  have hLift3 := zxwLiftConv 3
    [[ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2]
      [ZxpCell.zSpider 1 2, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift3
  refine ZxwConv.trans hStep3 ?_
  -- step 4: the extracted fork slides left through the ride crossing
  have hLift4 := zxwConvLift 3 0 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.symm (zxwSlideLeftConv (ZxpCell.zSpider 1 2)))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift4
  refine ZxwConv.trans hStep4 ?_
  -- step 5: the inner fork pulls back through its crossing (right slide)
  have hLift5 := zxwConvLift 3 1 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 2)))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift5
  refine ZxwConv.trans hStep5 ?_
  -- step 6: exchange pair — the stray crossing extracts past the far merge
  have hLift6 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.crossing]
      [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift6
  refine ZxwConv.trans hStep6 ?_
  -- step 7: the crossing feeding the far merge leg re-routes
  have hLift7 := zxwConvLift 3 2 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    zxtCrossThenMergeRight
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep7 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift7
  refine ZxwConv.trans hStep7 ?_
  -- step 8: Yang-Baxter on the inner crossing triple
  have hLift8 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    zxwYangBaxter
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep8 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift8
  refine ZxwConv.trans hStep8 ?_
  -- step 9: the crossing dies into the near merge (X commutativity)
  have hLift9 := zxwConvLift 3 1 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidComm))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep9 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift9
  refine ZxwConv.trans hStep9 ?_
  -- step 10: the crossing feeding the near merge leg re-routes (mirror brick)
  have hLift10 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    zxtMergeAfterCross
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep10 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift10
  refine ZxwConv.trans hStep10 ?_
  -- step 11: the sigma involution kills the doubled crossing pair
  have hLift11 := zxwConvLift 3 1 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep11 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift11
  refine ZxwConv.trans hStep11 ?_
  -- step 12: strip the dead wire layer
  have hLift12 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep12 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift12
  refine ZxwConv.trans hStep12 ?_
  -- step 13: the merge chain reassociates (X associativity)
  have hLift13 := zxwConvLift 3 2 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidAssoc))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep13 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift13
  refine ZxwConv.trans hStep13 ?_
  -- step 14: the remaining inner crossing dies into its merge
  have hLift14 := zxwConvLift 3 3 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidComm))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep14 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift14
  refine ZxwConv.trans hStep14 ?_
  -- step 15: the first fork pulls back through the leading crossing
  have hLift15 := zxwConvLift 3 0 2
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 2)))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep15 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift15
  refine ZxwConv.trans hStep15 ?_
  -- step 16: exchange pair — the outer crossing extracts past the far merge
  have hLift16 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.crossing]
      [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep16 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift16
  refine ZxwConv.trans hStep16 ?_
  -- step 17: exchange pair — the outer crossing extracts past the near merge
  have hLift17 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.crossing] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep17 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift17
  refine ZxwConv.trans hStep17 ?_
  -- step 18: exchange pair — the inner crossing extracts past the far merge
  have hLift18 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.crossing]
      [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep18 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift18
  refine ZxwConv.trans hStep18 ?_
  -- step 19: the inner crossing re-routes at the near merge
  have hLift19 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    zxtCrossThenMergeRight
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep19 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift19
  refine ZxwConv.trans hStep19 ?_
  -- step 20: Yang-Baxter backwards on the exit crossing triple
  have hLift20 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing]] []
    (ZxwConv.symm zxwYangBaxter)
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLift20
  have hStep20 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hLift20
  refine ZxwConv.trans hStep20 ?_
  -- step 21: the involution kills the doubled exit pair
  have hLift21 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep21 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hLift21
  refine ZxwConv.trans hStep21 ?_
  -- step 22: strip the dead wire layer
  have hLift22 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer [ZxpCell.crossing, ZxpCell.wire]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep22 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hLift22
  refine ZxwConv.trans hStep22 ?_
  -- step 23: exchange pair — the second fork re-enters past the far merge
  have hLift23 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtLeftFirstToRightFirst [ZxpCell.zSpider 1 2]
      [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep23 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hLift23
  refine ZxwConv.trans hStep23 ?_
  -- step 24: exchange pair — the fork passes the carrier crossing; the window
  -- closes on the committed right-hand side
  have hLift24 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtLeftFirstToRightFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep24 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hLift24
  exact hStep24

/-- CONTENT MARKER: the TT crossing window is machine-checked — the four-window
layer of the swap ride is COMPLETE (FF/FT/TF committed in FinalFlip, TT here).
Supersedes the r10 owner `zxfCrossWindowTTIsProven := false`, which stays
byte-intact in its home file. -/
def zxtCrossWindowTTIsProven : Bool := true

/-! ## Stage 3 — the four CNOT ride windows (the transvection ride layer)

The transvection ride conjugates the zipped double comb by a CNOT between the
two carriers (control = inner carrier, target = outer carrier; the gadget is
`[[w, z12], [x21, w]]` — fork the inner, merge into the outer).  Riding one
strand position transforms the window pair `(a, b)` into `(a, b)` with the
FIRST comb's tap flipped by the second's: `cnot ; D(a, b) ~ D(a xor b, b) ;
cnot'`.  Four windows: FF and TF are routing-only and PROVEN here; FT and TT
carry the algebraic content (the bialgebra square, respectively bialgebra plus
Hopf cancellation) and are walled owner-false with kernel span pins. -/

/-- THE FF CNOT WINDOW: the carrier CNOT passes a double-skip position — two
disjoint-block exchange pairs and the two fork/merge slides. -/
theorem zxtCnotWindowFFHolds :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := by
  -- step 1: the CNOT merge extracts past the skip crossing
  have hLift1 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift1
  refine ZxwConv.trans hStep1 ?_
  -- step 2: the merge slides right through the second crossing
  have hLift2 := zxwConvLift 3 0 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]] []
    (zxwSlideRightConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift2
  refine ZxwConv.trans hStep2 ?_
  -- step 3: the CNOT fork slides right through both crossings
  have hLift3 := zxwConvLift 3 1 0 []
    [[ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwSlideRightConv (ZxpCell.zSpider 1 2))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift3
  refine ZxwConv.trans hStep3 ?_
  -- step 4: the parked fork re-enters past the outer crossing
  have hLift4 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.crossing] [ZxpCell.zSpider 1 2])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift4
  exact hStep4

/-- THE TF CNOT WINDOW: the carrier CNOT passes a tap/skip position — the
inner carrier is forked twice (once for the CNOT, once for the tap), and the
two forks trade roles by Z-coassociativity; everything else is routing. -/
theorem zxtCnotWindowTFHolds :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := by
  -- step 1: the tap fork extracts past the CNOT merge
  have hLift1 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.zSpider 1 2, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift1
  refine ZxwConv.trans hStep1 ?_
  -- step 2: the CNOT merge extracts past the tap merge
  have hLift2 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift2
  refine ZxwConv.trans hStep2 ?_
  -- step 3: the CNOT merge extracts past the exit crossing
  have hLift3 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift3
  refine ZxwConv.trans hStep3 ?_
  -- step 4: the CNOT merge slides right through the outer crossing
  have hLift4 := zxwConvLift 3 0 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]] []
    (zxwSlideRightConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift4
  refine ZxwConv.trans hStep4 ?_
  -- step 5: the two forks trade roles (Z-coassociativity backwards)
  have hLift5 := zxwConvLift 3 1 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc)))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift5
  refine ZxwConv.trans hStep5 ?_
  -- step 6: the surviving fork extracts past the tap merge
  have hLift6 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.zSpider 1 2] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift6
  refine ZxwConv.trans hStep6 ?_
  -- step 7: the fork slides right through both remaining crossings
  have hLift7 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwSlideRightConv (ZxpCell.zSpider 1 2))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep7 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift7
  refine ZxwConv.trans hStep7 ?_
  -- step 8: the fork re-enters past the outer crossing
  have hLift8 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.crossing] [ZxpCell.zSpider 1 2])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep8 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift8
  exact hStep8

/-- THE FT CNOT WINDOW (owner-false residual): the carrier CNOT passes a
skip/tap position.  The algebraic content is THE BIALGEBRA SQUARE: after the
CNOT, the tap forks the x-merged carrier `t2 + t1`, and distributing that
Z-fork over the X-merge is exactly `ZxpRowTag.bialgSquare` (the layers
`[x21, w, w] ; [w, c] ; [z12, w, w]` rewrite through the whiskered square
`[[z12, z12], [w, c, w], [x21, x21]]` after one exchange pair), followed by
routing of the doubled carriers.  Documented attack (burned this round): the
square fires cleanly at whisker (0, 2) after exchanging the skip crossing
past the CNOT merge; the residual is the six-strand routing of the two
fork/merge pairs back into gadget shape — a Yang-Baxter/coassoc chain of
roughly two dozen further moves, not transcribed this round. -/
def zxtCnotWindowFTStatement : Prop :=
  ZxwConv
    { sourceArity := 3
      layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire]] }
    { sourceArity := 3
      layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }

/-- Kernel span pin: the FT CNOT window statement is semantically sound. -/
theorem zxtCnotWindowFTSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire]] })
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
            [ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }) = true := rfl

/-- OWNER MARKER (FALSE): the FT CNOT window is not machine-checked. -/
def zxtCnotWindowFTIsProven : Bool := false

/-- THE TT CNOT WINDOW (owner-false residual): the carrier CNOT passes a
double-tap position.  Content: the bialgebra square as in the FT window PLUS
the Hopf cancellation — the strand receives the inner carrier twice
(`a`-tap and the CNOT copy through the `b`-tap), and the double tap dies by
`ZxpRowTag.hopf` after the square distributes; the surviving window is the
`(F, T)` gadget pair.  Not attacked beyond the on-paper route this round. -/
def zxtCnotWindowTTStatement : Prop :=
  ZxwConv
    { sourceArity := 3
      layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire]] }
    { sourceArity := 3
      layers := [[ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }

/-- Kernel span pin: the TT CNOT window statement is semantically sound. -/
theorem zxtCnotWindowTTSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
            [ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire]] })
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }) = true := rfl

/-- OWNER MARKER (FALSE): the TT CNOT window is not machine-checked. -/
def zxtCnotWindowTTIsProven : Bool := false

/-! ## Stage 4 — the zipped double comb

The swap ride runs on the ZIPPED two-carrier comb: per strand position, the
inner-carrier gadget fires first (prefix `p + 1`), then the outer-carrier
gadget (prefix `p`, with the inner carrier passing on the right); at the end
both carriers discard (inner first).  Layer invariant:
`processed ++ [outer carrier, inner carrier] ++ unprocessed`. -/

/-- A leading wire absorbs into the left whisker block. -/
theorem zxtWhiskerBumpOne (leftWires rightWires : Nat) (cells : List ZxpCell) :
    zxpWhiskerLayer leftWires rightWires (ZxpCell.wire :: cells)
      = zxpWhiskerLayer (leftWires + 1) rightWires cells :=
  zxaWiresConsWire leftWires (zxpCatCells cells (zxpWireCells rightWires))

/-- The per-position gadget is well-formed at its window width. -/
theorem zxtGadgetLayersWF : (tapBit : Bool) -> (prefixWires rightWires : Nat) ->
    ZxpLayersWF (prefixWires + (2 + rightWires))
      (zxfGadgetLayers prefixWires rightWires tapBit)
  | false, prefixWires, rightWires => by
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
      rw [zxpWhiskerLayerDomArity]
      exact rfl
  | true, prefixWires, rightWires => by
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_
        (ZxpLayersWF.nil _)))
      · rw [zxpWhiskerLayerDomArity]
        exact congrArg (fun innerValue => prefixWires + innerValue)
          (zxnTwoPlusEqOnePlusSucc rightWires).symm
      · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
        exact (zxnForkArityShuffle prefixWires rightWires).symm
      · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
        exact zxnStepArityShuffle prefixWires rightWires

/-- The per-position gadget preserves its window width. -/
theorem zxtGadgetLayersCodArity : (tapBit : Bool) ->
    (prefixWires rightWires anyArity : Nat) ->
    zxpLayersCodArity anyArity (zxfGadgetLayers prefixWires rightWires tapBit)
      = prefixWires + (2 + rightWires)
  | false, prefixWires, rightWires, _anyArity => by
      show zxpLayerCodArity
          (zxpWhiskerLayer prefixWires rightWires [ZxpCell.crossing])
        = prefixWires + (2 + rightWires)
      rw [zxpWhiskerLayerCodArity]
      exact rfl
  | true, prefixWires, rightWires, _anyArity => by
      show zxpLayerCodArity
          (zxpWhiskerLayer prefixWires rightWires [ZxpCell.crossing])
        = prefixWires + (2 + rightWires)
      rw [zxpWhiskerLayerCodArity]
      exact rfl

/-- THE ZIPPED DOUBLE COMB: inner gadget, outer gadget, recurse; both carriers
discard at the end.  The off-diagonal (unequal-length) branches are junk and
return the empty layer list; every consumer carries the length equation. -/
def zxtDoubleLayers : Nat -> List Bool -> List Bool -> List (List ZxpCell)
  | prefixWires, [], [] =>
      [zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.zSpider 1 0],
        zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]]
  | _prefixWires, [], _secondBit :: _secondRest => []
  | _prefixWires, _firstBit :: _firstRest, [] => []
  | prefixWires, firstBit :: firstRest, secondBit :: secondRest =>
      zxpCatLayers (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
        (zxpCatLayers
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest))

/-- Well-formedness of the zipped double comb at its entry width. -/
theorem zxtDoubleLayersWF : (firstRow secondRow : List Bool) ->
    (prefixWires : Nat) -> secondRow.length = firstRow.length ->
    ZxpLayersWF (prefixWires + (2 + firstRow.length))
      (zxtDoubleLayers prefixWires firstRow secondRow)
  | [], [], prefixWires, _hLen => by
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
      · rw [zxpWhiskerLayerDomArity]
        exact rfl
      · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
        exact rfl
  | [], _secondBit :: secondRest, _prefixWires, hLen => Nat.noConfusion hLen
  | _firstBit :: firstRest, [], _prefixWires, hLen => Nat.noConfusion hLen
  | firstBit :: firstRest, secondBit :: secondRest, prefixWires, hLen => by
      have hTailLen : secondRest.length = firstRest.length :=
        Nat.succ.inj hLen
      show ZxpLayersWF (prefixWires + (2 + (firstRest.length + 1)))
        (zxpCatLayers (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxpCatLayers
            (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
            (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)))
      refine zxpLayersWFCat _ _ ?_ ?_
      · rw [zxnForkArityShuffle prefixWires firstRest.length]
        exact zxtGadgetLayersWF firstBit (prefixWires + 1) firstRest.length
      · rw [zxtGadgetLayersCodArity firstBit (prefixWires + 1) firstRest.length _]
        refine zxpLayersWFCat _ _ ?_ ?_
        · rw [<- zxnForkArityShuffle prefixWires firstRest.length]
          exact zxtGadgetLayersWF secondBit prefixWires (firstRest.length + 1)
        · rw [zxtGadgetLayersCodArity secondBit prefixWires
            (firstRest.length + 1) _]
          rw [zxnForkArityShuffle prefixWires firstRest.length]
          exact zxtDoubleLayersWF firstRest secondRest (prefixWires + 1) hTailLen

/-- Output arity of the zipped double comb: both carriers are gone. -/
theorem zxtDoubleLayersCodArity : (firstRow secondRow : List Bool) ->
    (prefixWires anyArity : Nat) -> secondRow.length = firstRow.length ->
    zxpLayersCodArity anyArity (zxtDoubleLayers prefixWires firstRow secondRow)
      = prefixWires + firstRow.length
  | [], [], prefixWires, _anyArity, _hLen => by
      show zxpLayerCodArity (zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0])
        = prefixWires + 0
      rw [zxpWhiskerLayerCodArity]
      exact rfl
  | [], _secondBit :: secondRest, _prefixWires, _anyArity, hLen =>
      Nat.noConfusion hLen
  | _firstBit :: firstRest, [], _prefixWires, _anyArity, hLen =>
      Nat.noConfusion hLen
  | firstBit :: firstRest, secondBit :: secondRest, prefixWires, anyArity,
      hLen => by
      have hTailLen : secondRest.length = firstRest.length :=
        Nat.succ.inj hLen
      show zxpLayersCodArity anyArity
          (zxpCatLayers (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
            (zxpCatLayers
              (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
              (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)))
        = prefixWires + (firstRest.length + 1)
      rw [zxpLayersCodArityCat, zxpLayersCodArityCat,
        zxtDoubleLayersCodArity firstRest secondRest (prefixWires + 1) _ hTailLen]
      exact zxnCombCodShuffle prefixWires firstRest.length

/-! ## Stage 5 — the crossing ride

The four committed windows lift to every prefix/remainder position, giving the
uniform step `crossing ; gadgetPair(a, b) ~ gadgetPair(b, a) ; crossing'`; the
induction rides the crossing down the zipped comb, swapping the carrier roles
position by position, and the boundary kills it against the two discards. -/

theorem zxtTwoPlusSuccShuffle (middleWires : Nat) :
    2 + (middleWires + 1) = 3 + middleWires :=
  (Nat.add_comm 2 (middleWires + 1)).trans (Nat.add_comm middleWires 3)

/-- THE WINDOW AT GENERAL POSITION: the ride step at any prefix and remainder,
uniform in the two tap bits — the crossing enters between the carriers, the
two gadgets swap roles, the crossing exits one position deeper. -/
theorem zxtCrossWindowAt (tapFirst tapSecond : Bool)
    (prefixWires middleWires : Nat) :
    ZxwConv
      { sourceArity := prefixWires + (2 + (middleWires + 1))
        layers := zxpWhiskerLayer prefixWires (middleWires + 1) [ZxpCell.crossing]
          :: zxpCatLayers
            (zxfGadgetLayers (prefixWires + 1) middleWires tapFirst)
            (zxfGadgetLayers prefixWires (middleWires + 1) tapSecond) }
      { sourceArity := prefixWires + (2 + (middleWires + 1))
        layers := zxpCatLayers
          (zxfGadgetLayers (prefixWires + 1) middleWires tapSecond)
          (zxpCatLayers
            (zxfGadgetLayers prefixWires (middleWires + 1) tapFirst)
            [zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]]) } := by
  cases tapFirst with
  | false =>
      cases tapSecond with
      | false =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxfCrossWindowFF (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift
      | true =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxfCrossWindowFT (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift
  | true =>
      cases tapSecond with
      | false =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxfCrossWindowTF (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift
      | true =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxtCrossWindowTTHolds (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift

/-- THE CROSSING RIDE: a crossing between the two carriers rides the whole
zipped double comb, swapping the carrier roles, and dies at the discard
boundary. -/
theorem zxtCrossRideDouble : (firstRow secondRow : List Bool) ->
    (prefixWires : Nat) -> secondRow.length = firstRow.length ->
    ZxwConv
      { sourceArity := prefixWires + (2 + firstRow.length)
        layers := zxpWhiskerLayer prefixWires firstRow.length [ZxpCell.crossing]
          :: zxtDoubleLayers prefixWires firstRow secondRow }
      { sourceArity := prefixWires + (2 + firstRow.length)
        layers := zxtDoubleLayers prefixWires secondRow firstRow }
  | [], [], prefixWires, _hLen => by
      show ZxwConv
        { sourceArity := prefixWires + (2 + 0)
          layers := [zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing],
            zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.zSpider 1 0],
            zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]] }
        { sourceArity := prefixWires + (2 + 0)
          layers := [zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.zSpider 1 0],
            zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]] }
      rw [<- zxtWhiskerBumpOne prefixWires 0 [ZxpCell.zSpider 1 0]]
      -- the crossing slides into the first discard
      have hSlideLift := zxwConvLift (prefixWires + (2 + 0)) prefixWires 0 []
        [zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]]
        (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 0)))
        (ZxpLayersWF.nil _) rfl
        (ZxpLayersWF.cons
          (zxpWhiskerLayerDomArity prefixWires 0 [ZxpCell.zSpider 1 0])
          (ZxpLayersWF.nil _))
      refine ZxwConv.trans hSlideLift ?_
      -- the two discards trade order through the merged discard layer
      have hSwapLift := zxwConvLift (prefixWires + (2 + 0)) prefixWires 0 [] []
        (zxtLeftFirstToRightFirst [ZxpCell.zSpider 1 0] [ZxpCell.zSpider 1 0])
        (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
      exact hSwapLift
  | [], _secondBit :: _secondRest, _prefixWires, hLen => Nat.noConfusion hLen
  | _firstBit :: _firstRest, [], _prefixWires, hLen => Nat.noConfusion hLen
  | firstBit :: firstRest, secondBit :: secondRest, prefixWires, hLen => by
      have hTailLen : secondRest.length = firstRest.length := Nat.succ.inj hLen
      have hFinalEq : zxtDoubleLayers prefixWires (secondBit :: secondRest)
          (firstBit :: firstRest)
          = zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
                (zxtDoubleLayers (prefixWires + 1) secondRest firstRest)) := by
        show zxpCatLayers
            (zxfGadgetLayers (prefixWires + 1) secondRest.length secondBit)
            (zxpCatLayers
              (zxfGadgetLayers prefixWires (secondRest.length + 1) firstBit)
              (zxtDoubleLayers (prefixWires + 1) secondRest firstRest))
          = zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
                (zxtDoubleLayers (prefixWires + 1) secondRest firstRest))
        rw [hTailLen]
      -- the window arity bookkeeping
      have hWinCod : zxpDiagramCodArity
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpWhiskerLayer prefixWires (firstRest.length + 1)
                [ZxpCell.crossing]
              :: zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit) }
          = prefixWires + (2 + (firstRest.length + 1)) := by
        show zxpLayersCodArity
            (zxpLayerCodArity
              (zxpWhiskerLayer prefixWires (firstRest.length + 1)
                [ZxpCell.crossing]))
            (zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
              (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
          = prefixWires + (2 + (firstRest.length + 1))
        rw [zxpLayersCodArityCat,
          zxtGadgetLayersCodArity firstBit (prefixWires + 1) firstRest.length _,
          zxtGadgetLayersCodArity secondBit prefixWires (firstRest.length + 1) _]
      -- step 1: the window fires over the double-comb tail
      have hWinLift := zxwLiftConv (prefixWires + (2 + (firstRest.length + 1)))
        [] (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)
        (zxtCrossWindowAt firstBit secondBit prefixWires firstRest.length)
        (ZxpLayersWF.nil _) rfl
        (by
          rw [hWinCod, zxnForkArityShuffle prefixWires firstRest.length]
          exact zxtDoubleLayersWF firstRest secondRest (prefixWires + 1) hTailLen)
      have hStepOne : ZxwConv
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpWhiskerLayer prefixWires (firstRest.length + 1)
                [ZxpCell.crossing]
              :: zxpCatLayers
                (zxpCatLayers
                  (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                  (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
                (zxtDoubleLayers (prefixWires + 1) firstRest secondRest) }
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
                (zxpCatLayers
                  (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
                  [zxpWhiskerLayer (prefixWires + 1) firstRest.length
                    [ZxpCell.crossing]]))
              (zxtDoubleLayers (prefixWires + 1) firstRest secondRest) } := hWinLift
      rw [zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
          (zxpCatLayers
            (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
            [zxpWhiskerLayer (prefixWires + 1) firstRest.length [ZxpCell.crossing]])
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest),
        zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
          [zxpWhiskerLayer (prefixWires + 1) firstRest.length [ZxpCell.crossing]]
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)] at hStepOne
      -- step 2: the ride recurses one position deeper
      have hInner := zxtCrossRideDouble firstRest secondRest (prefixWires + 1)
        hTailLen
      have hIHLift := zxwLiftConv (prefixWires + (2 + (firstRest.length + 1)))
        (zxpCatLayers
          (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit))
        [] hInner
        (by
          refine zxpLayersWFCat _ _ ?_ ?_
          · rw [zxnForkArityShuffle prefixWires firstRest.length]
            exact zxtGadgetLayersWF secondBit (prefixWires + 1) firstRest.length
          · rw [zxtGadgetLayersCodArity secondBit (prefixWires + 1)
              firstRest.length _,
              <- zxnForkArityShuffle prefixWires firstRest.length]
            exact zxtGadgetLayersWF firstBit prefixWires (firstRest.length + 1))
        (by
          rw [zxpLayersCodArityCat,
            zxtGadgetLayersCodArity secondBit (prefixWires + 1)
              firstRest.length _,
            zxtGadgetLayersCodArity firstBit prefixWires (firstRest.length + 1) _]
          exact zxnForkArityShuffle prefixWires firstRest.length)
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight,
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
          (zxpWhiskerLayer (prefixWires + 1) firstRest.length [ZxpCell.crossing]
            :: zxtDoubleLayers (prefixWires + 1) firstRest secondRest),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length secondBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) firstBit)
          (zxtDoubleLayers (prefixWires + 1) secondRest firstRest)] at hIHLift
      show ZxwConv
        { sourceArity := prefixWires + (2 + (firstRest.length + 1))
          layers := zxpWhiskerLayer prefixWires (firstRest.length + 1)
              [ZxpCell.crossing]
            :: zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
                (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)) }
        { sourceArity := prefixWires + (2 + (firstRest.length + 1))
          layers := zxtDoubleLayers prefixWires (secondBit :: secondRest)
            (firstBit :: firstRest) }
      rw [hFinalEq]
      exact ZxwConv.trans hStepOne hIHLift

/-! ## Stage 6 — parking a gadget behind a comb tail

The outer-carrier gadget acts on the two leftmost strands (plus right
passives); the inner comb tail acts strictly to their right.  The committed
block-routing engine commutes them, growing the gadget's right whisker by the
one strand the tail still owns. -/

theorem zxtOnePlusTwoShuffle (prefixWires tailLength : Nat) :
    prefixWires + (1 + (tailLength + 2)) = (prefixWires + 2) + (tailLength + 1) := by
  rw [Nat.add_comm 1 (tailLength + 2), Nat.add_assoc prefixWires 2 (tailLength + 1),
    Nat.add_comm 2 (tailLength + 1)]

theorem zxtDeepForkShuffle (prefixWires tailLength : Nat) :
    prefixWires + (2 + (tailLength + 2)) = (prefixWires + 3) + (tailLength + 1) := by
  rw [Nat.add_assoc prefixWires 3 (tailLength + 1), Nat.add_comm 2 (tailLength + 2),
    Nat.add_comm 3 (tailLength + 1)]

theorem zxtCarrierExitShuffle (prefixWires tailLength : Nat) :
    (prefixWires + 1) + (1 + (tailLength + 1))
      = (prefixWires + 2) + (tailLength + 1) := by
  rw [<- Nat.add_assoc (prefixWires + 1) 1 (tailLength + 1)]

/-- One left-strand block layer passes a whole comb tail (the engine instance
with the arities and the comb shift folded in). -/
theorem zxtBlockLayerPastCombTail (blockCells : List ZxpCell)
    (tailRow : List Bool) (blockDom blockCod : Nat)
    (hDomEq : zxpLayerDomArity blockCells = blockDom)
    (hCodEq : zxpLayerCodArity blockCells = blockCod) :
    ZxwConv
      { sourceArity := blockDom + (tailRow.length + 1)
        layers := zxpCatLayers
          (zxpWhiskerLayers blockDom 0 (zxnCombLayers 0 tailRow))
          [zxpCatCells blockCells (zxpWireCells tailRow.length)] }
      { sourceArity := blockDom + (tailRow.length + 1)
        layers := zxpCatCells blockCells (zxpWireCells (tailRow.length + 1))
          :: zxpWhiskerLayers blockCod 0 (zxnCombLayers 0 tailRow) } := by
  have hTailWF : ZxpLayersWF (tailRow.length + 1) (zxnCombLayers 0 tailRow) := by
    have hRaw := zxnCombLayersWF tailRow 0
    rw [Nat.zero_add, Nat.add_comm 1 tailRow.length] at hRaw
    exact hRaw
  have hEngine := zxwLayerPastRightLayers blockCells (zxnCombLayers 0 tailRow)
    (tailRow.length + 1) hTailWF
  have hTailCod : zxpLayersCodArity (tailRow.length + 1) (zxnCombLayers 0 tailRow)
      = tailRow.length :=
    (zxnCombLayersCodArity tailRow 0 _).trans (Nat.zero_add tailRow.length)
  rw [hDomEq, hCodEq, hTailCod] at hEngine
  exact ZxwConv.symm (zxwOfZxeConv hEngine)

/-- THE GADGET PARK: a comb tail followed by an outer gadget converts to the
(right-widened) outer gadget followed by the comb tail. -/
theorem zxtGadgetPastCombTail (tapBit : Bool) (tailRow : List Bool)
    (prefixWires : Nat) :
    ZxwConv
      { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
        layers := zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
          (zxfGadgetLayers prefixWires tailRow.length tapBit) }
      { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
        layers := zxpCatLayers
          (zxfGadgetLayers prefixWires (tailRow.length + 1) tapBit)
          (zxnCombLayers (prefixWires + 2) tailRow) } := by
  cases tapBit with
  | false =>
      have hPass := zxtBlockLayerPastCombTail
        (zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing]) tailRow
        (prefixWires + 2) (prefixWires + 2)
        (by rw [zxpWhiskerLayerDomArity]; exact rfl)
        (by rw [zxpWhiskerLayerCodArity]; exact rfl)
      have hCatOne : zxpCatCells (zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing])
          (zxpWireCells tailRow.length)
          = zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
            (zxpWireCells tailRow.length)
          = zxpCatCells (zxpWireCells prefixWires)
            (zxpCatCells [ZxpCell.crossing] (zxpWireCells tailRow.length))
        exact zxnCatCellsAssoc (zxpWireCells prefixWires) [ZxpCell.crossing]
          (zxpWireCells tailRow.length)
      have hCatTwo : zxpCatCells (zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing])
          (zxpWireCells (tailRow.length + 1))
          = zxpWhiskerLayer prefixWires (tailRow.length + 1) [ZxpCell.crossing] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
            (zxpWireCells (tailRow.length + 1))
          = zxpCatCells (zxpWireCells prefixWires)
            (zxpCatCells [ZxpCell.crossing] (zxpWireCells (tailRow.length + 1)))
        exact zxnCatCellsAssoc (zxpWireCells prefixWires) [ZxpCell.crossing]
          (zxpWireCells (tailRow.length + 1))
      rw [hCatOne, hCatTwo,
        <- zxfCombLayersShift (prefixWires + 2) tailRow 0] at hPass
      exact hPass
  | true =>
      -- the three gadget layers park one at a time, right to left
      have hCatZOne : zxpCatCells
          (zxpWhiskerLayer prefixWires 1 [ZxpCell.zSpider 1 2])
          (zxpWireCells tailRow.length)
          = zxpWhiskerLayer prefixWires (tailRow.length + 1)
              [ZxpCell.zSpider 1 2] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells prefixWires)
              [ZxpCell.zSpider 1 2, ZxpCell.wire])
            (zxpWireCells tailRow.length)
          = zxpCatCells (zxpWireCells prefixWires)
            (zxpCatCells [ZxpCell.zSpider 1 2, ZxpCell.wire]
              (zxpWireCells tailRow.length))
        exact zxnCatCellsAssoc _ _ _
      have hCatZTwo : zxpCatCells
          (zxpWhiskerLayer prefixWires 1 [ZxpCell.zSpider 1 2])
          (zxpWireCells (tailRow.length + 1))
          = zxpWhiskerLayer prefixWires (tailRow.length + 2)
              [ZxpCell.zSpider 1 2] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells prefixWires)
              [ZxpCell.zSpider 1 2, ZxpCell.wire])
            (zxpWireCells (tailRow.length + 1))
          = zxpCatCells (zxpWireCells prefixWires)
            (zxpCatCells [ZxpCell.zSpider 1 2, ZxpCell.wire]
              (zxpWireCells (tailRow.length + 1)))
        exact zxnCatCellsAssoc _ _ _
      have hCatXOne : zxpCatCells
          (zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.xSpider 2 1])
          (zxpWireCells tailRow.length)
          = zxpWhiskerLayer (prefixWires + 1) tailRow.length
              [ZxpCell.xSpider 2 1] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells (prefixWires + 1)) [ZxpCell.xSpider 2 1])
            (zxpWireCells tailRow.length)
          = zxpCatCells (zxpWireCells (prefixWires + 1))
            (zxpCatCells [ZxpCell.xSpider 2 1] (zxpWireCells tailRow.length))
        exact zxnCatCellsAssoc _ _ _
      have hCatXTwo : zxpCatCells
          (zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.xSpider 2 1])
          (zxpWireCells (tailRow.length + 1))
          = zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
              [ZxpCell.xSpider 2 1] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells (prefixWires + 1)) [ZxpCell.xSpider 2 1])
            (zxpWireCells (tailRow.length + 1))
          = zxpCatCells (zxpWireCells (prefixWires + 1))
            (zxpCatCells [ZxpCell.xSpider 2 1] (zxpWireCells (tailRow.length + 1)))
        exact zxnCatCellsAssoc _ _ _
      have hCatCOne : zxpCatCells
          (zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing])
          (zxpWireCells tailRow.length)
          = zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
            (zxpWireCells tailRow.length)
          = zxpCatCells (zxpWireCells prefixWires)
            (zxpCatCells [ZxpCell.crossing] (zxpWireCells tailRow.length))
        exact zxnCatCellsAssoc _ _ _
      have hCatCTwo : zxpCatCells
          (zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing])
          (zxpWireCells (tailRow.length + 1))
          = zxpWhiskerLayer prefixWires (tailRow.length + 1) [ZxpCell.crossing] := by
        show zxpCatCells
            (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
            (zxpWireCells (tailRow.length + 1))
          = zxpCatCells (zxpWireCells prefixWires)
            (zxpCatCells [ZxpCell.crossing] (zxpWireCells (tailRow.length + 1)))
        exact zxnCatCellsAssoc _ _ _
      -- pass 1: the fork layer
      have hPassOneRaw := zxtBlockLayerPastCombTail
        (zxpWhiskerLayer prefixWires 1 [ZxpCell.zSpider 1 2]) tailRow
        (prefixWires + 2) (prefixWires + 3)
        (by rw [zxpWhiskerLayerDomArity]; exact rfl)
        (by rw [zxpWhiskerLayerCodArity]; exact rfl)
      rw [hCatZOne, hCatZTwo, <- zxfCombLayersShift (prefixWires + 2) tailRow 0,
        <- zxfCombLayersShift (prefixWires + 3) tailRow 0] at hPassOneRaw
      have hPassOne : ZxwConv
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
              [zxpWhiskerLayer prefixWires (tailRow.length + 1)
                [ZxpCell.zSpider 1 2]] }
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2]
              :: zxnCombLayers (prefixWires + 3) tailRow } := hPassOneRaw
      have hLiftOne := zxwLiftConv ((prefixWires + 2) + (tailRow.length + 1)) []
        [zxpWhiskerLayer (prefixWires + 1) tailRow.length [ZxpCell.xSpider 2 1],
          zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]]
        hPassOne (ZxpLayersWF.nil _) rfl
        (by
          have hHeadCod : zxpDiagramCodArity
              { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
                layers := zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
                  [zxpWhiskerLayer prefixWires (tailRow.length + 1)
                    [ZxpCell.zSpider 1 2]] }
              = prefixWires + (2 + (tailRow.length + 1)) := by
            show zxpLayersCodArity ((prefixWires + 2) + (tailRow.length + 1))
                (zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
                  [zxpWhiskerLayer prefixWires (tailRow.length + 1)
                    [ZxpCell.zSpider 1 2]])
              = prefixWires + (2 + (tailRow.length + 1))
            rw [zxpLayersCodArityCat]
            show zxpLayerCodArity
                (zxpWhiskerLayer prefixWires (tailRow.length + 1)
                  [ZxpCell.zSpider 1 2])
              = prefixWires + (2 + (tailRow.length + 1))
            rw [zxpWhiskerLayerCodArity]
            exact rfl
          rw [hHeadCod]
          refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
          · rw [zxpWhiskerLayerDomArity]
            exact (zxnForkArityShuffle prefixWires tailRow.length).symm
          · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
            exact zxnStepArityShuffle prefixWires tailRow.length)
      have hStepOne : ZxwConv
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpCatLayers
              (zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
                [zxpWhiskerLayer prefixWires (tailRow.length + 1)
                  [ZxpCell.zSpider 1 2]])
              [zxpWhiskerLayer (prefixWires + 1) tailRow.length [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]] }
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2]
              :: zxpCatLayers (zxnCombLayers (prefixWires + 3) tailRow)
                [zxpWhiskerLayer (prefixWires + 1) tailRow.length
                    [ZxpCell.xSpider 2 1],
                  zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]] } :=
        hLiftOne
      rw [zxnCatLayersAssoc (zxnCombLayers (prefixWires + 2) tailRow)
        [zxpWhiskerLayer prefixWires (tailRow.length + 1) [ZxpCell.zSpider 1 2]]
        [zxpWhiskerLayer (prefixWires + 1) tailRow.length [ZxpCell.xSpider 2 1],
          zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]]]
        at hStepOne
      -- pass 2: the merge layer
      have hPassTwoRaw := zxtBlockLayerPastCombTail
        (zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.xSpider 2 1]) tailRow
        (prefixWires + 3) (prefixWires + 2)
        (by rw [zxpWhiskerLayerDomArity]; exact rfl)
        (by rw [zxpWhiskerLayerCodArity]; exact rfl)
      rw [hCatXOne, hCatXTwo, <- zxfCombLayersShift (prefixWires + 3) tailRow 0,
        <- zxfCombLayersShift (prefixWires + 2) tailRow 0] at hPassTwoRaw
      have hPassTwo : ZxwConv
          { sourceArity := (prefixWires + 3) + (tailRow.length + 1)
            layers := zxpCatLayers (zxnCombLayers (prefixWires + 3) tailRow)
              [zxpWhiskerLayer (prefixWires + 1) tailRow.length
                [ZxpCell.xSpider 2 1]] }
          { sourceArity := (prefixWires + 3) + (tailRow.length + 1)
            layers := zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
                [ZxpCell.xSpider 2 1]
              :: zxnCombLayers (prefixWires + 2) tailRow } := hPassTwoRaw
      have hLiftTwo := zxwLiftConv ((prefixWires + 2) + (tailRow.length + 1))
        [zxpWhiskerLayer prefixWires (tailRow.length + 2) [ZxpCell.zSpider 1 2]]
        [zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]]
        hPassTwo
        (ZxpLayersWF.cons
          (by
            rw [zxpWhiskerLayerDomArity]
            exact zxtOnePlusTwoShuffle prefixWires tailRow.length)
          (ZxpLayersWF.nil _))
        (by
          show zxpLayerCodArity
              (zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2])
            = (prefixWires + 3) + (tailRow.length + 1)
          rw [zxpWhiskerLayerCodArity]
          exact zxtDeepForkShuffle prefixWires tailRow.length)
        (by
          have hHeadCod : zxpDiagramCodArity
              { sourceArity := (prefixWires + 3) + (tailRow.length + 1)
                layers := zxpCatLayers (zxnCombLayers (prefixWires + 3) tailRow)
                  [zxpWhiskerLayer (prefixWires + 1) tailRow.length
                    [ZxpCell.xSpider 2 1]] }
              = (prefixWires + 1) + (1 + tailRow.length) := by
            show zxpLayersCodArity ((prefixWires + 3) + (tailRow.length + 1))
                (zxpCatLayers (zxnCombLayers (prefixWires + 3) tailRow)
                  [zxpWhiskerLayer (prefixWires + 1) tailRow.length
                    [ZxpCell.xSpider 2 1]])
              = (prefixWires + 1) + (1 + tailRow.length)
            rw [zxpLayersCodArityCat]
            show zxpLayerCodArity
                (zxpWhiskerLayer (prefixWires + 1) tailRow.length
                  [ZxpCell.xSpider 2 1])
              = (prefixWires + 1) + (1 + tailRow.length)
            rw [zxpWhiskerLayerCodArity]
            exact rfl
          rw [hHeadCod]
          refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
          rw [zxpWhiskerLayerDomArity]
          exact zxnStepArityShuffle prefixWires tailRow.length)
      have hStepTwo : ZxwConv
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2]
              :: zxpCatLayers
                (zxpCatLayers (zxnCombLayers (prefixWires + 3) tailRow)
                  [zxpWhiskerLayer (prefixWires + 1) tailRow.length
                    [ZxpCell.xSpider 2 1]])
                [zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]] }
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2]
              :: zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
                  [ZxpCell.xSpider 2 1]
              :: zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
                [zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]] } :=
        hLiftTwo
      rw [zxnCatLayersAssoc (zxnCombLayers (prefixWires + 3) tailRow)
        [zxpWhiskerLayer (prefixWires + 1) tailRow.length [ZxpCell.xSpider 2 1]]
        [zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]]]
        at hStepTwo
      -- pass 3: the carrier crossing
      have hPassThreeRaw := zxtBlockLayerPastCombTail
        (zxpWhiskerLayer prefixWires 0 [ZxpCell.crossing]) tailRow
        (prefixWires + 2) (prefixWires + 2)
        (by rw [zxpWhiskerLayerDomArity]; exact rfl)
        (by rw [zxpWhiskerLayerCodArity]; exact rfl)
      rw [hCatCOne, hCatCTwo,
        <- zxfCombLayersShift (prefixWires + 2) tailRow 0] at hPassThreeRaw
      have hPassThree : ZxwConv
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
              [zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]] }
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 1)
                [ZxpCell.crossing]
              :: zxnCombLayers (prefixWires + 2) tailRow } := hPassThreeRaw
      have hLiftThree := zxwLiftConv ((prefixWires + 2) + (tailRow.length + 1))
        [zxpWhiskerLayer prefixWires (tailRow.length + 2) [ZxpCell.zSpider 1 2],
          zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
            [ZxpCell.xSpider 2 1]] []
        hPassThree
        (ZxpLayersWF.cons
          (by
            rw [zxpWhiskerLayerDomArity]
            exact zxtOnePlusTwoShuffle prefixWires tailRow.length)
          (ZxpLayersWF.cons
            (by
              rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
              exact (zxnForkArityShuffle prefixWires (tailRow.length + 1)).symm)
            (ZxpLayersWF.nil _)))
        (by
          show zxpLayerCodArity
              (zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
                [ZxpCell.xSpider 2 1])
            = (prefixWires + 2) + (tailRow.length + 1)
          rw [zxpWhiskerLayerCodArity]
          exact zxtCarrierExitShuffle prefixWires tailRow.length)
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLiftThree
      have hStepThree : ZxwConv
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2]
              :: zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
                  [ZxpCell.xSpider 2 1]
              :: zxpCatLayers (zxnCombLayers (prefixWires + 2) tailRow)
                [zxpWhiskerLayer prefixWires tailRow.length [ZxpCell.crossing]] }
          { sourceArity := (prefixWires + 2) + (tailRow.length + 1)
            layers := zxpWhiskerLayer prefixWires (tailRow.length + 2)
                [ZxpCell.zSpider 1 2]
              :: zxpWhiskerLayer (prefixWires + 1) (tailRow.length + 1)
                  [ZxpCell.xSpider 2 1]
              :: zxpWhiskerLayer prefixWires (tailRow.length + 1) [ZxpCell.crossing]
              :: zxnCombLayers (prefixWires + 2) tailRow } := hLiftThree
      exact ZxwConv.trans hStepOne (ZxwConv.trans hStepTwo hStepThree)

/-! ## Stage 7 — THE INTERLEAVING: two sequential solo combs zip

`combLayers (p+1) r ; combLayers p s` converts to the zipped double comb: at
each position the outer gadget parks backward past the inner comb tail
(`zxtGadgetPastCombTail`), then the tails recurse. -/

theorem zxtDoubleOfCombLayers : (firstRow secondRow : List Bool) ->
    (prefixWires : Nat) -> secondRow.length = firstRow.length ->
    ZxwConv
      { sourceArity := prefixWires + (2 + firstRow.length)
        layers := zxpCatLayers (zxnCombLayers (prefixWires + 1) firstRow)
          (zxnCombLayers prefixWires secondRow) }
      { sourceArity := prefixWires + (2 + firstRow.length)
        layers := zxtDoubleLayers prefixWires firstRow secondRow }
  | [], [], prefixWires, _hLen =>
      ZxwConv.refl _ (zxtDoubleLayersWF [] [] prefixWires rfl)
  | [], _secondBit :: _secondRest, _prefixWires, hLen => Nat.noConfusion hLen
  | _firstBit :: _firstRest, [], _prefixWires, hLen => Nat.noConfusion hLen
  | firstBit :: firstRest, secondBit :: secondRest, prefixWires, hLen => by
      have hTailLen : secondRest.length = firstRest.length := Nat.succ.inj hLen
      show ZxwConv
        { sourceArity := prefixWires + (2 + (firstRest.length + 1))
          layers := zxpCatLayers
            (zxnCombLayers (prefixWires + 1) (firstBit :: firstRest))
            (zxnCombLayers prefixWires (secondBit :: secondRest)) }
        { sourceArity := prefixWires + (2 + (firstRest.length + 1))
          layers := zxtDoubleLayers prefixWires (firstBit :: firstRest)
            (secondBit :: secondRest) }
      rw [zxfCombLayersCons (prefixWires + 1) firstBit firstRest,
        zxfCombLayersCons prefixWires secondBit secondRest, hTailLen,
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxnCombLayers (prefixWires + 2) firstRest)
          (zxpCatLayers (zxfGadgetLayers prefixWires firstRest.length secondBit)
            (zxnCombLayers (prefixWires + 1) secondRest)),
        <- zxnCatLayersAssoc (zxnCombLayers (prefixWires + 2) firstRest)
          (zxfGadgetLayers prefixWires firstRest.length secondBit)
          (zxnCombLayers (prefixWires + 1) secondRest)]
      -- the outer gadget parks backward past the inner comb tail
      have hPark := zxtGadgetPastCombTail secondBit firstRest prefixWires
      have hParkLift := zxwLiftConv (prefixWires + (2 + (firstRest.length + 1)))
        (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
        (zxnCombLayers (prefixWires + 1) secondRest) hPark
        (by
          rw [zxnForkArityShuffle prefixWires firstRest.length]
          exact zxtGadgetLayersWF firstBit (prefixWires + 1) firstRest.length)
        (by
          rw [zxtGadgetLayersCodArity firstBit (prefixWires + 1)
            firstRest.length _]
          exact (zxnStepArityShuffle (prefixWires + 1) firstRest.length).trans
            (congrArg (fun innerValue => (prefixWires + 2) + innerValue)
              (Nat.add_comm 1 firstRest.length)))
        (by
          have hParkCod : zxpDiagramCodArity
              { sourceArity := (prefixWires + 2) + (firstRest.length + 1)
                layers := zxpCatLayers
                  (zxnCombLayers (prefixWires + 2) firstRest)
                  (zxfGadgetLayers prefixWires firstRest.length secondBit) }
              = prefixWires + (2 + firstRest.length) := by
            show zxpLayersCodArity ((prefixWires + 2) + (firstRest.length + 1))
                (zxpCatLayers (zxnCombLayers (prefixWires + 2) firstRest)
                  (zxfGadgetLayers prefixWires firstRest.length secondBit))
              = prefixWires + (2 + firstRest.length)
            rw [zxpLayersCodArityCat,
              zxtGadgetLayersCodArity secondBit prefixWires firstRest.length _]
          rw [hParkCod, zxnStepArityShuffle prefixWires firstRest.length,
            <- hTailLen]
          exact zxnCombLayersWF secondRest (prefixWires + 1))
      have hParkStep : ZxwConv
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
              (zxpCatLayers
                (zxpCatLayers (zxnCombLayers (prefixWires + 2) firstRest)
                  (zxfGadgetLayers prefixWires firstRest.length secondBit))
                (zxnCombLayers (prefixWires + 1) secondRest)) }
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
              (zxpCatLayers
                (zxpCatLayers
                  (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
                  (zxnCombLayers (prefixWires + 2) firstRest))
                (zxnCombLayers (prefixWires + 1) secondRest)) } := hParkLift
      rw [zxnCatLayersAssoc
        (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
        (zxnCombLayers (prefixWires + 2) firstRest)
        (zxnCombLayers (prefixWires + 1) secondRest)] at hParkStep
      refine ZxwConv.trans hParkStep ?_
      -- the tails recurse under the two leading gadgets
      have hInner := zxtDoubleOfCombLayers firstRest secondRest (prefixWires + 1)
        hTailLen
      have hIHLift := zxwLiftConv (prefixWires + (2 + (firstRest.length + 1)))
        (zxpCatLayers
          (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
        [] hInner
        (by
          refine zxpLayersWFCat _ _ ?_ ?_
          · rw [zxnForkArityShuffle prefixWires firstRest.length]
            exact zxtGadgetLayersWF firstBit (prefixWires + 1) firstRest.length
          · rw [zxtGadgetLayersCodArity firstBit (prefixWires + 1)
                firstRest.length _,
              <- zxnForkArityShuffle prefixWires firstRest.length]
            exact zxtGadgetLayersWF secondBit prefixWires (firstRest.length + 1))
        (by
          rw [zxpLayersCodArityCat,
            zxtGadgetLayersCodArity firstBit (prefixWires + 1) firstRest.length _,
            zxtGadgetLayersCodArity secondBit prefixWires (firstRest.length + 1) _]
          exact zxnForkArityShuffle prefixWires firstRest.length)
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hIHLift
      have hStepTwo : ZxwConv
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
              (zxpCatLayers (zxnCombLayers (prefixWires + 2) firstRest)
                (zxnCombLayers (prefixWires + 1) secondRest)) }
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
              (zxtDoubleLayers (prefixWires + 1) firstRest secondRest) } := hIHLift
      rw [zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxpCatLayers (zxnCombLayers (prefixWires + 2) firstRest)
            (zxnCombLayers (prefixWires + 1) secondRest)),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)] at hStepTwo
      exact hStepTwo

/-! ## Stage 8 — THE ADJACENT COMB SWAP

Park the second creation behind the first comb through the block-routing
engine, zip the two solo combs, insert the birth crossing backwards
(`zxfCreatesCrossInsert`), ride it down the zipped comb, and unpark on the
other side. -/

/-- The parked solo comb: a one-strand left whisker of the conditional-xor
block is the same block one position deeper. -/
theorem zxtParkedXorRowShape (row : List Bool) :
    zxpWhiskerLayers 1 0 (zxnXorRowLayers row)
      = zxpWhiskerLayer 1 row.length [ZxpCell.zSpider 0 1]
        :: zxnCombLayers 1 row := by
  show zxpWhiskerLayer 1 0 (zxpWhiskerLayer 0 row.length [ZxpCell.zSpider 0 1])
      :: zxpWhiskerLayers 1 0 (zxnCombLayers 0 row)
    = zxpWhiskerLayer 1 row.length [ZxpCell.zSpider 0 1] :: zxnCombLayers 1 row
  rw [zxnWhiskerLayerCompose 1 0 0 row.length [ZxpCell.zSpider 0 1],
    <- zxfCombLayersShift 1 row 0]
  exact rfl

/-- CONVERSION TO THE ZIPPED FORM: two sequential conditional-xor blocks
convert to two creations followed by the zipped double comb. -/
theorem zxtXorPairToDouble (firstRow secondRow : List Bool)
    (hLen : secondRow.length = firstRow.length) :
    ZxwConv
      { sourceArity := firstRow.length
        layers := zxpCatLayers (zxnXorRowLayers firstRow)
          (zxnXorRowLayers secondRow) }
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxtDoubleLayers 0 firstRow secondRow } := by
  -- step 1: the second creation parks behind the first comb
  have hParkRaw := zxwLayerPastRightLayers [ZxpCell.zSpider 0 1]
    (zxnXorRowLayers firstRow) firstRow.length (zxnXorRowLayersWF firstRow)
  have hParkCast : ZxeConv
      { sourceArity := 0 + firstRow.length
        layers := zxpCatCells [ZxpCell.zSpider 0 1]
            (zxpWireCells firstRow.length)
          :: zxpWhiskerLayers 1 0 (zxnXorRowLayers firstRow) }
      { sourceArity := 0 + firstRow.length
        layers := zxpCatLayers (zxpWhiskerLayers 0 0 (zxnXorRowLayers firstRow))
          [zxpCatCells [ZxpCell.zSpider 0 1]
            (zxpWireCells
              (zxpLayersCodArity firstRow.length (zxnXorRowLayers firstRow)))] } :=
    hParkRaw
  rw [Nat.zero_add, zxpWhiskerLayersZero, zxnXorRowLayersCodArity,
    zxtParkedXorRowShape] at hParkCast
  have hParkTwo : ZxwConv
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxnCombLayers 1 firstRow }
      { sourceArity := firstRow.length
        layers := zxpCatLayers (zxnXorRowLayers firstRow)
          [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]] } :=
    zxwOfZxeConv hParkCast
  -- step 2: lift the reversed park over the second comb tail
  have hCodEq : zxpDiagramCodArity
      { sourceArity := firstRow.length
        layers := zxpCatLayers (zxnXorRowLayers firstRow)
          [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]] }
      = 0 + (1 + firstRow.length) := by
    show zxpLayersCodArity firstRow.length
        (zxpCatLayers (zxnXorRowLayers firstRow)
          [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]])
      = 0 + (1 + firstRow.length)
    rw [zxpLayersCodArityCat]
    show zxpLayerCodArity
        (zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1])
      = 0 + (1 + firstRow.length)
    rw [zxpWhiskerLayerCodArity]
    exact rfl
  have hLiftPark := zxwLiftConv firstRow.length []
    (zxnCombLayers 0 secondRow) (ZxwConv.symm hParkTwo)
    (ZxpLayersWF.nil _) rfl
    (by
      rw [hCodEq, <- hLen]
      exact zxnCombLayersWF secondRow 0)
  have hStepPark : ZxwConv
      { sourceArity := firstRow.length
        layers := zxpCatLayers
          (zxpCatLayers (zxnXorRowLayers firstRow)
            [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]])
          (zxnCombLayers 0 secondRow) }
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpCatLayers (zxnCombLayers 1 firstRow)
            (zxnCombLayers 0 secondRow) } := hLiftPark
  have hAttach : zxpCatLayers
      (zxpCatLayers (zxnXorRowLayers firstRow)
        [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]])
      (zxnCombLayers 0 secondRow)
      = zxpCatLayers (zxnXorRowLayers firstRow) (zxnXorRowLayers secondRow) := by
    rw [zxnCatLayersAssoc (zxnXorRowLayers firstRow)
      [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]]
      (zxnCombLayers 0 secondRow), <- hLen]
    exact rfl
  rw [hAttach] at hStepPark
  refine ZxwConv.trans hStepPark ?_
  -- step 3: the two solo combs zip under the creations
  have hInner := zxtDoubleOfCombLayers firstRow secondRow 0 hLen
  have hCreatesWF : ZxpLayersWF firstRow.length
      [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1],
        zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]] := by
    refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
    · rw [zxpWhiskerLayerDomArity]
      show 0 + (0 + firstRow.length) = firstRow.length
      rw [Nat.zero_add, Nat.zero_add]
    · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
      show 1 + (0 + firstRow.length) = 0 + (1 + firstRow.length)
      rw [Nat.zero_add, Nat.zero_add]
  have hCreatesCod : zxpLayersCodArity firstRow.length
      [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1],
        zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]]
      = 0 + (2 + firstRow.length) := by
    show zxpLayerCodArity
        (zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1])
      = 0 + (2 + firstRow.length)
    rw [zxpWhiskerLayerCodArity]
    show 1 + (1 + firstRow.length) = 0 + (2 + firstRow.length)
    exact (Nat.add_assoc 1 1 firstRow.length).symm.trans
      (Nat.zero_add (2 + firstRow.length)).symm
  have hLiftZip := zxwLiftConv firstRow.length
    [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1],
      zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]]
    [] hInner hCreatesWF hCreatesCod (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLiftZip
  exact hLiftZip

/-- THE ADJACENT COMB SWAP, WHOLE: the r10 residual `zxfCombSwapStatement` is
proven — zip, insert the birth crossing, ride, unzip. -/
theorem zxtCombSwapHolds : zxfCombSwapStatement := by
  intro strandWidth firstRow secondRow hFirstLen hSecondLen
  subst hFirstLen
  have hForward := zxtXorPairToDouble firstRow secondRow hSecondLen
  have hBackward := zxtXorPairToDouble secondRow firstRow hSecondLen.symm
  rw [hSecondLen] at hBackward
  -- the birth crossing appears between the two creations
  have hInsertLift := zxwConvLift firstRow.length 0 firstRow.length []
    (zxtDoubleLayers 0 firstRow secondRow)
    (ZxwConv.symm zxfCreatesCrossInsert) (ZxpLayersWF.nil _)
    (((Nat.zero_add (0 + firstRow.length)).trans
      (Nat.zero_add firstRow.length)).symm)
    (zxtDoubleLayersWF firstRow secondRow 0 hSecondLen)
  have hStepInsert : ZxwConv
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 0 firstRow.length [ZxpCell.wire, ZxpCell.zSpider 0 1]
          :: zxtDoubleLayers 0 firstRow secondRow }
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 0 firstRow.length [ZxpCell.wire, ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 0 firstRow.length [ZxpCell.crossing]
          :: zxtDoubleLayers 0 firstRow secondRow } := hInsertLift
  rw [zxtWhiskerBumpOne 0 firstRow.length [ZxpCell.zSpider 0 1]] at hStepInsert
  -- the crossing rides the zipped comb and dies at the boundary
  have hRide := zxtCrossRideDouble firstRow secondRow 0 hSecondLen
  have hCreatesWF : ZxpLayersWF firstRow.length
      [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1],
        zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]] := by
    refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
    · rw [zxpWhiskerLayerDomArity]
      show 0 + (0 + firstRow.length) = firstRow.length
      rw [Nat.zero_add, Nat.zero_add]
    · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
      show 1 + (0 + firstRow.length) = 0 + (1 + firstRow.length)
      rw [Nat.zero_add, Nat.zero_add]
  have hCreatesCod : zxpLayersCodArity firstRow.length
      [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1],
        zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]]
      = 0 + (2 + firstRow.length) := by
    show zxpLayerCodArity
        (zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1])
      = 0 + (2 + firstRow.length)
    rw [zxpWhiskerLayerCodArity]
    show 1 + (1 + firstRow.length) = 0 + (2 + firstRow.length)
    exact (Nat.add_assoc 1 1 firstRow.length).symm.trans
      (Nat.zero_add (2 + firstRow.length)).symm
  have hRideLift := zxwLiftConv firstRow.length
    [zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1],
      zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]]
    [] hRide hCreatesWF hCreatesCod (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hRideLift
  have hStepRide : ZxwConv
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 0 firstRow.length [ZxpCell.crossing]
          :: zxtDoubleLayers 0 firstRow secondRow }
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxtDoubleLayers 0 secondRow firstRow } := hRideLift
  exact ZxwConv.trans hForward (ZxwConv.trans hStepInsert
    (ZxwConv.trans hStepRide (ZxwConv.symm hBackward)))

/-- CONTENT MARKER: the adjacent comb swap is machine-checked — the first of
the two named comb moves of the transport assembly is DONE.  Supersedes the
r10 owner `zxfCombSwapIsProven := false`, which stays byte-intact in its home
file. -/
def zxtCombSwapIsProven : Bool := true

/-! ## Stage 9 — fires -/

/-- Fire 1: the comb swap at width two on literal rows. -/
theorem zxtCombSwapFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpCatLayers (zxnXorRowLayers [true, false])
          (zxnXorRowLayers [false, true]) }
      { sourceArity := 2
        layers := zxpCatLayers (zxnXorRowLayers [false, true])
          (zxnXorRowLayers [true, false]) } :=
  zxtCombSwapHolds 2 [true, false] [false, true] rfl rfl

/-- Kernel span pin for fire 1. -/
theorem zxtCombSwapFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpCatLayers (zxnXorRowLayers [true, false])
            (zxnXorRowLayers [false, true]) })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpCatLayers (zxnXorRowLayers [false, true])
            (zxnXorRowLayers [true, false]) }) = true := rfl

/-- Fire 2: a whole two-row normal form converts to the row-swapped normal
form (the comb swap lifted between the shared init and kill layers). -/
theorem zxtNormalFormSwapFire :
    ZxwConv
      (zxnNormalForm 1 1 [[true, false], [true, true]])
      (zxnNormalForm 1 1 [[true, true], [true, false]]) := by
  have hSwap := zxtCombSwapHolds 2 [true, false] [true, true] rfl rfl
  have hLift := zxwLiftConv 1 [zxnInitLayer 1 1] [zxnKillLayer 1 1] hSwap
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  exact hLift

/-- Kernel span pin for fire 2. -/
theorem zxtNormalFormSwapFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, false], [true, true]]))
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, true], [true, false]]))
      = true := rfl

/-! ## Stage 10 — the honest marker ledger -/

/-- MARKER (FALSE): the comb transvection (`zxfCombXorAbsorbStatement`) is NOT
proven this round.  Landed toward it: the FF and TF CNOT ride windows (proven
above), the FT/TT CNOT window statements with kernel span pins, and — through
the swap ride — the COMPLETE reusable ride skeleton (`zxtDoubleLayers`,
`zxtDoubleOfCombLayers`, `zxtGadgetPastCombTail`, `zxtCrossRideDouble`,
`zxtXorPairToDouble`).  Remaining: the FT and TT CNOT windows (the bialgebra
square and its Hopf-cancelled double-tap), a CNOT analogue of
`zxtCrossWindowAt`/`zxtCrossRideDouble` (the gadget is two layers instead of
one crossing, entering via `zxfCreatesCnotInsert` and dying at the discard
boundary via the counit routing), and the top-level assembly mirroring
`zxtCombSwapHolds`. -/
def zxtCombXorAbsorbIsProven : Bool := false

/-- MARKER (FALSE): `zxwGeneratorTransportStatement` is NOT proven — the
committed assembly `zxfTransportOfCombMoves` now has its FIRST input
(`zxtCombSwapHolds`); the residual is exactly `zxfCombXorAbsorbStatement`.
The committed FinalFlip/WiringFlip owners stay byte-intact and false. -/
def zxtGeneratorTransportIsProven : Bool := false

/-- MARKER: the swap-ride layer of the transport round is LIVE — the TT
crossing window (completing the four-window layer), the zipped double comb
with well-formedness and arity lemmas, the interleaving of two solo combs,
the crossing ride with its discard boundary, the creation park, and the whole
adjacent comb swap, fired at a literal pair and at a whole two-row normal
form. -/
def zxtHasSwapRide : Bool := true

end FX1Poly.Polygraph.Omega.ZXPhaseFree
