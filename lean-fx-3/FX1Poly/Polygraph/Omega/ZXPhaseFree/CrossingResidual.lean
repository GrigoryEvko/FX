import FX1Poly.Polygraph.Omega.ZXPhaseFree.AbsorptionInduction

/-! # Polygraph/Omega/ZXPhaseFree/CrossingResidual — the single-comb
strand-crossing ride: the crossing residual reduced to one kill-death

The r13 assembly (`AbsorptionInduction`) reduced phase-free completeness to
four cell-level residuals and named the crossing residual's route: a NEW
window family in which a strand crossing rides BELOW the walking carrier of
a SINGLE comb (the committed r11 windows ride a crossing BETWEEN the two
carriers of the zipped double comb — a different geometry).  This round
builds that family in full and reduces `zxbCrossingAbsorbStatement` to
EXACTLY ONE named cell-level statement, the kill-death
`zxcCrossIntoKillStatement` (`zxcCrossingAbsorbOfKillDeath`):

* (i)   THE MINIMAL WINDOW QUADRUPLE (`zxcStrandWindowFF/FT/TF/TT`): a
  crossing on the two strands entering a two-gadget comb segment commutes to
  the other side with the two tap bits swapped.  FF is Yang-Baxter verbatim;
  FT/TF are seven-to-nine lifted moves through the slides, the merge-routing
  bricks, the involution and one strip; TT is the long chain — the two-fork
  extraction, the E-ladder of merge slides, and THE COPY-TRIPLE SYMMETRY
  (`zxcCopyTripleSwap`, coassociativity + cocommutativity: the three copies
  of a double fork are interchangeable), the genuinely comonoidal step.
* (ii)  THE WINDOW AT GENERAL POSITION (`zxcStrandCrossWindowAt`): the
  quadruple lifted to every prefix/remainder, uniform in the tap bits
  (whisker lift + the bump discipline, r11 template).
* (iii) THE GADGET PASS (`zxcCrossPastGadget`): a strand crossing strictly
  right of one comb gadget commutes past it whole — one firing of the
  committed disjoint-block engine, uniform in the tap bit.
* (iv)  THE COMB RIDE (`zxcCombCrossRide`): induction on the strands left of
  the crossing; each step is the gadget pass, the base is the window plus
  the block engine past the comb tail.
* (v)   THE BLOCK RIDE (`zxcXorRowCrossRide`): the crossing enters one
  whole conditional-xor generator block — create-layer exchange, comb ride —
  and exits at the SAME strand pair with the row's two bits swapped.
* (vi)  THE GENERATOR-BLOCKS FOLD (`zxcGeneratorBlocksCrossRide`): the block
  ride folded over the whole generator list; the crossing rides through every
  block swapping the two crossed columns (`zxcSwapRowsAt leftWires`), exiting
  below at the same position.
* (vii) THE INIT PASS (`zxcCrossPastInit`): the crossing above the init layer
  commutes below it (one firing of the disjoint-block zero-state engine),
  widening its right remainder by the codomain width.
* (viii) THE ABSORPTION, REDUCED (`zxcCrossingAbsorbOfKillDeath`): the whole
  crossing residual `zxbCrossingAbsorbStatement` is PROVED modulo exactly ONE
  named cell-level statement, the kill-death `zxcCrossIntoKillStatement` — the
  crossing rides past init (vii), through every generator block (vi), and dies
  in the kill layer (the residual hypothesis); the absorbed generator list is
  `zxcSwapRowsAt leftWires generatorRows`.

WALL NOTE (the one remaining residual): `zxcCrossIntoKillStatement` — a crossing
whiskered at any position above the kill layer dies, both crossed strands
feeding adjacent kill collectors.  The width-2 witness is the committed r13
`zxbCrossingIntoKillPairFire`; the general-position death with WIRE spectators is
CLOSED (`zxcCrossIntoKillPairWhiskered`, this round).  The open gap is exactly the
spectator KILL cells on the side bands: the general death needs a tensor-band
interchange (a middle killed band with kill-cell contexts left and right) that
does not instantiate the existing disjoint-block engines `zxwLayerPastRightLayers`
/`zxwLayersPastRightLayer` (which handle a block passing layers on the OTHER
strands, not a symmetric-collector death on the SAME strands).  Two attacks
burned: (a) whiskered-death plus a sequential kill-layer factoring `[kill] ~
[M, killRest]`; (b) an interchange peel by induction on `leftWires`.  Both need
the middle-band interchange, not a one-liner; reduced to a single owner-false
statement with a soundness span pin (`zxcCrossIntoKillResidualSpanPin`).

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no
`List.append`, no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match
arms over inductive scrutinees.  Committed owner-false flags stay
byte-intact in their home files; the crossing residual did NOT flip
unconditionally (`zxcCrossingResidualIsClosed := false`); the fresh true
content marker is the ride (`zxcHasCrossingRide := true`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the minimal strand-crossing windows (three strands: the
carrier at position 0, the two crossed strands at positions 1 and 2)

Each window: our crossing at strands (1,2), then the comb gadget for the
first bit (prefix 0), then the gadget for the second bit (prefix 1);
convertible to the gadgets with the two tap bits SWAPPED followed by the
exit crossing at strands (0,1). -/

/-- THE FF WINDOW: both bits skip — exactly Yang-Baxter. -/
theorem zxcStrandWindowFF :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } :=
  zxwYangBaxter

/-- THE FT WINDOW: skip then tap — the tap migrates to the first slot.
Chain: fork slide backwards, two disjoint exchanges, the merge-routing
brick, the involution, one strip, Yang-Baxter. -/
theorem zxcStrandWindowFT :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := by
  -- step 1: the fork extracts up through the carrier walk (slideRight
  -- backwards at the fork, whisker (0,1))
  have hForkLift := zxwConvLift 3 0 1 [[ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 2)))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hForkLift
  refine ZxwConv.trans hStep1 ?_
  -- step 2: our crossing exchanges past the extracted fork
  have hExchOneLift := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hExchOneLift
  refine ZxwConv.trans hStep2 ?_
  -- step 3: the walk crossing exchanges past the far merge
  have hExchTwoLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing]]
    (zxtLeftFirstToRightFirst [ZxpCell.crossing] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hExchTwoLift
  refine ZxwConv.trans hStep3 ?_
  -- step 4: the crossing feeds the merge's left leg and re-routes
  have hRouteLift := zxwConvLift 3 1 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    zxtCrossThenMergeRight
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hRouteLift
  refine ZxwConv.trans hStep4 ?_
  -- step 5: the doubled crossing dies (involution, whisker (2,0))
  have hInvLift := zxwConvLift 3 2 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hInvLift
  refine ZxwConv.trans hStep5 ?_
  -- step 6: strip the wire layer
  have hStripLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hStripLift
  refine ZxwConv.trans hStep6 ?_
  -- step 7: Yang-Baxter on the trailing crossing triple
  have hYangLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] []
    zxwYangBaxter
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  exact hYangLift

/-- THE TF WINDOW: tap then skip — the tap migrates to the second slot.
Chain: exchange, the mirror merge-routing brick, a grown involution pair
absorbed by the forward fork slide, one exchange, Yang-Baxter backwards, the
involution, and the trailing wire layer dissolved. -/
theorem zxcStrandWindowTF :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := by
  -- step 1: our crossing exchanges past the fork
  have hExchOneLift := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hExchOneLift
  refine ZxwConv.trans hStep1 ?_
  -- step 2: the crossing feeds the merge's right leg and re-routes
  have hRouteLift := zxwConvLift 3 1 0 [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    zxtMergeAfterCross
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hRouteLift
  refine ZxwConv.trans hStep2 ?_
  -- step 3a: grow a wire layer above the far merge
  have hGrowLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (ZxwConv.symm (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1])))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hGrowLift
  refine ZxwConv.trans hStep3 ?_
  -- step 3b: the wire pair becomes a crossing pair (involution backwards)
  have hPairLift := zxwConvLift 3 0 2
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (ZxwConv.symm (zxwMoveConv ZxwWindowMove.sigmaInvolution))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hPairLift
  refine ZxwConv.trans hStep4 ?_
  -- step 3c: the fork slides forward through the first crossing pair
  have hSlideLift := zxwConvLift 3 0 1 []
    [[ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwSlideRightConv (ZxpCell.zSpider 1 2))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hSlideLift
  refine ZxwConv.trans hStep5 ?_
  -- step 4: the remaining leading crossing exchanges past the far merge
  have hExchTwoLift := zxwLiftConv 3
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxtLeftFirstToRightFirst [ZxpCell.crossing] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hExchTwoLift
  refine ZxwConv.trans hStep6 ?_
  -- step 5: Yang-Baxter backwards on the middle crossing triple
  have hYangLift := zxwLiftConv 3
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.crossing]]
    (ZxwConv.symm zxwYangBaxter)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep7 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing]] } := hYangLift
  refine ZxwConv.trans hStep7 ?_
  -- step 6: the doubled trailing crossing dies (involution, whisker (1,0))
  have hInvLift := zxwConvLift 3 1 0
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    []
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStep8 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]] } := hInvLift
  refine ZxwConv.trans hStep8 ?_
  -- step 7: the trailing all-wire layer dissolves (splitLayer backwards)
  have hTailLift := zxwLiftConv 3
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    []
    (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
      (ZxrWindowMove.seed
        (ZxpWindowMove.splitLayer [ZxpCell.crossing, ZxpCell.wire] []))))))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  exact hTailLift

/-- THE COPY-TRIPLE SYMMETRY: the second and third copies produced by a
double fork are interchangeable — coassociativity across, cocommutativity
under the inner fork, coassociativity back.  The genuinely comonoidal step
of the TT window. -/
theorem zxcCopyTripleSwap :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 1 2, ZxpCell.wire]] } := by
  -- step 1: coassociativity across (the double fork reassociates)
  have hCoassocLift := zxwLiftConv 1 [] [[ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.crossing]] } := hCoassocLift
  refine ZxwConv.trans hStep1 ?_
  -- step 2: cocommutativity under the inner fork (whisker (1,0))
  have hCocommLift := zxwConvLift 1 1 0 [[ZxpCell.zSpider 1 2]] []
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCocomm))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStep2 : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.zSpider 1 2]] } := hCocommLift
  refine ZxwConv.trans hStep2 ?_
  -- step 3: coassociativity back
  exact ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc))

/-- THE TT WINDOW: both bits tap — the long chain.  Forward: the two forks
extract to the top (exchanges + the backward fork slide), the E-ladder of
merge slides normalizes the crossing block, and THE COPY-TRIPLE SYMMETRY
absorbs the residual crossing between the fork copies.  Backward from the
right side: the same extraction meets at the identical canonical stack. -/
theorem zxcStrandWindowTT :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := by
  -- ================= the left chain: LHS down to the canonical stack ====
  -- A1: our crossing exchanges past the first fork
  have hA1 := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA1
  refine ZxwConv.trans hStepA1 ?_
  -- A2: the crossing feeds the first merge's right leg and re-routes
  have hA2 := zxwConvLift 3 1 0 [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    zxtMergeAfterCross
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA2
  refine ZxwConv.trans hStepA2 ?_
  -- A3: the second fork extracts up through the carrier walk
  have hA3 := zxwConvLift 3 0 1
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 2)))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA3
  refine ZxwConv.trans hStepA3 ?_
  -- A4: the carrier walk of gadget one exchanges past the second fork
  have hA4 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA4
  refine ZxwConv.trans hStepA4 ?_
  -- A5: the first merge exchanges past the second fork
  have hA5 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA5
  refine ZxwConv.trans hStepA5 ?_
  -- A6: the walk crossing exchanges past the second fork
  have hA6 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA6
  refine ZxwConv.trans hStepA6 ?_
  -- A7: the walk crossing feeds the deep merge's left leg and re-routes
  have hA7 := zxwConvLift 3 2 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    zxtCrossThenMergeRight
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA7 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA7
  refine ZxwConv.trans hStepA7 ?_
  -- A8: the doubled crossing dies and the wire layer strips
  have hA8a := zxwConvLift 3 2 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA8a : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA8a
  refine ZxwConv.trans hStepA8a ?_
  have hA8b := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepA8b : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] } := hA8b
  refine ZxwConv.trans hStepA8b ?_
  -- l1: the deep walk crossing exchanges past the low merge
  have hL1 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing]]
    (zxtLeftFirstToRightFirst [ZxpCell.crossing] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepL1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hL1
  refine ZxwConv.trans hStepL1 ?_
  -- l2: the middle crossing feeds the low merge's left leg and re-routes
  have hL2 := zxwConvLift 3 1 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    zxtCrossThenMergeRight
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepL2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hL2
  refine ZxwConv.trans hStepL2 ?_
  -- l3: the crossing extracts up through the high merge (slide backwards)
  have hL3 := zxwConvLift 3 2 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwSlideRightConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepL3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hL3
  refine ZxwConv.trans hStepL3 ?_
  -- l4: the doubled deep crossing dies and the wire layer strips
  have hL4a := zxwConvLift 3 3 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepL4a : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hL4a
  refine ZxwConv.trans hStepL4a ?_
  have hL4b := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepL4b : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hL4b
  refine ZxwConv.trans hStepL4b ?_
  -- b1: the low trailing crossing extracts up through the low merge
  have hB1 := zxwConvLift 3 1 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwSlideRightConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB1
  refine ZxwConv.trans hStepB1 ?_
  -- b2: the next crossing extracts up through the high merge
  have hB2 := zxwConvLift 3 2 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwSlideLeftConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB2
  refine ZxwConv.trans hStepB2 ?_
  -- b3: the doubled crossing dies and the wire layer strips
  have hB3a := zxwConvLift 3 2 1
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB3a : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB3a
  refine ZxwConv.trans hStepB3a ?_
  have hB3b := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB3b : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB3b
  refine ZxwConv.trans hStepB3b ?_
  -- b4: the middle crossing extracts up through the shifted merge
  have hB4 := zxwConvLift 3 1 1
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwSlideLeftConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB4
  refine ZxwConv.trans hStepB4 ?_
  -- b5: the two merges exchange into canonical order
  have hB5 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.xSpider 2 1] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB5
  refine ZxwConv.trans hStepB5 ?_
  -- b6: the two disjoint crossings exchange
  have hB6 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxtRightFirstToLeftFirst [ZxpCell.wire, ZxpCell.crossing] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepB6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hB6
  refine ZxwConv.trans hStepB6 ?_
  -- the copy-triple symmetry absorbs the residual crossing
  have hTriple := zxwConvLift 3 0 2 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    zxcCopyTripleSwap
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepTriple : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hTriple
  refine ZxwConv.trans hStepTriple ?_
  -- ================= the right chain: RHS down to the SAME stack ========
  refine ZxwConv.symm ?_
  -- B1: the second fork extracts up through the carrier walk
  have hR1 := zxwConvLift 3 0 1
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 2)))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepR1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hR1
  refine ZxwConv.trans hStepR1 ?_
  -- B2: the first merge exchanges past the second fork
  have hR2 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2] [ZxpCell.xSpider 2 1, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepR2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hR2
  refine ZxwConv.trans hStepR2 ?_
  -- r1: the low walk crossing exchanges past the low merge
  have hR3 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.crossing] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepR3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hR3
  refine ZxwConv.trans hStepR3 ?_
  -- r2: the middle crossing feeds the low merge's left leg and re-routes
  have hR4 := zxwConvLift 3 1 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    zxtCrossThenMergeRight
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepR4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hR4
  refine ZxwConv.trans hStepR4 ?_
  -- r3: the crossing extracts up through the high merge (slide forward)
  have hR5 := zxwConvLift 3 2 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxwSlideRightConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepR5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hR5
  refine ZxwConv.trans hStepR5 ?_
  -- the bottom braid word normalizes: Yang-Baxter, involution, tail kill
  have hR6 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    zxwYangBaxter
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepR6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hR6
  refine ZxwConv.trans hStepR6 ?_
  have hR7 := zxwConvLift 3 0 1
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing]]
    []
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStepR7 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]] } := hR7
  refine ZxwConv.trans hStepR7 ?_
  have hR8 := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    []
    (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
      (ZxrWindowMove.seed
        (ZxpWindowMove.splitLayer [ZxpCell.wire, ZxpCell.crossing] []))))))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  exact hR8

/-! ## Stage 1 — the window at general position -/

/-- THE STRAND WINDOW AT GENERAL POSITION: at any prefix and remainder, a
strand crossing entering the two-gadget comb segment below the carrier
commutes across with the two tap bits swapped, exiting one position shallower
— uniform in the tap bits. -/
theorem zxcStrandCrossWindowAt (tapFirst tapSecond : Bool)
    (prefixWires middleWires : Nat) :
    ZxwConv
      { sourceArity := prefixWires + (2 + (middleWires + 1))
        layers := zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]
          :: zxpCatLayers
            (zxfGadgetLayers prefixWires (middleWires + 1) tapFirst)
            (zxfGadgetLayers (prefixWires + 1) middleWires tapSecond) }
      { sourceArity := prefixWires + (2 + (middleWires + 1))
        layers := zxpCatLayers
          (zxfGadgetLayers prefixWires (middleWires + 1) tapSecond)
          (zxpCatLayers
            (zxfGadgetLayers (prefixWires + 1) middleWires tapFirst)
            [zxpWhiskerLayer prefixWires (middleWires + 1) [ZxpCell.crossing]]) } := by
  cases tapFirst with
  | false =>
      cases tapSecond with
      | false =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxcStrandWindowFF (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift
      | true =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxcStrandWindowFT (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
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
            prefixWires middleWires [] [] zxcStrandWindowTF (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
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
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
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
            prefixWires middleWires [] [] zxcStrandWindowTT (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift

/-! ## Stage 2 — the gadget pass: a crossing strictly right of one comb
gadget commutes past it whole (the disjoint-block engine, uniform in the
tap bit) -/

/-- `(p + 1) + (2 + m) = p + (2 + (m + 1))` (the ride entry shuffle). -/
theorem zxcRideEntryShuffle (prefixWires middleWires : Nat) :
    (prefixWires + 1) + (2 + middleWires) = prefixWires + (2 + (middleWires + 1)) :=
  (Nat.add_assoc prefixWires 1 (2 + middleWires)).trans
    (congrArg (fun innerValue => prefixWires + innerValue)
      ((Nat.add_assoc 1 2 middleWires).symm.trans
        (zxtTwoPlusSuccShuffle middleWires).symm))

/-- `(p + 1) + (2 + m) = (p + 2) + (1 + m)` (the window-to-tail shuffle). -/
theorem zxcWindowToTailShuffle (prefixWires middleWires : Nat) :
    (prefixWires + 1) + (2 + middleWires) = (prefixWires + 2) + (1 + middleWires) := by
  rw [Nat.add_assoc prefixWires 1 (2 + middleWires),
    Nat.add_assoc prefixWires 2 (1 + middleWires)]
  refine congrArg (fun innerValue => prefixWires + innerValue) ?_
  rw [<- Nat.add_assoc 1 2 middleWires, <- Nat.add_assoc 2 1 middleWires,
    Nat.add_comm 1 2]

/-- Right-whiskering a gadget widens its remainder. -/
theorem zxcGadgetWhiskerRight (tapBit : Bool) (prefixWires gapWires extraWires : Nat) :
    zxpWhiskerLayers 0 extraWires (zxfGadgetLayers prefixWires gapWires tapBit)
      = zxfGadgetLayers prefixWires (gapWires + extraWires) tapBit := by
  cases tapBit with
  | false =>
      show [zxpWhiskerLayer 0 extraWires
          (zxpWhiskerLayer prefixWires gapWires [ZxpCell.crossing])]
        = [zxpWhiskerLayer prefixWires (gapWires + extraWires) [ZxpCell.crossing]]
      rw [zxnWhiskerLayerCompose 0 extraWires prefixWires gapWires [ZxpCell.crossing],
        Nat.zero_add prefixWires]
  | true =>
      show [zxpWhiskerLayer 0 extraWires
          (zxpWhiskerLayer prefixWires (gapWires + 1) [ZxpCell.zSpider 1 2]),
        zxpWhiskerLayer 0 extraWires
          (zxpWhiskerLayer (prefixWires + 1) gapWires [ZxpCell.xSpider 2 1]),
        zxpWhiskerLayer 0 extraWires
          (zxpWhiskerLayer prefixWires gapWires [ZxpCell.crossing])]
        = [zxpWhiskerLayer prefixWires ((gapWires + extraWires) + 1)
            [ZxpCell.zSpider 1 2],
          zxpWhiskerLayer (prefixWires + 1) (gapWires + extraWires)
            [ZxpCell.xSpider 2 1],
          zxpWhiskerLayer prefixWires (gapWires + extraWires) [ZxpCell.crossing]]
      rw [zxnWhiskerLayerCompose 0 extraWires prefixWires (gapWires + 1)
          [ZxpCell.zSpider 1 2],
        zxnWhiskerLayerCompose 0 extraWires (prefixWires + 1) gapWires
          [ZxpCell.xSpider 2 1],
        zxnWhiskerLayerCompose 0 extraWires prefixWires gapWires [ZxpCell.crossing],
        Nat.zero_add prefixWires, Nat.zero_add (prefixWires + 1),
        Nat.succ_add gapWires extraWires]

/-- THE GADGET PASS: a strand crossing strictly right of a comb gadget's
window commutes past the whole gadget — one firing of the committed
disjoint-block engine, uniform in the tap bit. -/
theorem zxcCrossPastGadget (tapBit : Bool) (prefixWires gapWires rightLen : Nat) :
    ZxwConv
      { sourceArity := (prefixWires + (2 + gapWires)) + (2 + rightLen)
        layers := zxpWhiskerLayer (prefixWires + (2 + gapWires)) rightLen
            [ZxpCell.crossing]
          :: zxfGadgetLayers prefixWires (gapWires + (2 + rightLen)) tapBit }
      { sourceArity := (prefixWires + (2 + gapWires)) + (2 + rightLen)
        layers := zxpCatLayers
          (zxfGadgetLayers prefixWires (gapWires + (2 + rightLen)) tapBit)
          [zxpWhiskerLayer (prefixWires + (2 + gapWires)) rightLen
            [ZxpCell.crossing]] } := by
  have hEngine := zxwOfZxeConv (zxwLayersPastRightLayer
    (zxpCatCells [ZxpCell.crossing] (zxpWireCells rightLen))
    (zxfGadgetLayers prefixWires gapWires tapBit)
    (prefixWires + (2 + gapWires))
    (zxtGadgetLayersWF tapBit prefixWires gapWires))
  have hDomBlock : zxpLayerDomArity
      (zxpCatCells [ZxpCell.crossing] (zxpWireCells rightLen)) = 2 + rightLen := by
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
    exact rfl
  have hCodBlock : zxpLayerCodArity
      (zxpCatCells [ZxpCell.crossing] (zxpWireCells rightLen)) = 2 + rightLen := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
    exact rfl
  rw [hDomBlock, hCodBlock,
    zxcGadgetWhiskerRight tapBit prefixWires gapWires (2 + rightLen),
    zxtGadgetLayersCodArity tapBit prefixWires gapWires
      (prefixWires + (2 + gapWires))] at hEngine
  exact hEngine

/-! ## Stage 3 — the comb ride -/

/-- `(p + 1) + (1 + x) = p + (2 + x)` (the carry shuffle). -/
theorem zxcCarryShuffle (prefixWires innerCount : Nat) :
    (prefixWires + 1) + (1 + innerCount) = prefixWires + (2 + innerCount) := by
  rw [Nat.add_assoc prefixWires 1 (1 + innerCount),
    <- Nat.add_assoc 1 1 innerCount]

/-- `(p + (2 + f)) + (2 + m) = p + (2 + (f + (2 + m)))` (the pass entry
shuffle). -/
theorem zxcPassEntryShuffle (prefixWires gapWires middleWires : Nat) :
    (prefixWires + (2 + gapWires)) + (2 + middleWires)
      = prefixWires + (2 + (gapWires + (2 + middleWires))) := by
  rw [Nat.add_assoc prefixWires (2 + gapWires) (2 + middleWires),
    Nat.add_assoc 2 gapWires (2 + middleWires)]

/-- THE COMB RIDE: a strand crossing entering one conditional-xor comb at any
two adjacent unprocessed strands commutes through the whole comb — the two
crossed row bits swap, the crossing exits one position shallower below the
comb.  Induction on the strands left of the crossing; each step is the
gadget pass, the base is the general-position window plus the block engine
past the comb tail. -/
theorem zxcCombCrossRide : (frontBits : List Bool) -> (bitA bitB : Bool) ->
    (backBits : List Bool) -> (prefixWires : Nat) ->
    ZxwConv
      { sourceArity := (prefixWires + (1 + frontBits.length)) + (2 + backBits.length)
        layers := zxpWhiskerLayer (prefixWires + (1 + frontBits.length))
            backBits.length [ZxpCell.crossing]
          :: zxnCombLayers prefixWires (zxpCat frontBits (bitA :: bitB :: backBits)) }
      { sourceArity := (prefixWires + (1 + frontBits.length)) + (2 + backBits.length)
        layers := zxpCatLayers
          (zxnCombLayers prefixWires (zxpCat frontBits (bitB :: bitA :: backBits)))
          [zxpWhiskerLayer (prefixWires + frontBits.length) backBits.length
            [ZxpCell.crossing]] }
  | [], bitA, bitB, backBits, prefixWires => by
      show ZxwConv
        { sourceArity := (prefixWires + 1) + (2 + backBits.length)
          layers := zxpWhiskerLayer (prefixWires + 1) backBits.length
              [ZxpCell.crossing]
            :: zxnCombLayers prefixWires (bitA :: bitB :: backBits) }
        { sourceArity := (prefixWires + 1) + (2 + backBits.length)
          layers := zxpCatLayers
            (zxnCombLayers prefixWires (bitB :: bitA :: backBits))
            [zxpWhiskerLayer prefixWires backBits.length [ZxpCell.crossing]] }
      rw [zxfCombLayersCons prefixWires bitA (bitB :: backBits),
        zxfCombLayersCons (prefixWires + 1) bitB backBits,
        zxfCombLayersCons prefixWires bitB (bitA :: backBits),
        zxfCombLayersCons (prefixWires + 1) bitA backBits,
        <- zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (bitB :: backBits).length bitA)
          (zxfGadgetLayers (prefixWires + 1) backBits.length bitB)
          (zxnCombLayers (prefixWires + 1 + 1) backBits),
        zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (bitA :: backBits).length bitB)
          (zxpCatLayers (zxfGadgetLayers (prefixWires + 1) backBits.length bitA)
            (zxnCombLayers (prefixWires + 1 + 1) backBits))
          [zxpWhiskerLayer prefixWires backBits.length [ZxpCell.crossing]],
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) backBits.length bitA)
          (zxnCombLayers (prefixWires + 1 + 1) backBits)
          [zxpWhiskerLayer prefixWires backBits.length [ZxpCell.crossing]],
        <- zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (bitA :: backBits).length bitB)
          (zxfGadgetLayers (prefixWires + 1) backBits.length bitA)
          (zxpCatLayers (zxnCombLayers (prefixWires + 1 + 1) backBits)
            [zxpWhiskerLayer prefixWires backBits.length [ZxpCell.crossing]])]
      -- step 1: the window fires over the comb tail
      have hWindowLift := zxwLiftConv ((prefixWires + 1) + (2 + backBits.length))
        [] (zxnCombLayers (prefixWires + 2) backBits)
        (zxcStrandCrossWindowAt bitA bitB prefixWires backBits.length)
        (ZxpLayersWF.nil _)
        (zxcRideEntryShuffle prefixWires backBits.length)
        (by
          show ZxpLayersWF
            (zxpLayersCodArity
              (zxpLayerCodArity (zxpWhiskerLayer (prefixWires + 1)
                backBits.length [ZxpCell.crossing]))
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (backBits.length + 1) bitA)
                (zxfGadgetLayers (prefixWires + 1) backBits.length bitB)))
            (zxnCombLayers (prefixWires + 2) backBits)
          rw [zxpLayersCodArityCat,
            zxtGadgetLayersCodArity bitA prefixWires (backBits.length + 1),
            zxtGadgetLayersCodArity bitB (prefixWires + 1) backBits.length,
            zxcWindowToTailShuffle prefixWires backBits.length]
          exact zxnCombLayersWF backBits (prefixWires + 2))
      -- massage the window's exit into head position
      rw [zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (backBits.length + 1) bitB)
          (zxpCatLayers (zxfGadgetLayers (prefixWires + 1) backBits.length bitA)
            [zxpWhiskerLayer prefixWires (backBits.length + 1) [ZxpCell.crossing]])
          (zxnCombLayers (prefixWires + 2) backBits),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) backBits.length bitA)
          [zxpWhiskerLayer prefixWires (backBits.length + 1) [ZxpCell.crossing]]
          (zxnCombLayers (prefixWires + 2) backBits),
        <- zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (backBits.length + 1) bitB)
          (zxfGadgetLayers (prefixWires + 1) backBits.length bitA)
          (zxpCatLayers
            [zxpWhiskerLayer prefixWires (backBits.length + 1) [ZxpCell.crossing]]
            (zxnCombLayers (prefixWires + 2) backBits))] at hWindowLift
      refine ZxwConv.trans hWindowLift ?_
      -- step 2: the exit crossing passes the comb tail (block engine)
      have hPassRaw := zxwOfZxeConv (zxwLayerPastRightLayers
        (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
        (zxnCombLayers 0 backBits) (0 + (1 + backBits.length))
        (zxnCombLayersWF backBits 0))
      have hDomBlock : zxpLayerDomArity
          (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
          = prefixWires + 2 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        exact rfl
      have hCodBlock : zxpLayerCodArity
          (zxpCatCells (zxpWireCells prefixWires) [ZxpCell.crossing])
          = prefixWires + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        exact rfl
      have hTailCod := zxnCombLayersCodArity backBits 0 (0 + (1 + backBits.length))
      rw [hDomBlock, hCodBlock, hTailCod,
        <- zxfCombLayersShift (prefixWires + 2) backBits 0,
        Nat.zero_add (1 + backBits.length), Nat.zero_add backBits.length,
        Nat.add_comm 1 backBits.length,
        zxnCatCellsAssoc (zxpWireCells prefixWires) [ZxpCell.crossing]
          (zxpWireCells (backBits.length + 1)),
        zxnCatCellsAssoc (zxpWireCells prefixWires) [ZxpCell.crossing]
          (zxpWireCells backBits.length)] at hPassRaw
      have hPassLift := zxwLiftConv ((prefixWires + 1) + (2 + backBits.length))
        (zxpCatLayers (zxfGadgetLayers prefixWires (backBits.length + 1) bitB)
          (zxfGadgetLayers (prefixWires + 1) backBits.length bitA))
        [] hPassRaw
        (by
          refine zxpLayersWFCat _ _ ?_ ?_
          · rw [zxcRideEntryShuffle prefixWires backBits.length]
            exact zxtGadgetLayersWF bitB prefixWires (backBits.length + 1)
          · rw [zxtGadgetLayersCodArity bitB prefixWires (backBits.length + 1),
              <- zxcRideEntryShuffle prefixWires backBits.length]
            exact zxtGadgetLayersWF bitA (prefixWires + 1) backBits.length)
        (by
          rw [zxpLayersCodArityCat,
            zxtGadgetLayersCodArity bitB prefixWires (backBits.length + 1),
            zxtGadgetLayersCodArity bitA (prefixWires + 1) backBits.length]
          exact (zxcWindowToTailShuffle prefixWires backBits.length).trans
            (congrArg (fun innerValue => (prefixWires + 2) + innerValue)
              (Nat.add_comm 1 backBits.length)))
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hPassLift
      exact hPassLift
  | frontHead :: frontRest, bitA, bitB, backBits, prefixWires => by
      show ZxwConv
        { sourceArity := (prefixWires + (1 + (frontRest.length + 1)))
            + (2 + backBits.length)
          layers := zxpWhiskerLayer (prefixWires + (1 + (frontRest.length + 1)))
              backBits.length [ZxpCell.crossing]
            :: zxnCombLayers prefixWires
              (frontHead :: zxpCat frontRest (bitA :: bitB :: backBits)) }
        { sourceArity := (prefixWires + (1 + (frontRest.length + 1)))
            + (2 + backBits.length)
          layers := zxpCatLayers
            (zxnCombLayers prefixWires
              (frontHead :: zxpCat frontRest (bitB :: bitA :: backBits)))
            [zxpWhiskerLayer (prefixWires + (frontRest.length + 1))
              backBits.length [ZxpCell.crossing]] }
      rw [show (1 + (frontRest.length + 1)) = 2 + frontRest.length from
          (zxnTwoPlusEqOnePlusSucc frontRest.length).symm,
        show frontRest.length + 1 = 1 + frontRest.length from
          Nat.add_comm frontRest.length 1,
        <- Nat.add_assoc prefixWires 1 frontRest.length,
        zxfCombLayersCons prefixWires frontHead
          (zxpCat frontRest (bitA :: bitB :: backBits)),
        zxfCombLayersCons prefixWires frontHead
          (zxpCat frontRest (bitB :: bitA :: backBits)),
        zxpCatLength frontRest (bitA :: bitB :: backBits),
        zxpCatLength frontRest (bitB :: bitA :: backBits),
        show (bitA :: bitB :: backBits).length = 2 + backBits.length from
          Nat.add_comm backBits.length 2,
        show (bitB :: bitA :: backBits).length = 2 + backBits.length from
          Nat.add_comm backBits.length 2]
      -- step 1: the crossing passes the head gadget
      have hPassLift := zxwLiftConv
        ((prefixWires + (2 + frontRest.length)) + (2 + backBits.length))
        [] (zxnCombLayers (prefixWires + 1)
          (zxpCat frontRest (bitA :: bitB :: backBits)))
        (zxcCrossPastGadget frontHead prefixWires frontRest.length
          backBits.length)
        (ZxpLayersWF.nil _) rfl
        (by
          show ZxpLayersWF
            (zxpLayersCodArity
              (zxpLayerCodArity (zxpWhiskerLayer
                (prefixWires + (2 + frontRest.length)) backBits.length
                [ZxpCell.crossing]))
              (zxfGadgetLayers prefixWires
                (frontRest.length + (2 + backBits.length)) frontHead))
            (zxnCombLayers (prefixWires + 1)
              (zxpCat frontRest (bitA :: bitB :: backBits)))
          rw [zxtGadgetLayersCodArity frontHead prefixWires
              (frontRest.length + (2 + backBits.length)),
            <- zxcCarryShuffle prefixWires
              (frontRest.length + (2 + backBits.length))]
          have hInnerWF := zxnCombLayersWF
            (zxpCat frontRest (bitA :: bitB :: backBits)) (prefixWires + 1)
          rw [zxpCatLength frontRest (bitA :: bitB :: backBits),
            show (bitA :: bitB :: backBits).length = 2 + backBits.length from
              Nat.add_comm backBits.length 2] at hInnerWF
          exact hInnerWF)
      -- step 2: the ride recurses one strand deeper
      have hInnerRide := zxcCombCrossRide frontRest bitA bitB backBits
        (prefixWires + 1)
      rw [zxcCarryShuffle prefixWires frontRest.length] at hInnerRide
      have hRideLift := zxwLiftConv
        ((prefixWires + (2 + frontRest.length)) + (2 + backBits.length))
        (zxfGadgetLayers prefixWires
          (frontRest.length + (2 + backBits.length)) frontHead)
        [] hInnerRide
        (by
          rw [zxcPassEntryShuffle prefixWires frontRest.length backBits.length]
          exact zxtGadgetLayersWF frontHead prefixWires
            (frontRest.length + (2 + backBits.length)))
        (by
          rw [zxtGadgetLayersCodArity frontHead prefixWires
            (frontRest.length + (2 + backBits.length))]
          exact (zxcPassEntryShuffle prefixWires frontRest.length
            backBits.length).symm)
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hRideLift
      -- re-type both lifted steps into clean record shapes, then reassociate
      have hPassClean : ZxwConv
          { sourceArity := (prefixWires + (2 + frontRest.length))
              + (2 + backBits.length)
            layers := zxpWhiskerLayer (prefixWires + (2 + frontRest.length))
                backBits.length [ZxpCell.crossing]
              :: zxpCatLayers
                (zxfGadgetLayers prefixWires
                  (frontRest.length + (2 + backBits.length)) frontHead)
                (zxnCombLayers (prefixWires + 1)
                  (zxpCat frontRest (bitA :: bitB :: backBits))) }
          { sourceArity := (prefixWires + (2 + frontRest.length))
              + (2 + backBits.length)
            layers := zxpCatLayers
              (zxpCatLayers
                (zxfGadgetLayers prefixWires
                  (frontRest.length + (2 + backBits.length)) frontHead)
                [zxpWhiskerLayer (prefixWires + (2 + frontRest.length))
                  backBits.length [ZxpCell.crossing]])
              (zxnCombLayers (prefixWires + 1)
                (zxpCat frontRest (bitA :: bitB :: backBits))) } := hPassLift
      rw [zxnCatLayersAssoc
        (zxfGadgetLayers prefixWires
          (frontRest.length + (2 + backBits.length)) frontHead)
        [zxpWhiskerLayer (prefixWires + (2 + frontRest.length))
          backBits.length [ZxpCell.crossing]]
        (zxnCombLayers (prefixWires + 1)
          (zxpCat frontRest (bitA :: bitB :: backBits)))] at hPassClean
      have hRideClean : ZxwConv
          { sourceArity := (prefixWires + (2 + frontRest.length))
              + (2 + backBits.length)
            layers := zxpCatLayers
              (zxfGadgetLayers prefixWires
                (frontRest.length + (2 + backBits.length)) frontHead)
              (zxpWhiskerLayer (prefixWires + (2 + frontRest.length))
                  backBits.length [ZxpCell.crossing]
                :: zxnCombLayers (prefixWires + 1)
                  (zxpCat frontRest (bitA :: bitB :: backBits))) }
          { sourceArity := (prefixWires + (2 + frontRest.length))
              + (2 + backBits.length)
            layers := zxpCatLayers
              (zxfGadgetLayers prefixWires
                (frontRest.length + (2 + backBits.length)) frontHead)
              (zxpCatLayers
                (zxnCombLayers (prefixWires + 1)
                  (zxpCat frontRest (bitB :: bitA :: backBits)))
                [zxpWhiskerLayer (prefixWires + 1 + frontRest.length)
                  backBits.length [ZxpCell.crossing]]) } := hRideLift
      rw [<- zxnCatLayersAssoc
        (zxfGadgetLayers prefixWires
          (frontRest.length + (2 + backBits.length)) frontHead)
        (zxnCombLayers (prefixWires + 1)
          (zxpCat frontRest (bitB :: bitA :: backBits)))
        [zxpWhiskerLayer (prefixWires + 1 + frontRest.length)
          backBits.length [ZxpCell.crossing]]] at hRideClean
      exact ZxwConv.trans hPassClean hRideClean

/-! ## Stage 4 — the block ride: one whole conditional-xor generator block -/

/-- Swap the first two bits of a row (shorter rows untouched). -/
def zxcSwapHere : List Bool -> List Bool
  | [] => []
  | onlyBit :: [] => onlyBit :: []
  | bitA :: bitB :: restBits => bitB :: bitA :: restBits

/-- Swap the two bits at an adjacent position pair of a row.  Structured with
one scrutinee per level (`position` primary, the row inside) so it reduces
definitionally like the comb builders. -/
def zxcSwapAdjacent : Nat -> List Bool -> List Bool
  | 0, row => zxcSwapHere row
  | position + 1, row =>
      match row with
      | [] => []
      | headBit :: restBits => headBit :: zxcSwapAdjacent position restBits

/-- The head-swap preserves the row length. -/
theorem zxcSwapHereLength : (row : List Bool) ->
    (zxcSwapHere row).length = row.length
  | [] => rfl
  | _onlyBit :: [] => rfl
  | _bitA :: _bitB :: _restBits => rfl

/-- Swapping preserves the row length. -/
theorem zxcSwapAdjacentLength : (position : Nat) -> (row : List Bool) ->
    (zxcSwapAdjacent position row).length = row.length
  | 0, row => zxcSwapHereLength row
  | _position + 1, [] => rfl
  | position + 1, headBit :: restBits => by
      show (headBit :: zxcSwapAdjacent position restBits).length
        = (headBit :: restBits).length
      exact congrArg (fun innerValue => innerValue + 1)
        (zxcSwapAdjacentLength position restBits)

/-- The swap at the concatenation seam swaps exactly the two named bits. -/
theorem zxcSwapAdjacentAtCat : (frontBits : List Bool) -> (bitA bitB : Bool) ->
    (backBits : List Bool) ->
    zxcSwapAdjacent frontBits.length (zxpCat frontBits (bitA :: bitB :: backBits))
      = zxpCat frontBits (bitB :: bitA :: backBits)
  | [], _bitA, _bitB, _backBits => rfl
  | frontHead :: frontRest, bitA, bitB, backBits => by
      show frontHead :: zxcSwapAdjacent frontRest.length
          (zxpCat frontRest (bitA :: bitB :: backBits))
        = frontHead :: zxpCat frontRest (bitB :: bitA :: backBits)
      exact congrArg (fun innerRow => frontHead :: innerRow)
        (zxcSwapAdjacentAtCat frontRest bitA bitB backBits)

/-- Swap the adjacent column pair in every generator row. -/
def zxcSwapRowsAt (position : Nat) : List (List Bool) -> List (List Bool)
  | [] => []
  | row :: restRows => zxcSwapAdjacent position row :: zxcSwapRowsAt position restRows

/-- The column swap preserves every row width. -/
theorem zxcSwapRowsAtAllWidth (position : Nat) : {rowWidth : Nat} ->
    (generatorRows : List (List Bool)) ->
    ZxpAllWidth rowWidth generatorRows ->
    ZxpAllWidth rowWidth (zxcSwapRowsAt position generatorRows)
  | _rowWidth, [], _hAll => ZxpAllWidth.nil
  | rowWidth, row :: restRows, hAll => by
      cases hAll with
      | cons hHead hRest =>
          exact ZxpAllWidth.cons
            ((zxcSwapAdjacentLength position row).trans hHead)
            (zxcSwapRowsAtAllWidth position restRows hRest)

/-- Split a row at an adjacent column pair. -/
theorem zxcRowSplitAt : (leftWires : Nat) -> (row : List Bool) -> (tailLen : Nat) ->
    row.length = leftWires + (2 + tailLen) ->
    Exists fun frontBits => Exists fun bitA => Exists fun bitB =>
      Exists fun backBits =>
      row = zxpCat frontBits (bitA :: bitB :: backBits)
        /\ frontBits.length = leftWires /\ backBits.length = tailLen
  | 0, row, tailLen, hLen => by
      rw [Nat.zero_add, Nat.add_comm 2 tailLen] at hLen
      obtain ⟨bitA, restOne, hRowShape, hRestOneLen⟩ :=
        zxnLengthSuccShape row (tailLen + 1) hLen
      obtain ⟨bitB, restTwo, hRestOneShape, hRestTwoLen⟩ :=
        zxnLengthSuccShape restOne tailLen hRestOneLen
      refine Exists.intro [] (Exists.intro bitA (Exists.intro bitB
        (Exists.intro restTwo (And.intro ?_ (And.intro rfl hRestTwoLen)))))
      rw [hRowShape, hRestOneShape]
      exact rfl
  | leftPred + 1, row, tailLen, hLen => by
      rw [Nat.add_comm 2 tailLen] at hLen
      obtain ⟨headBit, restBits, hRowShape, hRestLen⟩ :=
        zxnLengthSuccShape row ((leftPred + 1) + (tailLen + 1)) hLen
      rw [Nat.add_assoc leftPred 1 (tailLen + 1),
        <- zxnTwoPlusEqOnePlusSucc tailLen,
        Nat.add_comm 2 tailLen] at hRestLen
      rw [<- Nat.add_comm 2 tailLen] at hRestLen
      obtain ⟨frontRest, bitA, bitB, backBits, hRestShape, hFrontLen, hBackLen⟩ :=
        zxcRowSplitAt leftPred restBits tailLen hRestLen
      refine Exists.intro (headBit :: frontRest) (Exists.intro bitA
        (Exists.intro bitB (Exists.intro backBits
          (And.intro ?_ (And.intro ?_ hBackLen)))))
      · rw [hRowShape, hRestShape]
        exact rfl
      · show frontRest.length + 1 = leftPred + 1
        rw [hFrontLen]

/-- THE BLOCK RIDE: a strand crossing above one whole conditional-xor
generator block commutes through it — create-layer exchange, then the comb
ride — exiting at the SAME strand pair with the row's two bits swapped. -/
theorem zxcXorRowCrossRide (frontBits : List Bool) (bitA bitB : Bool)
    (backBits : List Bool) :
    ZxwConv
      { sourceArity := frontBits.length + (2 + backBits.length)
        layers := zxpWhiskerLayer frontBits.length backBits.length
            [ZxpCell.crossing]
          :: zxnXorRowLayers (zxpCat frontBits (bitA :: bitB :: backBits)) }
      { sourceArity := frontBits.length + (2 + backBits.length)
        layers := zxpCatLayers
          (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits)))
          [zxpWhiskerLayer frontBits.length backBits.length
            [ZxpCell.crossing]] } := by
  show ZxwConv
    { sourceArity := frontBits.length + (2 + backBits.length)
      layers := zxpWhiskerLayer frontBits.length backBits.length
          [ZxpCell.crossing]
        :: zxpWhiskerLayer 0
            (zxpCat frontBits (bitA :: bitB :: backBits)).length
            [ZxpCell.zSpider 0 1]
        :: zxnCombLayers 0 (zxpCat frontBits (bitA :: bitB :: backBits)) }
    { sourceArity := frontBits.length + (2 + backBits.length)
      layers := zxpCatLayers
        (zxpWhiskerLayer 0
            (zxpCat frontBits (bitB :: bitA :: backBits)).length
            [ZxpCell.zSpider 0 1]
          :: zxnCombLayers 0 (zxpCat frontBits (bitB :: bitA :: backBits)))
        [zxpWhiskerLayer frontBits.length backBits.length
          [ZxpCell.crossing]] }
  rw [zxpCatLength frontBits (bitA :: bitB :: backBits),
    zxpCatLength frontBits (bitB :: bitA :: backBits),
    show (bitA :: bitB :: backBits).length = 2 + backBits.length from
      Nat.add_comm backBits.length 2,
    show (bitB :: bitA :: backBits).length = 2 + backBits.length from
      Nat.add_comm backBits.length 2]
  -- step 1: the crossing exchanges past the coefficient creation
  have hCreateExch := zxwLiftConv (frontBits.length + (2 + backBits.length))
    [] (zxnCombLayers 0 (zxpCat frontBits (bitA :: bitB :: backBits)))
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 0 1]
      (zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing]))
    (ZxpLayersWF.nil _)
    (by
      show frontBits.length + (2 + backBits.length)
        = zxpLayerDomArity [ZxpCell.zSpider 0 1]
          + zxpLayerDomArity (zxpWhiskerLayer frontBits.length
            backBits.length [ZxpCell.crossing])
      rw [zxpWhiskerLayerDomArity]
      exact (Nat.zero_add
        (frontBits.length + (zxpLayerDomArity [ZxpCell.crossing]
          + backBits.length))).symm)
    (by
      show ZxpLayersWF
        (zxpDiagramCodArity (zxeExchangeLhs [ZxpCell.zSpider 0 1]
          (zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing])))
        (zxnCombLayers 0 (zxpCat frontBits (bitA :: bitB :: backBits)))
      rw [zxeExchangeLhsCodArity [ZxpCell.zSpider 0 1]
          (zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing]),
        zxpWhiskerLayerCodArity]
      have hCombWF := zxnCombLayersWF
        (zxpCat frontBits (bitA :: bitB :: backBits)) 0
      rw [zxpCatLength frontBits (bitA :: bitB :: backBits),
        show (bitA :: bitB :: backBits).length = 2 + backBits.length from
          Nat.add_comm backBits.length 2,
        Nat.zero_add] at hCombWF
      exact hCombWF)
  rw [zxpWhiskerLayerDomArity frontBits.length backBits.length
      [ZxpCell.crossing],
    show zxpLayerDomArity [ZxpCell.crossing] = 2 from rfl,
    show zxpLayerCodArity [ZxpCell.zSpider 0 1] = 1 from rfl,
    zxpWhiskerLayerCodArity frontBits.length backBits.length [ZxpCell.crossing],
    show zxpLayerCodArity [ZxpCell.crossing] = 2 from rfl,
    show zxpLayerDomArity [ZxpCell.zSpider 0 1] = 0 from rfl] at hCreateExch
  -- step 2: the comb ride at prefix zero
  have hRide := zxcCombCrossRide frontBits bitA bitB backBits 0
  rw [Nat.zero_add (1 + frontBits.length), Nat.zero_add frontBits.length,
    Nat.add_comm 1 frontBits.length] at hRide
  have hRideLift := zxwLiftConv (frontBits.length + (2 + backBits.length))
    [zxpWhiskerLayer 0 (frontBits.length + (2 + backBits.length))
      [ZxpCell.zSpider 0 1]]
    [] hRide
    (ZxpLayersWF.cons (by
      rw [zxpWhiskerLayerDomArity, Nat.zero_add,
        show zxpLayerDomArity [ZxpCell.zSpider 0 1] = 0 from rfl,
        Nat.zero_add]) (ZxpLayersWF.nil _))
    (by
      show zxpLayerCodArity (zxpWhiskerLayer 0
          (frontBits.length + (2 + backBits.length)) [ZxpCell.zSpider 0 1])
        = (frontBits.length + 1) + (2 + backBits.length)
      rw [zxpWhiskerLayerCodArity, Nat.zero_add]
      exact (Nat.add_assoc 1 frontBits.length (2 + backBits.length)).symm.trans
        (congrArg (fun innerValue => innerValue + (2 + backBits.length))
          (Nat.add_comm 1 frontBits.length)))
    (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hRideLift
  refine ZxwConv.trans ?_ hRideLift
  exact hCreateExch

/-! ## Stage 5 — the generator-blocks fold: the crossing rides through the whole
generator block list, swapping the two crossed columns in every row -/

/-- THE GENERATOR-BLOCKS RIDE: a strand crossing entering the whole generator
block list of a normal form commutes through it — every row's two crossed
columns swap (`zxcSwapRowsAt leftWires`), the crossing exits below the last
block at the same position.  Induction on the generator rows; each step is one
block ride (`zxcXorRowCrossRide`). -/
theorem zxcGeneratorBlocksCrossRide (leftWires rightWires : Nat) :
    (generatorRows : List (List Bool)) ->
    ZxpAllWidth (leftWires + (2 + rightWires)) generatorRows ->
    ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]
          :: zxnGeneratorBlockLayers generatorRows }
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxpCatLayers
          (zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
          [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]] }
  | [], _hAll => by
      refine ZxwConv.refl _ ?_
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
      rw [zxpWhiskerLayerDomArity, show zxpLayerDomArity [ZxpCell.crossing] = 2 from rfl]
  | generatorRow :: restRows, hAll => by
      have hRowLen : generatorRow.length = leftWires + (2 + rightWires) := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth (leftWires + (2 + rightWires)) restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      obtain ⟨frontBits, bitA, bitB, backBits, hRowShape, hFrontLen, hBackLen⟩ :=
        zxcRowSplitAt leftWires generatorRow rightWires hRowLen
      subst hFrontLen
      subst hBackLen
      subst hRowShape
      -- expose the block structure on both sides
      show ZxwConv
        { sourceArity := frontBits.length + (2 + backBits.length)
          layers := zxpWhiskerLayer frontBits.length backBits.length
              [ZxpCell.crossing]
            :: zxpCatLayers
              (zxnXorRowLayers (zxpCat frontBits (bitA :: bitB :: backBits)))
              (zxnGeneratorBlockLayers restRows) }
        { sourceArity := frontBits.length + (2 + backBits.length)
          layers := zxpCatLayers
            (zxpCatLayers
              (zxnXorRowLayers
                (zxcSwapAdjacent frontBits.length
                  (zxpCat frontBits (bitA :: bitB :: backBits))))
              (zxnGeneratorBlockLayers (zxcSwapRowsAt frontBits.length restRows)))
            [zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing]] }
      rw [zxcSwapAdjacentAtCat frontBits bitA bitB backBits]
      -- step 1: ride the crossing through the first block, past the tail
      have hBlock := zxcXorRowCrossRide frontBits bitA bitB backBits
      have hBlockLift := zxwLiftConv (frontBits.length + (2 + backBits.length))
        [] (zxnGeneratorBlockLayers restRows) hBlock (ZxpLayersWF.nil _) rfl
        (by
          show ZxpLayersWF
            (zxpLayersCodArity
              (zxpLayerCodArity (zxpWhiskerLayer frontBits.length backBits.length
                [ZxpCell.crossing]))
              (zxnXorRowLayers (zxpCat frontBits (bitA :: bitB :: backBits))))
            (zxnGeneratorBlockLayers restRows)
          rw [zxpWhiskerLayerCodArity,
            show zxpLayerCodArity [ZxpCell.crossing] = 2 from rfl,
            zxnXorRowLayersCodArity, zxpCatLength frontBits (bitA :: bitB :: backBits),
            show (bitA :: bitB :: backBits).length = 2 + backBits.length from
              Nat.add_comm backBits.length 2]
          exact zxnGeneratorBlockLayersWF restRows
            (frontBits.length + (2 + backBits.length)) hRestAll)
      have hBlockShaped : ZxwConv
          { sourceArity := frontBits.length + (2 + backBits.length)
            layers := zxpWhiskerLayer frontBits.length backBits.length
                [ZxpCell.crossing]
              :: zxpCatLayers
                (zxnXorRowLayers (zxpCat frontBits (bitA :: bitB :: backBits)))
                (zxnGeneratorBlockLayers restRows) }
          { sourceArity := frontBits.length + (2 + backBits.length)
            layers := zxpCatLayers
              (zxpCatLayers
                (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits)))
                [zxpWhiskerLayer frontBits.length backBits.length
                  [ZxpCell.crossing]])
              (zxnGeneratorBlockLayers restRows) } := hBlockLift
      rw [zxnCatLayersAssoc
        (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits)))
        [zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing]]
        (zxnGeneratorBlockLayers restRows)] at hBlockShaped
      refine ZxwConv.trans hBlockShaped ?_
      -- step 2: recurse through the remaining blocks
      have hRec := zxcGeneratorBlocksCrossRide frontBits.length backBits.length
        restRows hRestAll
      have hRecLift := zxwLiftConv (frontBits.length + (2 + backBits.length))
        (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits))) [] hRec
        (by
          have hWF := zxnXorRowLayersWF (zxpCat frontBits (bitB :: bitA :: backBits))
          rw [zxpCatLength frontBits (bitB :: bitA :: backBits),
            show (bitB :: bitA :: backBits).length = 2 + backBits.length from
              Nat.add_comm backBits.length 2] at hWF
          exact hWF)
        (by
          rw [zxnXorRowLayersCodArity, zxpCatLength frontBits (bitB :: bitA :: backBits),
            show (bitB :: bitA :: backBits).length = 2 + backBits.length from
              Nat.add_comm backBits.length 2])
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hRecLift
      have hRecShaped : ZxwConv
          { sourceArity := frontBits.length + (2 + backBits.length)
            layers := zxpCatLayers
              (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits)))
              (zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing]
                :: zxnGeneratorBlockLayers restRows) }
          { sourceArity := frontBits.length + (2 + backBits.length)
            layers := zxpCatLayers
              (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits)))
              (zxpCatLayers
                (zxnGeneratorBlockLayers (zxcSwapRowsAt frontBits.length restRows))
                [zxpWhiskerLayer frontBits.length backBits.length
                  [ZxpCell.crossing]]) } := hRecLift
      rw [<- zxnCatLayersAssoc
        (zxnXorRowLayers (zxpCat frontBits (bitB :: bitA :: backBits)))
        (zxnGeneratorBlockLayers (zxcSwapRowsAt frontBits.length restRows))
        [zxpWhiskerLayer frontBits.length backBits.length [ZxpCell.crossing]]]
        at hRecShaped
      exact hRecShaped

/-! ## Stage 6 — the boundary commutes: the crossing past the init layer and
into the kill layer -/

/-- THE INIT PASS: a strand crossing above the init layer commutes below it —
the init layer creates its zero states on the disjoint appended strands, so the
crossing rides through unchanged, widening its right remainder by the codomain
width.  One firing of the disjoint-block engine with the zero-state block. -/
theorem zxcCrossPastInit (leftWires rightWires codWidth : Nat) :
    ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing],
          zxnInitLayer (leftWires + (2 + rightWires)) codWidth] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxnInitLayer (leftWires + (2 + rightWires)) codWidth,
          zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]] } := by
  have hEngine := zxwOfZxeConv (zxwLayersPastRightLayer
    (zxnZeroStateCells codWidth)
    [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]]
    (leftWires + (2 + rightWires))
    (ZxpLayersWF.cons (by
        rw [zxpWhiskerLayerDomArity,
          show zxpLayerDomArity [ZxpCell.crossing] = 2 from rfl])
      (ZxpLayersWF.nil _)))
  rw [zxnZeroStateCellsDomArity codWidth, Nat.add_zero,
    zxnZeroStateCellsCodArity codWidth,
    show zxpWhiskerLayers 0 codWidth
          [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]]
        = [zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]] from by
      show [zxpWhiskerLayer 0 codWidth
          (zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing])] = _
      rw [zxnWhiskerLayerCompose 0 codWidth leftWires rightWires [ZxpCell.crossing],
        Nat.zero_add],
    zxpWhiskerLayersZero [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]],
    show zxpLayersCodArity (leftWires + (2 + rightWires))
          [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]]
        = leftWires + (2 + rightWires) from by
      show zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing])
        = leftWires + (2 + rightWires)
      rw [zxpWhiskerLayerCodArity,
        show zxpLayerCodArity [ZxpCell.crossing] = 2 from rfl]] at hEngine
  exact ZxwConv.symm hEngine

/-- THE KILL-DEATH RESIDUAL (owner false, the one remaining cell-level wall for
the crossing residual): a strand crossing above the kill layer dies — both
crossed strands feed adjacent kill collectors, so the symmetric collection
absorbs the crossing.  The `zxbCrossingIntoKillPairFire` boundary fire (r13) is
the width-2 witness; the general form needs the tensor-band interchange
(spectator kill cells on both sides), the one piece not yet reduced to an
existing disjoint-block engine. -/
def zxcCrossIntoKillStatement : Prop :=
  (leftWires rightWires codWidth : Nat) ->
  ZxwConv
    { sourceArity := (leftWires + (2 + rightWires)) + codWidth
      layers := [zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing],
        zxnKillLayer (leftWires + (2 + rightWires)) codWidth] }
    { sourceArity := (leftWires + (2 + rightWires)) + codWidth
      layers := [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] }

/-! ## Stage 7 — THE CROSSING RESIDUAL, reduced to the kill-death

The crossing residual `zxbCrossingAbsorbStatement` is now PROVED modulo exactly
the one kill-death `zxcCrossIntoKillStatement`: the crossing rides past the init
layer (`zxcCrossPastInit`), through every generator block swapping the two
crossed columns (`zxcGeneratorBlocksCrossRide`), and dies in the kill layer
(the residual hypothesis).  The absorbed generator list is
`zxcSwapRowsAt leftWires generatorRows`. -/

/-- THE CROSSING ABSORPTION FROM THE KILL-DEATH: given the kill-death residual,
the whole crossing residual holds — the crossing rides through the entire normal
form, swapping the two crossed columns in every generator row and dying in the
kill layer. -/
theorem zxcCrossingAbsorbOfKillDeath (hKill : zxcCrossIntoKillStatement) :
    zxbCrossingAbsorbStatement := by
  intro leftWires rightWires codWidth entryWidth exitWidth hEntryEq hExitEq
    generatorRows hAll
  subst hEntryEq
  subst hExitEq
  have hWidthAssoc : (leftWires + (2 + rightWires)) + codWidth
      = leftWires + (2 + (rightWires + codWidth)) := by
    rw [Nat.add_assoc leftWires (2 + rightWires) codWidth,
      Nat.add_assoc 2 rightWires codWidth]
  have hSwapAll : ZxpAllWidth ((leftWires + (2 + rightWires)) + codWidth)
      (zxcSwapRowsAt leftWires generatorRows) :=
    zxcSwapRowsAtAllWidth leftWires generatorRows hAll
  refine Exists.intro (zxcSwapRowsAt leftWires generatorRows)
    (And.intro hSwapAll ?_)
  have hNFWF := zxnNormalFormWF (leftWires + (2 + rightWires)) codWidth
    generatorRows hAll
  -- step 1: past the init layer
  have hP1 := zxwLiftConv (leftWires + (2 + rightWires)) []
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (2 + rightWires)) codWidth])
    (zxcCrossPastInit leftWires rightWires codWidth)
    (ZxpLayersWF.nil _) rfl
    (by
      cases hNFWF with
      | cons _hInitDom hTail => exact hTail)
  have hP1Shaped : ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]
          :: zxnInitLayer (leftWires + (2 + rightWires)) codWidth
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
            [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxnInitLayer (leftWires + (2 + rightWires)) codWidth
          :: zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
            [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] } := hP1
  -- step 2: through the generator blocks (swapping the crossed columns)
  have hRide := zxcGeneratorBlocksCrossRide leftWires (rightWires + codWidth)
    generatorRows (zxpAllWidthCast hWidthAssoc hAll)
  have hP2 := zxwLiftConv (leftWires + (2 + rightWires))
    [zxnInitLayer (leftWires + (2 + rightWires)) codWidth]
    [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] hRide
    (ZxpLayersWF.cons (zxnInitLayerDomArity (leftWires + (2 + rightWires)) codWidth)
      (ZxpLayersWF.nil _))
    (by
      show zxpLayerCodArity (zxnInitLayer (leftWires + (2 + rightWires)) codWidth)
        = leftWires + (2 + (rightWires + codWidth))
      rw [zxnInitLayerCodArity]
      exact hWidthAssoc)
    (by
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
      show zxpLayerDomArity (zxnKillLayer (leftWires + (2 + rightWires)) codWidth)
        = zxpLayersCodArity
            (zxpLayerCodArity
              (zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]))
            (zxnGeneratorBlockLayers generatorRows)
      rw [zxnKillLayerDomArity, zxpWhiskerLayerCodArity,
        show zxpLayerCodArity [ZxpCell.crossing] = 2 from rfl,
        zxnGeneratorBlockLayersCodArity generatorRows
          (leftWires + (2 + (rightWires + codWidth))) (zxpAllWidthCast hWidthAssoc hAll)]
      exact hWidthAssoc)
  have hP2Shaped : ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxnInitLayer (leftWires + (2 + rightWires)) codWidth
          :: zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
            [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxnInitLayer (leftWires + (2 + rightWires)) codWidth
          :: zxpCatLayers
            (zxpCatLayers
              (zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
              [zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]])
            [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] } := hP2
  rw [zxnCatLayersAssoc
    (zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
    [zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing]]
    [zxnKillLayer (leftWires + (2 + rightWires)) codWidth]] at hP2Shaped
  -- step 3: into the kill layer (the crossing dies)
  have hP3 := zxwLiftConv (leftWires + (2 + rightWires))
    (zxnInitLayer (leftWires + (2 + rightWires)) codWidth
      :: zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
    [] (hKill leftWires rightWires codWidth)
    (ZxpLayersWF.cons (zxnInitLayerDomArity (leftWires + (2 + rightWires)) codWidth)
      (by
        rw [zxnInitLayerCodArity]
        exact zxnGeneratorBlockLayersWF (zxcSwapRowsAt leftWires generatorRows)
          ((leftWires + (2 + rightWires)) + codWidth) hSwapAll))
    (by
      show zxpLayersCodArity
          (zxpLayerCodArity (zxnInitLayer (leftWires + (2 + rightWires)) codWidth))
          (zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
        = (leftWires + (2 + rightWires)) + codWidth
      rw [zxnInitLayerCodArity,
        zxnGeneratorBlockLayersCodArity (zxcSwapRowsAt leftWires generatorRows)
          ((leftWires + (2 + rightWires)) + codWidth) hSwapAll])
    (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hP3
  have hP3Shaped : ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxnInitLayer (leftWires + (2 + rightWires)) codWidth
          :: zxpCatLayers
            (zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
            [zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing],
              zxnKillLayer (leftWires + (2 + rightWires)) codWidth] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := zxnInitLayer (leftWires + (2 + rightWires)) codWidth
          :: zxpCatLayers
            (zxnGeneratorBlockLayers (zxcSwapRowsAt leftWires generatorRows))
            [zxnKillLayer (leftWires + (2 + rightWires)) codWidth] } := hP3
  exact ZxwConv.trans hP1Shaped (ZxwConv.trans hP2Shaped hP3Shaped)

/-! ## Stage 8 — kill-death evidence, fires, and the honest marker ledger -/

/-- EVIDENCE for the kill-death wall: a strand crossing at ANY position, above
its own two adjacent kill collectors with WIRE spectators on both sides, dies —
the committed r13 boundary fire whiskered to general prefix/remainder.  The gap
to the full `zxcCrossIntoKillStatement` is exactly the spectator KILL cells (the
side bands carry collectors, not wires); the death mechanism itself is closed
here at every position. -/
theorem zxcCrossIntoKillPairWhiskered (leftWires rightWires : Nat) :
    ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing],
          zxpWhiskerLayer leftWires rightWires (zxnKillLayer 2 0)] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires (zxnKillLayer 2 0)] } := by
  have hLift := zxwConvLift (leftWires + (2 + rightWires)) leftWires rightWires
    [] [] zxbCrossingIntoKillPairFire (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
  dsimp only [zxpPadDiagram] at hLift
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLift
  exact hLift

/-- Fire: the block ride at a literal instance — a crossing above the single
conditional-xor block of the row `[true, false]` commutes through, exiting
below with the row's two bits swapped to `[false, true]`. -/
theorem zxcXorRowCrossRideFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpWhiskerLayer 0 0 [ZxpCell.crossing]
          :: zxnXorRowLayers [true, false] }
      { sourceArity := 2
        layers := zxpCatLayers (zxnXorRowLayers [false, true])
          [zxpWhiskerLayer 0 0 [ZxpCell.crossing]] } :=
  zxcXorRowCrossRide [] true false []

/-- Kernel span pin for the block-ride fire. -/
theorem zxcXorRowCrossRideFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayer 0 0 [ZxpCell.crossing]
            :: zxnXorRowLayers [true, false] })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpCatLayers (zxnXorRowLayers [false, true])
            [zxpWhiskerLayer 0 0 [ZxpCell.crossing]] }) = true := rfl

/-- Fire: the generator-blocks ride at a two-row instance — a crossing above two
conditional-xor blocks commutes through both, swapping the two crossed columns
in each row. -/
theorem zxcGeneratorBlocksCrossRideFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpWhiskerLayer 0 0 [ZxpCell.crossing]
          :: zxnGeneratorBlockLayers [[true, false], [false, true]] }
      { sourceArity := 2
        layers := zxpCatLayers
          (zxnGeneratorBlockLayers (zxcSwapRowsAt 0 [[true, false], [false, true]]))
          [zxpWhiskerLayer 0 0 [ZxpCell.crossing]] } :=
  zxcGeneratorBlocksCrossRide 0 0 [[true, false], [false, true]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-- Fire: the init pass at a literal instance — a crossing above the init layer
of a two-strand, one-codomain-wire normal form widens past it. -/
theorem zxcCrossPastInitFire :
    ZxwConv
      { sourceArity := 2
        layers := [zxpWhiskerLayer 0 0 [ZxpCell.crossing], zxnInitLayer 2 1] }
      { sourceArity := 2
        layers := [zxnInitLayer 2 1, zxpWhiskerLayer 0 1 [ZxpCell.crossing]] } :=
  zxcCrossPastInit 0 0 1

/-- Kernel span pin: the kill-death residual is semantically sound at a content
instance with a codomain wire — the crossing above the two-strand kill layer
(codWidth = 1) denotes the same span as the kill layer alone.  This is the
soundness certificate the walled `zxcCrossIntoKillStatement` needs. -/
theorem zxcCrossIntoKillResidualSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2 + 1
          layers := [zxpWhiskerLayer 0 (0 + 1) [ZxpCell.crossing],
            zxnKillLayer 2 1] })
      (zxpDiagramDenote { sourceArity := 2 + 1, layers := [zxnKillLayer 2 1] })
      = true := rfl

/-- Refutation fire: a crossing whiskered above a normal form does NOT collapse
to a span-DISTINCT normal form — the crossing residual has genuine content
(the swap is not vacuous). -/
theorem zxcCrossingRideSpanDistinctNotConv :
    Not (ZxwConv (zxnNormalForm 2 0 [[true, false]]) (zxnNormalForm 2 0 [[false, true]])) := by
  intro hConv
  have hTrue := zxwConvSpanEqB hConv
  have hFalse : zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm 2 0 [[true, false]]))
      (zxpDiagramDenote (zxnNormalForm 2 0 [[false, true]])) = false := rfl
  rw [hFalse] at hTrue
  exact Bool.noConfusion hTrue

/-- CONTENT MARKER: THE SINGLE-COMB CROSSING RIDE IS LIVE — the window quadruple
(`zxcStrandWindowFF/FT/TF/TT`), the general-position window
(`zxcStrandCrossWindowAt`), the gadget pass (`zxcCrossPastGadget`), the comb ride
(`zxcCombCrossRide`), the block ride (`zxcXorRowCrossRide`), the generator-blocks
fold (`zxcGeneratorBlocksCrossRide`), and the init pass (`zxcCrossPastInit`) are
all machine-checked zero-axiom.  The crossing residual `zxbCrossingAbsorbStatement`
is PROVED modulo exactly one named cell-level statement, the kill-death
`zxcCrossIntoKillStatement` (`zxcCrossingAbsorbOfKillDeath`). -/
def zxcHasCrossingRide : Bool := true

/-- OWNER MARKER (FALSE): the crossing residual did NOT flip unconditionally this
round — `zxcCrossIntoKillStatement` (the tensor-band death with spectator kill
cells) remains open, so `zxcCrossingAbsorbOfKillDeath` is a conditional assembly,
not an inhabitant of `zxbCrossingAbsorbStatement`.  The committed owner-false
flags in `AbsorptionInduction` stay byte-intact. -/
def zxcCrossingResidualIsClosed : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
