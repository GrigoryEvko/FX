import FX1Poly.Polygraph.Omega.ZXPhaseFree.TransportRides

/-! # Polygraph/Omega/ZXPhaseFree/TransvectionRide — the CNOT ride and the
generator transport

The TransportRides round landed the swap ride whole
(`zxtCombSwapHolds : zxfCombSwapStatement`) and walled the FT/TT CNOT windows
owner-false.  This round lands THE TRANSVECTION RIDE and with it the
generator transport:

* (i)   THE FT CNOT WINDOW (`zxvCnotWindowFTHolds : zxtCnotWindowFTStatement`):
  the carrier CNOT passes a skip/tap position.  The transcribed chain: one
  exchange pair extracts the skip crossing, THE BIALGEBRA SQUARE fires at
  whisker (0, 2), and the six-strand residual routes the doubled carriers
  back into gadget shape — twenty-nine further lifted moves through the
  committed exchange pairs, the merge-routing bricks, both fork slides, the
  Z-coassociativity/cocommutativity dance on the triple-forked inner carrier,
  X-associativity on the merge chain, and one sigma-involution kill.
* (ii)  THE TT CNOT WINDOW (`zxvCnotWindowTTHolds : zxtCnotWindowTTStatement`):
  FT plus the Hopf cancellation, factored through two fresh bricks — the
  shared-control CNOT slide (`zxvSharedControlSlide`: two CNOTs reading the
  same control and writing disjoint targets commute, pure
  coassociativity/routing) and THE TAP-PAIR COLLAPSE (`zxvTapPairCollapse`:
  a CNOT applied twice is the identity — exchange, coassociativity,
  X-associativity backwards, THE HOPF ROW, the X-unit, and the fork-right
  discard `zxvForkRightDiscard`).
* (iii) THE CNOT RIDE (`zxvCnotRideDouble`): the two-layer CNOT rider
  (`zxvCnotRiderLayers`) rides the whole zipped double comb, xoring the second
  row's tap bits into the first position by position through the
  four-window layer (`zxvCnotWindowAt`), and dies at the discard boundary
  (`zxvCnotIntoDiscards` — the bialgebra copy-mult row splits the discards).
* (iv)  THE COMB TRANSVECTION (`zxvCombXorAbsorbHolds :
  zxfCombXorAbsorbStatement`): zip, insert the birth CNOT
  (`zxfCreatesCnotInsert` backwards), ride, unzip — mirroring
  `zxtCombSwapHolds`.
* (v)   THE HEADLINE (`zxvGeneratorTransportHolds :
  zxwGeneratorTransportStatement`): the committed conditional assembly
  `zxfTransportOfCombMoves` fires on the two now-proven comb moves.  The
  committed owner-false flags (`zxtCnotWindowFTIsProven`,
  `zxtCnotWindowTTIsProven`, `zxtCombXorAbsorbIsProven`,
  `zxtGeneratorTransportIsProven`, `zxfCombXorAbsorbIsProven`,
  `zxfGeneratorTransportIsProven`, `zxwGeneratorTransportIsProven`) stay
  byte-intact in their home files; the fresh true markers below supersede
  them.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no
`List.append`, no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match
arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 1 — THE FT CNOT WINDOW, WHOLE

The r11 wall (`zxtCnotWindowFTStatement`) falls to the documented route: the
skip crossing extracts past the CNOT merge (one exchange pair), the CNOT
merge meets the tap fork and THE BIALGEBRA SQUARE fires at whisker (0, 2),
and the residual six-strand routing re-gadgets the doubled carriers: the
merge side postpones the left merge to the very end (five exchange pairs,
one merge-routing brick, one merge slide), the fork side rebrackets the
triple-forked inner carrier (coassociativity twice around a cocommutativity
insertion whose crossing pushes down and dies by the sigma involution), the
merge chain reassociates (X-associativity), and both forks slide back into
gadget position. -/

/-- THE FT CNOT WINDOW: the carrier CNOT passes a skip/tap position; the
skip tap flips to a tap — the bialgebra square distributed over one strand
position. -/
theorem zxvCnotWindowFTHolds : zxtCnotWindowFTStatement := by
  show ZxwConv
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
  -- step 1: the skip crossing extracts past the CNOT merge
  have hLift1 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift1
  refine ZxwConv.trans hStep1 ?_
  -- step 2: THE BIALGEBRA SQUARE at whisker (0, 2)
  have hLift2 := zxwConvLift 3 0 2
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.bialgSquare))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift2
  refine ZxwConv.trans hStep2 ?_
  -- step 3: the double fork extracts past the parked skip crossing
  have hLift3 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2]
      [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift3
  refine ZxwConv.trans hStep3 ?_
  -- step 4: the two parked crossings trade order (disjoint blocks)
  have hLift4 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]
      [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift4
  refine ZxwConv.trans hStep4 ?_
  -- step 5: the deep crossing extracts past the double merge
  have hLift5 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1]
      [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift5
  refine ZxwConv.trans hStep5 ?_
  -- step 6: the crossing feeding the near merge leg re-routes (mirror brick)
  have hLift6 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    zxtMergeAfterCross
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift6
  refine ZxwConv.trans hStep6 ?_
  -- step 7: the double merge fissions, right merge first
  have hLift7 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
      (ZxeWindowMove.rightFirstExchange [ZxpCell.xSpider 2 1]
        [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]))))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep7 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift7
  refine ZxwConv.trans hStep7 ?_
  -- step 8: the left merge extracts past the routing crossing
  have hLift8 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.crossing, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep8 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift8
  refine ZxwConv.trans hStep8 ?_
  -- step 9: the left merge extracts past the (+s) merge
  have hLift9 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep9 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift9
  refine ZxwConv.trans hStep9 ?_
  -- step 10: the left merge extracts past the exit crossing
  have hLift10 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep10 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLift10
  refine ZxwConv.trans hStep10 ?_
  -- step 11: the left merge slides right through the exit crossing
  have hLift11 := zxwConvLift 3 0 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]] []
    (zxwSlideRightConv (ZxpCell.xSpider 2 1))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStep11 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift11
  refine ZxwConv.trans hStep11 ?_
  -- step 12: the double fork fissions, inner fork first
  have hLift12 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
      (ZxeWindowMove.rightFirstExchange [ZxpCell.zSpider 1 2]
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]))))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep12 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift12
  refine ZxwConv.trans hStep12 ?_
  -- step 13: the two inner-carrier forks rebracket (coassociativity)
  have hLift13 := zxwConvLift 3 1 1 []
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep13 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift13
  refine ZxwConv.trans hStep13 ?_
  -- step 14: cocommutativity inserts a crossing after the inner fork
  have hLift14 := zxwConvLift 3 2 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCocomm)))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep14 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift14
  refine ZxwConv.trans hStep14 ?_
  -- step 15: the inserted crossing extracts past the outer fork
  have hLift15 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2]
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep15 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift15
  refine ZxwConv.trans hStep15 ?_
  -- step 16: the inserted crossing passes the disjoint routing crossing
  have hLift16 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.wire, ZxpCell.crossing]
      [ZxpCell.crossing, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep16 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift16
  refine ZxwConv.trans hStep16 ?_
  -- step 17: the pushed crossing re-routes at the right merge (mirror brick)
  have hLift17 := zxwConvLift 3 2 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    zxtMergeAfterCross
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep17 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift17
  refine ZxwConv.trans hStep17 ?_
  -- step 18: the sigma involution kills the doubled crossing
  have hLift18 := zxwConvLift 3 2 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep18 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift18
  refine ZxwConv.trans hStep18 ?_
  -- step 19: strip the dead wire layer
  have hLift19 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep19 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift19
  refine ZxwConv.trans hStep19 ?_
  -- step 20: the fork pair rebrackets back (coassociativity backwards)
  have hLift20 := zxwConvLift 3 1 1 []
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc)))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep20 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift20
  refine ZxwConv.trans hStep20 ?_
  -- step 21: the merge chain reassociates (X-associativity)
  have hLift21 := zxwConvLift 3 3 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidAssoc))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep21 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift21
  refine ZxwConv.trans hStep21 ?_
  -- step 22: the outer fork extracts past the inner fork
  have hLift22 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.zSpider 1 2]
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep22 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift22
  refine ZxwConv.trans hStep22 ?_
  -- step 23: the inner fork slides left back through the routing crossings
  have hLift23 := zxwConvLift 3 1 2
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwSlideLeftConv (ZxpCell.zSpider 1 2))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep23 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift23
  refine ZxwConv.trans hStep23 ?_
  -- step 24: the inner fork extracts past the (+s) merge
  have hLift24 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.zSpider 1 2]
      [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep24 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift24
  refine ZxwConv.trans hStep24 ?_
  -- step 25: the inner fork extracts past the chain merge
  have hLift25 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.zSpider 1 2]
      [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep25 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift25
  refine ZxwConv.trans hStep25 ?_
  -- step 26: the inner fork slides right into CNOT exit position
  have hLift26 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwSlideRightConv (ZxpCell.zSpider 1 2))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep26 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift26
  refine ZxwConv.trans hStep26 ?_
  -- step 27: the exit crossing extracts past the deep fork
  have hLift27 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtRightFirstToLeftFirst [ZxpCell.crossing] [ZxpCell.zSpider 1 2])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep27 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift27
  refine ZxwConv.trans hStep27 ?_
  -- step 28: the routing crossing extracts past the (+s) merge
  have hLift28 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.crossing] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep28 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift28
  refine ZxwConv.trans hStep28 ?_
  -- step 29: the outer fork extracts past the (+s) merge
  have hLift29 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.zSpider 1 2] [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep29 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift29
  refine ZxwConv.trans hStep29 ?_
  -- step 30: the second-gadget shape reassembles (mirror brick backwards)
  have hLift30 := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (ZxwConv.symm zxtMergeAfterCross)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep30 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift30
  refine ZxwConv.trans hStep30 ?_
  -- step 31: the skip crossing re-enters past the second-gadget fork
  have hLift31 := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.zSpider 1 2] [ZxpCell.crossing])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep31 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLift31
  exact hStep31

/-- CONTENT MARKER: the FT CNOT window is machine-checked.  Supersedes the
r11 owner `zxtCnotWindowFTIsProven := false`, which stays byte-intact in its
home file. -/
def zxvCnotWindowFTIsProven : Bool := true

/-! ## Stage 2 — the TT CNOT window bricks

Three reusable bricks factor the TT window: the fork-right discard (a fork
whose SECOND output dies is a wire — cocommutativity insertion, the discard
slides back through the inserted crossing, counit), the shared-control slide
(two gadgets reading the same control and writing disjoint targets commute —
two exchange pairs around a coassociativity rebracketing), and THE TAP-PAIR
COLLAPSE (the same tap applied twice is the identity — exchange,
coassociativity, X-associativity backwards, THE HOPF ROW, the fork-right
discard, and the X-unit). -/

/-- FORK-RIGHT DISCARD: a fork whose second output is discarded is a wire.
Route: grow a crossing by cocommutativity read backwards, pull the discard
back through it (right slide read backwards), close by the counit row. -/
theorem zxvForkRightDiscard :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 1, layers := [[ZxpCell.wire]] } := by
  -- step 1: cocommutativity read backwards grows a crossing under the fork
  have hLiftGrow := zxwLiftConv 1 [] [[ZxpCell.wire, ZxpCell.zSpider 1 0]]
    (ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCocomm)))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepGrow : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.zSpider 1 0]] } := hLiftGrow
  refine ZxwConv.trans hStepGrow ?_
  -- step 2: the discard pulls back through the crossing (right slide backwards)
  have hLiftSlide := zxwLiftConv 1 [[ZxpCell.zSpider 1 2]] []
    (ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 0)))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStepSlide : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 1 0, ZxpCell.wire]] } :=
    hLiftSlide
  refine ZxwConv.trans hStepSlide ?_
  -- step 3: the counit row closes
  exact zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCounit)

/-- THE SHARED-CONTROL SLIDE: the CNOT gadget (fork the control, merge into
the near target) commutes past the tap gadget (fork the control, merge into
the far target).  Two exchange pairs park the merges, coassociativity
rebrackets the fork pair, two exchange pairs restore gadget shape. -/
theorem zxvSharedControlSlide :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] } := by
  -- step 1: the CNOT merge extracts past the second fork
  have hLiftOne := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.zSpider 1 2, ZxpCell.wire])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepOne : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftOne
  refine ZxwConv.trans hStepOne ?_
  -- step 2: the CNOT merge extracts past the tap merge
  have hLiftTwo := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]] []
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.wire, ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStepTwo : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] } := hLiftTwo
  refine ZxwConv.trans hStepTwo ?_
  -- step 3: the fork pair rebrackets (coassociativity backwards)
  have hLiftThree := zxwConvLift 3 1 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]]
    (ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc)))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepThree : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] } := hLiftThree
  refine ZxwConv.trans hStepThree ?_
  -- step 4: the tap merge re-enters past the deep fork
  have hLiftFour := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]]
    (zxtLeftFirstToRightFirst [ZxpCell.wire, ZxpCell.zSpider 1 2] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepFour : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] } := hLiftFour
  exact hStepFour

/-- THE TAP-PAIR COLLAPSE: the same tap applied twice is the identity — the
double tap dies by THE HOPF ROW after the fork pair rebrackets and the merge
pair reassociates, the dead branch discards through the fork-right discard,
and the X-unit swallows the fresh unit. -/
theorem zxvTapPairCollapse :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]] } := by
  -- step 1: the second fork extracts past the first tap merge
  have hLiftOne := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    (zxtRightFirstToLeftFirst [ZxpCell.wire, ZxpCell.zSpider 1 2] [ZxpCell.xSpider 2 1])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepOne : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftOne
  refine ZxwConv.trans hStepOne ?_
  -- step 2: the fork pair rebrackets forward (coassociativity)
  have hLiftTwo := zxwConvLift 3 1 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCoassoc))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepTwo : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftTwo
  refine ZxwConv.trans hStepTwo ?_
  -- step 3: the merge pair reassociates backwards (X-associativity backwards)
  have hLiftThree := zxwConvLift 3 2 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]] []
    (ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidAssoc)))
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStepThree : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftThree
  refine ZxwConv.trans hStepThree ?_
  -- step 4: THE HOPF ROW kills the inner fork/merge pair
  have hLiftFour := zxwConvLift 3 2 1
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.hopf))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepFour : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftFour
  refine ZxwConv.trans hStepFour ?_
  -- step 5: the dead branch discards (fork-right discard at whisker (1, 1))
  have hLiftFive := zxwConvLift 3 1 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    zxvForkRightDiscard
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepFive : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftFive
  refine ZxwConv.trans hStepFive ?_
  -- step 6: strip the dead wire layer
  have hLiftSix := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire]))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepSix : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] } := hLiftSix
  refine ZxwConv.trans hStepSix ?_
  -- step 7: the X-unit swallows the fresh unit
  have hLiftSeven := zxwConvLift 3 2 0 [] []
    (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidUnit))
    (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
  have hStepSeven : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]] } := hLiftSeven
  exact hStepSeven

/-! ## Stage 3 — THE TT CNOT WINDOW, WHOLE

The r11 wall (`zxtCnotWindowTTStatement`) falls compositionally: the CNOT
slides past the first tap (shared-control slide), fires through the second
tap by THE PROVEN FT WINDOW (which mints a second copy of the first tap),
and the resulting double tap dies by THE TAP-PAIR COLLAPSE. -/

/-- THE TT CNOT WINDOW: the carrier CNOT passes a double-tap position; the
first tap cancels (T xor T = F) — shared-control slide, the FT window, the
tap-pair collapse, one strip. -/
theorem zxvCnotWindowTTHolds : zxtCnotWindowTTStatement := by
  show ZxwConv
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
  -- phase 1: the CNOT slides past the first tap (shared-control slide)
  have hLiftSlide := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    zxvSharedControlSlide
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepSlide : ZxwConv
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
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hLiftSlide
  refine ZxwConv.trans hStepSlide ?_
  -- phase 2: THE PROVEN FT WINDOW fires behind the parked tap
  have hLiftFire := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] []
    zxvCnotWindowFTHolds
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  have hStepFire : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLiftFire
  refine ZxwConv.trans hStepFire ?_
  -- phase 3: the double tap dies (tap-pair collapse)
  have hLiftCollapse := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    zxvTapPairCollapse
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepCollapse : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLiftCollapse
  refine ZxwConv.trans hStepCollapse ?_
  -- phase 4: strip the dead wire layer
  have hLiftStrip := zxwLiftConv 3 []
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer [ZxpCell.wire, ZxpCell.crossing]))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepStrip : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire]] } := hLiftStrip
  exact hStepStrip

/-- CONTENT MARKER: the TT CNOT window is machine-checked — the four-window
layer of the transvection ride is COMPLETE (FF/TF committed in
TransportRides, FT/TT here).  Supersedes the r11 owner
`zxtCnotWindowTTIsProven := false`, which stays byte-intact in its home
file. -/
def zxvCnotWindowTTIsProven : Bool := true

/-! ## Stage 4 — THE CNOT RIDE

The transvection rider is the two-layer CNOT gadget between the two zipped
carriers (fork the inner, merge into the outer).  It enters at the birth
(`zxfCreatesCnotInsert` backwards), passes each strand position through the
four-window layer (`zxvCnotWindowAt`, xoring the second comb's tap bit into
the first), and dies at the discard boundary (`zxvCnotIntoDiscards`). -/

/-- The CNOT rider between the two carriers at a general position: fork the
inner carrier, merge the copy into the outer carrier. -/
def zxvCnotRiderLayers (prefixWires rightWires : Nat) : List (List ZxpCell) :=
  [zxpWhiskerLayer prefixWires rightWires [ZxpCell.wire, ZxpCell.zSpider 1 2],
    zxpWhiskerLayer prefixWires (rightWires + 1) [ZxpCell.xSpider 2 1]]

/-- THE DISCARD BOUNDARY: the CNOT rider dies into the two carrier discards —
one exchange pair, the fork-right discard, a strip, the copy-mult bialgebra
row, and the discard-pair split. -/
theorem zxvCnotIntoDiscards :
    ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 0],
          [ZxpCell.zSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 0], [ZxpCell.zSpider 1 0]] } := by
  -- step 1: the CNOT merge extracts past the inner discard
  have hLiftOne := zxwLiftConv 2
    [[ZxpCell.wire, ZxpCell.zSpider 1 2]]
    [[ZxpCell.zSpider 1 0]]
    (zxtLeftFirstToRightFirst [ZxpCell.xSpider 2 1] [ZxpCell.zSpider 1 0])
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepOne : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 0],
          [ZxpCell.zSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0],
          [ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 0]] } := hLiftOne
  refine ZxwConv.trans hStepOne ?_
  -- step 2: the dead fork branch discards (fork-right discard at whisker (1, 0))
  have hLiftTwo := zxwConvLift 2 1 0 []
    [[ZxpCell.xSpider 2 1], [ZxpCell.zSpider 1 0]]
    zxvForkRightDiscard
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepTwo : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0],
          [ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 0]] } := hLiftTwo
  refine ZxwConv.trans hStepTwo ?_
  -- step 3: strip the dead wire layer
  have hLiftThree := zxwLiftConv 2 [] [[ZxpCell.zSpider 1 0]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer [ZxpCell.xSpider 2 1]))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStepThree : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 2 1],
          [ZxpCell.zSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 2 1], [ZxpCell.zSpider 1 0]] } := hLiftThree
  refine ZxwConv.trans hStepThree ?_
  -- step 4: the copy-mult bialgebra row splits the discard over the merge
  have hStepFour : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 2 1], [ZxpCell.zSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 1 0, ZxpCell.zSpider 1 0]] } :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.bialgCopyMult)
  refine ZxwConv.trans hStepFour ?_
  -- step 5: the merged discard pair splits right-first
  have hStepFive : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 1 0, ZxpCell.zSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 0], [ZxpCell.zSpider 1 0]] } :=
    ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
      (ZxeWindowMove.rightFirstExchange [ZxpCell.zSpider 1 0] [ZxpCell.zSpider 1 0])))
  exact hStepFive

/-- THE CNOT WINDOW AT GENERAL POSITION: the ride step at any prefix and
remainder, uniform in the two tap bits — the CNOT rider enters between the
carriers, the first tap bit xors with the second, the rider exits one
position deeper. -/
theorem zxvCnotWindowAt (tapFirst tapSecond : Bool)
    (prefixWires middleWires : Nat) :
    ZxwConv
      { sourceArity := prefixWires + (2 + (middleWires + 1))
        layers := zxpCatLayers
          (zxvCnotRiderLayers prefixWires (middleWires + 1))
          (zxpCatLayers
            (zxfGadgetLayers (prefixWires + 1) middleWires tapFirst)
            (zxfGadgetLayers prefixWires (middleWires + 1) tapSecond)) }
      { sourceArity := prefixWires + (2 + (middleWires + 1))
        layers := zxpCatLayers
          (zxfGadgetLayers (prefixWires + 1) middleWires
            (zxpXorB tapFirst tapSecond))
          (zxpCatLayers
            (zxfGadgetLayers prefixWires (middleWires + 1) tapSecond)
            (zxvCnotRiderLayers (prefixWires + 1) middleWires)) } := by
  cases tapFirst with
  | false =>
      cases tapSecond with
      | false =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxtCnotWindowFFHolds (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.zSpider 1 2],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire]]
          exact hLift
      | true =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxvCnotWindowFTHolds (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
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
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.zSpider 1 2],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing]]
          exact hLift
  | true =>
      cases tapSecond with
      | false =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxtCnotWindowTFHolds (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire]] }
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 2) middleWires [ZxpCell.xSpider 2 1],
                zxpWhiskerLayer (prefixWires + 1) middleWires [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.zSpider 1 2],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire]]
          exact hLift
      | true =>
          have hLift := zxwConvLift (prefixWires + (2 + (middleWires + 1)))
            prefixWires middleWires [] [] zxvCnotWindowTTHolds (ZxpLayersWF.nil _)
            (congrArg (fun innerValue => prefixWires + innerValue)
              (zxtTwoPlusSuccShuffle middleWires))
            (ZxpLayersWF.nil _)
          show ZxwConv
            { sourceArity := prefixWires + (2 + (middleWires + 1))
              layers := [zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
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
                  [ZxpCell.crossing],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire],
                zxpWhiskerLayer prefixWires middleWires
                  [ZxpCell.crossing, ZxpCell.wire],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.wire, ZxpCell.zSpider 1 2],
                zxpWhiskerLayer (prefixWires + 1) middleWires
                  [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
          rw [<- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.zSpider 1 2, ZxpCell.wire],
            <- zxtWhiskerBumpOne (prefixWires + 1) middleWires [ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.xSpider 2 1],
            <- zxtWhiskerBumpOne prefixWires middleWires [ZxpCell.crossing],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.wire, ZxpCell.zSpider 1 2],
            <- zxtWhiskerBumpOne prefixWires middleWires
              [ZxpCell.xSpider 2 1, ZxpCell.wire]]
          exact hLift

/-- THE CNOT RIDE: the CNOT rider between the two carriers rides the whole
zipped double comb, xoring the second comb's tap bits into the first position
by position, and dies at the discard boundary. -/
theorem zxvCnotRideDouble : (firstRow secondRow : List Bool) ->
    (prefixWires : Nat) -> secondRow.length = firstRow.length ->
    ZxwConv
      { sourceArity := prefixWires + (2 + firstRow.length)
        layers := zxpCatLayers
          (zxvCnotRiderLayers prefixWires firstRow.length)
          (zxtDoubleLayers prefixWires firstRow secondRow) }
      { sourceArity := prefixWires + (2 + firstRow.length)
        layers := zxtDoubleLayers prefixWires
          (zxpRowXor firstRow secondRow) secondRow }
  | [], [], prefixWires, _hLen => by
      show ZxwConv
        { sourceArity := prefixWires + (2 + 0)
          layers := [zxpWhiskerLayer prefixWires 0
              [ZxpCell.wire, ZxpCell.zSpider 1 2],
            zxpWhiskerLayer prefixWires 1 [ZxpCell.xSpider 2 1],
            zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.zSpider 1 0],
            zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]] }
        { sourceArity := prefixWires + (2 + 0)
          layers := [zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.zSpider 1 0],
            zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]] }
      rw [<- zxtWhiskerBumpOne prefixWires 0 [ZxpCell.zSpider 1 0]]
      exact zxwConvLift (prefixWires + (2 + 0)) prefixWires 0 [] []
        zxvCnotIntoDiscards (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
  | [], _secondBit :: _secondRest, _prefixWires, hLen => Nat.noConfusion hLen
  | _firstBit :: _firstRest, [], _prefixWires, hLen => Nat.noConfusion hLen
  | firstBit :: firstRest, secondBit :: secondRest, prefixWires, hLen => by
      have hTailLen : secondRest.length = firstRest.length := Nat.succ.inj hLen
      have hXorTailLen : (zxpRowXor firstRest secondRest).length
          = firstRest.length :=
        zxpRowXorLength firstRest secondRest firstRest.length rfl hTailLen
      have hFinalEq : zxtDoubleLayers prefixWires
          (zxpRowXor (firstBit :: firstRest) (secondBit :: secondRest))
          (secondBit :: secondRest)
          = zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length
                (zxpXorB firstBit secondBit))
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
                (zxtDoubleLayers (prefixWires + 1)
                  (zxpRowXor firstRest secondRest) secondRest)) := by
        show zxpCatLayers
            (zxfGadgetLayers (prefixWires + 1)
              (zxpRowXor firstRest secondRest).length (zxpXorB firstBit secondBit))
            (zxpCatLayers
              (zxfGadgetLayers prefixWires
                ((zxpRowXor firstRest secondRest).length + 1) secondBit)
              (zxtDoubleLayers (prefixWires + 1)
                (zxpRowXor firstRest secondRest) secondRest))
          = zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length
                (zxpXorB firstBit secondBit))
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
                (zxtDoubleLayers (prefixWires + 1)
                  (zxpRowXor firstRest secondRest) secondRest))
        rw [hXorTailLen]
      -- the window arity bookkeeping
      have hWinCod : zxpDiagramCodArity
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxvCnotRiderLayers prefixWires (firstRest.length + 1))
              (zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)) }
          = prefixWires + (2 + (firstRest.length + 1)) := by
        show zxpLayersCodArity (prefixWires + (2 + (firstRest.length + 1)))
            (zxpCatLayers
              (zxvCnotRiderLayers prefixWires (firstRest.length + 1))
              (zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)))
          = prefixWires + (2 + (firstRest.length + 1))
        rw [zxpLayersCodArityCat, zxpLayersCodArityCat,
          zxtGadgetLayersCodArity secondBit prefixWires (firstRest.length + 1) _]
      -- step 1: the window fires over the double-comb tail
      have hWinLift := zxwLiftConv (prefixWires + (2 + (firstRest.length + 1)))
        [] (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)
        (zxvCnotWindowAt firstBit secondBit prefixWires firstRest.length)
        (ZxpLayersWF.nil _) rfl
        (by
          rw [hWinCod, zxnForkArityShuffle prefixWires firstRest.length]
          exact zxtDoubleLayersWF firstRest secondRest (prefixWires + 1) hTailLen)
      have hStepOne : ZxwConv
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxpCatLayers
                (zxvCnotRiderLayers prefixWires (firstRest.length + 1))
                (zxpCatLayers
                  (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
                  (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)))
              (zxtDoubleLayers (prefixWires + 1) firstRest secondRest) }
          { sourceArity := prefixWires + (2 + (firstRest.length + 1))
            layers := zxpCatLayers
              (zxpCatLayers
                (zxfGadgetLayers (prefixWires + 1) firstRest.length
                  (zxpXorB firstBit secondBit))
                (zxpCatLayers
                  (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
                  (zxvCnotRiderLayers (prefixWires + 1) firstRest.length)))
              (zxtDoubleLayers (prefixWires + 1) firstRest secondRest) } := hWinLift
      rw [zxnCatLayersAssoc
          (zxvCnotRiderLayers prefixWires (firstRest.length + 1))
          (zxpCatLayers
            (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
            (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length
            (zxpXorB firstBit secondBit))
          (zxpCatLayers
            (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
            (zxvCnotRiderLayers (prefixWires + 1) firstRest.length))
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest),
        zxnCatLayersAssoc
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxvCnotRiderLayers (prefixWires + 1) firstRest.length)
          (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)] at hStepOne
      -- step 2: the ride recurses one position deeper
      have hInner := zxvCnotRideDouble firstRest secondRest (prefixWires + 1)
        hTailLen
      have hIHLift := zxwLiftConv (prefixWires + (2 + (firstRest.length + 1)))
        (zxpCatLayers
          (zxfGadgetLayers (prefixWires + 1) firstRest.length
            (zxpXorB firstBit secondBit))
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit))
        [] hInner
        (by
          refine zxpLayersWFCat _ _ ?_ ?_
          · rw [zxnForkArityShuffle prefixWires firstRest.length]
            exact zxtGadgetLayersWF (zxpXorB firstBit secondBit) (prefixWires + 1)
              firstRest.length
          · rw [zxtGadgetLayersCodArity (zxpXorB firstBit secondBit)
              (prefixWires + 1) firstRest.length _,
              <- zxnForkArityShuffle prefixWires firstRest.length]
            exact zxtGadgetLayersWF secondBit prefixWires (firstRest.length + 1))
        (by
          rw [zxpLayersCodArityCat,
            zxtGadgetLayersCodArity (zxpXorB firstBit secondBit) (prefixWires + 1)
              firstRest.length _,
            zxtGadgetLayersCodArity secondBit prefixWires (firstRest.length + 1) _]
          exact zxnForkArityShuffle prefixWires firstRest.length)
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight,
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length
            (zxpXorB firstBit secondBit))
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxpCatLayers (zxvCnotRiderLayers (prefixWires + 1) firstRest.length)
            (zxtDoubleLayers (prefixWires + 1) firstRest secondRest)),
        zxnCatLayersAssoc
          (zxfGadgetLayers (prefixWires + 1) firstRest.length
            (zxpXorB firstBit secondBit))
          (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
          (zxtDoubleLayers (prefixWires + 1)
            (zxpRowXor firstRest secondRest) secondRest)] at hIHLift
      show ZxwConv
        { sourceArity := prefixWires + (2 + (firstRest.length + 1))
          layers := zxpCatLayers
            (zxvCnotRiderLayers prefixWires (firstRest.length + 1))
            (zxpCatLayers
              (zxfGadgetLayers (prefixWires + 1) firstRest.length firstBit)
              (zxpCatLayers
                (zxfGadgetLayers prefixWires (firstRest.length + 1) secondBit)
                (zxtDoubleLayers (prefixWires + 1) firstRest secondRest))) }
        { sourceArity := prefixWires + (2 + (firstRest.length + 1))
          layers := zxtDoubleLayers prefixWires
            (zxpRowXor (firstBit :: firstRest) (secondBit :: secondRest))
            (secondBit :: secondRest) }
      rw [hFinalEq]
      exact ZxwConv.trans hStepOne hIHLift

/-! ## Stage 5 — THE COMB TRANSVECTION

Mirror of `zxtCombSwapHolds`: zip the two solo combs, insert the birth CNOT
(`zxfCreatesCnotInsert` backwards), ride it down the zipped comb, unzip. -/

/-- THE COMB TRANSVECTION, WHOLE: the r10 residual `zxfCombXorAbsorbStatement`
is proven — xoring the second row into the first comb of an adjacent pair
preserves convertibility. -/
theorem zxvCombXorAbsorbHolds : zxfCombXorAbsorbStatement := by
  intro strandWidth firstRow secondRow hFirstLen hSecondLen
  subst hFirstLen
  have hXorLen : (zxpRowXor firstRow secondRow).length = firstRow.length :=
    zxpRowXorLength firstRow secondRow firstRow.length rfl hSecondLen
  -- the xored pair zips
  have hForward := zxtXorPairToDouble (zxpRowXor firstRow secondRow) secondRow
    (hSecondLen.trans hXorLen.symm)
  rw [hXorLen] at hForward
  -- the plain pair zips
  have hBackward := zxtXorPairToDouble firstRow secondRow hSecondLen
  -- the birth CNOT appears between the two creations
  have hInsertLift := zxwConvLift firstRow.length 0 firstRow.length []
    (zxtDoubleLayers 0 firstRow secondRow)
    (ZxwConv.symm zxfCreatesCnotInsert) (ZxpLayersWF.nil _)
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
          :: zxpWhiskerLayer 0 firstRow.length [ZxpCell.wire, ZxpCell.zSpider 1 2]
          :: zxpWhiskerLayer 0 firstRow.length [ZxpCell.xSpider 2 1, ZxpCell.wire]
          :: zxtDoubleLayers 0 firstRow secondRow } := hInsertLift
  rw [zxtWhiskerBumpOne 0 firstRow.length [ZxpCell.zSpider 0 1]] at hStepInsert
  -- the CNOT rides the zipped comb and dies at the boundary
  have hRide := zxvCnotRideDouble firstRow secondRow 0 hSecondLen
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
          :: zxpCatLayers (zxvCnotRiderLayers 0 firstRow.length)
            (zxtDoubleLayers 0 firstRow secondRow) }
      { sourceArity := firstRow.length
        layers := zxpWhiskerLayer 0 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxpWhiskerLayer 1 firstRow.length [ZxpCell.zSpider 0 1]
          :: zxtDoubleLayers 0 (zxpRowXor firstRow secondRow) secondRow } :=
    hRideLift
  exact ZxwConv.trans hForward (ZxwConv.trans (ZxwConv.symm hStepRide)
    (ZxwConv.trans (ZxwConv.symm hStepInsert) (ZxwConv.symm hBackward)))

/-- CONTENT MARKER: the comb transvection is machine-checked — the SECOND of
the two named comb moves of the transport assembly is DONE.  Supersedes the
r10 owner `zxfCombXorAbsorbIsProven := false` and the r11 owner
`zxtCombXorAbsorbIsProven := false`, both byte-intact in their home files. -/
def zxvCombXorAbsorbIsProven : Bool := true

/-! ## Stage 6 — THE GENERATOR TRANSPORT (the round's headline) -/

/-- THE GENERATOR TRANSPORT: span-equal generator lists give convertible
normal forms — the committed conditional assembly fires on the two now-proven
comb moves. -/
theorem zxvGeneratorTransportHolds : zxwGeneratorTransportStatement :=
  zxfTransportOfCombMoves zxtCombSwapHolds zxvCombXorAbsorbHolds

/-- CONTENT MARKER: the generator-list transport is machine-checked.
Supersedes the committed owners `zxwGeneratorTransportIsProven := false`
(WiringFlip), `zxfGeneratorTransportIsProven := false` (FinalFlip), and
`zxtGeneratorTransportIsProven := false` (TransportRides), all byte-intact
in their home files. -/
def zxvGeneratorTransportIsProven : Bool := true

/-! ## Stage 7 — fires -/

/-- Fire 1: the comb transvection at width two on literal rows —
`rowXor [true, false] [true, true] = [false, true]` absorbs. -/
theorem zxvCombXorAbsorbFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpCatLayers (zxnXorRowLayers [false, true])
          (zxnXorRowLayers [true, true]) }
      { sourceArity := 2
        layers := zxpCatLayers (zxnXorRowLayers [true, false])
          (zxnXorRowLayers [true, true]) } :=
  zxvCombXorAbsorbHolds 2 [true, false] [true, true] rfl rfl

/-- Kernel span pin for fire 1. -/
theorem zxvCombXorAbsorbFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpCatLayers (zxnXorRowLayers [false, true])
            (zxnXorRowLayers [true, true]) })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpCatLayers (zxnXorRowLayers [true, false])
            (zxnXorRowLayers [true, true]) }) = true := rfl

/-- Fire 2: a whole two-row normal form converts to the row-xored normal form
(the transvection lifted between the shared init and kill layers). -/
theorem zxvNormalFormXorFire :
    ZxwConv
      (zxnNormalForm 1 1 [[false, true], [true, true]])
      (zxnNormalForm 1 1 [[true, false], [true, true]]) := by
  have hAbsorb := zxvCombXorAbsorbHolds 2 [true, false] [true, true] rfl rfl
  have hLift := zxwLiftConv 1 [zxnInitLayer 1 1] [zxnKillLayer 1 1] hAbsorb
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  exact hLift

/-- Kernel span pin for fire 2. -/
theorem zxvNormalFormXorFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm 1 1 [[false, true], [true, true]]))
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, false], [true, true]]))
      = true := rfl

/-- Fire 3 (THE TRANSPORT FIRE): two span-equal two-generator lists that are
neither equal nor a permutation — `{[true, false], [true, true]}` and
`{[false, true], [true, true]}` — give convertible normal forms through the
headline assembly. -/
theorem zxvGeneratorTransportFire :
    ZxwConv
      (zxnNormalForm 1 1 [[true, false], [true, true]])
      (zxnNormalForm 1 1 [[false, true], [true, true]]) :=
  zxvGeneratorTransportHolds 1 1 [[true, false], [true, true]]
    [[false, true], [true, true]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))
    rfl

/-- Kernel span pin for fire 3 (the span decision itself, decided by the
kernel). -/
theorem zxvGeneratorTransportFireSpanPin :
    zxpSpanEqB [[true, false], [true, true]] [[false, true], [true, true]]
      = true := rfl

end FX1Poly.Polygraph.Omega.ZXPhaseFree
