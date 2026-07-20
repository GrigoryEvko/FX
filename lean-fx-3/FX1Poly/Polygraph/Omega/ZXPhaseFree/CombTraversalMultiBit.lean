import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombTraversal

/-! # Polygraph/Omega/ZXPhaseFree/CombTraversalMultiBit — THE TWO-BIT COMB
TRAVERSAL: a created state fed into the smallest genuinely-feeding two-bit comb
is fully traversed and absorbed to the two correlated free bits

The prior round (`CombTraversal`, the `zxu*` atoms) landed the routing engine
(`zxuStateWalk`, general in the gap width), the feeding-column cells and the
feeding-column collapse (`zxuFeedColumnCollapse`), and ONE full comb traversal
(`zxuCombTraversalOneBit`, the `[true]` comb), then walled the general `rowBits`
fold with the exact burn: the `[true, true]` comb (the 8-layer staircase) needs
the carrier to WALK between the two set-bit columns, the feeding column collapse
firing at a MOVING position with the whiskered arity growing with the bit index.

This round BUILDS that assembly for the smallest genuinely-feeding two-bit case:

* THE TWO-BIT TRAVERSAL (`zxmCombTraversalTwoBit`, PROVED): two created X states
  fed into `zxnXorRowLayers [true, true]` traverse the whole 8-layer machine and
  collapse to the Z-copy state `[[zSpider 0 1], [zSpider 1 2]]` — the two
  correlated free bits.  Assembled EXACTLY per the r18 burn as an explicit
  twelve-move `ZxwConv` chain: reorder the carrier above the fed states
  (`zxsWhiskerCellPastInit`), split the fed-state init layer (the interchange
  `zxeExchangeConv`), feed-collapse at the FIRST set bit
  (`zxuFeedColumnCollapse` whiskered by the spectator second fed state), route
  that fed state's creation BETWEEN the two set-bit columns past the fork/cross/
  fork (three `zxsWhiskerCellPastInit` commutations — the walk the burn named),
  absorb at the SECOND set bit (`zxuStateMergeAbsorbsRight` whiskered), then the
  carrier cleanup (strip, discard-past-cross, counit, strip, cocommutativity).

* THE FUSED CODOMAIN (`zxmCombTraversalTwoBitFused`, PROVED): the same traversal
  landed against the single fused Z spider `[[zSpider 0 2]]` (the parallel-fusion
  tail), the canonical two-output copy state.

The general `rowBits` fold stays walled with the precise successor burn: the
per-bit routing count grows with the inter-set-bit gap and the number of
set bits, and the whiskered feed-collapse fires at a strand index that moves per
set bit — the moving-position fold is a distinct induction, not assembled here.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Committed owner-false flags stay byte-intact; the fresh markers are
this file's `zxm*`.

(Prefix note: the natural `zxv` prefix is already taken by `TransvectionRide`, so
this file uses the fresh globally-unused `zxm` prefix.) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the explicit-form pin: the two-bit comb IS the 8-layer staircase

`zxnXorRowLayers [true, true]` unfolds (definitionally) to the exact 8-layer
staircase the r18 burn named: create the Z carrier, fork/merge/cross at bit 0,
fork/merge/cross at bit 1, discard.  This pin lets the traversal chain state its
source diagram in explicit layer form. -/

/-- THE TWO-BIT COMB, EXPLICIT: `zxnXorRowLayers [true, true]` is the 8-layer
carrier staircase (create carrier; per-bit fork/merge/cross; discard). -/
theorem zxmTwoBitCombLayers :
    zxnXorRowLayers [true, true] =
      [[ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
       [ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] := rfl

/-! ## Stage 1 — THE TWO-BIT TRAVERSAL (T1, the round's victory condition) -/

/-- THE TWO-BIT COMB TRAVERSAL: two created X states fed into the smallest
genuinely-feeding two-bit comb `zxnXorRowLayers [true, true]` traverse the whole
8-layer machine and collapse to the two correlated free bits (the Z-copy state
`[[zSpider 0 1], [zSpider 1 2]]`).  This is the round's victory condition:
the created states feed-collapse at the FIRST set bit, the relevant carrier copy
routes (`zxuStateWalk 1`, three crossing commutations) BETWEEN the two set-bit
columns, the second created state absorbs at the SECOND set bit, and the carrier
is born, forked, and discarded.  Twelve explicit `ZxwConv` moves. -/
theorem zxmCombTraversalTwoBit :
    ZxwConv
      { sourceArity := 0
        layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true, true] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] } := by
  show ZxwConv
    { sourceArity := 0
      layers :=
        [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
         [ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire],
         [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
         [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
         [ZxpCell.crossing, ZxpCell.wire],
         [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
         [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
         [ZxpCell.wire, ZxpCell.crossing],
         [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
    { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] }
  -- STEP 1: reorder the carrier creation above the two fed states.
  have hStep1 : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
           [ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
           [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
            [ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire]] }
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 1],
            [ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] } :=
      ZxwConv.symm (zxsWhiskerCellPastInit (ZxpCell.zSpider 0 1) 0 0 2)
    have hLift := zxwLiftConv 0 []
      [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
       [ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 2: split the fed-state init layer (I1 first, then I0).
  have hStep2 : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
           [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
           [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 1
          layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] }
        { sourceArity := 1
          layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1],
            [ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire]] } :=
      ZxwConv.symm (zxwOfZxeConv
        (zxeExchangeConv [ZxpCell.wire, ZxpCell.xSpider 0 1] [ZxpCell.xSpider 0 1]))
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]]
      [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
       [ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 3: feed-collapse at the FIRST set bit (I1 the right spectator).
  have hStep3 : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1, ZxpCell.wire],
           [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hLift := zxwConvLift 0 0 1
      [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1]]
      [[ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      zxuFeedColumnCollapse (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells] at hLift
    exact hLift
  -- STEP 4a: route the second fed state's creation past the fork.
  have hStep4a : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 1
          layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2, ZxpCell.wire]] }
        { sourceArity := 1
          layers := [[ZxpCell.zSpider 1 2],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1]] } :=
      ZxwConv.symm (zxsWhiskerCellPastInit (ZxpCell.zSpider 1 2) 0 0 1)
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]]
      [[ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 4b: route the second fed state's creation past the crossing.
  have hStep4b : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
            [ZxpCell.crossing, ZxpCell.wire]] }
        { sourceArity := 2
          layers := [[ZxpCell.crossing],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1]] } :=
      ZxwConv.symm (zxsWhiskerCellPastInit ZxpCell.crossing 0 0 1)
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]]
      [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 4c: route the second fed state's creation past the second fork (fork1).
  have hStep4c : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
            [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]] }
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1]] } :=
      ZxwConv.symm (zxsWhiskerCellPastInit (ZxpCell.zSpider 1 2) 1 0 1)
    have hLift := zxwLiftConv 0
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing]]
      [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 5: absorb the second fed state at the SECOND set bit (merge1).
  have hStep5 : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hLift := zxwConvLift 0 2 0
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.zSpider 1 2]]
      [[ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      zxuStateMergeAbsorbsRight (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells] at hLift
    exact hLift
  -- STEP 6a: strip the trailing wire layer left by the merge absorb.
  have hStep6a : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]] }
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2]] } :=
      zxwOfZxeConv (zxeStripTrailingWireLayer [ZxpCell.wire, ZxpCell.zSpider 1 2])
    have hLift := zxwLiftConv 0
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing]]
      [[ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 6b: slide the discard back across the last crossing (counit naturality).
  have hStep6b : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.zSpider 1 0, ZxpCell.wire]] } := by
    have hMove : ZxwConv
        { sourceArity := 2
          layers := [[ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
        { sourceArity := 2, layers := [[ZxpCell.zSpider 1 0, ZxpCell.wire]] } :=
      ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 0))
    have hLift := zxwConvLift 0 1 0
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.zSpider 1 2]]
      []
      hMove (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells, zxpCatLayersNilRight] at hLift
    exact hLift
  -- STEP 6c: the copy-counit fires (fork then discard = identity).
  have hStep6c : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.zSpider 1 2],
           [ZxpCell.wire, ZxpCell.zSpider 1 0, ZxpCell.wire]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire]] } := by
    have hMove : ZxwConv
        { sourceArity := 1
          layers := [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 1 0, ZxpCell.wire]] }
        { sourceArity := 1, layers := [[ZxpCell.wire]] } :=
      zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCounit)
    have hLift := zxwConvLift 0 1 0
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing]]
      []
      hMove (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells, zxpCatLayersNilRight] at hLift
    exact hLift
  -- STEP 6d: strip the trailing wire layer against the crossing.
  have hStep6d : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing]] } := by
    have hMove : ZxwConv
        { sourceArity := 2
          layers := [[ZxpCell.crossing], [ZxpCell.wire, ZxpCell.wire]] }
        { sourceArity := 2, layers := [[ZxpCell.crossing]] } :=
      zxwOfZxeConv (zxeStripTrailingWireLayer [ZxpCell.crossing])
    have hLift := zxwLiftConv 0
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]]
      []
      hMove (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 6e: fork then cross = fork (Z-copy cocommutativity).
  have hStep6e : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.zSpider 0 1],
           [ZxpCell.zSpider 1 2],
           [ZxpCell.crossing]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] } := by
    have hMove : ZxwConv
        { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2], [ZxpCell.crossing]] }
        { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2]] } :=
      zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCocomm)
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]] []
      hMove (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
    simp only [zxpCatLayers] at hLift
    exact hLift
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2 (ZxwConv.trans hStep3
    (ZxwConv.trans hStep4a (ZxwConv.trans hStep4b (ZxwConv.trans hStep4c
      (ZxwConv.trans hStep5 (ZxwConv.trans hStep6a (ZxwConv.trans hStep6b
        (ZxwConv.trans hStep6c (ZxwConv.trans hStep6d hStep6e))))))))))

/-- THE FUSED CODOMAIN: the two-bit traversal landed against the single fused Z
spider `[[zSpider 0 2]]` — the canonical two-output copy state (the two correlated
free bits as one 0-to-2 Z spider), reached by the parallel-fusion tail. -/
theorem zxmCombTraversalTwoBitFused :
    ZxwConv
      { sourceArity := 0
        layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true, true] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 2]] } :=
  ZxwConv.trans zxmCombTraversalTwoBit (zxwParallelFusionZ 0 2 0)

/-! ## Stage 2 — fires and kernel span pins -/

/-- FIRE: the two-bit traversal as an explicit chain (the round's victory cell). -/
theorem zxmCombTraversalTwoBitFire :
    ZxwConv
      { sourceArity := 0
        layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true, true] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] } :=
  zxmCombTraversalTwoBit

/-- Kernel span pin: the two-bit traversal is a semantic equivalence — the two
created states are genuinely absorbed to the two correlated free bits. -/
theorem zxmCombTraversalTwoBitSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true, true] })
      (zxpDiagramDenote
        { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] }) = true :=
  rfl

/-- Kernel span pin: the fused-codomain traversal is a semantic equivalence. -/
theorem zxmCombTraversalTwoBitFusedSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true, true] })
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 2]] }) = true :=
  rfl

/-- Kernel span pin (endpoint reconciliation): the copy state `[[Z01],[Z12]]` and
the fused spider `[[Z02]]` denote the same two-correlated-bit span. -/
theorem zxmCopyStateFusedSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] })
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 2]] }) = true :=
  rfl

/-! ## Stage 3 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): THE TWO-BIT COMB TRAVERSAL is LANDED
(`zxmCombTraversalTwoBit`) — two created X states fed into the smallest
genuinely-feeding two-bit comb `zxnXorRowLayers [true, true]` traverse the whole
8-layer machine and collapse to the two correlated free bits, as an explicit
twelve-move `ZxwConv` chain (reorder ; split ; feed-collapse at bit 0 ; route the
second fed state between the two set-bit columns past fork/cross/fork ; absorb at
bit 1 ; carrier cleanup), with kernel span pins.  This closes the r18 burn's named
successor: the `[true, true]` staircase needing the walk BETWEEN the two set-bit
columns is assembled, feed-collapse firing at the moving position. -/
def zxmHasTwoBitTraversal : Bool := true

/-- CONTENT MARKER (TRUE): the fused-codomain form is LANDED
(`zxmCombTraversalTwoBitFused`) — the same traversal against the single Z spider
`[[zSpider 0 2]]`, the canonical two-output copy state, via the parallel-fusion
tail, with a kernel span pin. -/
def zxmHasFusedCodomain : Bool := true

/-- OWNER MARKER (FALSE): the GENERAL `rowBits` comb traversal did NOT land — a
created-state block fed into an arbitrary comb `zxnXorRowLayers rowBits` (a state
per row bit) is not built for general `rowBits`.  The committed owner-false flags
`zxuHasGeneralIdentityAbsorb`, `zxiHasFeedingCombRouter`, `zxjHasIdentityAbsorb`,
`zxkIdentityAbsorbIsProven` stay byte-intact false.

Two genuinely different attacks burned, both converging on the SAME missing
moving-position fold:

* (A) THE MOVING-POSITION FEED-COLLAPSE FOLD.  The `[true, true]` traversal
  succeeds because the inter-set-bit gap is EXACTLY ONE: the second fed state's
  creation routes past exactly THREE cells (fork, cross, fork1) — the three
  `zxsWhiskerCellPastInit` commutations `hStep4a/4b/4c`, i.e. `zxuStateWalk 1`.
  A general comb `zxnXorRowLayers rowBits` with set bits at positions `j0 < j1 <
  ...` needs each fed state to route past the intervening cells to reach its
  merge, and the route length GROWS with the gap (each intervening `false` bit
  adds a crossing per `zxnCombLayers`'s `false` arm, each intervening `true` bit
  adds a fork/merge/cross triple); worse, the whiskered feed-collapse at set bit
  `j_k` fires at strand index `k` (the count of already-processed set bits), a
  MOVING position, so its left-whisker width grows per set bit.  The per-position
  collapse (`zxuFeedColumnCollapse`) and the per-cell route
  (`zxsWhiskerCellPastInit`) are both present; the fold that threads them over
  `rowBits` with a per-set-bit-incrementing left-pad and a per-gap-growing route
  is a distinct structural induction, not assembled here.

* (B) THE INIT-SPLIT CASCADE.  The `[true, true]` proof splits the two-state
  init `[w, X01, X01]` into two single-state creations with ONE interchange
  (`hStep2`), then routes ONE of them.  A general `rowBits` with `setCount` set
  bits needs the `setCount`-state init block split into `setCount` single
  creations, each routed independently to its merge past a DIFFERENT run of
  cells, and the splits interleave with the routes (a fed state created earlier
  must ride past the routes of the later ones) — the split/route interleaving is
  the same moving-position bookkeeping as (A), not a separate closable piece.
  Both attacks reduce to the identical unbuilt fold; per the stall policy this
  round ships the smallest genuinely-feeding instance and names the successor. -/
def zxmHasGeneralCombTraversal : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
