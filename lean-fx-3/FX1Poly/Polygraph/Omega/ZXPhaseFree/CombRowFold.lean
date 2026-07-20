import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombTraversalMultiBit

/-! # Polygraph/Omega/ZXPhaseFree/CombRowFold — THE MOVING-POSITION SINGLE-ROW
COMB TRAVERSAL: created states fed into an arbitrary single-row comb collapse to
the free-bit span state, built past the r19 all-set-bit wall

The prior round (`CombTraversalMultiBit`, the `zxm*` atoms) landed the smallest
genuinely-feeding case — two created X states fed into `zxnXorRowLayers
[true, true]` (all set bits, the 8-layer staircase) collapse to the two
correlated free bits `[[zSpider 0 1], [zSpider 1 2]]` — and walled the general
`rowBits` fold on the precise successor: the feed-collapse fires at a MOVING
strand index, and intervening UNSET bits (the `zxnCombLayers` `false` arm the
all-true r19 case never exercises) route the carrier past a fed state that
SURVIVES to the output.

This round pushes the wall on both axes with the smallest FRESH gaps:

* THE UNSET-BIT TRAVERSAL (`zxqCombTraversalFalseTrue`, PROVED): two created X
  states fed into `zxnXorRowLayers [false, true]` — a comb whose FIRST bit is
  unset — traverse the 6-layer machine and collapse to the two-layer normal form
  `[[xSpider 0 1], [wire, zSpider 0 1]]`: strand 0 keeps its fed `|0>` (the
  surviving fed state the all-true case never produced), strand 1 carries the
  single free bit.  The new content over r19 is the `false`-arm crossing: the
  carrier SLIDES past the first fed state WITHOUT forking (`zxwSlideRightConv` on
  the carrier), which deposits that `|0>` as a final output and reduces the rest
  to the r19-committed `[true]` traversal (`zxuCombTraversalOneBit`) whiskered by
  the deposited `|0>`.  The output is `zxpSpanEqB` to the fused one-layer form
  `[[xSpider 0 1, zSpider 0 1]]`.

* THE SPAN FIRES (`zxq*SpanPin`): `zxpSpanEqB` kernel pins for all four single-row
  targets — the regression pair `[true]` / `[true, true]` and the fresh pair
  `[false, true]` / `[true, false, true]` — each equating the created-state feed
  to the free-bit span state on the nose.

* THE GENERAL FOLD stays walled (`zxqHasGeneralCombFold := false`) with the two
  genuinely different burned attacks recorded precisely on the marker.  The
  committed owner-false flags stay byte-intact.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Fresh markers are this file's `zxq*`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the fold source and the explicit-form pins

The traversal source feeds one created `|0>` state (`xSpider 0 1`) into every
domain strand of the comb, so `zxnZeroStateCells rowBits.length` caps the whole
domain and the composite is a state (`sourceArity 0`).  `zxnZeroStateCells k` is
literally `k` copies of `xSpider 0 1`. -/

/-- THE FOLD SOURCE: feed one created `|0>` state into every domain strand, then
run the single-row comb `zxnXorRowLayers rowBits`. -/
def zxqFoldSource (rowBits : List Bool) : ZxpDiagram :=
  { sourceArity := 0, layers := zxnZeroStateCells rowBits.length :: zxnXorRowLayers rowBits }

/-- Pin: the `[true, true]` fold source is exactly the r19 traversal source (two
created X states above the all-set-bit comb). -/
theorem zxqFoldSourceTwoBitPin :
    zxqFoldSource [true, true]
      = { sourceArity := 0
          layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]
            :: zxnXorRowLayers [true, true] } := rfl

/-- Pin: the `[false, true]` comb is the 6-layer machine — create carrier; the
`false`-arm crossing walks it past the unset strand; the `true`-arm fork/merge/
cross feeds the set strand; discard. -/
theorem zxqFalseTrueCombLayers :
    zxnXorRowLayers [false, true] =
      [[ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] := rfl

/-- Pin: the `[true, false, true]` comb is the 9-layer machine — set at position
0, unset at position 1, set at position 2. -/
theorem zxqTrueFalseTrueCombLayers :
    zxnXorRowLayers [true, false, true] =
      [[ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] := rfl

/-! ## Stage 1 — THE SPAN FIRES: each single-row feed IS its free-bit span state -/

/-- FIRE (regression): the `[true]` feed collapses to the single free bit
`[[zSpider 0 1]]` — semantic span pin. -/
theorem zxqFoldSpanPinOneBit :
    zxpSpanEqB
      (zxpDiagramDenote (zxqFoldSource [true]))
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] }) = true :=
  rfl

/-- FIRE (regression): the `[true, true]` feed collapses to the two correlated
free bits `[[zSpider 0 1], [zSpider 1 2]]` — semantic span pin. -/
theorem zxqFoldSpanPinTwoBit :
    zxpSpanEqB
      (zxpDiagramDenote (zxqFoldSource [true, true]))
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] }) = true :=
  rfl

/-- FIRE (fresh): the `[false, true]` feed collapses to `[[xSpider 0 1,
zSpider 0 1]]` — the unset strand keeps its `|0>`, the set strand carries the
free bit.  A genuine gap over r19: the surviving fed state. -/
theorem zxqFoldSpanPinFalseTrue :
    zxpSpanEqB
      (zxpDiagramDenote (zxqFoldSource [false, true]))
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1, ZxpCell.zSpider 0 1]] }) = true :=
  rfl

/-- FIRE (fresh): the `[true, false, true]` feed collapses to `[[zSpider 0 1,
xSpider 0 1], [zSpider 1 2, wire], [wire, crossing]]` — the free bit copied to
strands 0 and 2 with a `|0>` on strand 1.  A genuine gap: moving-position
feed-collapse AND intervening unset crossing. -/
theorem zxqFoldSpanPinTrueFalseTrue :
    zxpSpanEqB
      (zxpDiagramDenote (zxqFoldSource [true, false, true]))
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 1, ZxpCell.xSpider 0 1],
            [ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.crossing]] }) = true :=
  rfl

/-! ## Stage 2 — regression re-exposure of the committed single-row traversals -/

/-- REGRESSION: the `[true]` traversal (the committed `zxuCombTraversalOneBit`)
restated against the fold source — a created state fed into the smallest feeding
comb collapses to the free bit. -/
theorem zxqCombTraversalOneBit :
    ZxwConv (zxqFoldSource [true])
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] } :=
  zxuCombTraversalOneBit

/-- REGRESSION: the `[true, true]` traversal (the committed r19
`zxmCombTraversalTwoBit`) restated against the fold source — the all-set-bit
8-layer machine collapses to the two correlated free bits. -/
theorem zxqCombTraversalTwoBit :
    ZxwConv (zxqFoldSource [true, true])
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] } :=
  zxmCombTraversalTwoBit

/-! ## Stage 3 — THE UNSET-BIT TRAVERSAL: the `false`-arm crossing and the
surviving fed state (the fresh gap over the all-true r19 case) -/

/-- THE UNSET-BIT TRAVERSAL: two created X states fed into `zxnXorRowLayers
[false, true]` — a comb whose first bit is unset — traverse the 6-layer machine
and collapse to the two-layer normal form `[[xSpider 0 1], [wire, zSpider 0 1]]`.
The carrier is created at strand 0 and SLIDES past the first fed state's crossing
(`zxwSlideRightConv`) WITHOUT forking, depositing that `|0>` as the final output
on strand 0; the residual is then the committed `[true]` traversal
(`zxuCombTraversalOneBit`) whiskered by the deposited `|0>`, so strand 1 carries
the single free bit.  This is the genuine successor content to the r19 all-true
wall: the `zxnCombLayers` `false` arm and a fed state that SURVIVES to the
output, neither of which the all-set-bit case exercises.  The output is
`zxpSpanEqB` to the fused one-layer state `[[xSpider 0 1, zSpider 0 1]]`
(`zxqFalseTrueOutputFusedSpanPin`). -/
theorem zxqCombTraversalFalseTrue :
    ZxwConv
      { sourceArity := 0
        layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [false, true] }
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] } := by
  show ZxwConv
    { sourceArity := 0
      layers :=
        [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
         [ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire],
         [ZxpCell.crossing, ZxpCell.wire],
         [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
         [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
         [ZxpCell.wire, ZxpCell.crossing],
         [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
    { sourceArity := 0
      layers := [[ZxpCell.xSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] }
  -- STEP 1: slide the carrier past the unset-bit crossing (carrier walks to strand 1).
  have hStep1 : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
           [ZxpCell.zSpider 0 1, ZxpCell.wire, ZxpCell.wire],
           [ZxpCell.crossing, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hLift := zxwConvLift 0 0 1 [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]]
      [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      (zxwSlideRightConv (ZxpCell.zSpider 0 1)) (zxpLayersWFOfB _ _ rfl) rfl
      (zxpLayersWFOfB _ _ rfl)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells, zxwSlideRightLhs, zxwSlideRightRhs,
      zxwStairFromRightLayers, zxpCellDomArity] at hLift
    exact hLift
  -- STEP 2a: split the two fed states (right-first exchange).
  have hStep2a : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1],
           [ZxpCell.xSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] }
        { sourceArity := 0,
          layers := [[ZxpCell.xSpider 0 1], [ZxpCell.xSpider 0 1, ZxpCell.wire]] } :=
      ZxwConv.symm (zxwOfZxeConv (zxeExchangeConv [ZxpCell.xSpider 0 1] [ZxpCell.xSpider 0 1]))
    have hLift := zxwLiftConv 0 []
      [[ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 2b: reposition the second fed state to strand 1 (past-init reorder).
  have hStep2b : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1],
           [ZxpCell.xSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hMove : ZxwConv
        { sourceArity := 0,
          layers := [[ZxpCell.xSpider 0 1], [ZxpCell.xSpider 0 1, ZxpCell.wire]] }
        { sourceArity := 0,
          layers := [[ZxpCell.xSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1]] } :=
      ZxwConv.symm (zxsWhiskerCellPastInit (ZxpCell.xSpider 0 1) 0 0 1)
    have hLift := zxwLiftConv 0 []
      [[ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
       [ZxpCell.wire, ZxpCell.crossing],
       [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]]
      hMove (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- STEP 3: the residual is the committed `[true]` traversal whiskered by the
  -- deposited `|0>` on strand 0.
  have hStep3 : ZxwConv
      { sourceArity := 0
        layers :=
          [[ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.xSpider 0 1],
           [ZxpCell.wire, ZxpCell.zSpider 0 1, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
           [ZxpCell.wire, ZxpCell.crossing],
           [ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] } := by
    have hLift := zxwConvLift 0 1 0 [[ZxpCell.xSpider 0 1]] []
      zxuCombTraversalOneBit (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells, zxnXorRowLayers, zxnCombLayers,
      zxpCatLayersNilRight] at hLift
    exact hLift
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2a (ZxwConv.trans hStep2b hStep3))

/-- FIRE: the unset-bit traversal as an explicit chain (the fresh victory cell). -/
theorem zxqCombTraversalFalseTrueFire :
    ZxwConv
      { sourceArity := 0
        layers := [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1] :: zxnXorRowLayers [false, true] }
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] } :=
  zxqCombTraversalFalseTrue

/-- Kernel span pin: the unset-bit traversal's two-layer output is `zxpSpanEqB` to
the fused one-layer state `[[xSpider 0 1, zSpider 0 1]]` — the `|0>`-then-free
normal form denotes the same span as the fused `(|0>, free)` state. -/
theorem zxqFalseTrueOutputFusedSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] })
      (zxpDiagramDenote
        { sourceArity := 0, layers := [[ZxpCell.xSpider 0 1, ZxpCell.zSpider 0 1]] }) = true :=
  rfl

/-! ## Stage 3b — THE PREFIX-SHIFT IDENTITY: the structural fact underneath the
`false`-arm reduction (the proven half of the general fold's attack A) -/

/-- THE COMB PREFIX-SHIFT IDENTITY: incrementing the processed-prefix width of a
comb is exactly whiskering it by one wire on the left — `zxnCombLayers
(prefixWires + 1) rowBits = zxpWhiskerLayers 1 0 (zxnCombLayers prefixWires
rowBits)`.  Structural induction on `rowBits` mirroring its three-way match, with
the head layers reconciled by `zxnWhiskerLayerCompose` and `Nat.add_comm`.  This
is the identity that lets a leading unset bit reduce to a WHISKERED smaller comb —
the proven backbone of the general fold's `false` arm; the `true` arm's correlated
Z-copy prefix is what stays unbuilt (see `zxqHasGeneralCombFold`). -/
theorem zxqCombPrefixShift : (rowBits : List Bool) -> (prefixWires : Nat) ->
    zxnCombLayers (prefixWires + 1) rowBits
      = zxpWhiskerLayers 1 0 (zxnCombLayers prefixWires rowBits)
  | [], prefixWires => by
      show [zxpWhiskerLayer (prefixWires + 1) 0 [ZxpCell.zSpider 1 0]]
        = [zxpWhiskerLayer 1 0 (zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0])]
      rw [zxnWhiskerLayerCompose 1 0 prefixWires 0 [ZxpCell.zSpider 1 0],
        Nat.add_comm 1 prefixWires]
  | false :: rest, prefixWires => by
      show zxpWhiskerLayer (prefixWires + 1) rest.length [ZxpCell.crossing]
          :: zxnCombLayers (prefixWires + 1 + 1) rest
        = zxpWhiskerLayer 1 0 (zxpWhiskerLayer prefixWires rest.length [ZxpCell.crossing])
          :: zxpWhiskerLayers 1 0 (zxnCombLayers (prefixWires + 1) rest)
      rw [zxnWhiskerLayerCompose 1 0 prefixWires rest.length [ZxpCell.crossing],
        Nat.add_comm 1 prefixWires, zxqCombPrefixShift rest (prefixWires + 1)]
      rfl
  | true :: rest, prefixWires => by
      show zxpWhiskerLayer (prefixWires + 1) (rest.length + 1) [ZxpCell.zSpider 1 2]
          :: zxpWhiskerLayer (prefixWires + 1 + 1) rest.length [ZxpCell.xSpider 2 1]
          :: zxpWhiskerLayer (prefixWires + 1) rest.length [ZxpCell.crossing]
          :: zxnCombLayers (prefixWires + 1 + 1) rest
        = zxpWhiskerLayer 1 0 (zxpWhiskerLayer prefixWires (rest.length + 1) [ZxpCell.zSpider 1 2])
          :: zxpWhiskerLayer 1 0 (zxpWhiskerLayer (prefixWires + 1) rest.length [ZxpCell.xSpider 2 1])
          :: zxpWhiskerLayer 1 0 (zxpWhiskerLayer prefixWires rest.length [ZxpCell.crossing])
          :: zxpWhiskerLayers 1 0 (zxnCombLayers (prefixWires + 1) rest)
      rw [zxnWhiskerLayerCompose 1 0 prefixWires (rest.length + 1) [ZxpCell.zSpider 1 2],
        zxnWhiskerLayerCompose 1 0 (prefixWires + 1) rest.length [ZxpCell.xSpider 2 1],
        zxnWhiskerLayerCompose 1 0 prefixWires rest.length [ZxpCell.crossing],
        Nat.add_comm 1 prefixWires, Nat.add_comm 1 (prefixWires + 1),
        zxqCombPrefixShift rest (prefixWires + 1)]
      rfl

/-- COROLLARY: a comb with a LEADING UNSET bit is the carrier-create layer, then
the `false`-arm crossing, then the whole TAIL comb whiskered by one wire on the
left — `zxnXorRowLayers (false :: rest)` unfolds through `zxqCombPrefixShift` to
expose `zxpWhiskerLayers 1 0 (zxnCombLayers 0 rest)`.  This is the exact structure
the `[false, true]` traversal consumes: slide the carrier past the crossing, then
recurse on the whiskered tail. -/
theorem zxqFalseLeadCombStructure (rest : List Bool) :
    zxnXorRowLayers (false :: rest) =
      zxpWhiskerLayer 0 (rest.length + 1) [ZxpCell.zSpider 0 1]
        :: zxpWhiskerLayer 0 rest.length [ZxpCell.crossing]
        :: zxpWhiskerLayers 1 0 (zxnCombLayers 0 rest) := by
  show zxpWhiskerLayer 0 (rest.length + 1) [ZxpCell.zSpider 0 1]
      :: zxpWhiskerLayer 0 rest.length [ZxpCell.crossing]
      :: zxnCombLayers 1 rest
    = zxpWhiskerLayer 0 (rest.length + 1) [ZxpCell.zSpider 0 1]
      :: zxpWhiskerLayer 0 rest.length [ZxpCell.crossing]
      :: zxpWhiskerLayers 1 0 (zxnCombLayers 0 rest)
  rw [zxqCombPrefixShift rest 0]

/-! ## Stage 4 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the fresh unset-bit single-row traversal is LANDED
(`zxqCombTraversalFalseTrue`) — two created X states fed into
`zxnXorRowLayers [false, true]` collapse to the two-layer free-bit span state, the
carrier sliding past the `false`-arm crossing and depositing the surviving fed
`|0>`.  This is the genuine successor content to the r19 all-true wall: the
`zxnCombLayers` `false` arm and a fed state that survives to the output, neither
exercised by `[true, true]`.  The reduction to the committed `[true]` traversal
whiskered by the deposited `|0>` is the modular shape a general `false`-arm fold
would iterate. -/
def zxqHasUnsetBitTraversal : Bool := true

/-- CONTENT MARKER (TRUE): the four single-row span fires are LIVE
(`zxqFoldSpanPin*`) — the regression pair `[true]` / `[true, true]` and the fresh
pair `[false, true]` / `[true, false, true]`, each `zxpSpanEqB`-pinning the
created-state feed to its free-bit span state on the nose, plus the fused-output
pin `zxqFalseTrueOutputFusedSpanPin`. -/
def zxqHasSingleRowSpanFires : Bool := true

/-- CONTENT MARKER (TRUE): the comb prefix-shift identity is LANDED
(`zxqCombPrefixShift`, general in `rowBits` and `prefixWires`) with its
leading-unset corollary (`zxqFalseLeadCombStructure`).  This is the proven
backbone of the general fold's `false` arm — incrementing a comb's processed
prefix is exactly a one-wire left-whisker, so a leading unset bit reduces to a
whiskered SMALLER comb.  It narrows the general-fold wall precisely to the `true`
arm's correlated Z-copy prefix. -/
def zxqHasPrefixShiftIdentity : Bool := true

/-- OWNER MARKER (FALSE): the GENERAL single-row fold did NOT land — a created
`|0>` block fed into an arbitrary comb `zxnXorRowLayers rowBits` is not converted
to its free-bit span state for general `rowBits`.  The committed owner-false flags
`zxuHasGeneralIdentityAbsorb`, `zxmHasGeneralCombTraversal`,
`zxiHasFeedingCombRouter`, `zxjHasIdentityAbsorb`, `zxkIdentityAbsorbIsProven`
stay byte-intact false.

Two genuinely different attacks burned, both stalling on the shared-carrier
correlation across set bits:

* (A) THE PREFIX-SHIFT INDUCTION.  The `[false, true]` traversal closes cleanly
  because the `false` arm reduces to a WHISKERED SMALLER traversal: slide the
  carrier past the crossing (`zxwSlideRightConv`), deposit the surviving `|0>`,
  and the residual is exactly `zxuCombTraversalOneBit` whiskered by that `|0>`.
  The structural identity that powers this — `zxnCombLayers (prefixWires + 1) rest
  = zxpWhiskerLayers 1 0 (zxnCombLayers prefixWires rest)` — IS PROVEN here
  (`zxqCombPrefixShift`, general; corollary `zxqFalseLeadCombStructure`), so the
  general `false` arm is backed.  BURN: the `true` arm does NOT reduce to a plain
  whiskered fold — when the carrier forks at a set bit, one copy becomes the
  strand-0 output and the OTHER continues to every later set bit, so the output
  bits at all set positions are the SAME carrier value (correlated).  The residual
  is `zxqFoldSource rest` whiskered by a strand-0 output that is Z-COPY-SHARED with
  the carrier inside the recursion — not a spectator `|0>` — so the whiskered-IH
  shape the `false` arm uses does not transport the `true` arm; the target is a
  copy-CHAIN (`[[Z01],[Z12],...]`), not a whiskered smaller state.  The wall is now
  precisely the `true`-arm correlated Z-copy prefix, not the `false` arm.

* (B) THE FEED-COLLAPSE-FIRST ASSEMBLY (r19 shape).  Mirroring r19's explicit
  chain generically: split the `setCount`-state init into per-set-bit creations,
  feed-collapse at each set bit, route each surviving state to its column.  BURN:
  the feed-collapse at set bit `j_k` fires at a MOVING left-pad width (r19's
  `zxwConvLift 0 0 1` at bit 0 vs `zxwConvLift 0 2 0` at bit 1 — the pad is the
  processed-prefix WIDTH, which grows by the Z-copy leg each set bit adds and by
  the `|0>` each unset bit deposits), and the per-state route length grows with
  the inter-set-bit gap; threading both counters over `rowBits` with the growing
  correlated copy-prefix is the same distinct structural induction r19 named, not
  assembled here.  Both attacks reduce to the identical unbuilt piece: the
  correlated Z-copy prefix that a set bit shares with the continuing carrier. -/
def zxqHasGeneralCombFold : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
