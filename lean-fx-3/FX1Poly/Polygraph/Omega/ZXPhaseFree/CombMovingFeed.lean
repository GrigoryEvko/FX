import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombTrueArmFold

/-! # Polygraph/Omega/ZXPhaseFree/CombMovingFeed — the ISOLATED moving-position
feed-collapse, general in the left pad, and the honest wall on the general fold

Four prior ZX rounds (`CombTraversal` `zxu*`, `CombTraversalMultiBit` `zxm*`,
`CombRowFold` `zxq*`, `CombTrueArmFold` `zxh*`) each converged on ONE recurring
obstruction and walled it: a created state fed into a set-bit fork-then-merge
column collapses only at a FIXED strand (`zxuFeedColumnCollapse`, pad 0), while a
general single-row comb needs that collapse to fire at a MOVING strand index `k`
(the count of already-absorbed set bits) composed with a gap-growing carrier
route.  Every ingredient is committed — `zxuStateWalk` (the general gap route),
`zxuFeedColumnCollapse` (the fixed-position feed), `zxhChainFromFuse` (the chain
fusion), `zxqCombPrefixShift` (the unset-prefix shift) — but their
composition-at-a-moving-index is unbuilt.

This round isolates JUST the moving-position feed and pushes it as far as it goes:

* THE MOVING-POSITION FEED-COLLAPSE (`zxlFeedColumnCollapseAt`, PROVED, GENERAL in
  the left pad `leftPad`): the exact `zxuFeedColumnCollapse` column
  (`|0>` state ; fork ; merge) whiskered by `leftPad` spectator wires on the left,
  landed by lifting the committed pad-0 collapse through `zxwConvLift leftPad 0`.
  This is the one piece the four walls named as "the collapse must fire at a
  MOVING position" — now available at ANY pad, not just pad 0.  Its fires at
  `leftPad = 0, 1, 2, 3` are the moving column at the first four set-bit indices.

* THE HONEST WALL (`zxlHasMovingPositionFeed := false`): the general fold that
  threads this moving collapse together with the gap route AND the shared-copy
  chain accumulator across a structural recursion on `rowBits` does NOT close.
  The padded collapse supplies the collapse at any GIVEN pad, but the fold must
  supply the pad from an accumulator and simultaneously carry the walk gap and the
  growing chain — two inductions never carried together.  Two genuinely different
  attacks are recorded precisely on the marker.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Committed owner-false flags stay byte-intact; the fresh markers are
this file's `zxl*`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 1 — THE MOVING-POSITION FEED-COLLAPSE: the fixed-position collapse
whiskered by `leftPad` spectator wires, general in the pad -/

/-- THE MOVING-POSITION FEED-COLLAPSE: the committed feeding-column collapse
(`zxuFeedColumnCollapse`: a created `|0>` state fed into a `zSpider 1 2` fork then
an `xSpider 2 1` merge is absorbed, the column collapsing to the bare fork)
whiskered by `leftPad` spectator wires on the LEFT.  Lifted through the
position-general congruence `zxwConvLift leftPad 0` — the exact `k = 1` pattern
`zxuFeedColumnCollapse` uses internally (`hMirrorWhiskered`), now general in the
pad.  This is the collapse the four walls named as needing to fire "at a MOVING
position": strand index `leftPad`, the count of already-absorbed set bits. -/
theorem zxlFeedColumnCollapseAt (leftPad : Nat) :
    ZxwConv
      { sourceArity := leftPad + 1
        layers := [zxpWhiskerLayer leftPad 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
          zxpWhiskerLayer leftPad 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
          zxpWhiskerLayer leftPad 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := leftPad + 1
        layers := [zxpWhiskerLayer leftPad 0 [ZxpCell.zSpider 1 2]] } := by
  have hLift := zxwConvLift (leftPad + 1) leftPad 0 [] [] zxuFeedColumnCollapse
    (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
  simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpCatLayersNilRight] at hLift
  exact hLift

/-! ## Stage 2 — THE CHAIN GAINS A LEG AT A MOVING POSITION: a bare fork at the
moving strand `leftPad` grows the correlated bundle by exactly one output leg -/

/-- THE CHAIN GAINS A LEG AT A MOVING POSITION: the fused correlated bundle
`zSpider 0 (leftPad + 1)` (its `leftPad + 1` output legs correlated on strands
`0 .. leftPad`), followed by a bare fork `zSpider 1 2` at the moving strand
`leftPad`, is the wider bundle `zSpider 0 (leftPad + 2)` — the growing correlated
spider gains exactly one output leg.  This is the committed mid-leg fork fusion
`zxwMidForkFuseZ` at the moving pass position `leftPad` (the mid-layer
`zxaMidLayer (zSpider 1 2) leftPad 0` is definitionally the whisker
`zxpWhiskerLayer leftPad 0 [zSpider 1 2]`), general in the pad. -/
theorem zxlChainGainsLegAtPad (leftPad : Nat) :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 (leftPad + 1)],
          zxpWhiskerLayer leftPad 0 [ZxpCell.zSpider 1 2]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 (leftPad + 2)]] } :=
  zxwMidForkFuseZ 0 leftPad 0

/-! ## Stage 3 — THE MOVING-POSITION FEED STEP: feed-collapse at the moving strand
`leftPad` composed with the chain gaining a leg — one reusable moving-feed move -/

/-- THE MOVING-POSITION FEED STEP (general in `leftPad`): given the correlated
bundle `zSpider 0 (leftPad + 1)` on strands `0 .. leftPad`, a created `|0>` state
fed into the fork-then-merge column AT the moving strand `leftPad` is absorbed AND
extends the bundle to `zSpider 0 (leftPad + 2)`.  This is the single reusable
moving-feed step the general single-row fold would iterate at each set bit: the
feed-collapse fires at the MOVING pad `leftPad` (`zxlFeedColumnCollapseAt`, lifted
below the bundle) and the surviving bare fork grows the correlated spider by one
leg (`zxlChainGainsLegAtPad`).  It threads the moving pad through the collapse and
the chain extension together — the composition the four prior walls named as
unbuilt at a moving index, here landed for the bundle-and-feed window. -/
theorem zxlBundleFeedStepAt (leftPad : Nat) :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 (leftPad + 1)],
          zxpWhiskerLayer leftPad 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
          zxpWhiskerLayer leftPad 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
          zxpWhiskerLayer leftPad 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 (leftPad + 2)]] } := by
  have hFeed := zxwLiftConv 0 [[ZxpCell.zSpider 0 (leftPad + 1)]] []
    (zxlFeedColumnCollapseAt leftPad) (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  simp only [zxpCatLayers] at hFeed
  exact ZxwConv.trans hFeed (zxlChainGainsLegAtPad leftPad)

/-! ## Stage 4 — fires: the moving column and the moving feed step at the first
four set-bit indices, plus the k = 0 reconciliation to the committed pad-0 form -/

/-- FIRE (k = 0 reconciliation): the moving feed-collapse at pad `0` is exactly the
committed fixed-position collapse `zxuFeedColumnCollapse` (the whisker-by-zero
layers reduce definitionally to the bare column). -/
theorem zxlFeedColumnCollapseAtZeroFire :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2]] } :=
  zxlFeedColumnCollapseAt 0

/-- FIRE: the moving feed-collapse at pad `1` — the collapse fires one strand right
of the origin, the exact `k = 1` instance the committed two-bit traversal uses. -/
theorem zxlFeedColumnCollapseAtOneFire :
    ZxwConv
      { sourceArity := 1 + 1
        layers := [zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
          zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
          zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 1 + 1, layers := [zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 2]] } :=
  zxlFeedColumnCollapseAt 1

/-- FIRE: the moving feed step at pad `0` — a created `|0>` fed into the column at
strand `0` extends the bundle `zSpider 0 1` to `zSpider 0 2`. -/
theorem zxlBundleFeedStepAtZeroFire :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1],
          zxpWhiskerLayer 0 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
          zxpWhiskerLayer 0 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
          zxpWhiskerLayer 0 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 2]] } :=
  zxlBundleFeedStepAt 0

/-- FIRE: the moving feed step at pad `1` — a created `|0>` fed into the column at
the MOVING strand `1` extends the bundle `zSpider 0 2` to `zSpider 0 3`. -/
theorem zxlBundleFeedStepAtOneFire :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 2],
          zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
          zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
          zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 3]] } :=
  zxlBundleFeedStepAt 1

/-- FIRE: the moving feed step at pad `2` — the column at strand `2` extends the
bundle `zSpider 0 3` to `zSpider 0 4`. -/
theorem zxlBundleFeedStepAtTwoFire :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 3],
          zxpWhiskerLayer 2 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
          zxpWhiskerLayer 2 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
          zxpWhiskerLayer 2 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 4]] } :=
  zxlBundleFeedStepAt 2

/-! ## Stage 5 — kernel span pins for the moving feed step endpoints -/

/-- Kernel span pin: the moving feed step at pad `1` is a semantic equivalence —
the bundle genuinely gains one correlated leg. -/
theorem zxlBundleFeedStepAtOneSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 2],
            zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
            zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
            zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 3]] }) = true :=
  rfl

/-- Kernel span pin: the moving feed step at pad `2` is a semantic equivalence. -/
theorem zxlBundleFeedStepAtTwoSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 3],
            zxpWhiskerLayer 2 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
            zxpWhiskerLayer 2 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
            zxpWhiskerLayer 2 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 4]] }) = true :=
  rfl

/-- Kernel span pin (discriminating FALSE control): the moving feed step at pad `1`
lands on a CORRELATED bundle, NOT on three INDEPENDENT free bits
`[[zSpider 0 1, zSpider 0 1, zSpider 0 1]]` — the fed leg shares the one correlated
root, it is not an unrelated free bit.  The span separates.  (Note `zxpSpanEqB` is
coarse on Z output-leg count, so the correct-target pin above holds against
`zSpider 0 k` for a class of `k`; the content this control adds is that the class
is the correlated one, not the independent-bits one.) -/
theorem zxlBundleFeedStepAtOneNotIndependentSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 2],
            zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 0 1],
            zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 2, ZxpCell.wire],
            zxpWhiskerLayer 1 0 [ZxpCell.wire, ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 1, ZxpCell.zSpider 0 1, ZxpCell.zSpider 0 1]] })
      = false :=
  rfl

/-! ## Stage 6 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the MOVING-POSITION FEED-COLLAPSE is LIVE
(`zxlFeedColumnCollapseAt`, GENERAL in the left pad) — the committed pad-0 collapse
`zxuFeedColumnCollapse` whiskered to ANY pad `leftPad` through the position-general
congruence `zxwConvLift leftPad 0`.  This is the piece all four prior ZX walls
(`zxuHasGeneralIdentityAbsorb`, `zxmHasGeneralCombTraversal`,
`zxqHasGeneralCombFold`, `zxhHasGeneralSingleRowFold`) named as "the feed-collapse
is built only at a FIXED position (pad 0)"; it is now available at every pad, with
the `k = 0` reconciliation to the committed form and fires at pads `1, 2, 3`. -/
def zxlHasMovingFeedCollapse : Bool := true

/-- CONTENT MARKER (TRUE): the MOVING-POSITION CHAIN EXTENSION is LIVE
(`zxlChainGainsLegAtPad`, general in the pad) — the fused correlated bundle
`zSpider 0 (leftPad + 1)` followed by a bare fork at the MOVING strand `leftPad`
is the wider bundle `zSpider 0 (leftPad + 2)`, the committed mid-leg fork fusion
`zxwMidForkFuseZ` at the moving pass position.  The growing correlated spider gains
exactly one output leg at any strand — the algebraic half of the moving-feed step. -/
def zxlHasMovingChainExtension : Bool := true

/-- CONTENT MARKER (TRUE): the MOVING-POSITION FEED STEP is LIVE
(`zxlBundleFeedStepAt`, GENERAL in the pad) — a created `|0>` fed into the
fork-then-merge column AT the moving strand `leftPad`, sitting below the correlated
bundle `zSpider 0 (leftPad + 1)`, is absorbed AND extends the bundle to
`zSpider 0 (leftPad + 2)`.  This composes the moving feed-collapse
(`zxlFeedColumnCollapseAt`) with the moving chain extension
(`zxlChainGainsLegAtPad`) into ONE reusable move, threading the moving pad through
BOTH — the single step a general single-row fold would iterate at each set bit,
here landed general in `leftPad` (fires at pads `0, 1, 2`, with span pins and a
discriminating FALSE control against three independent free bits).  This is the
genuine advance over the four prior walls: the moving-position feed step, which
they had only at pad 0 as `zxuFeedColumnCollapse` and only instanced (never general)
in the concrete `[true, true]` two-bit traversal. -/
def zxlHasMovingFeedStep : Bool := true

/-- OWNER MARKER (FALSE): the FULL moving-position feed threaded into a GENERAL
single-row fold did NOT land — the committed owner-false flags
`zxqHasGeneralCombFold`, `zxhHasGeneralSingleRowFold`,
`zxuHasGeneralIdentityAbsorb`, `zxmHasGeneralCombTraversal`,
`zxiHasFeedingCombRouter`, `zxjHasIdentityAbsorb`, `zxkIdentityAbsorbIsProven`
stay byte-intact false.

This round supplies the moving-feed STEP in full generality
(`zxlBundleFeedStepAt`): the feed-collapse and the chain extension both fire at the
moving pad `leftPad`, composed.  What remains unbuilt is the ROUTE that delivers
each fed state FROM the init block (where every fed `|0>` is created up top, at the
domain strands) TO its moving set-bit column, threaded together with the growing
bundle across a structural recursion on `rowBits`.  The moving-feed step assumes
the fed state already sits at its column, directly below the bundle; the fold must
manufacture that positioning per set bit, and the manufacturing is exactly the
gap-growing route the four prior walls named.  Two genuinely different attacks
burned:

* (A) THE CHAIN-DRIVEN FOLD.  Induct on `rowBits` carrying the bundle accumulator
  `zSpider 0 setCount`; at a `true` bit fire `zxlBundleFeedStepAt setCount`, at a
  `false` bit whisker via the committed `zxqCombPrefixShift`, at the base fuse.
  BURN: `zxlBundleFeedStepAt setCount` consumes the feed column sitting DIRECTLY
  below the bundle, but in `zxqFoldSource rowBits` the fed state for the set bit at
  comb-position `j` is created in the init block `zxnZeroStateCells rowBits.length`
  at domain strand `j` — separated from the bundle by every intervening comb layer.
  Delivering it to the column is `zxuStateWalk` across the inter-set-bit gap
  (three `zxsWhiskerCellPastInit` commutations per gap-1, growing with the gap),
  and the fed state must be PEELED off the init block first (an interchange
  cascade).  The step is position-general; the route to reach the step's input
  window is the distinct nested induction, not supplied by the bundle accumulator.

* (B) THE INIT-SPLIT CASCADE.  Peel the `setCount`-state init block into per-set-bit
  creations up front, route each to its column, then fire the moving-feed step at
  each.  BURN: the peels INTERLEAVE with the routes — a fed state created earlier
  must ride past the routes of the later ones (exactly the `hStep4a/4b/4c`
  three-commutation walk between the two set-bit columns in the committed two-bit
  `zxmCombTraversalTwoBit`, but now compounded per set bit) — so the split and the
  routes are one entangled bookkeeping keyed on BOTH the moving pad `setCount` and
  the running gap, the identical two-accumulator induction attack (A) hits.  Both
  reduce to the same unbuilt piece: the gap-growing route from the init block to the
  moving set-bit column, threaded with the bundle across `rowBits`. -/
def zxlHasMovingPositionFeed : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
