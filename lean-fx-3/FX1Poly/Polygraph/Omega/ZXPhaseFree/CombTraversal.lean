import FX1Poly.Polygraph.Omega.ZXPhaseFree.IdentityRouter
import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderResidual

/-! # Polygraph/Omega/ZXPhaseFree/CombTraversal — the state-walk router and the
feeding-column cells: the created-state routing engine both identity/spider walls
named, built bottom-up

The prior rounds landed the local one-cell atoms a created state obeys at each
event of a comb column (`IdentityRouter`, the `zxi*` atoms) and the disjoint
create-state ride (`IdentityResidual`, `zxjZeroStateRidePastGenBlock`), then
walled `zxbIdentityAbsorbStatement` on the ONE missing move both attacks named:
*a created state routing past a comb column that feeds it*, whose "bookkeeping
grows with the gap width" (the iterated `zxiStateSlidesPastCrossing`).

This round BUILDS that routing engine bottom-up:

* THE STATE-WALK STAIRCASE (`zxuStateWalk`, PROVED, general in the gap width): a
  created X state on the left of a `gapWidth`-wide passing block routes to the
  far side by a crossing staircase — the iterated `zxiStateSlidesPastCrossing`
  under whisker padding, closed by a single induction on the gap.  This is the
  routing primitive the wall notes named as "growing with the gap width".

* THE FEEDING-COLUMN CELLS (`zxuStateForkOnCarrier`, `zxuStateMergeOnCarrier`,
  PROVED, in padded contexts): the state entering one leg of a `zSpider 1 2`
  fork (`bialgUnitCopy` whiskered) and the state fed into an `xSpider 2 1` merge
  (`xMonoidUnit` whiskered), landed in the padding contexts the comb's staircase
  produces.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Committed owner-false flags stay byte-intact; the fresh markers are
this file's `zxu*`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — literal-arity reconciliation helpers -/

/-- `2 + n = 1 + (1 + n)` (split the leading two). -/
theorem zxuTwoSplitLeft (anyCount : Nat) : 2 + anyCount = 1 + (1 + anyCount) :=
  (Nat.add_assoc 1 1 anyCount)

/-- `2 + n = 1 + (n + 1)` (split with the tail carrying the one). -/
theorem zxuTwoSplitRight (anyCount : Nat) : 2 + anyCount = 1 + (anyCount + 1) := by
  rw [zxuTwoSplitLeft, Nat.add_comm anyCount 1]

/-! ## Stage 1 — THE STATE-WALK STAIRCASE (T1): a created X state routes past a
run of passing wires by induction on the gap width -/

/-- The create-on-the-left layer: an X state is created at strand 0, the
`gapWidth` domain strands pass on the right. -/
def zxuCreateLeftLayer (gapWidth : Nat) : List ZxpCell :=
  ZxpCell.xSpider 0 1 :: zxpWireCells gapWidth

/-- The create-on-the-right layer: the `gapWidth` domain strands pass on the
left, an X state is created at the far strand. -/
def zxuCreateRightLayer (gapWidth : Nat) : List ZxpCell :=
  zxpCatCells (zxpWireCells gapWidth) [ZxpCell.xSpider 0 1]

/-- The walk layers that route the just-created leftmost state past `gapWidth`
passing wires — one crossing per wire, the front wire peeled first and the tail
recursion whiskered by that wire on the left. -/
def zxuStateWalkLayers : Nat -> List (List ZxpCell)
  | 0 => []
  | gapPred + 1 =>
      (ZxpCell.crossing :: zxpWireCells gapPred)
        :: zxpWhiskerLayers 1 0 (zxuStateWalkLayers gapPred)

/-- The cell-first side: create the state on the left, then walk it right. -/
def zxuStateWalkLhs (gapWidth : Nat) : ZxpDiagram :=
  { sourceArity := gapWidth
    layers := zxuCreateLeftLayer gapWidth :: zxuStateWalkLayers gapWidth }

/-- The staircase-free side: the wires pass, the state is created on the right. -/
def zxuStateWalkRhs (gapWidth : Nat) : ZxpDiagram :=
  { sourceArity := gapWidth, layers := [zxuCreateRightLayer gapWidth] }

theorem zxuCreateLeftLayerDomArity (gapWidth : Nat) :
    zxpLayerDomArity (zxuCreateLeftLayer gapWidth) = gapWidth := by
  show zxpCellDomArity (ZxpCell.xSpider 0 1) + zxpLayerDomArity (zxpWireCells gapWidth)
    = gapWidth
  rw [zxpWireCellsDomArity]
  show 0 + gapWidth = gapWidth
  rw [Nat.zero_add]

theorem zxuCreateLeftLayerCodArity (gapWidth : Nat) :
    zxpLayerCodArity (zxuCreateLeftLayer gapWidth) = 1 + gapWidth := by
  show (1 : Nat) + zxpLayerCodArity (zxpWireCells gapWidth) = 1 + gapWidth
  rw [zxpWireCellsCodArity]

/-- The head walk layer's codomain arity, in the `1 + ((1 + gapPred) + 0)` shape
the whisker-arity lemma consumes. -/
theorem zxuWalkHeadCodArity (gapPred : Nat) :
    zxpLayerCodArity (ZxpCell.crossing :: zxpWireCells gapPred)
      = 1 + ((1 + gapPred) + 0) := by
  show (2 : Nat) + zxpLayerCodArity (zxpWireCells gapPred) = 1 + ((1 + gapPred) + 0)
  rw [zxpWireCellsCodArity, Nat.add_zero]
  exact zxuTwoSplitLeft gapPred

/-- The walk layers are well formed at the post-create arity `1 + gapWidth`. -/
theorem zxuStateWalkLayersWF : (gapWidth : Nat) ->
    ZxpLayersWF (1 + gapWidth) (zxuStateWalkLayers gapWidth)
  | 0 => ZxpLayersWF.nil _
  | gapPred + 1 => by
      refine ZxpLayersWF.cons ?_ ?_
      · show (2 : Nat) + zxpLayerDomArity (zxpWireCells gapPred) = 1 + (gapPred + 1)
        rw [zxpWireCellsDomArity]
        exact zxuTwoSplitRight gapPred
      · rw [zxuWalkHeadCodArity gapPred]
        exact zxpWhiskerLayersWF 1 0 (zxuStateWalkLayers gapPred)
          (zxuStateWalkLayersWF gapPred)

/-- Running the walk layers preserves the strand count. -/
theorem zxuStateWalkLayersCodArity : (gapWidth : Nat) ->
    zxpLayersCodArity (1 + gapWidth) (zxuStateWalkLayers gapWidth) = 1 + gapWidth
  | 0 => rfl
  | gapPred + 1 => by
      show zxpLayersCodArity
          (zxpLayerCodArity (ZxpCell.crossing :: zxpWireCells gapPred))
          (zxpWhiskerLayers 1 0 (zxuStateWalkLayers gapPred))
        = 1 + (gapPred + 1)
      rw [zxuWalkHeadCodArity gapPred,
        zxpWhiskerLayersCodArity 1 0 (zxuStateWalkLayers gapPred) (1 + gapPred),
        zxuStateWalkLayersCodArity gapPred]
      show 1 + ((1 + gapPred) + 0) = 1 + (gapPred + 1)
      rw [Nat.add_zero, Nat.add_comm 1 gapPred]

theorem zxuStateWalkLhsWF (gapWidth : Nat) : ZxpDiagramWF (zxuStateWalkLhs gapWidth) := by
  refine ZxpLayersWF.cons (zxuCreateLeftLayerDomArity gapWidth) ?_
  rw [zxuCreateLeftLayerCodArity gapWidth]
  exact zxuStateWalkLayersWF gapWidth

/-- THE STATE-WALK STAIRCASE: a created X state on the left of `gapWidth` passing
wires routes to the far strand — the iterated `zxiStateSlidesPastCrossing` under
whisker padding, closed by induction on the gap width.  The front wire is peeled
by one slide, the tail is the induction hypothesis whiskered by that wire. -/
theorem zxuStateWalk : (gapWidth : Nat) ->
    ZxwConv (zxuStateWalkLhs gapWidth) (zxuStateWalkRhs gapWidth)
  | 0 => by
      refine ZxwConv.refl _ ?_
      exact zxuStateWalkLhsWF 0
  | gapPred + 1 => by
      -- Move 1: the state slides past the FRONT wire (slide atom whiskered by
      -- `gapPred` spectator wires on the right), the tail walk following.
      have hSlide : ZxwConv (zxwSlideRightLhs (ZxpCell.xSpider 0 1))
          (zxwSlideRightRhs (ZxpCell.xSpider 0 1)) :=
        zxwSlideRightConv (ZxpCell.xSpider 0 1)
      have hMove1 := zxwConvLift (gapPred + 1) 0 gapPred []
        (zxpWhiskerLayers 1 0 (zxuStateWalkLayers gapPred)) hSlide
        (ZxpLayersWF.nil _)
        (by
          show (gapPred + 1 : Nat) = 0 + (1 + gapPred)
          rw [Nat.zero_add, Nat.add_comm 1 gapPred])
        (by
          -- after-block WF at the slide's whiskered cod `0 + (2 + gapPred)`
          have hW := zxpWhiskerLayersWF 1 0 (zxuStateWalkLayers gapPred)
            (zxuStateWalkLayersWF gapPred)
          show ZxpLayersWF (0 + (zxpDiagramCodArity (zxwSlideRightLhs (ZxpCell.xSpider 0 1))
            + gapPred)) (zxpWhiskerLayers 1 0 (zxuStateWalkLayers gapPred))
          rw [zxwSlideRightLhsCodArity]
          show ZxpLayersWF (0 + ((1 + 1) + gapPred))
            (zxpWhiskerLayers 1 0 (zxuStateWalkLayers gapPred))
          rw [Nat.zero_add]
          show ZxpLayersWF (1 + 1 + gapPred)
            (zxpWhiskerLayers 1 0 (zxuStateWalkLayers gapPred))
          have hCast : (1 : Nat) + ((1 + gapPred) + 0) = 1 + 1 + gapPred := by
            rw [Nat.add_zero, Nat.add_assoc]
          rw [<- hCast]
          exact hW)
      -- Move 2: the induction hypothesis whiskered by the front wire on the left.
      have hMove2 := zxwConvLift (gapPred + 1) 1 0 [] [] (zxuStateWalk gapPred)
        (ZxpLayersWF.nil _)
        (by
          show (gapPred + 1 : Nat) = 1 + ((zxuStateWalkLhs gapPred).sourceArity + 0)
          rw [Nat.add_zero]
          exact Nat.add_comm gapPred 1)
        (ZxpLayersWF.nil _)
      -- both pad diagrams reduce definitionally to the explicit walk layer lists;
      -- the middle diagram is `whisker(1,0) (Lhs gapPred)` on both sides.
      simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxwSlideRightLhs,
        zxwSlideRightRhs, zxwStairFromRightLayers, zxpWhiskerLayer, zxpCatCells,
        zxpWireCells, zxpCellDomArity, zxuStateWalkLhs, zxuStateWalkRhs,
        zxuStateWalkLayers, zxuCreateLeftLayer, zxuCreateRightLayer,
        zxpCatCellsNilRight, zxpCatLayersNilRight] at hMove1 hMove2 ⊢
      exact ZxwConv.trans hMove1 hMove2

/-! ## Stage 2 — fires and kernel span pins for the state walk -/

/-- FIRE: the state walks past ONE passing wire (the bare slide atom, but now via
the general engine). -/
theorem zxuStateWalkOneFire :
    ZxwConv (zxuStateWalkLhs 1) (zxuStateWalkRhs 1) := zxuStateWalk 1

/-- FIRE: the state walks past TWO passing wires — the first gap where the
staircase recursion genuinely fires (a two-crossing walk). -/
theorem zxuStateWalkTwoFire :
    ZxwConv (zxuStateWalkLhs 2) (zxuStateWalkRhs 2) := zxuStateWalk 2

/-- FIRE: the state walks past THREE passing wires. -/
theorem zxuStateWalkThreeFire :
    ZxwConv (zxuStateWalkLhs 3) (zxuStateWalkRhs 3) := zxuStateWalk 3

/-- Kernel span pin: the one-wire walk is a semantic equivalence. -/
theorem zxuStateWalkOneSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxuStateWalkLhs 1))
      (zxpDiagramDenote (zxuStateWalkRhs 1)) = true := rfl

/-- Kernel span pin: the two-wire walk is a semantic equivalence. -/
theorem zxuStateWalkTwoSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxuStateWalkLhs 2))
      (zxpDiagramDenote (zxuStateWalkRhs 2)) = true := rfl

/-- Kernel span pin: the three-wire walk is a semantic equivalence. -/
theorem zxuStateWalkThreeSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxuStateWalkLhs 3))
      (zxpDiagramDenote (zxuStateWalkRhs 3)) = true := rfl

/-! ## Stage 3 — THE FEEDING-COLUMN CELLS (T2): the state entering the carrier
fork and the carrier merge, whiskered into the comb's padding contexts -/

/-- THE STATE-FORK CELL: a created X state above a `zSpider 1 2` copy becomes two
created X states, in any padding context `(leftWires, rightWires)` — the
`bialgUnitCopy` atom (`zxiStateCopyDuplicates`) lifted through `zxwConvLift`.
This is the state-through-fork event the comb performs at a set bit. -/
theorem zxuStateForkOnCarrier (leftWires rightWires : Nat) :
    ZxwConv
      { sourceArity := leftWires + rightWires
        layers := [zxpWhiskerLayer leftWires rightWires [ZxpCell.xSpider 0 1],
          zxpWhiskerLayer leftWires rightWires [ZxpCell.zSpider 1 2]] }
      { sourceArity := leftWires + rightWires
        layers := [zxpWhiskerLayer leftWires rightWires
          [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] } := by
  have hLift := zxwConvLift (leftWires + (0 + rightWires)) leftWires rightWires [] []
    zxiStateCopyDuplicates (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
  simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpCatLayersNilRight,
    Nat.zero_add] at hLift
  exact hLift

/-- THE STATE-MERGE CELL: a created X state fed into an `xSpider 2 1` merge
alongside a passing wire is the identity wire, in any padding context — the
`xMonoidUnit` atom (`zxiStateMergeAbsorbs`) lifted through `zxwConvLift`.  This is
the state-through-merge event: the carrier that fed the state is absorbed. -/
theorem zxuStateMergeOnCarrier (leftWires rightWires : Nat) :
    ZxwConv
      { sourceArity := leftWires + (1 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires [ZxpCell.xSpider 0 1, ZxpCell.wire],
          zxpWhiskerLayer leftWires rightWires [ZxpCell.xSpider 2 1]] }
      { sourceArity := leftWires + (1 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires [ZxpCell.wire]] } := by
  have hLift := zxwConvLift (leftWires + (1 + rightWires)) leftWires rightWires [] []
    zxiStateMergeAbsorbs (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
  simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpCatLayersNilRight] at hLift
  exact hLift

/-- FIRE: the state-fork cell with one spectator wire on each side. -/
theorem zxuStateForkOnCarrierFire :
    ZxwConv
      { sourceArity := 1 + 1
        layers := [zxpWhiskerLayer 1 1 [ZxpCell.xSpider 0 1],
          zxpWhiskerLayer 1 1 [ZxpCell.zSpider 1 2]] }
      { sourceArity := 1 + 1
        layers := [zxpWhiskerLayer 1 1 [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] } :=
  zxuStateForkOnCarrier 1 1

/-- FIRE: the state-merge cell with one spectator wire on each side. -/
theorem zxuStateMergeOnCarrierFire :
    ZxwConv
      { sourceArity := 1 + (1 + 1)
        layers := [zxpWhiskerLayer 1 1 [ZxpCell.xSpider 0 1, ZxpCell.wire],
          zxpWhiskerLayer 1 1 [ZxpCell.xSpider 2 1]] }
      { sourceArity := 1 + (1 + 1)
        layers := [zxpWhiskerLayer 1 1 [ZxpCell.wire]] } :=
  zxuStateMergeOnCarrier 1 1

/-- Kernel span pin: the state-fork cell is a semantic equivalence. -/
theorem zxuStateForkOnCarrierSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1 + 1
          layers := [zxpWhiskerLayer 1 1 [ZxpCell.xSpider 0 1],
            zxpWhiskerLayer 1 1 [ZxpCell.zSpider 1 2]] })
      (zxpDiagramDenote
        { sourceArity := 1 + 1
          layers := [zxpWhiskerLayer 1 1
            [ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] }) = true := rfl

/-- Kernel span pin: the state-merge cell is a semantic equivalence. -/
theorem zxuStateMergeOnCarrierSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1 + (1 + 1)
          layers := [zxpWhiskerLayer 1 1 [ZxpCell.xSpider 0 1, ZxpCell.wire],
            zxpWhiskerLayer 1 1 [ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote
        { sourceArity := 1 + (1 + 1)
          layers := [zxpWhiskerLayer 1 1 [ZxpCell.wire]] }) = true := rfl

/-! ## Stage 3b — the mirror merge cell: a created state on the RIGHT leg of the
merge is absorbed (the leg orientation the comb's staircase actually presents) -/

/-- THE MIRROR STATE-MERGE CELL: a created X state fed into the RIGHT leg of an
`xSpider 2 1` merge (the passing strand on the left) is the identity wire.  The
comb feeds the created carrier copy into the LEFT leg and the traversed state
into the RIGHT leg, so this is the orientation the traversal actually meets.
Derived from the left-leg unit (`zxiStateMergeAbsorbs`) by commuting the merge's
legs (`xMonoidComm`) and sliding the created state across the crossing. -/
theorem zxuStateMergeAbsorbsRight :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1], [ZxpCell.xSpider 2 1]] }
      { sourceArity := 1, layers := [[ZxpCell.wire]] } := by
  -- Step 1: expand the merge into `crossing ; merge` (xMonoidComm reversed),
  -- fired below the create-state layer.
  have hComm : ZxwConv (zxpRowRhs ZxpRowTag.xMonoidComm) (zxpRowLhs ZxpRowTag.xMonoidComm) :=
    ZxwConv.symm (zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidComm))
  have hStep1 := zxwLiftConv 1 [[ZxpCell.wire, ZxpCell.xSpider 0 1]] [] hComm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  -- Step 2: slide the created state across the crossing, above the merge.
  have hStep2 := zxwLiftConv 1 [] [[ZxpCell.xSpider 2 1]]
    (zxwSlideLeftConv (ZxpCell.xSpider 0 1))
    (ZxpLayersWF.nil _) rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  -- Step 3: the left-leg merge unit fires.
  have hStep3 : ZxwConv (zxpRowLhs ZxpRowTag.xMonoidUnit) (zxpRowRhs ZxpRowTag.xMonoidUnit) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidUnit)
  simp only [zxpRowLhs, zxpRowRhs, zxwSlideLeftLhs, zxwSlideLeftRhs,
    zxwStairFromLeftLayers, zxpCatLayers, zxpCellDomArity] at hStep1 hStep2 hStep3
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2 hStep3)

/-- Kernel span pin: the mirror merge cell is a semantic equivalence. -/
theorem zxuStateMergeAbsorbsRightSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1], [ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote { sourceArity := 1, layers := [[ZxpCell.wire]] }) = true := rfl

/-! ## Stage 3c — THE FEEDING-COLUMN COLLAPSE (T3 heart): a created state routed
into a comb's fork-then-merge column is absorbed, the carrier passing as a fork -/

/-- THE FEEDING-COLUMN COLLAPSE: a created X state fed into the fork-then-merge
column a comb performs at a set bit is ABSORBED — the carrier (input strand)
forks, one copy meets the created state at the merge and passes through unchanged
(the created state is the parity unit `|0>`), and the whole column collapses to
the bare fork.  This is the exact move both the identity and spider walls named:
a created state routing past the comb column that feeds it.  Assembled from the
past-init interchange (`zxsWhiskerCellPastInit`), the mirror merge cell
(`zxuStateMergeAbsorbsRight`), and the trailing-wire strip. -/
theorem zxuFeedColumnCollapse :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2]] } := by
  -- the created state and the fork commute (create the state after the fork)
  have hInter : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2, ZxpCell.wire]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1]] } :=
    ZxwConv.symm (zxsWhiskerCellPastInit (ZxpCell.zSpider 1 2) 0 0 1)
  -- the merge collapse, whiskered by the spectator fork-copy on the left
  have hMirrorWhiskered : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.wire]] } := by
    have hLift := zxwConvLift 2 1 0 [] [] zxuStateMergeAbsorbsRight
      (ZxpLayersWF.nil _) rfl (ZxpLayersWF.nil _)
    simp only [zxpPadDiagram, zxpCatLayers, zxpWhiskerLayers, zxpWhiskerLayer,
      zxpCatCells, zxpWireCells, zxpCatLayersNilRight] at hLift
    exact hLift
  -- the trailing identity wire layer strips against the fork
  have hStrip : ZxwConv
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.wire]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2]] } :=
    zxwOfZxeConv (zxeStripTrailingWireLayer [ZxpCell.zSpider 1 2])
  -- lift the interchange below the trailing merge
  have hStep1 : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] } := by
    have hLift := zxwLiftConv 1 [] [[ZxpCell.wire, ZxpCell.xSpider 2 1]] hInter
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- lift the merge collapse below the leading fork
  have hStep2 : ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.wire, ZxpCell.xSpider 2 1]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2], [ZxpCell.wire, ZxpCell.wire]] } := by
    have hLift := zxwLiftConv 1 [[ZxpCell.zSpider 1 2]] [] hMirrorWhiskered
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
    simp only [zxpCatLayers] at hLift
    exact hLift
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2 hStrip)

/-- Kernel span pin: the feeding-column collapse is a semantic equivalence — the
created state is genuinely absorbed. -/
theorem zxuFeedColumnCollapseSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1],
            [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote { sourceArity := 1, layers := [[ZxpCell.zSpider 1 2]] }) = true :=
  rfl

/-! ## Stage 3d — THE CARRIER BIRTH-AND-DEATH tail and THE FULL COMB TRAVERSAL
(T3): a created state fed into the smallest full comb is absorbed to the free bit -/

/-- THE CARRIER BIRTH-AND-DEATH: the comb's own carrier, created and forked, its
spare copy crossed and discarded, collapses to a single created free bit.  The
discard slides back across the crossing (the counit's naturality, a `slideRight`
of `zSpider 1 0`), then the copy-counit fires, then the trailing wire strips. -/
theorem zxuCarrierBirthDeath :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] } := by
  -- Move 1: slide the discard back across the crossing (counit naturality)
  have hDiscardPastCross : ZxwConv
      { sourceArity := 2, layers := [[ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 2, layers := [[ZxpCell.zSpider 1 0, ZxpCell.wire]] } :=
    ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 0))
  have hStep1 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 1 0, ZxpCell.wire]] } := by
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2]] []
      hDiscardPastCross
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))) rfl
      (ZxpLayersWF.nil _)
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- Move 2: the copy-counit fires (fork then discard-left = wire)
  have hCounit : ZxwConv (zxpRowLhs ZxpRowTag.zComonoidCounit)
      (zxpRowRhs ZxpRowTag.zComonoidCounit) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.zComonoidCounit)
  have hStep2 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 1 0, ZxpCell.wire]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire]] } := by
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]] [] hCounit
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
    simp only [zxpRowLhs, zxpRowRhs, zxpCatLayers] at hLift
    exact hLift
  -- Move 3: strip the trailing wire against the created free bit
  have hStrip : ZxwConv
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] } :=
    zxwOfZxeConv (zxeStripTrailingWireLayer [ZxpCell.zSpider 0 1])
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2 hStrip)

/-- THE FULL COMB TRAVERSAL (T3, the round's victory condition): a created X state
fed into the smallest feeding comb `zxnXorRowLayers [true]` is fully traversed and
absorbed — the whole `create-state ; comb` machine collapses to a single created
free bit `zSpider 0 1`.  This is one concrete end-to-end traversal of a created
state through a comb that feeds it: the created carrier and the fed state are
reordered, the fed state routes through the feeding column and is absorbed
(`zxuFeedColumnCollapse`), and the carrier is born, forked, and discarded
(`zxuCarrierBirthDeath`). -/
theorem zxuCombTraversalOneBit :
    ZxwConv
      { sourceArity := 0, layers := [ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] } := by
  -- reorder the created state and the carrier creation
  have hReorder : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 0 1, ZxpCell.wire]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1]] } :=
    ZxwConv.symm (zxsWhiskerCellPastInit (ZxpCell.zSpider 0 1) 0 0 1)
  have hStep1 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 0 1, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hLift := zxwLiftConv 0 []
      [[ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] hReorder
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl
        (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))))
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- the fed state routes through the feeding column and is absorbed
  have hStep2 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] } := by
    have hLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]]
      [[ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] zxuFeedColumnCollapse
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
    simp only [zxpCatLayers] at hLift
    exact hLift
  -- the comb reduces to its explicit layers; chain the three stages plus the tail
  show ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 0 1, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire], [ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing], [ZxpCell.wire, ZxpCell.zSpider 1 0]] }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] }
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2 zxuCarrierBirthDeath)

/-- Kernel span pin: the full comb traversal is a semantic equivalence — the
created state is genuinely absorbed to the free bit. -/
theorem zxuCombTraversalOneBitSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0, layers := [ZxpCell.xSpider 0 1] :: zxnXorRowLayers [true] })
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] }) = true :=
  rfl

/-- Kernel span pin: the carrier birth-and-death is a semantic equivalence. -/
theorem zxuCarrierBirthDeathSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.crossing],
            [ZxpCell.wire, ZxpCell.zSpider 1 0]] })
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 1]] }) = true :=
  rfl

/-! ## Stage 4 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the state-walk routing engine is LIVE — a created X
state routes past a `gapWidth`-wide passing block by the crossing staircase,
GENERAL in the gap width (`zxuStateWalk`), the iterated
`zxiStateSlidesPastCrossing` closed by induction.  This is the routing primitive
the `zxiHasFeedingCombRouter` / `zxjHasIdentityAbsorb` wall notes named as
"growing with the gap width". -/
def zxuHasStateWalkRouter : Bool := true

/-- CONTENT MARKER (TRUE): the feeding-column cells are LIVE — the state-fork
(`zxuStateForkOnCarrier`, `bialgUnitCopy` whiskered), the state-merge
(`zxuStateMergeOnCarrier`, `xMonoidUnit` whiskered), and the mirror merge
(`zxuStateMergeAbsorbsRight`, the right-leg orientation the comb presents) — the
events a created state performs at a comb's set bit, each with a kernel span pin. -/
def zxuHasFeedingColumnCells : Bool := true

/-- CONTENT MARKER (TRUE): the FEEDING-COLUMN COLLAPSE is LIVE
(`zxuFeedColumnCollapse`) — a created state routed into the fork-then-merge column
a comb performs at a set bit is ABSORBED, the carrier passing as a bare fork.
This is the exact primitive the `zxiHasFeedingCombRouter` / `zxjHasIdentityAbsorb`
wall notes named: a created state routing past the comb column that feeds it. -/
def zxuHasFeedingColumnCollapse : Bool := true

/-- CONTENT MARKER (TRUE): ONE FULL COMB TRAVERSAL is LANDED
(`zxuCombTraversalOneBit`) — a created X state fed into the smallest feeding comb
`zxnXorRowLayers [true]` traverses the whole machine and collapses to the free bit
`zSpider 0 1`, as an explicit `ZxwConv` chain (reorder ; feeding-column collapse ;
carrier birth-and-death), with a kernel span pin.  This is the round's victory
condition: one concrete end-to-end traversal of a created state through a comb
that feeds it. -/
def zxuHasFullCombTraversal : Bool := true

/-- OWNER MARKER (FALSE): the GENERAL identity residual `zxbIdentityAbsorbStatement`
did NOT flip — the committed owners `zxiHasIdentityAbsorb`,
`zxjHasIdentityAbsorb`, `zxkIdentityAbsorbIsProven` stay byte-intact false.  The
concrete `[true]` traversal is landed and the routing engine (`zxuStateWalk`) and
feeding-column collapse (`zxuFeedColumnCollapse`) are the general pieces, but the
general `rowBits` induction plus the `wireCount` step do NOT close here.

Two genuinely different attacks burned:

* (A) GENERAL rowBits INDUCTION ON THE COMB.  The `[true]` traversal collapses the
  comb because the carrier is created ADJACENT to the fed state (no routing).  A
  general comb `zxnXorRowLayers rowBits` with a set bit at position `j > 0` needs
  the carrier to WALK from strand 0 to strand `j` before it forks/merges — that is
  the `zxuStateWalk` staircase composed WITH `zxuFeedColumnCollapse` at each set
  bit, plus the interleaved unset-bit crossings (`zxnCombLayers`'s `false` arm).
  The composition is not a single fold: the walk shifts the carrier's strand
  index, so the feeding column collapse must fire at a MOVING position, and the
  arity bookkeeping of the whiskered collapse at position `j` grows with `j` — the
  smallest genuinely-feeding instance (`rowBits = [true, true]`, the 8-layer
  staircase) already needs the walk (`zxuStateWalk 1`) between the two set-bit
  columns.  The per-position collapse is built (`zxuFeedColumnCollapse`) but the
  moving-position fold over `rowBits` is a distinct construction, not assembled.

* (B) THE `wireCount` IDENTITY-NF INDUCTION.  `zxbIdentityAbsorbStatement`'s step
  `wire (x) NF(m) ~ NF(m+1)` (per `zxiHasIdentityAbsorb` / `zxjHasIdentityAbsorb`)
  needs the created state on codomain strand `m + j` to route past the `m`
  generator combs that COUPLE it (`zxpIdRows` rows are `e_i ++ e_i`, coupling
  domain strand `i` with codomain strand `m + i`).  The per-comb feeding is now
  `zxuFeedColumnCollapse`, but the created state must first `zxuStateWalk` past the
  intervening `m` combs' carriers, AND the identity NF interleaves an INIT (create
  all states) and a KILL (collect all domain strands) that the single-comb
  traversal does not exercise — the whiskered init/kill re-interleaving remains the
  separate arc `zxjEmptyRidesToWhiskeredIdentity` named.  The pieces are present;
  the full `wireCount` assembly is not wired. -/
def zxuHasGeneralIdentityAbsorb : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
