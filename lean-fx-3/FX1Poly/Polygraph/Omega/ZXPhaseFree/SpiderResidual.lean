import FX1Poly.Polygraph.Omega.ZXPhaseFree.CrossingResidual

/-! # Polygraph/Omega/ZXPhaseFree/SpiderResidual — the whiskered-spider boundary
pass and the identity-spider corner: the two spider residuals reduced to one
named tail-death each

The r13 assembly (`AbsorptionInduction`) reduced phase-free completeness to four
cell-level residuals; r14 (`CrossingResidual`) closed the crossing residual modulo
one kill-death.  This round attacks the two SPIDER residuals
(`zxbZSpiderAbsorbStatement` / `zxbXSpiderAbsorbStatement`) — the last two of the
four — and reduces each to EXACTLY ONE named cell-level statement, the tail-death
`zxsZSpiderTailDeathStatement` / `zxsXSpiderTailDeathStatement`
(`zxsZSpiderAbsorbOfTailDeath` / `zxsXSpiderAbsorbOfTailDeath`):

* (i)   THE GENERIC WHISKERED-CELL PAST-INIT PASS (`zxsWhiskerCellPastInit`): a
  single whiskered cell above the init layer commutes below it — the init layer
  creates its zero states on the DISJOINT appended codomain strands, so the cell
  rides through unchanged (its right remainder widened by the codomain width),
  regardless of whether the cell preserves width.  One firing of the committed
  disjoint-block engine `zxwLayersPastRightLayer` with the zero-state block; the
  same brick that carried the crossing past init, generalized to any cell (Z, X,
  wire, crossing) so BOTH spider colours reuse it verbatim.
* (ii)  THE IDENTITY-SPIDER CORNER, UNCONDITIONAL (`zxsZIdentitySpiderAbsorb` /
  `zxsXIdentitySpiderAbsorb`): the degenerate one-in/one-out spider IS the
  identity wire (`ZxpRowTag.zIdentitySpider` / `xIdentitySpider`, Kissinger Fig. 1
  identity component); rewritten to the wire cell it strips against the init layer
  through the committed `zxbWireCellAbsorb`.  This INHABITS both spider residuals
  at `topLegCount = 1 = botLegCount` for every whisker position, arity, codomain
  width, and generator list — a genuine unconditional slice of each residual.
* (iii) THE TAIL-DEATH WALLS (owner false): the whiskered spider above the
  generator-block/kill CORE of the normal form (init already peeled by (i)) absorbs
  into SOME generator list on the exit boundary.  This is the whole width-changing
  spider-through-blocks-and-kill, reduced to a single named existential per colour,
  each carrying a kernel span pin certifying semantic soundness at a content
  instance where the width genuinely changes (`2 -> 1` for Z, `1 -> 2` for X).
* (iv)  THE CONDITIONAL FLIP (`zxsZSpiderAbsorbOfTailDeath` /
  `zxsXSpiderAbsorbOfTailDeath`): the tail-death implies the full residual — the
  spider rides past the init layer (i), then the tail-death fires on the core.  The
  shared plumbing is `zxsCellAbsorbStepOfTailDeath`, generic over the cell.

WALL NOTE (the remaining death, per colour): the tail-death is genuinely a
SUBSPACE operation, NOT the per-row column permutation that let the crossing fold
through its generator blocks.  Two attacks burned:

* (a) PER-BLOCK FOLD (the crossing-ride template `zxcGeneratorBlocksCrossRide`):
  a copy-spider `zSpider 1 2` forces its two bottom strands EQUAL, so it cannot
  commute past a conditional-xor block that treats them differently — kernel
  `#eval` confirms the blocks `[true, false]` and `[false, true]` ride to NO single
  transformed block (only the constant blocks `[true, true]`/`[false, false]` do).
  The absorbed rows depend GLOBALLY on the whole generator set through the kill
  layer (the differing-bit blocks collapse to the empty absorbed list `[]` only
  when the kill is present), so no fold over the block list exists; the intersection
  is a Gaussian elimination the strict-layer rewriter has no engine for.
* (b) SPIDER DECOMPOSITION into fork/merge plus the bialgebra/Frobenius algebra —
  the general-k fusion engines plus a carrier-staircase interaction family per leg
  (per the `AbsorptionInduction` header, "each colour is a ride-scale project on
  its own"); not attempted this round per the stall policy, budget went to the
  boundary pass and the identity corner.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Committed owner-false flags stay byte-intact in their home files; the
two spider residuals did NOT flip unconditionally
(`zxsZSpiderResidualIsClosed := false`, `zxsXSpiderResidualIsClosed := false`); the
fresh true content markers are the decompositions
(`zxsHasZSpiderDecomposition := true`, `zxsHasXSpiderDecomposition := true`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the generic whiskered-cell past-init pass -/

/-- THE PAST-INIT PASS: a whiskered cell above the init layer commutes below it —
the init layer creates its zero states on the disjoint appended codomain strands,
so the cell rides through unchanged, widening its right remainder by the codomain
width.  One firing of the disjoint-block engine with the zero-state block; works
for a width-CHANGING cell (the walk's top arity differs from its bottom arity). -/
theorem zxsWhiskerCellPastInit (cell : ZxpCell) (leftWires rightWires codWidth : Nat) :
    ZxwConv
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires [cell],
          zxnInitLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth] }
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := [zxnInitLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth,
          zxpWhiskerLayer leftWires (rightWires + codWidth) [cell]] } := by
  have hEngine := zxwOfZxeConv (zxwLayersPastRightLayer
    (zxnZeroStateCells codWidth)
    [zxpWhiskerLayer leftWires rightWires [cell]]
    (leftWires + (zxpCellDomArity cell + rightWires))
    (ZxpLayersWF.cons (zxpWhiskerLayerDomArity leftWires rightWires [cell])
      (ZxpLayersWF.nil _)))
  rw [zxnZeroStateCellsDomArity codWidth, Nat.add_zero, zxnZeroStateCellsCodArity codWidth,
    show zxpWhiskerLayers 0 codWidth [zxpWhiskerLayer leftWires rightWires [cell]]
        = [zxpWhiskerLayer leftWires (rightWires + codWidth) [cell]] from by
      show [zxpWhiskerLayer 0 codWidth (zxpWhiskerLayer leftWires rightWires [cell])] = _
      rw [zxnWhiskerLayerCompose 0 codWidth leftWires rightWires [cell], Nat.zero_add],
    zxpWhiskerLayersZero [zxpWhiskerLayer leftWires rightWires [cell]],
    show zxpLayersCodArity (leftWires + (zxpCellDomArity cell + rightWires))
          [zxpWhiskerLayer leftWires rightWires [cell]]
        = leftWires + (zxpCellCodArity cell + rightWires) from
      zxpWhiskerLayerCodArity leftWires rightWires [cell]] at hEngine
  exact ZxwConv.symm hEngine

/-! ## Stage 1 — the identity-spider corner (unconditional)

The one-in/one-out spider IS the identity wire; rewritten to the wire cell it
strips against the init layer through the committed wire-cell absorption. -/

/-- THE Z-IDENTITY-SPIDER ABSORB (unconditional): a whiskered `zSpider 1 1` above
the normal form absorbs, with `absorbedRows = generatorRows`.  The identity spider
rewrites to the wire cell (`zIdentitySpider` row), which strips against the init
layer (`zxbWireCellAbsorb`). -/
theorem zxsZIdentitySpiderAbsorb (leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (1 + rightWires)) + codWidth) generatorRows) :
    ZxwConv
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.zSpider 1 1]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers }
      (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows) := by
  have hRowLift : ZxwConv
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.zSpider 1 1]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers }
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.wire]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers } :=
    zxwConvLift (leftWires + (1 + rightWires)) leftWires rightWires []
      (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers
      (zxwOfZxpConv (zxpRowConv ZxpRowTag.zIdentitySpider))
      (ZxpLayersWF.nil _) rfl
      (zxnNormalFormWF (leftWires + (1 + rightWires)) codWidth generatorRows hAll)
  exact ZxwConv.trans hRowLift
    (zxbWireCellAbsorb leftWires rightWires codWidth generatorRows hAll)

/-- THE X-IDENTITY-SPIDER ABSORB (unconditional): the colour mirror — a whiskered
`xSpider 1 1` above the normal form absorbs, with `absorbedRows = generatorRows`
(`xIdentitySpider` row, then the wire strip). -/
theorem zxsXIdentitySpiderAbsorb (leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (1 + rightWires)) + codWidth) generatorRows) :
    ZxwConv
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.xSpider 1 1]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers }
      (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows) := by
  have hRowLift : ZxwConv
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.xSpider 1 1]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers }
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.wire]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers } :=
    zxwConvLift (leftWires + (1 + rightWires)) leftWires rightWires []
      (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows).layers
      (zxwOfZxpConv (zxpRowConv ZxpRowTag.xIdentitySpider))
      (ZxpLayersWF.nil _) rfl
      (zxnNormalFormWF (leftWires + (1 + rightWires)) codWidth generatorRows hAll)
  exact ZxwConv.trans hRowLift
    (zxbWireCellAbsorb leftWires rightWires codWidth generatorRows hAll)

/-! ## Stage 2 — the tail-death walls (owner false)

Each: a whiskered spider above the generator-block/kill CORE of the normal form
(init peeled) absorbs into SOME generator list on the exit boundary.  This is the
whole width-changing spider-through-blocks-and-kill — a subspace intersection, not
a per-row fold (see the file header's burned attacks). -/

/-- THE Z-SPIDER TAIL-DEATH (owner false): the whiskered copy-spider above the
generator-block/kill core absorbs into some exit-boundary generator list.  The
width changes from `botLegCount` to `topLegCount` on the middle band. -/
def zxsZSpiderTailDeathStatement : Prop :=
  (topLegCount botLegCount leftWires rightWires codWidth : Nat) ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows ->
  Exists fun absorbedRows =>
    And (ZxpAllWidth ((leftWires + (topLegCount + rightWires)) + codWidth) absorbedRows)
      (ZxwConv
        { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
          layers := zxpWhiskerLayer leftWires (rightWires + codWidth)
              [ZxpCell.zSpider topLegCount botLegCount]
            :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
                [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth] }
        { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
          layers := zxpCatLayers (zxnGeneratorBlockLayers absorbedRows)
              [zxnKillLayer (leftWires + (topLegCount + rightWires)) codWidth] })

/-- THE X-SPIDER TAIL-DEATH (owner false): the colour mirror. -/
def zxsXSpiderTailDeathStatement : Prop :=
  (topLegCount botLegCount leftWires rightWires codWidth : Nat) ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows ->
  Exists fun absorbedRows =>
    And (ZxpAllWidth ((leftWires + (topLegCount + rightWires)) + codWidth) absorbedRows)
      (ZxwConv
        { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
          layers := zxpWhiskerLayer leftWires (rightWires + codWidth)
              [ZxpCell.xSpider topLegCount botLegCount]
            :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
                [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth] }
        { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
          layers := zxpCatLayers (zxnGeneratorBlockLayers absorbedRows)
              [zxnKillLayer (leftWires + (topLegCount + rightWires)) codWidth] })

/-! ## Stage 3 — the conditional flip (the tail-death implies the residual)

The shared plumbing `zxsCellAbsorbStepOfTailDeath` rides the cell past the init
layer, then fires the supplied tail-death on the core. -/

/-- THE GENERIC ABSORB STEP: given the tail-death conversion for a specific cell,
the whiskered cell absorbs into the normal form of the absorbed rows.  Rides past
init (`zxsWhiskerCellPastInit`), then fires the supplied core conversion. -/
theorem zxsCellAbsorbStepOfTailDeath (cell : ZxpCell)
    (leftWires rightWires codWidth : Nat) (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (zxpCellCodArity cell + rightWires)) + codWidth)
      generatorRows)
    (absorbedRows : List (List Bool))
    (hTailConv : ZxwConv
      { sourceArity := (leftWires + (zxpCellDomArity cell + rightWires)) + codWidth
        layers := zxpWhiskerLayer leftWires (rightWires + codWidth) [cell]
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
              [zxnKillLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth] }
      { sourceArity := (leftWires + (zxpCellDomArity cell + rightWires)) + codWidth
        layers := zxpCatLayers (zxnGeneratorBlockLayers absorbedRows)
            [zxnKillLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth] }) :
    ZxwConv
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [cell]
          :: (zxnNormalForm (leftWires + (zxpCellCodArity cell + rightWires)) codWidth
              generatorRows).layers }
      (zxnNormalForm (leftWires + (zxpCellDomArity cell + rightWires)) codWidth
        absorbedRows) := by
  have hNFWF := zxnNormalFormWF (leftWires + (zxpCellCodArity cell + rightWires)) codWidth
    generatorRows hAll
  -- step 1: past-init lifted over the tail
  have hP1 := zxwLiftConv (leftWires + (zxpCellDomArity cell + rightWires)) []
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth])
    (zxsWhiskerCellPastInit cell leftWires rightWires codWidth)
    (ZxpLayersWF.nil _) rfl
    (by cases hNFWF with | cons _hInitDom hTail => exact hTail)
  have hP1Shaped : ZxwConv
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [cell]
          :: zxnInitLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
              [zxnKillLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth] }
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := zxnInitLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth
          :: zxpWhiskerLayer leftWires (rightWires + codWidth) [cell]
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
              [zxnKillLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth] } := hP1
  -- step 2: lift init(exit) over the tail-death core conversion
  have hP2 := zxwLiftConv (leftWires + (zxpCellDomArity cell + rightWires))
    [zxnInitLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth] [] hTailConv
    (ZxpLayersWF.cons
      (zxnInitLayerDomArity (leftWires + (zxpCellDomArity cell + rightWires)) codWidth)
      (ZxpLayersWF.nil _))
    (zxnInitLayerCodArity (leftWires + (zxpCellDomArity cell + rightWires)) codWidth)
    (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hP2
  have hP2Shaped : ZxwConv
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := zxnInitLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth
          :: zxpWhiskerLayer leftWires (rightWires + codWidth) [cell]
          :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
              [zxnKillLayer (leftWires + (zxpCellCodArity cell + rightWires)) codWidth] }
      { sourceArity := leftWires + (zxpCellDomArity cell + rightWires)
        layers := zxnInitLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth
          :: zxpCatLayers (zxnGeneratorBlockLayers absorbedRows)
              [zxnKillLayer (leftWires + (zxpCellDomArity cell + rightWires)) codWidth] } := hP2
  exact ZxwConv.trans hP1Shaped hP2Shaped

/-- THE Z-SPIDER RESIDUAL FROM THE TAIL-DEATH: the Z tail-death implies the full
committed Z-spider residual — the spider rides past init, then dies in the core. -/
theorem zxsZSpiderAbsorbOfTailDeath (hTail : zxsZSpiderTailDeathStatement) :
    zxbZSpiderAbsorbStatement := by
  intro topLegCount botLegCount leftWires rightWires codWidth entryWidth exitWidth
    hEntryEq hExitEq generatorRows hAll
  subst hEntryEq
  subst hExitEq
  obtain ⟨absorbedRows, hAbsorbedAll, hTailConv⟩ :=
    hTail topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll
  exact Exists.intro absorbedRows (And.intro hAbsorbedAll
    (zxsCellAbsorbStepOfTailDeath (ZxpCell.zSpider topLegCount botLegCount)
      leftWires rightWires codWidth generatorRows hAll absorbedRows hTailConv))

/-- THE X-SPIDER RESIDUAL FROM THE TAIL-DEATH: the colour mirror. -/
theorem zxsXSpiderAbsorbOfTailDeath (hTail : zxsXSpiderTailDeathStatement) :
    zxbXSpiderAbsorbStatement := by
  intro topLegCount botLegCount leftWires rightWires codWidth entryWidth exitWidth
    hEntryEq hExitEq generatorRows hAll
  subst hEntryEq
  subst hExitEq
  obtain ⟨absorbedRows, hAbsorbedAll, hTailConv⟩ :=
    hTail topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll
  exact Exists.intro absorbedRows (And.intro hAbsorbedAll
    (zxsCellAbsorbStepOfTailDeath (ZxpCell.xSpider topLegCount botLegCount)
      leftWires rightWires codWidth generatorRows hAll absorbedRows hTailConv))

/-! ## Stage 4 — fires, kernel span pins, and the refutation -/

/-- Fire: the past-init pass at a Z-spider instance — a `zSpider 1 2` above the
one-codomain-wire init layer widens past it. -/
theorem zxsWhiskerCellPastInitZFire :
    ZxwConv
      { sourceArity := 1
        layers := [zxpWhiskerLayer 0 0 [ZxpCell.zSpider 1 2], zxnInitLayer 2 1] }
      { sourceArity := 1
        layers := [zxnInitLayer 1 1, zxpWhiskerLayer 0 1 [ZxpCell.zSpider 1 2]] } :=
  zxsWhiskerCellPastInit (ZxpCell.zSpider 1 2) 0 0 1

/-- Kernel span pin for the Z past-init fire. -/
theorem zxsWhiskerCellPastInitZFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := [zxpWhiskerLayer 0 0 [ZxpCell.zSpider 1 2], zxnInitLayer 2 1] })
      (zxpDiagramDenote
        { sourceArity := 1
          layers := [zxnInitLayer 1 1, zxpWhiskerLayer 0 1 [ZxpCell.zSpider 1 2]] })
      = true := rfl

/-- Fire: the past-init pass at an X-spider instance — an `xSpider 2 1` above the
one-codomain-wire init layer widens past it. -/
theorem zxsWhiskerCellPastInitXFire :
    ZxwConv
      { sourceArity := 2
        layers := [zxpWhiskerLayer 0 0 [ZxpCell.xSpider 2 1], zxnInitLayer 1 1] }
      { sourceArity := 2
        layers := [zxnInitLayer 2 1, zxpWhiskerLayer 0 1 [ZxpCell.xSpider 2 1]] } :=
  zxsWhiskerCellPastInit (ZxpCell.xSpider 2 1) 0 0 1

/-- Fire: the Z-identity-spider absorb at a content instance — a whiskered
`zSpider 1 1` above a two-row, one-codomain-wire normal form strips away. -/
theorem zxsZIdentitySpiderAbsorbFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 1]
          :: (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]).layers }
      (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]) :=
  zxsZIdentitySpiderAbsorb 1 0 1 [[true, false, true], [false, true, false]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-- Kernel span pin for the Z-identity-spider absorb fire. -/
theorem zxsZIdentitySpiderAbsorbFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayer 1 0 [ZxpCell.zSpider 1 1]
            :: (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]).layers })
      (zxpDiagramDenote (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]))
      = true := rfl

/-- Fire: the X-identity-spider absorb at a content instance — the colour mirror. -/
theorem zxsXIdentitySpiderAbsorbFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpWhiskerLayer 1 0 [ZxpCell.xSpider 1 1]
          :: (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]).layers }
      (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]) :=
  zxsXIdentitySpiderAbsorb 1 0 1 [[true, false, true], [false, true, false]]
    (ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil))

/-- Kernel span pin for the X-identity-spider absorb fire. -/
theorem zxsXIdentitySpiderAbsorbFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayer 1 0 [ZxpCell.xSpider 1 1]
            :: (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]).layers })
      (zxpDiagramDenote (zxnNormalForm 2 1 [[true, false, true], [false, true, false]]))
      = true := rfl

/-- Kernel span pin: the Z-spider tail-death is semantically sound at a content
instance where the width genuinely changes (`botLegCount = 2` down to
`topLegCount = 1`) — the copy-spider above the two-strand full-effect core
(`generatorRows = [[1,0],[0,1]]`) denotes the same span as the one-strand
full-effect core (`absorbedRows = [[1]]`).  This certifies the existential candidate
the walled `zxsZSpiderTailDeathStatement` needs. -/
theorem zxsZSpiderTailDeathSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := zxpWhiskerLayer 0 0 [ZxpCell.zSpider 1 2]
            :: zxpCatLayers (zxnGeneratorBlockLayers [[true, false], [false, true]])
                [zxnKillLayer 2 0] })
      (zxpDiagramDenote
        { sourceArity := 1
          layers := zxpCatLayers (zxnGeneratorBlockLayers [[true]]) [zxnKillLayer 1 0] })
      = true := rfl

/-- Kernel span pin: the X-spider tail-death is semantically sound at a content
instance where the width genuinely changes (`botLegCount = 1` up to
`topLegCount = 2`) — the merge-spider above the one-strand full-effect core
(`generatorRows = [[1]]`) denotes the same span as the two-strand full-effect core
(`absorbedRows = [[1,0],[0,1]]`). -/
theorem zxsXSpiderTailDeathSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayer 0 0 [ZxpCell.xSpider 2 1]
            :: zxpCatLayers (zxnGeneratorBlockLayers [[true]]) [zxnKillLayer 1 0] })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpCatLayers (zxnGeneratorBlockLayers [[true, false], [false, true]])
              [zxnKillLayer 2 0] })
      = true := rfl

/-- Refutation fire: span-DISTINCT normal forms are NOT `ZxwConv`-convertible —
the full one-strand effect and the trivial one-strand effect separate, so a spider
absorption that changed the span could never be a conversion (the tail-death carries
genuine content, its candidate absorbed rows are not free). -/
theorem zxsSpiderRideSpanDistinctNotConv :
    Not (ZxwConv (zxnNormalForm 1 0 [[true]]) (zxnNormalForm 1 0 [])) := by
  intro hConv
  have hTrue := zxwConvSpanEqB hConv
  have hFalse : zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm 1 0 [[true]]))
      (zxpDiagramDenote (zxnNormalForm 1 0 [])) = false := rfl
  rw [hFalse] at hTrue
  exact Bool.noConfusion hTrue

/-! ## Stage 5 — the honest marker ledger -/

/-- CONTENT MARKER: THE Z-SPIDER DECOMPOSITION IS LIVE — the generic past-init pass
(`zxsWhiskerCellPastInit`) and the unconditional identity-spider corner
(`zxsZIdentitySpiderAbsorb`, inhabiting the residual at `1 -> 1`) are machine-checked
zero-axiom, and the full Z-spider residual `zxbZSpiderAbsorbStatement` is PROVED
modulo exactly one named cell-level statement, the tail-death
`zxsZSpiderTailDeathStatement` (`zxsZSpiderAbsorbOfTailDeath`), with a kernel span
pin certifying semantic soundness at a width-changing content instance. -/
def zxsHasZSpiderDecomposition : Bool := true

/-- CONTENT MARKER: THE X-SPIDER DECOMPOSITION IS LIVE — the colour mirror
(`zxsXIdentitySpiderAbsorb`, `zxsXSpiderAbsorbOfTailDeath`,
`zxsXSpiderTailDeathSpanPin`). -/
def zxsHasXSpiderDecomposition : Bool := true

/-- OWNER MARKER (FALSE): the Z-spider residual did NOT flip unconditionally this
round — `zxsZSpiderTailDeathStatement` (the spider-through-blocks-and-kill subspace
intersection) remains open, so `zxsZSpiderAbsorbOfTailDeath` is a conditional
assembly, not an inhabitant of `zxbZSpiderAbsorbStatement`.  The committed
owner-false flags in `AbsorptionInduction` stay byte-intact. -/
def zxsZSpiderResidualIsClosed : Bool := false

/-- OWNER MARKER (FALSE): the X-spider residual did NOT flip unconditionally this
round — `zxsXSpiderTailDeathStatement` remains open. -/
def zxsXSpiderResidualIsClosed : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
