import FX1Poly.Polygraph.Omega.ZXPhaseFree.TransvectionRide

/-! # Polygraph/Omega/ZXPhaseFree/AbsorptionInduction — THE ABSORPTION ASSEMBLY:
the induction is closed, the residual is exactly four cell-level statements

The r12 round proved the generator transport
(`zxvGeneratorTransportHolds : zxwGeneratorTransportStatement`), leaving phase-free
completeness hanging on exactly `zxwAbsorptionStatement`.  This round closes THE
INDUCTION SKELETON of that statement — the layer recursion, the layer-to-cell
fission, the identity-layer strip, and the transport re-canonicalization are all
PROVED — and reduces the whole absorption to FOUR named cell-level residuals:

* (i)   THE LAYER RECURSION (`zxbAbsorptionGo` / `zxbAbsorptionOfResiduals`):
  induction on the layer list; each new head layer is lifted over the absorbed
  tail (`zxwLiftConv`), absorbed by the layer-step, and the resulting generator
  list is RE-CANONICALIZED to the diagram's own denotation through the r12
  transport — the span equality needed by the transport comes FOR FREE from
  `zxwConvSpanEqB` soundness of the conversion built so far, so no composite
  matrix is ever computed syntactically.
* (ii)  THE LAYER-TO-CELL FISSION (`zxbPaddedLayerAbsorb`): one `splitLayer`
  window per cell peels the layer `wires(p) ++ (cell :: rest)` into the whiskered
  single cell over the peeled remainder; the recursion absorbs the remainder
  first, then the cell fires on the fresh normal form.  The all-wire remainder
  case is closed by THE IDENTITY-LAYER STRIP (`zxbWireLayerStrip`, the
  `splitLayer []` move read backwards) — PROVED, not a residual.
* (iii) THE WIRE CELL IS ABSORBED UNCONDITIONALLY (`zxbWireCellAbsorb`): the
  whiskered wire cell is the identity layer, stripped against the normal form's
  init layer; fired at a literal instance (`zxbWireAbsorbFire`).
* (iv)  THE FOUR RESIDUALS (owner false, honest walls): `zxbZSpiderAbsorbStatement`,
  `zxbXSpiderAbsorbStatement`, `zxbCrossingAbsorbStatement` (per-cell absorption
  into the normal form at every whisker position), and
  `zxbIdentityAbsorbStatement` (the empty diagram at every arity — n = 0 is the
  committed `zxwEmptyDiagramAbsorbed`, re-fired below).  Each residual carries a
  kernel span pin on a CONTENT instance proving the candidate statement is
  semantically sound.
* (v)   THE CONDITIONAL FLIP (`zxbCompletenessOfResiduals`,
  `zxbDecisionOfResiduals`): the four residuals imply `zxwAbsorptionStatement`,
  hence `zxwCompletenessStatement` through the committed assembly
  `zxwCompletenessOfAbsorptionAndTransport` fired on the r12 transport, hence the
  full span decision through `zxwDecisionUnderCompleteness`.

WALL NOTES (the burned attack shapes, per residual):

* CROSSING (`zxbCrossingAbsorbStatement`): the needed engine is a SINGLE-comb
  strand-crossing ride — a crossing between two adjacent STRANDS rides down one
  generator comb, swapping the two row bits, and dies in the kill layer (two
  adjacent `xSpider 1 0` collectors, killable by the `slideRight (xSpider 1 0)`
  instance).  The committed r11/r12 window layer (`zxtCrossWindowAt`,
  `zxtCrossRideDouble`) rides a crossing between the two CARRIERS of a ZIPPED
  DOUBLE comb — a genuinely different window family (the strand crossing sits
  BELOW the walking carrier, not between two carriers), so those windows do not
  instantiate; a fresh FF/FT/TF/TT window quadruple plus a ride clone is the
  route (ride skeleton reusable per the r12 route note).  Not attempted beyond
  shape analysis this round — budget went to the assembly.
* Z/X SPIDERS (`zxbZSpiderAbsorbStatement` / `zxbXSpiderAbsorbStatement`): the
  spider's legs enter the comb forks/merges of EVERY generator row incident to
  the touched strands; the absorption re-presents the generator list on the new
  boundary (Kissinger Lemma 3.3's per-generator case), needing the general-k
  fusion engines plus a carrier-staircase interaction family per leg — each
  colour is a ride-scale project on its own.
* IDENTITY (`zxbIdentityAbsorbStatement`): `boneZ` fired backwards materializes
  create/discard pairs from the empty diagram, but assembling the n interleaved
  `e_i ++ e_i` combs of `zxnNormalForm n n (zxpIdRows n)` needs the column
  routing of the crossing residual; blocked on the same wall.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Committed owner-false flags (`zxwAbsorptionIsProven`,
`zxwCompletenessIsProven`, `zxwHasFullDecision`) stay byte-intact in their home
file; nothing here supersedes them — the fresh content marker is the ASSEMBLY
(`zxbHasAbsorptionAssembly := true`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — THE IDENTITY-LAYER STRIP

The `splitLayer` window with an empty left block reads, backwards, as: an
all-wire layer sitting immediately above any layer deletes.  This is the
identity-layer strip the absorption bookkeeping needs at every wire cell. -/

/-- An all-wire layer above a nonempty tail strips (the `splitLayer []` move
read backwards, fired at the head of the tail). -/
theorem zxbWireLayerStrip (strandCount : Nat) (headLayer : List ZxpCell)
    (restLayers : List (List ZxpCell))
    (hHeadDom : zxpLayerDomArity headLayer = strandCount)
    (hRestWF : ZxpLayersWF (zxpLayerCodArity headLayer) restLayers) :
    ZxwConv
      { sourceArity := strandCount
        layers := zxpWireCells strandCount :: headLayer :: restLayers }
      { sourceArity := strandCount, layers := headLayer :: restLayers } := by
  have hBeforeCod : zxpLayersCodArity strandCount ([] : List (List ZxpCell))
      = zxpLayerDomArity ([] : List ZxpCell) + zxpLayerDomArity headLayer := by
    show strandCount = 0 + zxpLayerDomArity headLayer
    rw [Nat.zero_add, hHeadDom]
  have hAfterWF : ZxpLayersWF
      (zxpDiagramCodArity
        { sourceArity := zxpLayerDomArity ([] : List ZxpCell)
            + zxpLayerDomArity headLayer
          layers := [zxpCatCells [] headLayer] })
      restLayers := by
    show ZxpLayersWF (zxpLayerCodArity headLayer) restLayers
    exact hRestWF
  have hStep := zxwStepConv strandCount [] restLayers
    (ZxwWindowMove.base (ZxeWindowMove.base (ZxrWindowMove.seed
      (ZxpWindowMove.splitLayer [] headLayer))))
    (ZxpLayersWF.nil strandCount) hBeforeCod hAfterWF
  have hShaped : ZxwConv
      { sourceArity := strandCount, layers := headLayer :: restLayers }
      { sourceArity := strandCount
        layers := zxpWireCells (zxpLayerDomArity headLayer)
          :: headLayer :: restLayers } := hStep
  rw [hHeadDom] at hShaped
  exact ZxwConv.symm hShaped

/-! ## Stage 1 — the four named cell-level residuals

Each statement: a single whiskered cell above the normal form of some generator
list converts to the normal form of SOME generator list on the new boundary.
Boundary widths are passed with explicit equations so consumers can feed any
associativity shape. -/

/-- THE Z-SPIDER RESIDUAL (owner false): a whiskered Z-spider absorbs into the
normal form below it, at every arity pair and whisker position. -/
def zxbZSpiderAbsorbStatement : Prop :=
  (topLegCount botLegCount leftWires rightWires codWidth entryWidth exitWidth
      : Nat) ->
  leftWires + (botLegCount + rightWires) = entryWidth ->
  leftWires + (topLegCount + rightWires) = exitWidth ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth (entryWidth + codWidth) generatorRows ->
  Exists fun absorbedRows =>
    And (ZxpAllWidth (exitWidth + codWidth) absorbedRows)
      (ZxwConv
        { sourceArity := exitWidth
          layers := zxpWhiskerLayer leftWires rightWires
              [ZxpCell.zSpider topLegCount botLegCount]
            :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
        (zxnNormalForm exitWidth codWidth absorbedRows))

/-- THE X-SPIDER RESIDUAL (owner false): the colour mirror. -/
def zxbXSpiderAbsorbStatement : Prop :=
  (topLegCount botLegCount leftWires rightWires codWidth entryWidth exitWidth
      : Nat) ->
  leftWires + (botLegCount + rightWires) = entryWidth ->
  leftWires + (topLegCount + rightWires) = exitWidth ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth (entryWidth + codWidth) generatorRows ->
  Exists fun absorbedRows =>
    And (ZxpAllWidth (exitWidth + codWidth) absorbedRows)
      (ZxwConv
        { sourceArity := exitWidth
          layers := zxpWhiskerLayer leftWires rightWires
              [ZxpCell.xSpider topLegCount botLegCount]
            :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
        (zxnNormalForm exitWidth codWidth absorbedRows))

/-- THE CROSSING RESIDUAL (owner false): a whiskered strand crossing absorbs
into the normal form below it (the single-comb strand-crossing ride — see the
wall note in the file header). -/
def zxbCrossingAbsorbStatement : Prop :=
  (leftWires rightWires codWidth entryWidth exitWidth : Nat) ->
  leftWires + (2 + rightWires) = entryWidth ->
  leftWires + (2 + rightWires) = exitWidth ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth (entryWidth + codWidth) generatorRows ->
  Exists fun absorbedRows =>
    And (ZxpAllWidth (exitWidth + codWidth) absorbedRows)
      (ZxwConv
        { sourceArity := exitWidth
          layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]
            :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
        (zxnNormalForm exitWidth codWidth absorbedRows))

/-- THE IDENTITY RESIDUAL (owner false): the empty diagram at every arity
converts to the normal form of its own denotation (the base case of the layer
recursion; `wireCount = 0` is the committed `zxwEmptyDiagramAbsorbed`). -/
def zxbIdentityAbsorbStatement : Prop :=
  (wireCount : Nat) ->
  ZxwConv { sourceArity := wireCount, layers := [] }
    (zxnNormalForm wireCount wireCount
      (zxpDiagramDenote { sourceArity := wireCount, layers := [] }))

/-- THE UNIFIED CELL RESIDUAL: one statement quantified over the cell — the
exact per-cell interface the layer fission consumes. -/
def zxbCellAbsorbStatement : Prop :=
  (theCell : ZxpCell) ->
  (leftWires rightWires codWidth entryWidth exitWidth : Nat) ->
  leftWires + (zxpCellCodArity theCell + rightWires) = entryWidth ->
  leftWires + (zxpCellDomArity theCell + rightWires) = exitWidth ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth (entryWidth + codWidth) generatorRows ->
  Exists fun absorbedRows =>
    And (ZxpAllWidth (exitWidth + codWidth) absorbedRows)
      (ZxwConv
        { sourceArity := exitWidth
          layers := zxpWhiskerLayer leftWires rightWires [theCell]
            :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
        (zxnNormalForm exitWidth codWidth absorbedRows))

/-! ## Stage 2 — THE WIRE CELL IS ABSORBED (proved, not a residual) -/

/-- A whiskered wire cell above a normal form strips away: the whisker of one
wire IS the identity layer, deleted against the init layer. -/
theorem zxbWireCellAbsorb (leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAllRows : ZxpAllWidth ((leftWires + (1 + rightWires)) + codWidth)
      generatorRows) :
    ZxwConv
      { sourceArity := leftWires + (1 + rightWires)
        layers := zxpWhiskerLayer leftWires rightWires [ZxpCell.wire]
          :: (zxnNormalForm (leftWires + (1 + rightWires)) codWidth
              generatorRows).layers }
      (zxnNormalForm (leftWires + (1 + rightWires)) codWidth generatorRows) := by
  have hWireShape : zxpWhiskerLayer leftWires rightWires [ZxpCell.wire]
      = zxpWireCells (leftWires + (1 + rightWires)) := by
    have hCat := zxnWireCellsCat leftWires (rightWires + 1)
    have hIndexEq : leftWires + (rightWires + 1) = leftWires + (1 + rightWires) :=
      congrArg (fun innerValue => leftWires + innerValue)
        (Nat.add_comm rightWires 1)
    exact hCat.trans (congrArg zxpWireCells hIndexEq)
  rw [hWireShape]
  have hNFWF := zxnNormalFormWF (leftWires + (1 + rightWires)) codWidth
    generatorRows hAllRows
  show ZxwConv
    { sourceArity := leftWires + (1 + rightWires)
      layers := zxpWireCells (leftWires + (1 + rightWires))
        :: zxnInitLayer (leftWires + (1 + rightWires)) codWidth
        :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (1 + rightWires)) codWidth] }
    { sourceArity := leftWires + (1 + rightWires)
      layers := zxnInitLayer (leftWires + (1 + rightWires)) codWidth
        :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (1 + rightWires)) codWidth] }
  refine zxbWireLayerStrip (leftWires + (1 + rightWires))
    (zxnInitLayer (leftWires + (1 + rightWires)) codWidth)
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (1 + rightWires)) codWidth]) ?_ ?_
  · exact zxnInitLayerDomArity (leftWires + (1 + rightWires)) codWidth
  · cases hNFWF with
    | cons _hInitDom hRestWF => exact hRestWF

/-! ## Stage 3 — the cell dispatch: the unified residual from the four kinds -/

/-- The unified cell residual follows from the three spider/crossing residuals;
the wire kind is discharged by the PROVEN strip. -/
theorem zxbCellAbsorbOfKinds (hZSpider : zxbZSpiderAbsorbStatement)
    (hXSpider : zxbXSpiderAbsorbStatement)
    (hCrossing : zxbCrossingAbsorbStatement) : zxbCellAbsorbStatement := by
  intro theCell leftWires rightWires codWidth entryWidth exitWidth hEntryEq
    hExitEq generatorRows hAllRows
  cases theCell with
  | zSpider topLegCount botLegCount =>
      exact hZSpider topLegCount botLegCount leftWires rightWires codWidth
        entryWidth exitWidth hEntryEq hExitEq generatorRows hAllRows
  | xSpider topLegCount botLegCount =>
      exact hXSpider topLegCount botLegCount leftWires rightWires codWidth
        entryWidth exitWidth hEntryEq hExitEq generatorRows hAllRows
  | wire =>
      subst hEntryEq
      subst hExitEq
      exact Exists.intro generatorRows (And.intro hAllRows
        (zxbWireCellAbsorb leftWires rightWires codWidth generatorRows hAllRows))
  | crossing =>
      exact hCrossing leftWires rightWires codWidth entryWidth exitWidth
        hEntryEq hExitEq generatorRows hAllRows

/-! ## Stage 4 — THE LAYER-TO-CELL FISSION (the layer step, proved from the
cell residual)

`zxbPaddedLayerAbsorb` runs on layers of shape `wires(p) ++ cells`, peeling one
cell per `splitLayer` window; the peeled remainder absorbs first (recursion),
the whiskered head cell fires on the fresh normal form. -/

theorem zxbPaddedLayerAbsorb (hCell : zxbCellAbsorbStatement) :
    (layerCells : List ZxpCell) ->
    (passWires codWidth entryWidth exitWidth : Nat) ->
    passWires + zxpLayerCodArity layerCells = entryWidth ->
    passWires + zxpLayerDomArity layerCells = exitWidth ->
    (generatorRows : List (List Bool)) ->
    ZxpAllWidth (entryWidth + codWidth) generatorRows ->
    Exists fun absorbedRows =>
      And (ZxpAllWidth (exitWidth + codWidth) absorbedRows)
        (ZxwConv
          { sourceArity := exitWidth
            layers := zxpCatCells (zxpWireCells passWires) layerCells
              :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
          (zxnNormalForm exitWidth codWidth absorbedRows))
  | [], passWires, codWidth, entryWidth, exitWidth, hEntryEq, hExitEq,
      generatorRows, hAllRows => by
      subst hEntryEq
      subst hExitEq
      refine Exists.intro generatorRows (And.intro hAllRows ?_)
      have hHeadWires : zxpCatCells (zxpWireCells passWires) ([] : List ZxpCell)
          = zxpWireCells passWires := zxnWireCellsCat passWires 0
      rw [hHeadWires]
      show ZxwConv
        { sourceArity := passWires
          layers := zxpWireCells passWires
            :: zxnInitLayer passWires codWidth
            :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
              [zxnKillLayer passWires codWidth] }
        { sourceArity := passWires
          layers := zxnInitLayer passWires codWidth
            :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
              [zxnKillLayer passWires codWidth] }
      have hNFWF := zxnNormalFormWF passWires codWidth generatorRows hAllRows
      refine zxbWireLayerStrip passWires (zxnInitLayer passWires codWidth)
        (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer passWires codWidth]) ?_ ?_
      · exact zxnInitLayerDomArity passWires codWidth
      · cases hNFWF with
        | cons _hInitDom hRestWF => exact hRestWF
  | headCell :: restCells, passWires, codWidth, entryWidth, exitWidth,
      hEntryEq, hExitEq, generatorRows, hAllRows => by
      -- arity bookkeeping for the split window
      have hCatDom : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passWires) [headCell])
          = passWires + zxpCellDomArity headCell := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        exact rfl
      have hCatCod : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passWires) [headCell])
          = passWires + zxpCellCodArity headCell := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        exact rfl
      have hBeforeCodSplit : zxpLayersCodArity exitWidth
          ([] : List (List ZxpCell))
          = zxpLayerDomArity (zxpCatCells (zxpWireCells passWires) [headCell])
            + zxpLayerDomArity restCells := by
        show exitWidth
          = zxpLayerDomArity (zxpCatCells (zxpWireCells passWires) [headCell])
            + zxpLayerDomArity restCells
        rw [hCatDom, <- hExitEq]
        exact (Nat.add_assoc passWires (zxpCellDomArity headCell)
          (zxpLayerDomArity restCells)).symm
      have hSplitLayerCod : zxpLayerCodArity
          (zxpCatCells (zxpCatCells (zxpWireCells passWires) [headCell])
            restCells)
          = entryWidth := by
        rw [zxpCatCellsCodArity, zxpCatCellsCodArity, zxpWireCellsCodArity,
          <- hEntryEq]
        exact Nat.add_assoc passWires (zxpCellCodArity headCell)
          (zxpLayerCodArity restCells)
      have hAfterWFSplit : ZxpLayersWF
          (zxpDiagramCodArity
            { sourceArity :=
                zxpLayerDomArity (zxpCatCells (zxpWireCells passWires) [headCell])
                  + zxpLayerDomArity restCells
              layers := [zxpCatCells
                (zxpCatCells (zxpWireCells passWires) [headCell]) restCells] })
          (zxnNormalForm entryWidth codWidth generatorRows).layers := by
        show ZxpLayersWF
          (zxpLayerCodArity
            (zxpCatCells (zxpCatCells (zxpWireCells passWires) [headCell])
              restCells))
          (zxnNormalForm entryWidth codWidth generatorRows).layers
        rw [hSplitLayerCod]
        exact zxnNormalFormWF entryWidth codWidth generatorRows hAllRows
      have hSplitStep := zxwStepConv exitWidth []
        (zxnNormalForm entryWidth codWidth generatorRows).layers
        (ZxwWindowMove.base (ZxeWindowMove.base (ZxrWindowMove.seed
          (ZxpWindowMove.splitLayer
            (zxpCatCells (zxpWireCells passWires) [headCell]) restCells))))
        (ZxpLayersWF.nil exitWidth) hBeforeCodSplit hAfterWFSplit
      have hShaped : ZxwConv
          { sourceArity := exitWidth
            layers := zxpCatCells
                (zxpCatCells (zxpWireCells passWires) [headCell]) restCells
              :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
          { sourceArity := exitWidth
            layers := zxpCatCells
                (zxpCatCells (zxpWireCells passWires) [headCell])
                (zxpWireCells (zxpLayerDomArity restCells))
              :: zxpCatCells
                  (zxpWireCells (zxpLayerCodArity
                    (zxpCatCells (zxpWireCells passWires) [headCell])))
                  restCells
              :: (zxnNormalForm entryWidth codWidth generatorRows).layers } :=
        hSplitStep
      have hMergedShape : zxpCatCells
          (zxpCatCells (zxpWireCells passWires) [headCell]) restCells
          = zxpCatCells (zxpWireCells passWires) (headCell :: restCells) :=
        zxnCatCellsAssoc (zxpWireCells passWires) [headCell] restCells
      have hLOneShape : zxpCatCells
          (zxpCatCells (zxpWireCells passWires) [headCell])
          (zxpWireCells (zxpLayerDomArity restCells))
          = zxpWhiskerLayer passWires (zxpLayerDomArity restCells) [headCell] :=
        zxnCatCellsAssoc (zxpWireCells passWires) [headCell]
          (zxpWireCells (zxpLayerDomArity restCells))
      rw [hMergedShape, hLOneShape, hCatCod] at hShaped
      -- the peeled remainder absorbs first (recursion on the cell list)
      have hRemainder := zxbPaddedLayerAbsorb hCell restCells
        (passWires + zxpCellCodArity headCell) codWidth entryWidth
        ((passWires + zxpCellCodArity headCell) + zxpLayerDomArity restCells)
        ((Nat.add_assoc passWires (zxpCellCodArity headCell)
          (zxpLayerCodArity restCells)).trans hEntryEq)
        rfl generatorRows hAllRows
      obtain ⟨midRows, hMidAll, hMidConv⟩ := hRemainder
      -- lift the remainder absorption under the whiskered head cell
      have hLOneDom : zxpLayerDomArity
          (zxpWhiskerLayer passWires (zxpLayerDomArity restCells) [headCell])
          = exitWidth := by
        rw [zxpWhiskerLayerDomArity]
        exact hExitEq
      have hLOneCod : zxpLayersCodArity exitWidth
          [zxpWhiskerLayer passWires (zxpLayerDomArity restCells) [headCell]]
          = (passWires + zxpCellCodArity headCell)
            + zxpLayerDomArity restCells := by
        show zxpLayerCodArity
            (zxpWhiskerLayer passWires (zxpLayerDomArity restCells) [headCell])
          = (passWires + zxpCellCodArity headCell) + zxpLayerDomArity restCells
        rw [zxpWhiskerLayerCodArity]
        exact (Nat.add_assoc passWires (zxpCellCodArity headCell)
          (zxpLayerDomArity restCells)).symm
      have hLifted := zxwLiftConv exitWidth
        [zxpWhiskerLayer passWires (zxpLayerDomArity restCells) [headCell]]
        [] hMidConv
        (ZxpLayersWF.cons hLOneDom (ZxpLayersWF.nil _))
        hLOneCod (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLifted
      have hLiftedShaped : ZxwConv
          { sourceArity := exitWidth
            layers := zxpWhiskerLayer passWires (zxpLayerDomArity restCells)
                [headCell]
              :: zxpCatCells
                  (zxpWireCells (passWires + zxpCellCodArity headCell))
                  restCells
              :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
          { sourceArity := exitWidth
            layers := zxpWhiskerLayer passWires (zxpLayerDomArity restCells)
                [headCell]
              :: (zxnNormalForm
                  ((passWires + zxpCellCodArity headCell)
                    + zxpLayerDomArity restCells)
                  codWidth midRows).layers } := hLifted
      -- the head cell fires on the fresh normal form
      have hHeadStep := hCell headCell passWires (zxpLayerDomArity restCells)
        codWidth
        ((passWires + zxpCellCodArity headCell) + zxpLayerDomArity restCells)
        exitWidth
        (Nat.add_assoc passWires (zxpCellCodArity headCell)
          (zxpLayerDomArity restCells)).symm
        hExitEq midRows hMidAll
      obtain ⟨finalRows, hFinalAll, hFinalConv⟩ := hHeadStep
      refine Exists.intro finalRows (And.intro hFinalAll ?_)
      exact ZxwConv.trans hShaped (ZxwConv.trans hLiftedShaped hFinalConv)

/-- THE LAYER STEP packaged at plain layers (`passWires = 0`): any layer above
a normal form absorbs, given the cell residual. -/
theorem zxbLayerAbsorbOfCellAbsorb (hCell : zxbCellAbsorbStatement)
    (entryLayer : List ZxpCell) (codWidth entryWidth exitWidth : Nat)
    (hEntryEq : zxpLayerCodArity entryLayer = entryWidth)
    (hExitEq : zxpLayerDomArity entryLayer = exitWidth)
    (generatorRows : List (List Bool))
    (hAllRows : ZxpAllWidth (entryWidth + codWidth) generatorRows) :
    Exists fun absorbedRows =>
      And (ZxpAllWidth (exitWidth + codWidth) absorbedRows)
        (ZxwConv
          { sourceArity := exitWidth
            layers := entryLayer
              :: (zxnNormalForm entryWidth codWidth generatorRows).layers }
          (zxnNormalForm exitWidth codWidth absorbedRows)) :=
  zxbPaddedLayerAbsorb hCell entryLayer 0 codWidth entryWidth exitWidth
    ((Nat.zero_add (zxpLayerCodArity entryLayer)).trans hEntryEq)
    ((Nat.zero_add (zxpLayerDomArity entryLayer)).trans hExitEq)
    generatorRows hAllRows

/-! ## Stage 5 — THE LAYER RECURSION (the absorption induction, proved from
the cell and identity residuals)

Per layer: lift the absorbed tail, fire the layer step, then RE-CANONICALIZE
the produced generator list to the diagram's own denotation through the r12
transport — the span equality comes from `zxwConvSpanEqB` on the conversion
built so far, so the composite matrix is never computed syntactically. -/

theorem zxbAbsorptionGo (hCell : zxbCellAbsorbStatement)
    (hIdentity : zxbIdentityAbsorbStatement) :
    (layerList : List (List ZxpCell)) -> (sourceWidth : Nat) ->
    ZxpLayersWF sourceWidth layerList ->
    ZxwConv { sourceArity := sourceWidth, layers := layerList }
      (zxnNormalForm sourceWidth (zxpLayersCodArity sourceWidth layerList)
        (zxpLayersDenote sourceWidth layerList))
  | [], sourceWidth, _hWF => hIdentity sourceWidth
  | headLayer :: restLayers, sourceWidth, hWF => by
      cases hWF with
      | cons hDom hRest =>
          -- the absorbed tail, lifted under the head layer
          have hRestConv := zxbAbsorptionGo hCell hIdentity restLayers
            (zxpLayerCodArity headLayer) hRest
          have hLiftRaw := zxwLiftConv sourceWidth [headLayer] [] hRestConv
            (ZxpLayersWF.cons hDom (ZxpLayersWF.nil _)) rfl
            (ZxpLayersWF.nil _)
          rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLiftRaw
          have hLiftShaped : ZxwConv
              { sourceArity := sourceWidth, layers := headLayer :: restLayers }
              { sourceArity := sourceWidth
                layers := headLayer
                  :: (zxnNormalForm (zxpLayerCodArity headLayer)
                      (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
                      (zxpLayersDenote (zxpLayerCodArity headLayer) restLayers)
                    ).layers } := hLiftRaw
          -- the layer step
          have hRestDenoteAll : ZxpAllWidth
              (zxpLayerCodArity headLayer
                + zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
              (zxpLayersDenote (zxpLayerCodArity headLayer) restLayers) :=
            zxpLayersDenoteWidth restLayers hRest
          have hPadded := zxbPaddedLayerAbsorb hCell headLayer 0
            (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
            (zxpLayerCodArity headLayer) sourceWidth
            (Nat.zero_add (zxpLayerCodArity headLayer))
            ((Nat.zero_add (zxpLayerDomArity headLayer)).trans hDom)
            (zxpLayersDenote (zxpLayerCodArity headLayer) restLayers)
            hRestDenoteAll
          obtain ⟨stepRows, hStepAll, hStepConv⟩ := hPadded
          have hToNF := ZxwConv.trans hLiftShaped hStepConv
          -- re-canonicalize through the r12 transport
          have hDiagWF : ZxpLayersWF sourceWidth (headLayer :: restLayers) :=
            ZxpLayersWF.cons hDom hRest
          have hDenoteAll : ZxpAllWidth
              (sourceWidth
                + zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
              (zxpLayersDenote sourceWidth (headLayer :: restLayers)) :=
            zxpLayersDenoteWidth (headLayer :: restLayers) hDiagWF
          have hStepNFWF := zxnNormalFormWF sourceWidth
            (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
            stepRows hStepAll
          have hStepNFDenoteAll : ZxpAllWidth
              (sourceWidth
                + zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
              (zxpDiagramDenote (zxnNormalForm sourceWidth
                (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
                stepRows)) :=
            zxpAllWidthCast
              (congrArg (fun innerValue => sourceWidth + innerValue)
                (zxnNormalFormCodArity sourceWidth
                  (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
                  stepRows hStepAll))
              (zxpDiagramDenoteWidth
                (zxnNormalForm sourceWidth
                  (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
                  stepRows)
                hStepNFWF)
          have hSpanConv := zxwConvSpanEqB hToNF
          have hDiagramToNFDenote : ZxpRelEquiv sourceWidth
              (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
              (zxpLayersDenote sourceWidth (headLayer :: restLayers))
              (zxpDiagramDenote (zxnNormalForm sourceWidth
                (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
                stepRows)) :=
            zxpRelEquivOfSpanEqB hDenoteAll hStepNFDenoteAll hSpanConv
          have hNFDenotes := zxnNormalFormDenotes sourceWidth
            (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
            stepRows hStepAll
          have hStepRowsToDenote : ZxpRelEquiv sourceWidth
              (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
              stepRows (zxpLayersDenote sourceWidth (headLayer :: restLayers)) :=
            zxpRelEquivSymm (zxpRelEquivTrans hDiagramToNFDenote hNFDenotes)
          have hSpanStep : zxpSpanEqB stepRows
              (zxpLayersDenote sourceWidth (headLayer :: restLayers)) = true :=
            zxpSpanEqBOfRelEquiv hStepAll hDenoteAll hStepRowsToDenote
          have hTransport := zxvGeneratorTransportHolds sourceWidth
            (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
            stepRows (zxpLayersDenote sourceWidth (headLayer :: restLayers))
            hStepAll hDenoteAll hSpanStep
          exact ZxwConv.trans hToNF hTransport

/-- THE ABSORPTION ASSEMBLY: the four cell-level residuals imply the full
committed absorption statement. -/
theorem zxbAbsorptionOfResiduals (hZSpider : zxbZSpiderAbsorbStatement)
    (hXSpider : zxbXSpiderAbsorbStatement)
    (hCrossing : zxbCrossingAbsorbStatement)
    (hIdentity : zxbIdentityAbsorbStatement) : zxwAbsorptionStatement := by
  intro diagram hWF
  cases diagram with
  | mk sourceWidth layerList =>
      exact zxbAbsorptionGo (zxbCellAbsorbOfKinds hZSpider hXSpider hCrossing)
        hIdentity layerList sourceWidth hWF

/-! ## Stage 6 — THE CONDITIONAL FLIP -/

/-- COMPLETENESS FROM THE RESIDUALS: the four cell-level statements imply the
full committed completeness statement — the committed conditional assembly
fired on the r12 transport and this round's absorption assembly. -/
theorem zxbCompletenessOfResiduals (hZSpider : zxbZSpiderAbsorbStatement)
    (hXSpider : zxbXSpiderAbsorbStatement)
    (hCrossing : zxbCrossingAbsorbStatement)
    (hIdentity : zxbIdentityAbsorbStatement) : zxwCompletenessStatement :=
  zxwCompletenessOfAbsorptionAndTransport
    (zxbAbsorptionOfResiduals hZSpider hXSpider hCrossing hIdentity)
    zxvGeneratorTransportHolds

/-- THE CONDITIONAL DECISION: under the four residuals, `ZxwConv`
convertibility of boundary-matched well-formed diagrams IS the kernel span
decision. -/
theorem zxbDecisionOfResiduals (hZSpider : zxbZSpiderAbsorbStatement)
    (hXSpider : zxbXSpiderAbsorbStatement)
    (hCrossing : zxbCrossingAbsorbStatement)
    (hIdentity : zxbIdentityAbsorbStatement)
    (firstDiagram secondDiagram : ZxpDiagram)
    (hFirstWF : ZxpDiagramWF firstDiagram)
    (hSecondWF : ZxpDiagramWF secondDiagram)
    (hSourceEq : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCodEq : zxpDiagramCodArity firstDiagram
      = zxpDiagramCodArity secondDiagram) :
    Iff (ZxwConv firstDiagram secondDiagram)
      (zxpSpanEqB (zxpDiagramDenote firstDiagram)
        (zxpDiagramDenote secondDiagram) = true) :=
  zxwDecisionUnderCompleteness
    (zxbCompletenessOfResiduals hZSpider hXSpider hCrossing hIdentity)
    firstDiagram secondDiagram hFirstWF hSecondWF hSourceEq hCodEq

/-! ## Stage 7 — fires and kernel pins -/

/-- Fire: the wire-cell absorption at a literal instance — the whiskered wire
above the identity normal form strips away. -/
theorem zxbWireAbsorbFire :
    ZxwConv
      { sourceArity := 1
        layers := zxpWhiskerLayer 0 0 [ZxpCell.wire]
          :: (zxnNormalForm 1 1 [[true, true]]).layers }
      (zxnNormalForm 1 1 [[true, true]]) :=
  zxbWireCellAbsorb 0 0 1 [[true, true]]
    (ZxpAllWidth.cons rfl ZxpAllWidth.nil)

/-- Kernel span pin for the wire fire. -/
theorem zxbWireAbsorbFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := zxpWhiskerLayer 0 0 [ZxpCell.wire]
            :: (zxnNormalForm 1 1 [[true, true]]).layers })
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, true]])) = true := rfl

/-- Fire: the identity-layer strip at a literal instance — an all-wire layer
above the identity normal form deletes. -/
theorem zxbWireLayerStripFire :
    ZxwConv
      { sourceArity := 2
        layers := zxpWireCells 2 :: (zxnNormalForm 2 0 [[true, true]]).layers }
      { sourceArity := 2, layers := (zxnNormalForm 2 0 [[true, true]]).layers } := by
  have hNFWF := zxnNormalFormWF 2 0 [[true, true]]
    (ZxpAllWidth.cons rfl ZxpAllWidth.nil)
  show ZxwConv
    { sourceArity := 2
      layers := zxpWireCells 2
        :: zxnInitLayer 2 0
        :: zxpCatLayers (zxnGeneratorBlockLayers [[true, true]])
          [zxnKillLayer 2 0] }
    { sourceArity := 2
      layers := zxnInitLayer 2 0
        :: zxpCatLayers (zxnGeneratorBlockLayers [[true, true]])
          [zxnKillLayer 2 0] }
  refine zxbWireLayerStrip 2 (zxnInitLayer 2 0)
    (zxpCatLayers (zxnGeneratorBlockLayers [[true, true]]) [zxnKillLayer 2 0])
    ?_ ?_
  · exact zxnInitLayerDomArity 2 0
  · cases hNFWF with
    | cons _hInitDom hRestWF => exact hRestWF

/-- The committed zero-arity base instance of the identity residual, re-fired
verbatim: the residual statement is inhabited at `wireCount = 0`. -/
theorem zxbIdentityAbsorbZeroFire :
    ZxwConv { sourceArity := 0, layers := [] }
      (zxnNormalForm 0 0
        (zxpDiagramDenote { sourceArity := 0, layers := [] })) :=
  zxwEmptyDiagramAbsorbed

/-- Kernel span pin: the identity residual is semantically sound at
`wireCount = 1` — the empty one-wire diagram and the identity normal form
denote the same span. -/
theorem zxbIdentityResidualSpanPin :
    zxpSpanEqB (zxpDiagramDenote { sourceArity := 1, layers := [] })
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, true]])) = true := rfl

/-- Kernel span pin: the crossing residual is semantically sound at a content
instance — the crossing above the equal-pair effect normal form denotes the
same span as the normal form itself (`absorbedRows = generatorRows` here). -/
theorem zxbCrossingResidualSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayer 0 0 [ZxpCell.crossing]
            :: (zxnNormalForm 2 0 [[true, true]]).layers })
      (zxpDiagramDenote (zxnNormalForm 2 0 [[true, true]])) = true := rfl

/-- Kernel span pin: the Z-spider residual is semantically sound at a content
instance — the fork above the full two-strand effect normal form denotes the
full one-strand effect. -/
theorem zxbZSpiderResidualSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := zxpWhiskerLayer 0 0 [ZxpCell.zSpider 1 2]
            :: (zxnNormalForm 2 0 [[true, false], [false, true]]).layers })
      (zxpDiagramDenote (zxnNormalForm 1 0 [[true]])) = true := rfl

/-- Kernel span pin: the X-spider residual is semantically sound at a content
instance — the merge above the full one-strand effect normal form denotes the
full two-strand effect. -/
theorem zxbXSpiderResidualSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayer 0 0 [ZxpCell.xSpider 2 1]
            :: (zxnNormalForm 1 0 [[true]]).layers })
      (zxpDiagramDenote (zxnNormalForm 2 0 [[true, false], [false, true]]))
      = true := rfl

/-- BURNED-ATTACK FIRE for the crossing wall, the kill-boundary sub-route made
concrete: a crossing whose two legs feed two adjacent kill collectors DIES —
right-first fission of the kill pair, the `slideRight (xSpider 1 0)` instance
kills the crossing, left-first refusion.  This is the boundary case of the
single-comb strand-crossing ride named in the wall note; the open part of the
crossing residual is the ride THROUGH the combs, not this death. -/
theorem zxbCrossingIntoKillPairFire :
    ZxwConv
      { sourceArity := 2, layers := [[ZxpCell.crossing], zxnKillLayer 2 0] }
      { sourceArity := 2, layers := [zxnKillLayer 2 0] } := by
  -- step 1 (backward right-first exchange under the crossing):
  -- [crossing],[x10,x10] ~ [crossing],[wire,x10],[x10]
  have hExchange := zxwStepConv 2 [[ZxpCell.crossing]] []
    (ZxwWindowMove.base (ZxeWindowMove.rightFirstExchange
      [ZxpCell.xSpider 1 0] [ZxpCell.xSpider 1 0]))
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  have hExchangeShaped : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 1 0], [ZxpCell.xSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.crossing],
          [ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] } := hExchange
  -- step 2 (the slide kills the crossing):
  -- [x10,wire],[x10] ~ [crossing],[wire,x10],[x10]
  have hSlide := zxwStepConv 2 [] [[ZxpCell.xSpider 1 0]]
    (ZxwWindowMove.slideRight (ZxpCell.xSpider 1 0))
    (ZxpLayersWF.nil _) rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hSlideShaped : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 1 0, ZxpCell.wire], [ZxpCell.xSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 1 0], [ZxpCell.xSpider 1 0]] } := hSlide
  -- step 3 (left-first refusion): [x10,x10] ~ [x10,wire],[x10]
  have hRefuse := zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
    (ZxrWindowMove.seed (ZxpWindowMove.splitLayer
      [ZxpCell.xSpider 1 0] [ZxpCell.xSpider 1 0]))))
  have hRefuseShaped : ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] }
      { sourceArity := 2
        layers := [[ZxpCell.xSpider 1 0, ZxpCell.wire], [ZxpCell.xSpider 1 0]] } :=
    hRefuse
  exact ZxwConv.trans (ZxwConv.symm hExchangeShaped)
    (ZxwConv.trans (ZxwConv.symm hSlideShaped) (ZxwConv.symm hRefuseShaped))

/-- Kernel span pin for the kill-boundary death fire. -/
theorem zxbCrossingIntoKillPairFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2, layers := [[ZxpCell.crossing], zxnKillLayer 2 0] })
      (zxpDiagramDenote { sourceArity := 2, layers := [zxnKillLayer 2 0] })
      = true := rfl

/-- Refutation fire: span-DISTINCT normal forms are NOT `ZxwConv`-convertible
(the refutation bridge is unconditional — no residual needed). -/
theorem zxbSpanDistinctNormalFormsNotConv :
    Not (ZxwConv (zxnNormalForm 1 1 [[true, true]]) (zxnNormalForm 1 1 [])) := by
  intro hConv
  have hTrue := zxwConvSpanEqB hConv
  have hFalse : zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, true]]))
      (zxpDiagramDenote (zxnNormalForm 1 1 [])) = false := rfl
  rw [hFalse] at hTrue
  exact Bool.noConfusion hTrue

/-! ## Stage 8 — the honest marker ledger -/

/-- CONTENT MARKER: THE ABSORPTION ASSEMBLY IS LIVE — the layer recursion, the
layer-to-cell fission, the identity-layer strip, the wire-cell absorption, and
the transport re-canonicalization are all machine-checked
(`zxbAbsorptionOfResiduals`), so `zxwAbsorptionStatement` — and with it the
completeness flip (`zxbCompletenessOfResiduals`) and the full decision
(`zxbDecisionOfResiduals`) — now hangs on exactly FOUR named cell-level
residuals: `zxbZSpiderAbsorbStatement`, `zxbXSpiderAbsorbStatement`,
`zxbCrossingAbsorbStatement`, `zxbIdentityAbsorbStatement`, each with a kernel
span pin certifying semantic soundness of the candidate statement. -/
def zxbHasAbsorptionAssembly : Bool := true

/-- OWNER MARKER (FALSE): the absorption statement itself did NOT flip this
round — the four cell-level residuals are open.  The committed owner
`zxwAbsorptionIsProven := false` stays byte-intact in its home file; this
marker re-records the same honest state after the assembly landed. -/
def zxbAbsorptionIsProven : Bool := false

/-- OWNER MARKER (FALSE): completeness over `ZxwConv` did NOT flip this round;
`zxbCompletenessOfResiduals` is the conditional assembly, not an inhabitant.
The committed owners (`zxwCompletenessIsProven := false`,
`zxwHasFullDecision := false`) stay byte-intact. -/
def zxbCompletenessIsProven : Bool := false

/-- OWNER MARKER (FALSE): no unconditional decision instance exists in this
development; `zxbDecisionOfResiduals` is conditional on the four residuals. -/
def zxbHasFullDecision : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
