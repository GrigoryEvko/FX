import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellLift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FramedSpineChain

/-! # mode-3 keystone — the RIEHL–VERITY Prop 3.3.4 middle-four WIDTH-REDUCTION, as a
`SaturatedTwoCellConv`-valued STRUCTURAL recursion on the matched-pair width

Riehl–Verity ("The 2-category theory of quasi-categories", arXiv:1310.8279, Prop 3.3.4) presents the
walking-adjunction coherence word problem by a WIDTH induction: the width-`(r+1)` instance
`u^r f · η^(r+1) = (u^r · η^r u) f · η` is the width-`r` instance PLUS ONE triangle identity, so induction on
the matched-pair count `r` reduces every coherence to the single triangle.  This file ships that induction in FX,
against the shipped snake substrate — no `matchingOf` arc-readoff, no head-peel/tail-cancel.

## The FX image of the RV width index

The RV "width `r`" (count of matched cup·cap pairs) is, at the walking-adjunction seed, exactly the spine
`cupAtomCount = capAtomCount = r` (`GodementIndependence`), which is the `generatorCount`/2 the free relation cannot
drop but the saturated triangle can.  A right-nested `FramedSpineChain` readback whose head is a matched cup·cap
pair is the width-`(r+1)` chain; deleting that pair via the shipped `snakePrefixStraightens` (one triangle collapse
`cupFrame ⊟ capFrame ≈ id` + one `vcompAssoc` re-association) gives the width-`r` chain.  This is RV's "width-`r`
instance + one triangle · η" ON THE NOSE:

> RV `cup ⊟ (cap ⊟ tail) =[vcompAssoc] (cup ⊟ cap) ⊟ tail =[triangle] id ⊟ tail = tail`.

## What this file ships (each zero-axiom, structural on the matched-pair width)

  * ★ `spineAtomFrame` — the whiskered-generator readback frame of one spine atom (the exact
    `whiskerLeft ∘ whiskerRight ∘ gen` band `FramedSpineChain.readback` emits per `cons`).
  * ★ `framedChainConsConsReadback` (`rfl`) — the BRIDGE: the readback of a `cons cup (cons cap rest)` chain is
    DEFINITIONALLY the right-nested tower layer `cupFrame ⊟ (capFrame ⊟ rest.readback)`.  So the RV "width-`(r+1)`
    right-nested readback chain" IS a `MatchedSnakeTowerCell` layer — no coherence side conditions.
  * ★ `MatchedSnakeTowerCell` — the width-indexed matched-snake tower: `floor` (width 0 = the identity) and
    `layer` (a matched cup·cap frame pair, carrying its collapse witness, over an inner tower).  The `layer`
    constructor count IS the RV width `r`; the carrier returns to `basePath` after every pair (a genuine pair
    REMOVAL, never a head-peel with a tail-cancel obligation).
  * ★ `matchedSnakeTowerLayerStraightens` — the RV middle-four STEP: the width-`(r+1)` layer
    `cupFrame ⊟ (capFrame ⊟ inner) ≈ inner` (the width-`r` chain).  This is the shipped `snakePrefixStraightens`
    (triangle collapse + `vcompAssoc`) restated at the tower layer.
  * ★ `matchedSnakeTowerCell_collapses` — the RV Prop 3.3.4 INDUCTION: a matched-snake tower of ANY width
    collapses to the identity, by STRUCTURAL recursion on the tower (= on the matched-pair width `cupCount`), each
    step the middle-four move, base `refl` on the identity.  NO `WellFounded.fix`.
  * ★ `framedChainMatchedTowerCollapses` — the assembly: a `FramedSpineChain` whose readback is a matched tower
    reads back convertible to the identity, threading the `rfl` bridge.

## What this does NOT close (the honest residual — gates stay `false`)

The `layer.collapses` field is the per-pair TRIANGLE witness `cupFrame ⊟ capFrame ≈ id`.  Feeding it for a pair
LOCATED in a chain by reading the boundary matching `partnerIndexOf` (turning the decidable partner FACT into the
collapse WITNESS) is the standing open node — the spine-frame ↔ arc-partner lift (`CellStraightenStepInput`,
tracker #2185), NOT supplied here.  So this file ships the RV width-reduction MECHANISM (the middle-four step + the
width induction to the base) MODULO the partner witnesses each layer consumes; it does NOT build the tower FROM an
arbitrary chain, and `convOfMapEq` / `SaturatedMatchingCanonicalization` / the fib-3 gate flags stay `false`.  It
also does NOT touch the separately-open Godement/`SpineTraceEquiv` disjoint-support commutation companion
(Mazurkiewicz/Delpeuch–Vicary handed exchange), which is the SOUNDNESS-direction residual, distinct from this
COMPLETENESS-direction width reduction.

Raw Lean 4 + Init; the induction is STRUCTURAL on the `MatchedSnakeTowerCell` (matched-pair width), each step the
shipped `snakePrefixStraightens` + saturated `trans`/`refl`; `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`/`WellFounded.fix`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-atom readback frame -/

/-- The **readback frame** of one spine atom — the whiskered generator band `FramedSpineChain.readback` emits for
each `cons`: the generator whiskered by its right context, then by its left context.  Its boundary is exactly the
atom's frame source `⟶` frame target. -/
def spineAtomFrame {sourceMode targetMode : AdjunctionMode}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode) :
    RawTwoCellExpr adjunctionModeSignature
      (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
      (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) atom.leftContext
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) atom.rightContext
      (RawTwoCellExpr.gen atom.generator))

/-- ★ **The BRIDGE (`rfl`) — each readback `cons` emits a `spineAtomFrame` band.**  The readback of
`cons atom rest` is DEFINITIONALLY `spineAtomFrame atom ⊟ rest.readback` — the right-nested band the RV tower layer
consumes.  Iterated at a cup·cap head (with the boundaries the chain indices already align), the readback of a
matched cup·cap chain is the tower layer `cupFrame ⊟ (capFrame ⊟ rest.readback)` — so the "width-`(r+1)` right-nested
readback chain" IS a `MatchedSnakeTowerCell` layer, on the nose, no coherence massaging. -/
theorem framedChainConsReadback {sourceMode targetMode : AdjunctionMode}
    {targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (atom : SpineAtom adjunctionModeSignature sourceMode targetMode)
    {restAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (rest : FramedSpineChain adjunctionModeSignature
      (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
      targetPath restAtoms) :
    (FramedSpineChain.cons atom rest).readback
      = RawTwoCellExpr.vcomp (spineAtomFrame atom) rest.readback :=
  rfl

/-! ## The width-indexed matched-snake tower -/

/-- ★ **The width-indexed MATCHED-SNAKE TOWER over a fixed boundary `basePath`.**  `floor` is the width-0 tower —
the identity 2-cell.  `layer` prepends a matched cup·cap frame pair (`cupFrame : basePath ⟹ midPath`,
`capFrame : midPath ⟹ basePath`), carrying its per-pair TRIANGLE collapse witness `cupFrame ⊟ capFrame ≈ id`, over
an inner tower — a genuine pair that RETURNS to `basePath` (never a head-peel leaving a tail obligation).  The
`layer` constructor count is the RV width `r`; the readback of a matched cup·cap chain (via the `rfl` bridge) is
exactly this right-nested shape. -/
inductive MatchedSnakeTowerCell {sourceMode targetMode : AdjunctionMode}
    (basePath : ModalityPath adjunctionGraph sourceMode targetMode) :
    RawTwoCellExpr adjunctionModeSignature basePath basePath → Prop where
  /-- The width-0 tower: the identity 2-cell. -/
  | floor :
      MatchedSnakeTowerCell basePath
        (RawTwoCellExpr.id (signature := adjunctionModeSignature) basePath)
  /-- The width-`(r+1)` tower: a matched cup·cap frame pair with its collapse witness, over a width-`r` tower. -/
  | layer {midPath : ModalityPath adjunctionGraph sourceMode targetMode}
      (cupFrame : RawTwoCellExpr adjunctionModeSignature basePath midPath)
      (capFrame : RawTwoCellExpr adjunctionModeSignature midPath basePath)
      (collapses : SaturatedTwoCellConv (RawTwoCellExpr.vcomp cupFrame capFrame)
        (RawTwoCellExpr.id (signature := adjunctionModeSignature) basePath))
      {innerCell : RawTwoCellExpr adjunctionModeSignature basePath basePath}
      (inner : MatchedSnakeTowerCell basePath innerCell) :
      MatchedSnakeTowerCell basePath
        (RawTwoCellExpr.vcomp cupFrame (RawTwoCellExpr.vcomp capFrame innerCell))

/-! ## The RV middle-four step and the width induction -/

/-- ★ **The RV Prop 3.3.4 middle-four STEP — width-`(r+1)` ↝ width-`r`.**  A matched-tower layer
`cupFrame ⊟ (capFrame ⊟ inner)` straightens to its inner width-`r` tower `inner`, via the shipped
`snakePrefixStraightens`: one `vcompAssoc` re-bracketing `cup ⊟ (cap ⊟ inner) ↝ (cup ⊟ cap) ⊟ inner` then the
triangle collapse `(cup ⊟ cap) ↝ id`.  This is RV's "width-`r` instance + one triangle · η", removing the matched
pair (width −2), never peeling a head with a residual tail obligation. -/
theorem matchedSnakeTowerLayerStraightens {sourceMode targetMode : AdjunctionMode}
    {basePath midPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cupFrame : RawTwoCellExpr adjunctionModeSignature basePath midPath)
    (capFrame : RawTwoCellExpr adjunctionModeSignature midPath basePath)
    (collapses : SaturatedTwoCellConv (RawTwoCellExpr.vcomp cupFrame capFrame)
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) basePath))
    (innerCell : RawTwoCellExpr adjunctionModeSignature basePath basePath) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp cupFrame (RawTwoCellExpr.vcomp capFrame innerCell)) innerCell :=
  snakePrefixStraightens cupFrame capFrame collapses innerCell

/-- ★★ **The RV Prop 3.3.4 WIDTH INDUCTION — a matched-snake tower of ANY width collapses to the identity.**  By
STRUCTURAL recursion on the tower (= on the matched-pair width `r = cupCount = capCount`): the `floor` (width 0) is
`refl` on the identity; each `layer` fires the middle-four step (`matchedSnakeTowerLayerStraightens`) to reach the
inner width-`r` tower, then chains the inductive hypothesis by `trans`.  NO `WellFounded.fix` — the recursion is on
the tower's constructor depth, exactly the RV induction on the matched-pair count. -/
theorem matchedSnakeTowerCell_collapses {sourceMode targetMode : AdjunctionMode}
    {basePath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell : RawTwoCellExpr adjunctionModeSignature basePath basePath}
    (tower : MatchedSnakeTowerCell basePath cell) :
    SaturatedTwoCellConv cell
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) basePath) := by
  induction tower with
  | floor => exact SaturatedTwoCellConv.refl _
  | layer cupFrame capFrame collapses _ innerCollapses =>
      exact SaturatedTwoCellConv.trans
        (matchedSnakeTowerLayerStraightens cupFrame capFrame collapses _) innerCollapses

/-! ## Assembly: a chain whose readback is a matched tower -/

/-- ★ **A `FramedSpineChain` whose readback is a matched-snake tower reads back convertible to the identity.**  The
RV width reduction delivered on the readback carrier: given a chain whose readback IS a `MatchedSnakeTowerCell`
(the shape the `rfl` bridge exhibits for a matched cup·cap chain), the readback straightens to the identity by the
width induction.  This is the completeness-direction reconstruction AT the pure matched-tower seed — the
`convOfMapEq` special case where the cell is a stack of matched pairs over its boundary. -/
theorem framedChainMatchedTowerCollapses {sourceMode targetMode : AdjunctionMode}
    {basePath : ModalityPath adjunctionGraph sourceMode targetMode}
    {atoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (chain : FramedSpineChain adjunctionModeSignature basePath basePath atoms)
    (tower : MatchedSnakeTowerCell basePath chain.readback) :
    SaturatedTwoCellConv chain.readback
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) basePath) :=
  matchedSnakeTowerCell_collapses tower

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the Riehl–Verity Prop 3.3.4 middle-four WIDTH-REDUCTION is shipped as a
`SaturatedTwoCellConv`-valued STRUCTURAL recursion on the matched-pair width.**  The RV width index is the spine
`cupCount = capCount = r` (the `generatorCount`/2 the triangle drops); a right-nested readback chain with a cup·cap
head IS a `MatchedSnakeTowerCell` layer (`framedChainConsConsReadback`, `rfl`); the middle-four step
`matchedSnakeTowerLayerStraightens` (the shipped `snakePrefixStraightens` = one triangle + one `vcompAssoc`) removes
the matched pair (width −2); and `matchedSnakeTowerCell_collapses` runs the RV induction to the identity base by
STRUCTURAL recursion on the tower — no `WellFounded.fix`, no arc-readoff, no head-peel/tail-cancel.
`framedChainMatchedTowerCollapses` lands it on the readback carrier.

  What this marker does NOT claim (the honest residual — gates stay `false`):
  * the tower is CONSUMED, not BUILT — each `layer.collapses` is the per-pair triangle witness that a chain-located
    pair supplies by reading `matchingOf`/`partnerIndexOf` (the decidable partner FACT → the collapse WITNESS): the
    spine-frame ↔ arc-partner lift (`CellStraightenStepInput`, tracker #2185) is UN-shipped, so this file does not
    build a `MatchedSnakeTowerCell` from an arbitrary chain;
  * the general `convOfMapEq` additionally needs the descent-to-valley (the `CellDescentStepOracle`), the
    whole-valley Piece II (`CellValleyTraceEquiv`), and the SOUNDNESS-direction Godement/`SpineTraceEquiv`
    disjoint-support commutation companion (Mazurkiewicz/Delpeuch–Vicary) — all distinct, separately open.

So the RV width-reduction MECHANISM is closed; `convOfMapEq` / `SaturatedMatchingCanonicalization` and the fib-3
gate flags stay `false`.  `= true`. -/
def fxMode_hasFramedChainWidthReduction : Bool := true

end FX1Poly.Polygraph
