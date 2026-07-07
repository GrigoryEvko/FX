import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedSpineTraceLift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedZigZagStraightening
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # mode-3 keystone — Piece I cell-lifts (i)+(ii): the tag descent's per-step moves, lifted to CELLS

`SpineValleyDisorder` closed Piece I of the `MatchingReductsShareSpineTrace` beam AT THE PURE-TAG LEVEL: the
inversion measure `spineDisorder`, the terminating `valleyDescentDriver`, and the two strict-decrease facts
(`countInversions_swap_adjacent_lt` for COMMUTE, `countInversions_delete_head_lt` for STRAIGHTEN).  It left three
inputs open before the descent produces a `SaturatedTwoCellConv cellA (valleyNF cellA)`: (i) the TYPED spine
swap (each tag step must typecheck against the boundary-chained `SpineAtom` modes), (ii) the spine-position →
cell-subterm BRIDGE (each located `cup :: cap :: rest` split must be exhibited as a `vcomp`/whisker redex feeding
the shipped saturated moves), and (iii) the `reify` base case.

This file discharges the PER-STEP content of (i) and (ii) — the two saturated moves as reusable cell-level lift
lemmas in the exact right-nested `vcomp` shape the readback (`chainToCell`, `RealizedChain`) produces:

  * ★ **STRAIGHTEN, cell-level** — `snakePrefixStraightens` / `snakeStraightensInContext`.  A partner cup·cap
    pair whose two per-atom frames `cupFrame ⊟ capFrame` collapse to the identity (a zig-zag) STRAIGHTENS at the
    head of a right-nested readback chain (`cupFrame ⊟ (capFrame ⊟ tail) ≈ tail`), and inside any surrounding
    `pre ⊟ · ≈ pre ⊟ tail` context.  Built on the shipped `zigzagStraightensPrefix` (which fires the collapse
    under the vcomp congruences) plus one free `vcompAssoc` re-association — the readback is right-nested, the
    straighten wants the snake left-nested, and that is the whole gap.  This is the `generatorCount`-dropping move
    (two atoms deleted), unavailable in the free/trace layer.
  * ★ **COMMUTE, cell-level** — `godementExchangePrefix` / `godementExchangeInContext`.  Two horizontally-DISJOINT
    atoms (`cellA ▷ g` on the left band, `f' ◁ cellB` on the right band) TRANSPOSE at the head of a right-nested
    readback chain, and inside any surrounding vertical context, via the shipped `saturatedGodementExchange`
    bracketed by two free `vcompAssoc` re-associations.  This is the `generatorCount`-preserving move.
  * ★ **The TYPED swap → cell conversion** — `commuteAtomSwapCellLift`.  A genuine `SpineAtomSwap` on two cells'
    SPINES (the boundary-chained, mode-respecting adjacent transposition the shipped
    `adjunctionSpineAtomSwap_of_disjointWindows` produces from disjoint windows) lifts to a
    `SaturatedTwoCellConv` between the cells: the swap is a Godement spine step (`toGodementStep`), a trace
    equivalence (`SpineTraceEquiv.ofStep`), and thence a saturated convertibility (`ofSpineTraceEquiv`).  So the
    tag swap, once realized as a typed spine swap respecting the `SpineAtom` modes, IS a cell-level conversion —
    the currency the descent chains.

## What this does NOT close (gates stay `false`)

The per-step MOVES are lifted; the full Piece I cell descent is NOT assembled here.  It still owes:
  * the flat-`SpineBoundaryChained` → `RealizedSpineChain` realization (the totality bridge that turns a raw
    cell's spine into a boundary-coherent chain whose readback exhibits the located redex as one of the shapes
    above), plus the classifier that DISPATCHES commute-vs-straighten per adjacent pair (with the
    orientation-excluded case proven impossible) and re-types the tag driver as a `SaturatedTwoCellConv`-valued
    recursion (the straighten changes the carrier length, so it cannot ride the tag `List` permutation);
  * the `reify` base case (iii) — the canonical-cell FUNCTION with the tip-variance obstruction
    (`fxMode_hasArcCellReconstruction = false`), which the EXISTENCE route
    (`MatchingReductsShareSpineTrace`) bypasses entirely, reducing instead to Piece II (the separate
    `ValleyCup*`/`ValleyMatchingSpineTraceEquiv` whole-valley split).

So `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false`.

Raw Lean 4 + Init; every proof is saturated `trans`/congruence + the shipped `zigzagStraightensPrefix` /
`saturatedGodementExchange` + free `vcompAssoc`; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## STRAIGHTEN, cell-level — a collapsing frame-pair straightens at the head of a readback chain -/

/-- ★ **The STRAIGHTEN per-step lift (prefix).**  A partner cup·cap pair whose two per-atom frames compose to a
collapsing zig-zag (`cupFrame ⊟ capFrame ≈ id`) straightens away at the head of a right-nested readback chain:
`cupFrame ⊟ (capFrame ⊟ tail) ≈ tail`.  The readback (`chainToCell (cons cup (cons cap rest))`) is exactly this
right-nested shape; the proof re-associates it to `(cupFrame ⊟ capFrame) ⊟ tail` (free `vcompAssoc`, reversed)
and fires the shipped `zigzagStraightensPrefix` on the collapsing snake.  This is the `generatorCount`-dropping
move — two atoms removed — unavailable in the free/trace layer. -/
theorem snakePrefixStraightens {sourceMode targetMode : AdjunctionMode}
    {pathLow pathMid pathHigh : ModalityPath adjunctionGraph sourceMode targetMode}
    (cupFrame : RawTwoCellExpr adjunctionModeSignature pathLow pathMid)
    (capFrame : RawTwoCellExpr adjunctionModeSignature pathMid pathLow)
    (collapses : SaturatedTwoCellConv (RawTwoCellExpr.vcomp cupFrame capFrame)
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathLow))
    (tail : RawTwoCellExpr adjunctionModeSignature pathLow pathHigh) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp cupFrame (RawTwoCellExpr.vcomp capFrame tail)) tail :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.symm
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc cupFrame capFrame tail))))
    (zigzagStraightensPrefix (RawTwoCellExpr.vcomp cupFrame capFrame) collapses tail)

/-- ★ **The STRAIGHTEN per-step lift (in vertical context).**  The same collapsing frame-pair straightens away
inside any surrounding vertical prefix `pre`: `pre ⊟ (cupFrame ⊟ (capFrame ⊟ tail)) ≈ pre ⊟ tail`.  This is the
located-at-arbitrary-position STRAIGHTEN in the readback: a cup·cap redex appearing at depth in the right-nested
`chainToCell` reassembly, under the reassembly of the atoms before it. -/
theorem snakeStraightensInContext {sourceMode targetMode : AdjunctionMode}
    {pathPre pathLow pathMid pathHigh : ModalityPath adjunctionGraph sourceMode targetMode}
    (pre : RawTwoCellExpr adjunctionModeSignature pathPre pathLow)
    (cupFrame : RawTwoCellExpr adjunctionModeSignature pathLow pathMid)
    (capFrame : RawTwoCellExpr adjunctionModeSignature pathMid pathLow)
    (collapses : SaturatedTwoCellConv (RawTwoCellExpr.vcomp cupFrame capFrame)
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathLow))
    (tail : RawTwoCellExpr adjunctionModeSignature pathLow pathHigh) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp cupFrame (RawTwoCellExpr.vcomp capFrame tail)))
      (RawTwoCellExpr.vcomp pre tail) :=
  SaturatedTwoCellConv.vcompCongrRight pre (snakePrefixStraightens cupFrame capFrame collapses tail)

/-! ## COMMUTE, cell-level — two disjoint atoms transpose at the head of a readback chain -/

/-- ★ **The COMMUTE per-step lift (prefix).**  Two horizontally-DISJOINT atoms — `cellA` on the left band (over
`sourceMode ⟶ middleMode`) and `cellB` on the right band (over `middleMode ⟶ targetMode`) — transpose at the head
of a right-nested readback chain: `(cellA ▷ g) ⊟ ((f' ◁ cellB) ⊟ tail) ≈ (f ◁ cellB) ⊟ ((cellA ▷ g') ⊟ tail)`.
Built by bracketing the shipped `saturatedGodementExchange` (the naturality-square commutation `(cellA ▷ g) ⊟
(f' ◁ cellB) ≈ (f ◁ cellB) ⊟ (cellA ▷ g')`) between two free `vcompAssoc` re-associations that expose the head
band and re-nest afterwards.  This is the `generatorCount`-preserving move — the atoms are permuted, not
removed. -/
theorem godementExchangePrefix {sourceMode middleMode targetMode : AdjunctionMode}
    {oneCellF oneCellF' : ModalityPath adjunctionGraph sourceMode middleMode}
    {oneCellG oneCellG' : ModalityPath adjunctionGraph middleMode targetMode}
    (cellA : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellF')
    (cellB : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellG')
    {pathHigh : ModalityPath adjunctionGraph sourceMode targetMode}
    (tail : RawTwoCellExpr adjunctionModeSignature
      (composePath oneCellF' oneCellG') pathHigh) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellG cellA)
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellF' cellB) tail))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellF cellB)
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellG' cellA) tail)) :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.symm
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc (RawTwoCellExpr.whiskerRight oneCellG cellA)
          (RawTwoCellExpr.whiskerLeft oneCellF' cellB) tail))))
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.vcompCongrLeft tail (saturatedGodementExchange cellA cellB))
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc (RawTwoCellExpr.whiskerLeft oneCellF cellB)
          (RawTwoCellExpr.whiskerRight oneCellG' cellA) tail))))

/-- ★ **The COMMUTE per-step lift (in vertical context).**  The same disjoint transposition inside any
surrounding vertical prefix `pre` — the located-at-arbitrary-position COMMUTE in the readback. -/
theorem godementExchangeInContext {sourceMode middleMode targetMode : AdjunctionMode}
    {oneCellF oneCellF' : ModalityPath adjunctionGraph sourceMode middleMode}
    {oneCellG oneCellG' : ModalityPath adjunctionGraph middleMode targetMode}
    {pathPre : ModalityPath adjunctionGraph sourceMode targetMode}
    (pre : RawTwoCellExpr adjunctionModeSignature pathPre (composePath oneCellF oneCellG))
    (cellA : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellF')
    (cellB : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellG')
    {pathHigh : ModalityPath adjunctionGraph sourceMode targetMode}
    (tail : RawTwoCellExpr adjunctionModeSignature
      (composePath oneCellF' oneCellG') pathHigh) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellG cellA)
          (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellF' cellB) tail)))
      (RawTwoCellExpr.vcomp pre
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellF cellB)
          (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellG' cellA) tail))) :=
  SaturatedTwoCellConv.vcompCongrRight pre (godementExchangePrefix cellA cellB tail)

/-! ## The typed spine swap → cell conversion -/

/-- ★ **The TYPED spine swap lifts to a cell conversion.**  A genuine `SpineAtomSwap` between two cells' SPINES —
the boundary-chained, mode-respecting adjacent transposition the shipped `adjunctionSpineAtomSwap_of_disjointWindows`
produces from a disjoint-window pair (re-threading the second atom's left context through the first's source
1-cell and the first atom's right context through the second's target 1-cell) — realizes as a
`SaturatedTwoCellConv` between the cells.  The swap is a Godement spine step (`toGodementStep`), hence a single
trace equivalence (`SpineTraceEquiv.ofStep`), hence a saturated convertibility (`ofSpineTraceEquiv`).  So once a
tag swap is realized as a typed spine swap respecting the `SpineAtom` modes, it IS a cell-level conversion — the
currency the descent chains for its COMMUTE steps. -/
theorem commuteAtomSwapCellLift {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (swapStep : SpineAtomSwap adjunctionModeSignature cellFirst.spine cellSecond.spine) :
    SaturatedTwoCellConv cellFirst cellSecond :=
  SaturatedTwoCellConv.ofSpineTraceEquiv cellFirst cellSecond
    (SpineTraceEquiv.ofStep swapStep.toGodementStep)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the PER-STEP content of Piece I cell-lifts (i)+(ii) is DISCHARGED.**  Both saturated
descent moves are now reusable cell-level lift lemmas in the exact right-nested `vcomp` shape the readback
produces: STRAIGHTEN (`snakePrefixStraightens` / `snakeStraightensInContext`, a collapsing frame-pair removed via
`zigzagStraightensPrefix` + one `vcompAssoc`) and COMMUTE (`godementExchangePrefix` /
`godementExchangeInContext`, two disjoint atoms transposed via `saturatedGodementExchange` bracketed by two
`vcompAssoc`s).  The TYPED swap of (i) lifts to a cell conversion (`commuteAtomSwapCellLift`: `SpineAtomSwap` on
spines → Godement step → trace equivalence → `SaturatedTwoCellConv`).

  What this marker does NOT claim — the remaining Piece I ASSEMBLY (gates stay `false`):
  * the flat-`SpineBoundaryChained` → `RealizedSpineChain` realization + the commute/straighten CLASSIFIER
    (with the orientation-excluded case proven impossible) + the re-typed `SaturatedTwoCellConv`-valued driver
    (the straighten changes carrier length, so the descent is a MIXED recursion, not the tag `List` permutation);
  * the `reify` base case (iii) — the tip-variance-obstructed canonical-cell FUNCTION, which the EXISTENCE route
    `MatchingReductsShareSpineTrace` bypasses (reducing to Piece II's whole-valley split instead).

So the per-step MOVES are lifted; assembling them into `SaturatedTwoCellConv cellA (valleyNF cellA)` and thence
into `MatchingReductsShareSpineTrace` still needs the realization + classifier + driver + Piece II.  `convOfMapEq`
and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyCellLiftMoves : Bool := true

end FX1Poly.Polygraph
