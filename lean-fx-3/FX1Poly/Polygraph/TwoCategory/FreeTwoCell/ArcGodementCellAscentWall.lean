import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimStep
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshnessInvariant
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderCapCapClosure

/-! # MODE-COMMUTE — the CELL ASCENT wall, characterized (r20 B2)

The r19/r20 faithful reorder closure lives at STATE+KIND (atom-pair) granularity over the faithful engine.
The mode-side keystone the amalgamation consumer needs is the general-CELL commute
`ArcGodementSamePartitionFresh` (`ArcPartitionCommute.lean:472`): the Godement interchange of two ARBITRARY
two-cells `cellAlphaUpper` / `cellBeta` (each a whole spine, unbounded) run in the two orders, at the SHIPPED
engine `processArcSpine`, concluding `SameArcPartition`.  Its honesty pin
`fxMode_hasArcGodementSamePartitionFreshProof` (`:545`) flips ONLY if that LITERAL statement is proven
hypothesis-free at its stated generality.  This file characterizes the wall precisely — with machine-checked
evidence pinning where it is and where it is NOT — and names the exact obstructions and the next lever, WITHOUT
flipping the pin.  An honest wall beats a fake flip.

## What already works — the wall is NOT the readout (machine-checked here)

`runArcCell state leftAcc rightAcc cell = processArcSpine state (cell.spineDiff leftAcc rightAcc [])` runs a
whole cell's spine-diff through the SHIPPED engine.  The READOUT half ships:
`sameArcPartition_full_of_corePartitionSim` turns a CORE `ArcPartitionSim redexCore reductCore` into
`SameArcPartition` after a common `suffixCell`-then-`rest` — exactly :472's conclusion shape.  And the base case
is reachable: `cellAscentBase_sameArcPartition` (below) feeds an ATOM-PAIR cup-cup partition core
(`arcSwapCorePackage_cupCup`) into that readout and produces :472's conclusion shape after a common cell + rest.
So neither the readout nor the base case is the wall.

## Where the wall IS — the missing keystone `arcPartitionSim_blockSwapCore`

The one missing piece is the GENERAL two-cell block-swap partition core

  `arcPartitionSim_blockSwapCore :`
  `  ArcPartitionSim (compoundSigma ...)`
  `    (runArcCell (runArcCell S leftAcc (gLow++rightAcc) cellAlphaUpper) (leftAcc++fHigh) rightAcc cellBeta)`
  `    (runArcCell (runArcCell S (leftAcc++fMid) rightAcc cellBeta) leftAcc (gMid++rightAcc) cellAlphaUpper)`

for ARBITRARY `cellAlphaUpper` / `cellBeta`.  No lemma builds it.  Given it, :472 closes in a few lines: peel
the shared `cellAlpha` (both orders share it, definitionally), apply `arcPartitionSim_blockSwapCore`, then
`sameArcPartition_full_of_corePartitionSim` with `suffixCell := cellBetaUpper`.  Three named obstructions block
that keystone:

  * **WALL-BOX** (fatal at general signature).  A general cell contains arbitrary-arity generators; the shipped
    `stepArcAtom` box arm (arity not in `{0=>2, 2=>0}`) is machine-witnessed CORRUPT
    (`ArcCrossingBoxArmCorruption`), so there is NO `boxSwap_arcPartitionSim`.  All shipped swap cores are
    cup/cap only (`fxMode_hasArcPeelArityCeiling`).  Any induction bubbling `cellAlphaUpper` past `cellBeta`
    hits box-past-box with no core — confining the whole route to arity-`{cup, cap}` cells (the walking
    adjunction), NOT the general `ModeSignature` :472 quantifies over.
  * **WALL-WIDTH.**  The sigma must transpose two disjoint fresh ranges whose widths are the cells' TOTAL fresh
    allocations (unbounded).  `arcFreshBlockTransposition nextFresh w1 w2` is a single fixed-width block swap;
    composing across a cell needs a compound construction plus fresh `fixesZero` / `fixesBoundary` /
    `fixesAbove` / injectivity proofs.
  * **WALL-WHISKER.**  Between the two orders `cellBeta`'s atoms are shifted by `fHigh.length - fMid.length`
    and `cellAlphaUpper`'s by `gMid.length - gLow.length`; the fold must carry a disjoint-support invariant
    ("`cellAlphaUpper`'s atoms fire strictly left of `cellBeta`'s") so the block swap in `openMap` holds.

## The SECOND, orthogonal blocker to the LITERAL pin — the FOREST GAP

Even granting the keystone at arity-`{cup, cap}`, the literal :472 requires ONLY `ArcStateFresh state` — NO
forest hypothesis — yet every shipped partition core requires `isUnionFindForest state.links`.  And freshness
does NOT imply forest: `cellAscentForestGap_freshNotForest` (below) machine-checks a fresh-but-CYCLIC state
witnessing `ArcStateFresh state` together with `¬ isUnionFindForest state.links`.  So the literal :472 demands
the commute even for fresh-but-cyclic states no shipped core reaches.  A flip attempt must ALSO either prove the
cyclic case OR discover :472 is FALSE-as-stated for cyclic states — an over-quantification exactly like the
already-refuted unconditional `ArcGodementSamePartition` (`not_arcGodementSamePartition`).  This forest gap
ALONE blocks the pin flip until adjudicated.

## The next lever (a future skeleton, in dependency order)

`compoundFreshBlockTransposition` (+ its four fixing lemmas + injectivity) => `disjointWhiskerSupport`
predicate => `atomPastCell_arcPartitionSim` (one atom past a whole cell) => `arcPartitionSim_blockSwapCore`
(the keystone), all confined to arity-`{cup, cap}` by WALL-BOX; PLUS the forest-gap adjudication (prove the
cyclic case, or refute :472 for cyclic-fresh states).  NEVER route through `ArcStepSimCount` / `rootComm` /
`ArcGodementCoreSwapSimCount` on cap-cap — those are machine-refuted; only `ArcPartitionSim` survives cap-cap.

Raw Lean 4 + Init; the two evidence theorems are the shipped readout applied to a shipped core, and a `decide`
on a concrete state.  The honesty pin `fxMode_hasArcGodementSamePartitionFreshProof` stays `false`; the two
permanent keystones stay `false`.  Per-declaration `#assert_no_axioms` AND an independent `#print axioms` gated
in the audit twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Evidence 1 — the readout + base case discharge :472's conclusion shape (the wall is NOT here) -/

/-- ★ **The cell-ascent BASE CASE is reachable.**  An ATOM-PAIR cup-cup partition core
(`arcSwapCorePackage_cupCup`) fed through the shipped readout `sameArcPartition_full_of_corePartitionSim`
produces `SameArcPartition` after a common `suffixCell`-then-`rest` — precisely :472's conclusion SHAPE.  So the
readout and the base case are NOT the wall; the wall is the GENERAL two-cell core
`arcPartitionSim_blockSwapCore` for arbitrary `cellAlphaUpper` / `cellBeta`. -/
theorem cellAscentBase_sameArcPartition {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cellSource cellTarget : signature.graph.Mode}
    (state : ArcWireState) (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh)
    (bottomCount : Nat) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (gap positionLow : Nat) (positionBound : gap + positionLow ≤ state.openWires.length)
    (leftAccCell : ModalityPath signature.graph overallSource cellSource)
    (rightAccCell : ModalityPath signature.graph cellTarget overallTarget)
    {cellDom cellCod : ModalityPath signature.graph cellSource cellTarget}
    (suffixCell : RawTwoCellExpr signature cellDom cellCod)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    SameArcPartition bottomCount
      (processArcSpine (runArcCell
        (stepCupArc (stepCupArc state positionLow) (gap + 2 + positionLow))
        leftAccCell rightAccCell suffixCell) rest)
      (processArcSpine (runArcCell
        (stepCupArc (stepCupArc state (gap + positionLow)) positionLow)
        leftAccCell rightAccCell suffixCell) rest) :=
  let package := arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount
    boundaryBelowFresh gap positionLow positionBound
  sameArcPartition_full_of_corePartitionSim package.sigma package.sigmaFixesZero bottomCount
    package.fixesBoundary _ _ leftAccCell rightAccCell suffixCell rest package.fixesAbove
    package.coreSim

/-! ## Evidence 2 — the FOREST GAP blocks the LITERAL pin -/

/-- ★ **The forest gap: freshness does NOT imply forest.**  The literal :472 requires only `ArcStateFresh
state`, but every shipped partition core additionally requires `isUnionFindForest state.links`.  The fresh-but-
cyclic witness `arcFreshCyclicState` (`links = [(0,1),(1,0)]`, a 2-cycle, `nextFresh = 5`) is `ArcStateFresh`
yet is NOT a union-find forest — so the literal :472 demands the commute at states no shipped core reaches.
This is the second, orthogonal blocker to a flip of `fxMode_hasArcGodementSamePartitionFreshProof`. -/
theorem cellAscentForestGap_freshNotForest :
    ArcStateFresh arcFreshCyclicState ∧ ¬ isUnionFindForest arcFreshCyclicState.links :=
  ⟨arcFreshCyclicState_isFresh, arcFreshCyclicLinks_notForest⟩

/-! ## The wall marker + permanent-false pins -/

/-- ★ **Honesty marker — the CELL ASCENT wall is CHARACTERIZED.**  Not "the ascent is done" — the ascent is
WALLED.  The characterization ships: the readout + base case discharge :472's conclusion shape from an atom-
pair core (`cellAscentBase_sameArcPartition`), so the wall is precisely the general two-cell block-swap core
`arcPartitionSim_blockSwapCore`, blocked by WALL-BOX (no `boxSwap_arcPartitionSim` over the corrupt box arm,
confining the route to arity-`{cup, cap}`), WALL-WIDTH (compound fresh-block transposition unbuilt) and
WALL-WHISKER (disjoint-support invariant unbuilt); and the literal pin has a SECOND orthogonal blocker, the
FOREST GAP (`cellAscentForestGap_freshNotForest`: `ArcStateFresh` does not imply forest, so :472 as stated
quantifies over fresh-but-cyclic states).  `= true`. -/
def fxMode_hasArcGodementCellAscentWall : Bool := true

/-- **Honesty pin — the general-CELL fresh-partition keystone stays the open obligation.**  This file
CHARACTERIZES the wall; it does not build `arcPartitionSim_blockSwapCore`, so the literal :472
`ArcGodementSamePartitionFresh` is not proven hypothesis-free and
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcGodementCellAscentWall_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  WALL-BOX confines the route to
arity-`{cup, cap}`; the general-signature peel is not built.  `fxMode_hasArcPeelGeneralSignature` stays
`false`.  `rfl`. -/
theorem arcGodementCellAscentWall_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the root-level renaming vehicle stays PERMANENTLY refuted.**  The cell ascent rides the
representative-free PARTITION core, NOT the root-level renaming vehicle `rootComm`, which is machine-refuted at
the join-order flip (`ArcCoreSwapCapFlipRefutation`).  `fxMode_hasArcGodementSwapRenameableProof2` stays
`false` PERMANENTLY.  `rfl`. -/
theorem arcGodementCellAscentWall_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
