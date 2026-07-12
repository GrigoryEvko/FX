import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementCellAscentWall
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshGatedPartitionCommute
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # MODE-COMMUTE — the FOREST-GAP adjudication: the LITERAL fresh residual is FALSE (r21)

`ArcGodementSamePartitionFresh` (`ArcPartitionCommute.lean:472`) requires ONLY `ArcStateFresh state` — NO forest
hypothesis — yet asks the two Godement run orders to land `SameArcPartition` from EVERY fresh starting state.  The
r20 wall (`ArcGodementCellAscentWall`) already machine-witnessed that freshness does NOT imply forest
(`cellAscentForestGap_freshNotForest`, a fresh 2-cycle), and named the forest gap as the SECOND, orthogonal blocker
to any flip of `fxMode_hasArcGodementSamePartitionFreshProof` — leaving OPEN whether the literal is merely unproven
on cyclic states, or FALSE there.

This file ADJUDICATES it, branch (a): the literal :472 is **FALSE as stated**.  At a fresh-but-CYCLIC state whose
`links` carries one 2-cycle `{0,1}` alongside one loop-forming forest edge `{2,3}`, the two Godement run orders
(the CAP over CAP interchange at `adjunctionModeSignature`) yield DIFFERENT `SameArcPartition`: the internal
CAP-event count at boundary port `0` is `1` in the redex order and `0` in the reduct order.  This is a certified
refutation, mirroring the already-shipped unconditional precedent `not_arcGodementSamePartition`
(`ArcPartitionCommute.lean:422`).

## The mechanism (why the cycle breaks it)

`unionFindRootOf` walks parents with fuel `= links.length + 1`.  On a forest the walk settles to a parentless root
independent of `links.length` (`unionFindRootOf_parentless_of_forest`).  On a CYCLE the root is a function of the
global `links.length` PARITY.  The forest cap `{2,3}` forms a genuine loop, so its inner `unionFindJoin` is a no-op
and it adds an ODD number of edges (the event edge only); firing it before vs. after the cycle cap `{0,1}` flips the
parity the cycle cap observes, so the cycle cap attaches its cap-event node into a different component.  The coarse
boundary same-component relation survives (roots of `{0,1}` read `(1,0)` in BOTH orders), but the finer arc-turnback
attribution — which strand each cap sits on — diverges.  A forest forbids exactly this: the roots are parity-free.

## What this settles, and what stays open

The literal :472 is refuted, so `fxMode_hasArcGodementSamePartitionFreshProof` (`ArcPartitionCommute.lean:545`)
stays `false` FOREVER against it — it CANNOT be flipped, because the statement it names is false (exactly the
`not_arcGodementSamePartition` / `fxMode_hasArcSamePartitionProof` precedent).  Re-`rfl`'d below.

The genuine, well-formed replacement is NOT introduced here — it ALREADY exists: `ArcGodementSamePartitionFreshForest`
(`ArcFreshGatedPartitionCommute.lean:55`) is `ArcGodementSamePartitionFresh` strengthened with exactly
`isUnionFindForest state.links` (and `0 < state.nextFresh`), and is already the RECORDED target reduced from the
count route (`arcGodementSamePartitionFreshForest_of_coreSwapSimCount`), still OPEN at
`fxMode_hasArcForestFreshResidualClosed = false`.  This file's contribution to that target is the machine-checked
EXCLUSION witness: the counterexample state is `¬ isUnionFindForest links`, so the corrected residual dodges it
vacuously — the forest hypothesis is NECESSARY, not decorative.  The WALL-BOX / WALL-WIDTH / WALL-WHISKER census
from the wall is unchanged.

Raw Lean 4 + Init; every fire is `decide` on a concrete state (kernel `decide`, NOT `native_decide`), the same
discipline as the shipped `arcRefute_boundarySameComponent_differs`.  Per-declaration `#assert_no_axioms` AND an
independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two run orders spelled at `adjunctionModeSignature` -/

/-- The identity path on the base mode `tip`. -/
def nilTipPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.tip :=
  ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip

/-- The right-then-left composite path `R L : tip -> tip` — the domain of the adjunction counit. -/
def rightLeftPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.tip :=
  adjunctionRightThenLeft

/-- The identity two-cell on `R L` (the shared bottom cell `cellAlpha`). -/
def identityCellOnRightLeft : RawTwoCellExpr adjunctionModeSignature rightLeftPath rightLeftPath :=
  RawTwoCellExpr.id _

/-- The identity two-cell on `nilTip` (the shared top cell `cellBetaUpper`). -/
def identityCellOnNilTip : RawTwoCellExpr adjunctionModeSignature nilTipPath nilTipPath :=
  RawTwoCellExpr.id _

/-- ★ **The fresh-but-CYCLIC counterexample state.**  `links = [(0,1),(1,0),(2,3)]` — a 2-cycle `{0,1}` plus one
loop-forming forest edge `{2,3}` — with `nextFresh = 4` (every mentioned id lies in `{0,1,2,3} ⊂ [0,4)`), empty
open wires and empty event lists.  `ArcStateFresh` (below) yet `¬ isUnionFindForest links` (below): precisely the
gap the wall's `cellAscentForestGap_freshNotForest` names, sharpened with the loop-forming edge that makes the two
run orders' cap-event attribution diverge. -/
def arcFreshCyclicForestGapState : ArcWireState :=
  ArcWireState.mk [0, 1, 2, 3] [(0, 1), (1, 0), (2, 3)] 4 0 [] []

/-- The empty boundary tail `rest = []` at the base mode. -/
def emptyBoundaryRest : List (SpineAtom adjunctionModeSignature AdjunctionMode.tip AdjunctionMode.tip) := []

/-- The **redex** Godement run order (`cellAlphaUpper` fired before `cellBeta`) at the counterexample state, spelled
verbatim as the first `processArcSpine` argument of `ArcGodementSamePartitionFresh` instantiated at
`cellAlpha := identityCellOnRightLeft`, `cellAlphaUpper = cellBeta := adjunctionCounitTwoCell`,
`cellBetaUpper := identityCellOnNilTip`, `leftAcc = rightAcc := nilTipPath`. -/
def godementRedexState : ArcWireState :=
  processArcSpine
    (runArcCell (runArcCell (runArcCell
        (runArcCell arcFreshCyclicForestGapState nilTipPath (composePath rightLeftPath nilTipPath)
          identityCellOnRightLeft)
        nilTipPath (composePath rightLeftPath nilTipPath) adjunctionCounitTwoCell)
      (composePath nilTipPath nilTipPath) nilTipPath adjunctionCounitTwoCell)
      (composePath nilTipPath nilTipPath) nilTipPath identityCellOnNilTip) emptyBoundaryRest

/-- The **reduct** Godement run order (`cellBeta` fired before `cellAlphaUpper`) at the counterexample state,
spelled verbatim as the second `processArcSpine` argument of `ArcGodementSamePartitionFresh`. -/
def godementReductState : ArcWireState :=
  processArcSpine
    (runArcCell (runArcCell (runArcCell
        (runArcCell arcFreshCyclicForestGapState nilTipPath (composePath rightLeftPath nilTipPath)
          identityCellOnRightLeft)
        (composePath nilTipPath rightLeftPath) nilTipPath adjunctionCounitTwoCell)
      nilTipPath (composePath nilTipPath nilTipPath) adjunctionCounitTwoCell)
      (composePath nilTipPath nilTipPath) nilTipPath identityCellOnNilTip) emptyBoundaryRest

/-! ## The counterexample is FRESH, is NON-forest, and its boundary width fits -/

/-- ★ **The counterexample state is `ArcStateFresh`.**  Every mentioned id lies in `{0,1,2,3} ⊂ [0,4)`; open wires
are `{0,1,2,3}` (all `< 4`) and both event lists are empty. -/
theorem arcFreshCyclicForestGapState_isFresh : ArcStateFresh arcFreshCyclicForestGapState := by
  unfold ArcStateFresh arcFreshCyclicForestGapState
  decide

/-- ★ **The counterexample's `links` is NOT a union-find forest.**  `isUnionFindForest [(0,1),(1,0),(2,3)]` would
force the second endpoint `1` of the head edge `(0,1)` to be parentless in the tail `[(1,0),(2,3)]`, but
`unionFindParent [(1,0),(2,3)] 1 = some 0` (the cycle).  So the counterexample state is EXCLUDED from the corrected
residual `ArcGodementSamePartitionFreshForest` — the forest hypothesis is what dodges it.  Mirrors the wall's
`arcFreshCyclicLinks_notForest`, extended with the loop-forming edge. -/
theorem arcFreshCyclicForestGapLinks_notForest :
    ¬ isUnionFindForest [(0, 1), (1, 0), (2, 3)] := by
  intro forest
  rw [isUnionFindForest_cons] at forest
  exact absurd forest.2.1 (by decide)

/-- The counterexample state, projected, is not a forest — the `ArcWireState`-level form of the exclusion witness
(`arcFreshCyclicForestGapState.links` is definitionally `[(0,1),(1,0),(2,3)]`). -/
theorem arcFreshCyclicForestGapState_notForest :
    ¬ isUnionFindForest arcFreshCyclicForestGapState.links :=
  arcFreshCyclicForestGapLinks_notForest

/-- The boundary width `1` fits below `nextFresh = 4` — the `bottomCount ≤ state.nextFresh` proviso the residual
carries. -/
theorem bottomCountBelowFresh : (1 : Nat) ≤ arcFreshCyclicForestGapState.nextFresh := by decide

/-! ## The decided divergence -/

/-- ★ **The kernel-decided divergence.**  At boundary port `0`, the internal CAP-event count is `1` in the redex run
order and `0` in the reduct order — the two Godement orders attribute the cap turnback to DIFFERENT strands.  Decided
on the two concrete states (NOT the large parallel cells the perf rule warns against), so `decide`-discharged and
zero-axiom. -/
theorem internalCapCountAtPortZero_differs :
    internalEventCountAt godementRedexState.links (boundaryNodesOf 1 godementRedexState)
        godementRedexState.capEventNodes 0
      ≠ internalEventCountAt godementReductState.links (boundaryNodesOf 1 godementReductState)
        godementReductState.capEventNodes 0 := by
  decide

/-! ## The refutation -/

/-- ★ **The LITERAL fresh Godement arc residual is FALSE.**  `ArcGodementSamePartitionFresh adjunctionModeSignature`
(`ArcPartitionCommute.lean:472`) would force the two Godement run orders to agree on `SameArcPartition` from EVERY
fresh starting state; instantiated at the fresh-but-cyclic `arcFreshCyclicForestGapState` (cells: shared identity
bottom, two counits, shared identity top) it forces the internal CAP-event counts at port `0` to agree, contradicting
`internalCapCountAtPortZero_differs`.  Hence the freshness-only residual is unprovable — it is REFUTED — and
`fxMode_hasArcGodementSamePartitionFreshProof` CANNOT be flipped: the statement needs the FOREST precondition
(`ArcGodementSamePartitionFreshForest`, `ArcFreshGatedPartitionCommute.lean:55`).  Zero-axiom (the only nontrivial
steps are `decide` on the two small concrete states).  Mirrors the unconditional precedent
`not_arcGodementSamePartition` (`ArcPartitionCommute.lean:422`). -/
theorem not_arcGodementSamePartitionFresh :
    ¬ ArcGodementSamePartitionFresh adjunctionModeSignature := by
  intro everyFreshStateAgrees
  have samePartition := everyFreshStateAgrees identityCellOnRightLeft adjunctionCounitTwoCell
    adjunctionCounitTwoCell identityCellOnNilTip nilTipPath nilTipPath [] 1 arcFreshCyclicForestGapState
    arcFreshCyclicForestGapState_isFresh bottomCountBelowFresh
  exact internalCapCountAtPortZero_differs (samePartition.2.2.2.2 0 (by decide))

/-! ## Honesty markers + the graveyard pins -/

/-- ★ **Honesty marker — the LITERAL fresh residual is REFUTED (zero-axiom).**  `not_arcGodementSamePartitionFresh`
proves `¬ ArcGodementSamePartitionFresh adjunctionModeSignature` by exhibiting a fresh-but-cyclic state at which the
two Godement run orders disagree on the internal CAP-event count at boundary port `0` (`1` vs `0`).  This overturns
the standing "TRUE, computationally confirmed on fresh-but-cyclic starting states" claim in the :472 docstring: as
STATED (over ALL fresh states, no forest) it is FALSE.  The provable, well-formed replacement is the already-shipped
`ArcGodementSamePartitionFreshForest`, which adds exactly `isUnionFindForest state.links`.  `= true`. -/
def fxMode_hasArcGodementSamePartitionFreshRefuted : Bool := true

/-- **Graveyard pin — `fxMode_hasArcGodementSamePartitionFreshProof` stays `false` FOREVER against the refuted
literal.**  `ArcGodementSamePartitionFresh` is now machine-refuted (`not_arcGodementSamePartitionFresh`), so its
honesty pin (`ArcPartitionCommute.lean:545`, `def fxMode_hasArcGodementSamePartitionFreshProof : Bool := false`)
CANNOT be flipped — the statement it names is false.  This is the exact `not_arcGodementSamePartition` /
`fxMode_hasArcSamePartitionProof` precedent, transported to the fresh residual.  `rfl`. -/
theorem arcGodementFreshForestGapRefutation_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the CORRECTED (forest) residual is the RECORDED, still-OPEN target.**  The genuine replacement
`ArcGodementSamePartitionFreshForest` (`ArcFreshGatedPartitionCommute.lean:55`) is already recorded and reduced from
the count route (`arcGodementSamePartitionFreshForest_of_coreSwapSimCount`); its closure marker
`fxMode_hasArcForestFreshResidualClosed` stays `false` (residual (2) `ArcGodementCoreSwapSimCount` unbuilt — the
WALL-BOX / WALL-WIDTH / WALL-WHISKER census is unchanged).  The counterexample here is EXCLUDED from that target by
`arcFreshCyclicForestGapState_notForest`, so the forest hypothesis is necessary, not decorative.  `rfl`. -/
theorem arcGodementFreshForestGapRefutation_forestResidualClosed_stays_false :
    fxMode_hasArcForestFreshResidualClosed = false := rfl

end FX1Poly.Polygraph
