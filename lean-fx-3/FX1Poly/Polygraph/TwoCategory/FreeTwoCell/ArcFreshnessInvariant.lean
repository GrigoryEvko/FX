import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommuteRefutation

/-! # mode-3 floor — MODE-COMMUTE truth-probes: freshness is the reachable invariant, forest is the dividing line

`FreeTwoCellArcPartitionCommute` refuted the unconditional Godement arc residual `ArcGodementSamePartition`
(`not_arcGodementSamePartition`) and `FreeTwoCellArcPartitionCommuteRefutation` refuted the parent extract-level
`ArcGodementPartitionCommute` (`not_arcGodementPartitionCommute`) — both at the adversarial state
`ArcWireState.mk [] [(100, 0)] 100 0 [] []`, whose `links` names the id `100 = nextFresh`.  The corrected residual
is `ArcGodementSamePartitionFresh`, conditioned on `ArcStateFresh state` (every mentioned id `< nextFresh`).

Before proving anything, this file TRUTH-PROBES the invariant against the actual computation — the mandatory
sanity pins that any freshness-gated commute proof must respect:

  ★ **Positive control (the seed satisfies the invariant).**  The fold seed `mk (range n) [] n 0 [] []` is
    `ArcStateFresh`, `isUnionFindForest`, and (for `0 < n`) non-degenerate — the exact bundle the LIVE count-route
    `arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` consumes.

  ★ **Negative control (the r2 adversarial state VIOLATES the invariant).**  `refuteAdversarialState` is NOT
    `ArcStateFresh`: its single `links` edge `(100, 0)` has child endpoint `100 = nextFresh`, so
    `100 < nextFresh` is FALSE (`refuteAdversarialState_violatesFresh`).  And at that state the two Godement run
    orders genuinely DIVERGE on boundary connectivity (`arcAdversarialBoundaryDiverges`) — the divergence the
    freshness precondition rules out.

  ★ **The dividing line — freshness does NOT imply forest.**  A fresh-but-cyclic state (links `[(0,1),(1,0)]`,
    `nextFresh = 5`) IS `ArcStateFresh` (`arcFreshCyclicState_isFresh`) yet is NOT `isUnionFindForest`
    (`arcFreshCyclicLinks_notForest`).  So `ArcStateFresh` is strictly weaker than `ArcStateFresh ∧ forest` — the
    reason the count-route reduction genuinely needs the FOREST hypothesis (residual (2)
    `ArcGodementCoreSwapSimCount` requires `isUnionFindForest state.links`), and the reason the standalone
    `ArcGodementSamePartitionFresh` def is stronger than what the count-route provides.

  ★ **The gated commute on a concrete reachable state.**  From a slack-fresh forest state
    (`mk [] [(50,51)] 100 0 [] []`, `nextFresh` far above every mentioned id, `links` a genuine forest) the two
    Godement run orders AGREE on every partition-view component the residual reads
    (`arcSlackForestPartitionComponentsAgree`) — the same interchange the refutation `decide`d to DISagree from the
    adversarial state.  Freshness fixes it.

These probes DECIDE nothing about the general witness (residual (2) `ArcGodementCoreSwapSimCount`, the block-swap
`sigma` over arbitrary cells) — they only pin the invariant's boundary so no later step fabricates a flip.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.

Raw Lean 4 + Init; the invariant checks are `List.Mem`-constructor casing + `by decide` on closed `Nat` facts (the
same `decide`-on-small-concrete-states discipline the shipped `refute_diagram_differs` /
`freshSwapPartitionComponentsAgree` use), never `decide` on open terms.  No `omega`, no `simp`-AC, no `propext`
lemmas, no `WellFounded.fix`.  Per-declaration `#assert_no_axioms` + independent `#print axioms` in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Positive control — the fold SEED satisfies the full reachable-state bundle -/

/-- The canonical fold seed at boundary width 3 is `ArcStateFresh` (its open wires are `0…2 < 3 = nextFresh`, its
links / events empty). -/
theorem arcSeedThreeIsFresh : ArcStateFresh (ArcWireState.mk (List.range 3) [] 3 0 [] []) :=
  arcStateFresh_initial 3

/-- The fold seed has a FOREST `links` (empty) — the acyclicity the count-route consumes. -/
theorem arcSeedThreeIsForest :
    isUnionFindForest (ArcWireState.mk (List.range 3) [] 3 0 [] []).links :=
  isUnionFindForest_initialLinks 3

/-- The fold seed at a non-empty boundary is non-degenerate (`0 < nextFresh`) — the `nfPos` the count-route
consumes.  (At the EMPTY boundary `nextFresh = 0`, handled by the counter-shift proxy, not here.) -/
theorem arcSeedThreeIsNonDegenerate :
    0 < (ArcWireState.mk (List.range 3) [] 3 0 [] []).nextFresh := by decide

/-! ## Negative control — the r2 adversarial state VIOLATES freshness (and its run orders diverge) -/

/-- ★ **The adversarial state is NOT fresh.**  `refuteAdversarialState.links = [(100, 0)]` and
`refuteAdversarialState.nextFresh = 100`, so the freshness clause `edge.1 < nextFresh` on the edge `(100, 0)`
demands `100 < 100` — false.  This is the exact clause the refutation exploited: the first cup's fresh left leg
`nextFresh = 100` is pre-named by the `links` edge, so it is NOT a fresh root and drags boundary port `0` into a
different block per run order. -/
theorem refuteAdversarialState_violatesFresh : ¬ ArcStateFresh refuteAdversarialState := by
  intro stateFresh
  have edgeChildBelowFresh : (100, 0).1 < refuteAdversarialState.nextFresh :=
    (stateFresh.2.1 (100, 0) (List.Mem.head [])).1
  exact Nat.lt_irrefl 100 edgeChildBelowFresh

/-- ★ **The two Godement run orders DIVERGE on boundary connectivity at the adversarial state.**  Bottom port `0`
shares top port `3`'s component in the redex but not the reduct — kernel-decided on the two small concrete states
(the public-state twin of the parent's private `arcRefute_boundarySameComponent_differs`). -/
theorem arcAdversarialBoundaryDiverges :
    boundarySameComponent 3 refuteRedexState 0 3 ≠ boundarySameComponent 3 refuteReductState 0 3 := by
  decide

/-! ## The dividing line — freshness does NOT imply forest -/

/-- A **fresh-but-cyclic** arc state: `links = [(0,1),(1,0)]` names only ids `< 5 = nextFresh`, so it is fresh, but
the two edges form a 2-cycle, so it is not a union-find forest. -/
def arcFreshCyclicState : ArcWireState := ArcWireState.mk [] [(0, 1), (1, 0)] 5 0 [] []

/-- ★ **The cyclic state IS fresh.**  Every mentioned id lies in `{0,1} ⊂ [0,5)`; open wires and event lists are
empty. -/
theorem arcFreshCyclicState_isFresh : ArcStateFresh arcFreshCyclicState := by
  unfold ArcStateFresh arcFreshCyclicState
  decide

/-- ★ **The cyclic state's `links` is NOT a forest.**  `isUnionFindForest [(0,1),(1,0)]` would force the second
endpoint `1` of the head edge to be parentless in the tail `[(1,0)]`, but `unionFindParent [(1,0)] 1 = some 0`.  So
`ArcStateFresh` is strictly weaker than `ArcStateFresh ∧ isUnionFindForest links` — the gap the count-route's
forest hypothesis closes. -/
theorem arcFreshCyclicLinks_notForest : ¬ isUnionFindForest [(0, 1), (1, 0)] := by
  intro forest
  rw [isUnionFindForest_cons] at forest
  exact absurd forest.2.1 (by decide)

/-! ## The gated commute on a concrete reachable (slack-fresh, forest) state -/

/-- A **slack-fresh forest** starting state: `nextFresh = 100` sits far above every mentioned id, and the single
`links` edge `(50, 51)` is a genuine forest (distinct endpoints, empty tail).  Reachable-shaped — a pre-existing
disjoint component plus a slack counter — and, unlike the adversarial state, it names no id `≥ nextFresh`. -/
def arcSlackForestState : ArcWireState := ArcWireState.mk [] [(50, 51)] 100 0 [] []

/-- The slack-fresh forest state is `ArcStateFresh`: `{50,51} ⊂ [0,100)`, open wires and events empty. -/
theorem arcSlackForestState_isFresh : ArcStateFresh arcSlackForestState := by
  unfold ArcStateFresh arcSlackForestState
  decide

/-- The slack-fresh state's `links = [(50,51)]` is a forest (single edge, distinct endpoints). -/
theorem arcSlackForestState_isForest : isUnionFindForest arcSlackForestState.links := by
  rw [show arcSlackForestState.links = [(50, 51)] from rfl, isUnionFindForest_cons]
  exact ⟨rfl, rfl, by decide, trivial⟩

/-- The REDEX run order from the slack-fresh forest state: `cellAlphaUpper` (cup) then `cellBeta` (cup), with the
refutation instance's context shifts (the same interchange the parent refuted from the adversarial state). -/
def arcSlackRedexState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell arcSlackForestState refuteNilBase (composePath refuteNilBase refuteNilBase)
        refuteIdentityBase)
      refuteNilBase (composePath refuteNilBase refuteNilBase) adjunctionUnitTwoCell)
    (composePath refuteNilBase adjunctionLeftThenRight) refuteNilBase adjunctionUnitTwoCell)
    (composePath refuteNilBase adjunctionLeftThenRight) refuteNilBase refuteIdentityLeftRight

/-- The REDUCT run order — `cellBeta` and `cellAlphaUpper` transposed with their context shift. -/
def arcSlackReductState : ArcWireState :=
  runArcCell (runArcCell (runArcCell
      (runArcCell arcSlackForestState refuteNilBase (composePath refuteNilBase refuteNilBase)
        refuteIdentityBase)
      (composePath refuteNilBase refuteNilBase) refuteNilBase adjunctionUnitTwoCell)
    refuteNilBase (composePath adjunctionLeftThenRight refuteNilBase) adjunctionUnitTwoCell)
    (composePath refuteNilBase adjunctionLeftThenRight) refuteNilBase refuteIdentityLeftRight

/-- ★ **Freshness fixes the refutation on a reachable forest state.**  From the slack-fresh forest state the two
Godement run orders AGREE on every partition-view component the residual reads — the open-wire / loop counts, the
`boundarySameComponent` relation at the adversarially-diverging pair `(0, 3)` and at a connected cup pair `(3, 4)`,
and the per-port internal cup/cap counts at port `3`.  Kernel-decided on the two small concrete states, exactly as
`arcAdversarialBoundaryDiverges` `decide`s the DISagreement from the adversarial (non-fresh) state. -/
theorem arcSlackForestPartitionComponentsAgree :
    arcSlackRedexState.openWires.length = arcSlackReductState.openWires.length
    ∧ arcSlackRedexState.loops = arcSlackReductState.loops
    ∧ boundarySameComponent 3 arcSlackRedexState 0 3 = boundarySameComponent 3 arcSlackReductState 0 3
    ∧ boundarySameComponent 3 arcSlackRedexState 3 4 = boundarySameComponent 3 arcSlackReductState 3 4
    ∧ internalEventCountAt arcSlackRedexState.links (boundaryNodesOf 3 arcSlackRedexState)
          arcSlackRedexState.cupEventNodes 3
        = internalEventCountAt arcSlackReductState.links (boundaryNodesOf 3 arcSlackReductState)
          arcSlackReductState.cupEventNodes 3
    ∧ internalEventCountAt arcSlackRedexState.links (boundaryNodesOf 3 arcSlackRedexState)
          arcSlackRedexState.capEventNodes 3
        = internalEventCountAt arcSlackReductState.links (boundaryNodesOf 3 arcSlackReductState)
          arcSlackReductState.capEventNodes 3 := by
  decide

/-! ## Honesty marker -/

/-- **Honesty marker — the freshness invariant and the forest dividing line are TRUTH-PROBED.**  The fold seed
satisfies the reachable bundle (`arcSeedThreeIsFresh` / `arcSeedThreeIsForest` / `arcSeedThreeIsNonDegenerate`);
the r2 adversarial state violates freshness (`refuteAdversarialState_violatesFresh`) and its run orders diverge
(`arcAdversarialBoundaryDiverges`); freshness does NOT imply forest (`arcFreshCyclicState_isFresh` +
`arcFreshCyclicLinks_notForest`), so the count-route genuinely needs the forest hypothesis; and the gated commute
holds on a concrete reachable slack-fresh forest state (`arcSlackForestPartitionComponentsAgree`).  These pin the
invariant's boundary — they do NOT prove the general witness (residual (2) `ArcGodementCoreSwapSimCount`), so
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `= true`. -/
def fxMode_hasArcFreshnessInvariantProbed : Bool := true

end FX1Poly.Polygraph
