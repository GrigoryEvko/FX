import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcMatchViewBridge — the arc run's boundary connectivity IS the matching run's (event nodes peel)

The pure-block sorts (`pureCupSpine_sort`, `pureCapSpine_sort`) consume ARC-structure equality, while the
fib-3 valley descent supplies MATCHING equality (`matchingOf`).  Converting the second into the first needs the
**diagram = matching bridge**: `(arcStructureOfSpineList bc l).diagram = matchingOfSpineList bc l`.  The
`.diagram` field is `extractDiagram bc (arcToWire (processArcSpine …))`, so the bridge reduces to showing the arc
run's `WireState` projection and the matching run share the boundary-connectivity view that `extractDiagram`
reads (`extractDiagram_eq_of_connectivityView`).

This brick ships the **per-step event-node peel** that is the crux of that comparison: the arc step differs from
the matching step ONLY by a fresh event node unioned into its arc's component, and an event node is never a
boundary end, so it is invisible to the boundary same-component relation.  Concretely, a single arc step's
`links` (projected to a `WireState`) share the boundary connectivity of the corresponding matching step's
`links`, on every probe below the arc's freshness bound (plus the two fresh cup legs).

  * `arcToWire` — project an `ArcWireState` onto the `WireState` the matching extract reads.
  * ★ `isSameComponent_stepCupArc_eq_stepCup` — a CUP arc step's boundary view equals the matching CUP step's,
    on probes below `nextFresh + 2` (covering the two fresh legs); the event node `nextFresh + 2` peels.
  * ★ `isSameComponent_stepCapArc_eq_stepCap` — a CAP arc step's boundary view equals the matching CAP step's,
    on probes below `nextFresh` (a cap only removes wires, so no fresh boundary node appears); the event node
    `nextFresh` peels, and the matching cap's same-component no-op branch collapses to the genuine wire join.

Both reuse the shipped fresh-join transparency toolkit (`ArcFreshComponentInvisibility`).  What this brick does
NOT ship: the lockstep view-simulation fold over a whole spine, nor the assembled `.diagram = matchingOf`
bridge — those consume these step peels.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Project an `ArcWireState` onto the `WireState` the matching extract reads: drop the cup/cap event-node
bookkeeping, keep the open wires, links, fresh counter, and loop count.  Definitionally the `WireState`
`extractArc` feeds to `extractDiagram` for the arc structure's `.diagram` field. -/
def arcToWire (state : ArcWireState) : WireState :=
  { openWires := state.openWires, links := state.links, nextFresh := state.nextFresh, loops := state.loops }

/-- ★ **A cup arc step's boundary view equals the matching cup step's, below `nextFresh + 2`.**  The two steps
splice the SAME two fresh legs and differ only by the arc step's event node `nextFresh + 2` unioned into the
left leg's component.  That event node sits above every post-step boundary node (the two legs are `nextFresh`,
`nextFresh + 1`; every old node is below `nextFresh`), so it is component-invisible: the arc step's boundary
connectivity is exactly the matching step's leg join.  The event join peels via
`isSameComponent_unionFindJoin_offProbes`. -/
theorem isSameComponent_stepCupArc_eq_stepCup (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (probeOne probeTwo : Nat)
    (probeOneBelow : probeOne < state.nextFresh + 2) (probeTwoBelow : probeTwo < state.nextFresh + 2) :
    isSameComponent (stepCupArc state position).links probeOne probeTwo
      = isSameComponent (stepCup (arcToWire state) position).links probeOne probeTwo := by
  obtain ⟨_openBelow, linksBelow, _cupBelow, _capBelow⟩ := fresh
  have bumpTwo : state.nextFresh < state.nextFresh + 2 := Nat.lt_add_of_pos_right (by decide)
  have linksBelowBumped :
      ∀ edge ∈ state.links, edge.1 < state.nextFresh + 2 ∧ edge.2 < state.nextFresh + 2 :=
    fun edge edgeInLinks =>
      ⟨Nat.lt_trans (linksBelow edge edgeInLinks).1 bumpTwo,
        Nat.lt_trans (linksBelow edge edgeInLinks).2 bumpTwo⟩
  have parentsBelowBumped : ∀ edge ∈ state.links, edge.2 < state.nextFresh + 2 :=
    fun edge edgeInLinks => (linksBelowBumped edge edgeInLinks).2
  have leftLegRootBelow : unionFindRootOf state.links state.nextFresh < state.nextFresh + 2 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 2) parentsBelowBumped
      state.nextFresh bumpTwo
  have rightLegRootBelow :
      unionFindRootOf state.links (state.nextFresh + 1) < state.nextFresh + 2 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 2) parentsBelowBumped
      (state.nextFresh + 1) (Nat.add_lt_add_left (by decide) state.nextFresh)
  have legJoinBelow :
      ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
        edge.1 < state.nextFresh + 2 ∧ edge.2 < state.nextFresh + 2 :=
    unionFindJoin_all_lt (state.nextFresh + 2) state.links state.nextFresh (state.nextFresh + 1)
      linksBelowBumped leftLegRootBelow rightLegRootBelow
  have legJoinForest :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have offEventOne :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) probeOne = false :=
    isSameComponent_offFreshNode _ (state.nextFresh + 2)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).1)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).2)
      (state.nextFresh + 2) probeOne (Nat.le_refl (state.nextFresh + 2)) probeOneBelow
  have offEventTwo :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) probeTwo = false :=
    isSameComponent_offFreshNode _ (state.nextFresh + 2)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).1)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).2)
      (state.nextFresh + 2) probeTwo (Nat.le_refl (state.nextFresh + 2)) probeTwoBelow
  show isSameComponent (unionFindJoin (unionFindJoin state.links state.nextFresh
          (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) probeOne probeTwo
    = isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        probeOne probeTwo
  exact isSameComponent_unionFindJoin_offProbes
    (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) legJoinForest
    (state.nextFresh + 2) state.nextFresh probeOne probeTwo offEventOne offEventTwo

/-- The matching cap step's boundary view is the genuine wire join's: in the same-component branch the join is a
no-op (`unionFindJoin_ofSameComponent`), so the retained `state.links` already equals the join; in the other
branch the step IS the join. -/
theorem isSameComponent_stepCap_eq_wireJoin (state : WireState) (position : Nat)
    (probeOne probeTwo : Nat) :
    isSameComponent (stepCap state position).links probeOne probeTwo
      = isSameComponent
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          probeOne probeTwo := by
  dsimp only [stepCap]
  split
  · rename_i sameBranch
    rw [unionFindJoin_ofSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) sameBranch]
  · rfl

/-- ★ **A cap arc step's boundary view equals the matching cap step's, below `nextFresh`.**  A cap consumes two
wires and allocates only its event node `nextFresh`, so every post-step boundary node stays below `nextFresh`.
The arc step's view at such old probes is the genuine wire join's (`isSameComponent_stepCapArc_oldProbes`, the
event node peels), and the matching step's view is the same genuine wire join (`isSameComponent_stepCap_eq_wireJoin`).
The projected open wires and links match because `arcToWire` keeps them verbatim. -/
theorem isSameComponent_stepCapArc_eq_stepCap (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (probeOne probeTwo : Nat)
    (probeOneBelow : probeOne < state.nextFresh) (probeTwoBelow : probeTwo < state.nextFresh) :
    isSameComponent (stepCapArc state position).links probeOne probeTwo
      = isSameComponent (stepCap (arcToWire state) position).links probeOne probeTwo := by
  rw [isSameComponent_stepCapArc_oldProbes state position fresh forest probeOne probeTwo
      probeOneBelow probeTwoBelow,
    isSameComponent_stepCap_eq_wireJoin (arcToWire state) position probeOne probeTwo]
  dsimp only [arcToWire]

/-! ## Honesty marker -/

/-- **Honesty marker — the per-step event-node peel is SHIPPED.**  A cup arc step and a cap arc step, projected
to `WireState`s via `arcToWire`, share the boundary same-component view of the corresponding matching steps
(`isSameComponent_stepCupArc_eq_stepCup`, `isSameComponent_stepCapArc_eq_stepCap`): the fresh event node is
component-invisible to every boundary probe, reusing the shipped fresh-join transparency toolkit.  This is the
crux ingredient of the diagram = matching bridge.  What this brick does NOT claim: the lockstep view-simulation
fold over a whole spine (threading `ArcStateFresh` + forest on the arc side and `MatchingSwapStateConditions` on
the matching side, dispatching each atom onto these peels plus the shipped `matchingViewAgrees_step*`), nor the
assembled `(arcStructureOfSpineList bc l).diagram = matchingOfSpineList bc l` those consume.  `= true`. -/
def fxMode_hasArcMatchViewStepPeel : Bool := true

end FX1Poly.Polygraph
