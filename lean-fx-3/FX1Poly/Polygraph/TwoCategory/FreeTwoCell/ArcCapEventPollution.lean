import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcCapEventPollution — the half-touch kill's counting substrate

A cap that consumes exactly ONE tracked pair node "pollutes" that node's component with a
cap event; if a LATER cap consumes the other node, a second (fresh, hence distinct) event
joins the other component; the final partner pin merges both components, so the final count
of cap events on the pair's strand is at least TWO — contradicting the cap-head pin of
exactly one.  This file ships the counting substrate for that argument, designed so the
half-touch kill needs NO count-threading fold invariant — only end-state counting of two
persisted distinct events:

* `mem_capEventNodes_stepArcAtom` / `mem_capEventNodes_processArcSpine` — cap-event
  membership is monotone through the fold (cups and boxes keep the list, caps cons onto it);
* `stepCapArc_newEventMem` — the cap's own fresh event node is recorded;
* `isSameComponent_stepCapArc_eventFirstRead` / `isSameComponent_stepCapArc_consumedReads` —
  the cap links its event to its first read, and its two reads to each other (through the
  shipped joined/ofBase kit, threading the forest invariant);
* `countEventsInRoot_ge_one_ofMember` / ★ `countEventsInRoot_ge_two_ofDistinctMembers` —
  the counting: two DISTINCT recorded events whose roots match the probed root force a
  count of at least two;
* `isSameComponent_ofPartnerIndexOfHit` — the partner pin reader: a partner hit at distinct
  indices IS a same-component fact between the two boundary reads (scan soundness, no
  untouchedness needed).

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Cap-event membership is monotone through the fold -/

/-- One arc step keeps every recorded cap event recorded — cups and boxes leave the list
untouched, a cap conses its fresh event onto it. -/
theorem mem_capEventNodes_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    {event : Nat} (eventMem : event ∈ state.capEventNodes) :
    event ∈ (stepArcAtom state atom).capEventNodes := by
  unfold stepArcAtom
  split
  · exact eventMem
  · exact List.Mem.tail _ eventMem
  · exact eventMem

/-- The whole fold keeps every recorded cap event recorded. -/
theorem mem_capEventNodes_processArcSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} {event : Nat} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    event ∈ state.capEventNodes →
    event ∈ (processArcSpine state atoms).capEventNodes
  | [], _, eventMem => eventMem
  | atom :: rest, state, eventMem => by
      show event ∈ (processArcSpine (stepArcAtom state atom) rest).capEventNodes
      exact mem_capEventNodes_processArcSpine rest (stepArcAtom state atom)
        (mem_capEventNodes_stepArcAtom state atom eventMem)

/-- A cap step records its own fresh event node. -/
theorem stepCapArc_newEventMem (state : ArcWireState) (position : Nat) :
    state.nextFresh ∈ (stepCapArc state position).capEventNodes :=
  List.Mem.head _

/-! ## The cap's joins, read off at the step -/

/-- A cap links its fresh event node to its first consumed read. -/
theorem isSameComponent_stepCapArc_eventFirstRead (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepCapArc state position).links
      state.nextFresh (natListGetAt state.openWires position) = true := by
  show isSameComponent
    (unionFindJoin
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      state.nextFresh (natListGetAt state.openWires position))
    state.nextFresh (natListGetAt state.openWires position) = true
  exact isSameComponent_unionFindJoin_joined
    (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)))
    (isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest)
    state.nextFresh (natListGetAt state.openWires position)

/-- A cap links its two consumed reads to each other. -/
theorem isSameComponent_stepCapArc_consumedReads (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepCapArc state position).links
      (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) = true := by
  show isSameComponent
    (unionFindJoin
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      state.nextFresh (natListGetAt state.openWires position))
    (natListGetAt state.openWires position)
    (natListGetAt state.openWires (position + 1)) = true
  exact isSameComponent_unionFindJoin_ofBase
    (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)))
    (isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest)
    state.nextFresh (natListGetAt state.openWires position)
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (isSameComponent_unionFindJoin_joined state.links forest
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)))

/-! ## The counting: two distinct in-root events force a count of two -/

/-- One recorded event whose root matches the probed root gives a count of at least one. -/
theorem countEventsInRoot_ge_one_ofMember (links : List (Nat × Nat)) (rootHere : Nat)
    {event : Nat} : (eventNodes : List Nat) → event ∈ eventNodes →
    unionFindRootOf links event = rootHere →
    1 ≤ countEventsInRoot links rootHere eventNodes
  | [], eventMem, _ => nomatch eventMem
  | head :: rest, eventMem, eventRoot => by
      show 1 ≤ (if unionFindRootOf links head == rootHere then 1 else 0)
        + countEventsInRoot links rootHere rest
      cases eventMem with
      | head =>
          rw [eventRoot, show (rootHere == rootHere) = true from decide_eq_true rfl]
          exact Nat.le_add_right 1 (countEventsInRoot links rootHere rest)
      | tail _ inRest =>
          exact Nat.le_trans
            (countEventsInRoot_ge_one_ofMember links rootHere rest inRest eventRoot)
            (Nat.le_add_left (countEventsInRoot links rootHere rest) _)

/-- ★ **Two DISTINCT recorded events whose roots match the probed root force a count of at
least two** — the half-touch kill's arithmetic heart. -/
theorem countEventsInRoot_ge_two_ofDistinctMembers (links : List (Nat × Nat))
    (rootHere : Nat) {firstEvent secondEvent : Nat} :
    (eventNodes : List Nat) → firstEvent ∈ eventNodes → secondEvent ∈ eventNodes →
    firstEvent ≠ secondEvent →
    unionFindRootOf links firstEvent = rootHere →
    unionFindRootOf links secondEvent = rootHere →
    2 ≤ countEventsInRoot links rootHere eventNodes
  | [], firstMem, _, _, _, _ => nomatch firstMem
  | head :: rest, firstMem, secondMem, eventsNe, firstRoot, secondRoot => by
      show 2 ≤ (if unionFindRootOf links head == rootHere then 1 else 0)
        + countEventsInRoot links rootHere rest
      cases firstMem with
      | head =>
          cases secondMem with
          | head => exact absurd rfl eventsNe
          | tail _ secondInRest =>
              rw [firstRoot, show (rootHere == rootHere) = true from decide_eq_true rfl]
              show 2 ≤ 1 + countEventsInRoot links rootHere rest
              rw [Nat.add_comm 1 (countEventsInRoot links rootHere rest)]
              exact Nat.succ_le_succ
                (countEventsInRoot_ge_one_ofMember links rootHere rest secondInRest
                  secondRoot)
      | tail _ firstInRest =>
          cases secondMem with
          | head =>
              rw [secondRoot, show (rootHere == rootHere) = true from decide_eq_true rfl]
              show 2 ≤ 1 + countEventsInRoot links rootHere rest
              rw [Nat.add_comm 1 (countEventsInRoot links rootHere rest)]
              exact Nat.succ_le_succ
                (countEventsInRoot_ge_one_ofMember links rootHere rest firstInRest
                  firstRoot)
          | tail _ secondInRest =>
              exact Nat.le_trans
                (countEventsInRoot_ge_two_ofDistinctMembers links rootHere rest
                  firstInRest secondInRest eventsNe firstRoot secondRoot)
                (Nat.le_add_left (countEventsInRoot links rootHere rest) _)

/-! ## The partner pin reader -/

/-- **A partner hit IS a same-component fact**: when the partner read-off at an index names
a DIFFERENT index, the two boundary reads share a component — scan soundness, with no
untouchedness hypothesis. -/
theorem isSameComponent_ofPartnerIndexOfHit (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (total excludeIndex partnerIndex : Nat)
    (partnerNeExclude : partnerIndex ≠ excludeIndex)
    (hit : partnerIndexOf links boundaryNodes total excludeIndex = partnerIndex) :
    isSameComponent links (natListGetAt boundaryNodes excludeIndex)
      (natListGetAt boundaryNodes partnerIndex) = true := by
  have scanHit : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex
      (List.range total) = partnerIndex := hit
  have scanFound : findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex
      (List.range total) ≠ excludeIndex := by
    rw [scanHit]
    exact partnerNeExclude
  have rootEquation := findPartnerScan_root_ofFound links boundaryNodes
    (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex
    (List.range total) scanFound
  rw [scanHit] at rootEquation
  show (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)
      == unionFindRootOf links (natListGetAt boundaryNodes partnerIndex)) = true
  rw [rootEquation]
  exact decide_eq_true rfl

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-event pollution substrate is SHIPPED.**  Cap-event membership
is monotone through the fold, a cap records its fresh event and links it to its consumed
reads, two distinct in-root recorded events force a strand count of at least two, and a
partner hit reads off as a same-component fact.  NOT yet shipped: the half-touch kill
assembly (double scan + freshness-distinct events + these pieces against the cap-head count
pin of exactly one).  `= true`. -/
def fxMode_hasArcCapEventPollutionSubstrate : Bool := true

end FX1Poly.Polygraph
