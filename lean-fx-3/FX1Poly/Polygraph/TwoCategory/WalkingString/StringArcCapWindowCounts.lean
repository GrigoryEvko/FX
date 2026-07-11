import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowCounts
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHeadFoldedSim
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapSeedClosure
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcComponentPersistence

/-! # WalkingString/StringArcCapWindowCounts — the consumed strand's event counts at the cap head,
ported (FC-3 r20, THE CLONE CAMPAIGN — floor)

Phantom-signature two-token clone of the walking-adjunction `ArcCapWindowCounts`, re-plumbed onto the
FOUR-generator adjoint-triple seed.  The peeled cap's consumed strand carries exactly ONE cap event
(the head's own, riding the persistent event-to-wire link `stringArcCapHeadFolded_eventWireLinked`) and
NO cup event at the composite end state (every reindexed image misses the strand — the string
seed-closure payoff `stringArcCapHeadFolded_windowAnchorMissesReindexed` over the append-split event
lists from the string sim `stringArcPositionalShiftSim_capHeadFolded`).  The right port reads the same
strand (`stringArcCapHeadFolded_consumedPairLinked`), so its root coincides with the left's.  The
private plumbing is graph-neutral and re-declared verbatim; the signature is a pure phantom, so ONLY
the `SpineAtom`-quantified statements clone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

/-- A failed `Nat` equality test fails in the flipped order too. -/
private theorem natBeqSymmFalse {leftValue rightValue : Nat}
    (missEq : (leftValue == rightValue) = false) : (rightValue == leftValue) = false :=
  decide_eq_false (fun valuesEqual => of_decide_eq_false missEq valuesEqual.symm)

/-- A mapped event list contributes NOTHING to a root every image misses — structural on
the event list, with each head's failed test rewritten to `false`. -/
private theorem countEventsInRoot_mapMissesAll (links : List (Nat × Nat)) (rootHere : Nat)
    (sigma : Nat → Nat)
    (missesRoot : ∀ eventNode : Nat,
      (unionFindRootOf links (sigma eventNode) == rootHere) = false) :
    (events : List Nat) → countEventsInRoot links rootHere (events.map sigma) = 0
  | [] => rfl
  | eventNode :: restEvents => by
      have restZero := countEventsInRoot_mapMissesAll links rootHere sigma missesRoot
        restEvents
      show (if unionFindRootOf links (sigma eventNode) == rootHere then 1 else 0)
          + countEventsInRoot links rootHere (restEvents.map sigma) = 0
      rw [missesRoot eventNode, restZero]
      exact rfl

/-! ## The consumed strand's counts -/

/-- ★ **The consumed strand carries exactly ONE cap event** — the head's own.  The
composite cap-event list is the reindexed fresh list over the `[bottomCount]` suffix;
every reindexed image misses the strand (the seed-closure payoff), and the head event
node stays linked to the consumed left wire. -/
theorem stringArcCapHeadFolded_windowStrandCapCount
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    countEventsInRoot
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          windowPosition)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).capEventNodes = 1 := by
  have missesRoot : ∀ eventNode : Nat,
      (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
            eventNode)
        == unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          windowPosition) = false :=
    fun eventNode =>
      natBeqSymmFalse
        (stringArcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition
          tailBoundary windowFits tailBoundaryFits atoms chained eventNode)
  have mappedMiss := countEventsInRoot_mapMissesAll
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).links
    (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      windowPosition)
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    missesRoot
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).capEventNodes
  have eventRootHits : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        bottomCount
      == unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition) = true :=
    stringArcCapHeadFolded_eventWireLinked bottomCount windowPosition windowFits atoms
  have singletonHits : countEventsInRoot
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      [bottomCount] = 1 := by
    show (if unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            bottomCount
          == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            windowPosition
          then 1 else 0)
        + 0 = 1
    rw [eventRootHits]
    exact rfl
  rw [(stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms).capEventsMap,
    countEventsInRoot_append
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      ((processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).capEventNodes.map
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
      [bottomCount],
    mappedMiss, singletonHits]

/-- ★ **The consumed strand carries NO cup event**: the composite cup-event list is the
reindexed fresh list over an EMPTY head suffix, and every reindexed image misses the
strand. -/
theorem stringArcCapHeadFolded_windowStrandCupCount
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    countEventsInRoot
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          windowPosition)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).cupEventNodes = 0 := by
  have missesRoot : ∀ eventNode : Nat,
      (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
            eventNode)
        == unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          windowPosition) = false :=
    fun eventNode =>
      natBeqSymmFalse
        (stringArcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition
          tailBoundary windowFits tailBoundaryFits atoms chained eventNode)
  have mappedMiss := countEventsInRoot_mapMissesAll
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).links
    (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      windowPosition)
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    missesRoot
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      atoms).cupEventNodes
  rw [(stringArcPositionalShiftSim_capHeadFolded bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms).cupEventsMap,
    countEventsInRoot_append
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition)
      ((processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).cupEventNodes.map
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3))
      [],
    mappedMiss]
  exact rfl

/-- **The right window port reads the SAME strand**: the consumed pair stays linked at the
end state, so the two ports' component roots coincide — the right port inherits the left
port's counts. -/
theorem stringArcCapHeadFolded_windowRightRootEq
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1)
      = unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          windowPosition := by
  have pairRootsBeq : (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        windowPosition
      == unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (windowPosition + 1)) = true :=
    stringArcCapHeadFolded_consumedPairLinked bottomCount windowPosition windowFits atoms
  exact (of_decide_eq_true pairRootsBeq).symm

/-! ## Honesty marker -/

/-- **Honesty marker — the consumed strand's event counts, ported (FC-3 r20 clone campaign).**
`stringArcCapHeadFolded_windowStrandCapCount` / `_windowStrandCupCount`: the peeled cap's consumed
strand carries exactly one cap event (the head's own) and no cup event.
`stringArcCapHeadFolded_windowRightRootEq`: the right window port's root equals the left's, so both
spliced ports inherit these counts.  What this marker does NOT claim: the assembled internal-count LIST
transports or the `FullArcStructure` equality.  `= true`. -/
def fxString_hasArcCapWindowCounts : Bool := true

end FX1Poly.Polygraph
