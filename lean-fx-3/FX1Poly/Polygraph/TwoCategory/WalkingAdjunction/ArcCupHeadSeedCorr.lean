import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexInjective

/-! # ArcCupHeadSeedCorr — the seed component correspondence at the cup head (peel campaign H, seed rung)

The whole-spine component fold (`arcComponentShiftCorr_processArcSpine`) consumes a SEED
`ArcComponentShiftCorr` at the head pair's initial states.  This file builds that seed for the CUP
head — the last unclaimed leaf of the component leg.

The composite run's seed state is `stepCupArc <fresh bottomCount> windowPosition`, whose links are the
head cup's two joins `join(join([], bottomCount, bottomCount+1), bottomCount+2, bottomCount)` — the leg
join on the two fresh legs plus the event join.  The fresh tail run's seed has empty links.  The seed
correspondence factors as:

  * `arcCupHead_eventAbsorb` — the EVENT join `(bottomCount+2)~bottomCount` is invisible to every
    `sigma`-image query, because the reindexing never hits the event node
    (`arcCupHeadReindex_missesEventNode`), so the event node stays a singleton disconnected from every
    image;
  * the LEG join transports via the shipped `isSameComponent_unionFindJoin_mapTransport` with the
    empty-links base correspondence — which IS `arcCupHeadReindex_beqTransport` read through
    `isSameComponent_nilEq` — after rewriting the two legs `sigma windowPosition = bottomCount`,
    `sigma (windowPosition+1) = bottomCount+1` by the shipped `…leftLeg`/`…rightLeg` reads.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Over the empty link list every node is its own root, so same-component is bare equality
(definitional: `unionFindRootOf []` computes to the identity). -/
theorem isSameComponent_nilEq (firstNode secondNode : Nat) :
    isSameComponent [] firstNode secondNode = (firstNode == secondNode) := rfl

/-- **The cup-head event node is disconnected from every reindexing image.**  Over the leg-join
`join([], bottomCount, bottomCount+1)`, the event node `bottomCount+2` shares a component with a probe
value only when the probe already equals it — but the reindexing never produces `bottomCount+2`
(`missesEvent`), so the query is uniformly false. -/
theorem arcCupHead_eventDisconnected (bottomCount probeValue : Nat)
    (missesEvent : (bottomCount + 2 == probeValue) = false) :
    isSameComponent (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) probeValue
      = false := by
  have belowSuccTwo : (bottomCount == bottomCount + 2) = false :=
    decide_eq_false (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self bottomCount)))
  have eventNeSucc : (bottomCount + 2 == bottomCount + 1) = false :=
    decide_eq_false (Ne.symm (Nat.ne_of_lt (Nat.lt_succ_self (bottomCount + 1))))
  rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil bottomCount (bottomCount + 1)
      (bottomCount + 2) probeValue,
    isSameComponent_nilEq (bottomCount + 2) probeValue,
    isSameComponent_nilEq bottomCount (bottomCount + 2),
    isSameComponent_nilEq (bottomCount + 1) probeValue,
    isSameComponent_nilEq bottomCount probeValue,
    isSameComponent_nilEq (bottomCount + 2) (bottomCount + 1),
    missesEvent, belowSuccTwo, eventNeSucc, Bool.false_and, Bool.and_false, Bool.or_false,
    Bool.or_false]

/-- ★ **The event join is absorbed on every reindexing-image query.**  Both images miss the event
node, so joining `(bottomCount+2)~bottomCount` on top of the leg join changes no `sigma`-image
connectivity. -/
theorem arcCupHead_eventAbsorb (bottomCount sigmaLeft sigmaRight : Nat)
    (missesLeft : (bottomCount + 2 == sigmaLeft) = false)
    (missesRight : (bottomCount + 2 == sigmaRight) = false) :
    isSameComponent (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
        (bottomCount + 2) bottomCount) sigmaLeft sigmaRight
      = isSameComponent (unionFindJoin [] bottomCount (bottomCount + 1)) sigmaLeft sigmaRight := by
  rw [isSameComponent_unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1) isUnionFindForest_nil)
      (bottomCount + 2) bottomCount sigmaLeft sigmaRight,
    arcCupHead_eventDisconnected bottomCount sigmaLeft missesLeft,
    arcCupHead_eventDisconnected bottomCount sigmaRight missesRight,
    Bool.false_and, Bool.false_and, Bool.or_false, Bool.or_false]

/-- ★ **The seed component correspondence at the cup head.**  The composite run's cup-head state
(links = the two head-cup joins) corresponds, under the cup-head reindexing, to the fresh tail run's
seed (empty links) with the leg-join at the window applied — the base case the whole-spine component
fold folds over. -/
theorem arcComponentShiftCorr_cupHeadSeed (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      windowPosition (windowPosition + 1)
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []).links
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition).links := by
  intro probeLeft probeRight
  have baseCorr : ∀ firstProbe secondProbe : Nat,
      isSameComponent []
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1 firstProbe)
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1 secondProbe)
        = isSameComponent [] firstProbe secondProbe := by
    intro firstProbe secondProbe
    rw [isSameComponent_nilEq, isSameComponent_nilEq]
    exact arcCupHeadReindex_beqTransport bottomCount windowPosition firstProbe secondProbe
      windowFits
  have legTransport := isSameComponent_unionFindJoin_mapTransport
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1) [] [] isUnionFindForest_nil isUnionFindForest_nil
    baseCorr windowPosition (windowPosition + 1) probeLeft probeRight
  rw [arcCupHeadReindex_leftLeg bottomCount windowPosition windowFits,
    arcCupHeadReindex_rightLeg bottomCount windowPosition windowFits] at legTransport
  show isSameComponent (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
        (bottomCount + 2) bottomCount)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight)
    = isSameComponent (unionFindJoin [] windowPosition (windowPosition + 1)) probeLeft probeRight
  rw [arcCupHead_eventAbsorb bottomCount
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight)
      (arcCupHeadReindex_missesEventNode bottomCount windowPosition probeLeft windowFits)
      (arcCupHeadReindex_missesEventNode bottomCount windowPosition probeRight windowFits)]
  exact legTransport

/-! ## Honesty marker -/

/-- **Honesty marker — the SEED component correspondence at the cup head is SHIPPED (peel campaign H,
seed rung, component leg).**  `isSameComponent_nilEq` (empty-links same-component = equality),
`arcCupHead_eventDisconnected` + `arcCupHead_eventAbsorb` (the event join is invisible to reindexing
images, via `missesEventNode`), and `arcComponentShiftCorr_cupHeadSeed` (the seed
`ArcComponentShiftCorr` the whole-spine fold consumes) — assembled from the shipped
`isSameComponent_unionFindJoin_mapTransport`, `arcCupHeadReindex_beqTransport`/`_leftLeg`/`_rightLeg`.
What this marker does NOT claim: the cap-head seed analogue and the extract correspondence the
cancellation consumes.  `= true`. -/
def fxMode_hasArcCupHeadSeedCorr : Bool := true

end FX1Poly.Polygraph
