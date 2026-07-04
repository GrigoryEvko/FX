import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexInjectivity

/-! # ArcCupSeedCorr — the assembled component correspondence at the cup-head seed

The links leg of the head-cancellation seed, assembled from the value atoms: firing the
peeled CUP at the canonical seed produces the links
`join (join [] bottomCount (bottomCount+1)) (bottomCount+2) bottomCount` — the two fresh leg
wires joined, then the event node absorbed into their component.  Under the cup-head
reindexing every `sigma`-image query on that state reads as the fresh tail-run query with the
window pair joined first — `ArcComponentShiftCorr` at legs `windowPosition`,
`windowPosition + 1` over EMPTY base links.

The assembly is three moves.  The inner leg-join transports through the generic join
transport at empty link lists, whose pointwise hypothesis is definitionally the beq
correspondence (over `[]`, `isSameComponent` IS `==`); the zone reads rewrite its
`sigma`-image legs to the concrete fresh pair.  The outer event join expands through the
Boolean join characterization, and both extra disjuncts die because the event node
`bottomCount + 2` shares a component with NO reindexed probe — it is not a value of `sigma`
and differs from both legs literally.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The cup's event node `bottomCount + 2` shares no component of the joined leg pair with
any reindexed probe: the direct query is the event-node-avoidance atom, and the two
leg-routed disjuncts are literal mismatches. -/
private theorem cupSeedEventNodeMissesComponent (bottomCount windowPosition probeIndex : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    isSameComponent (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeIndex) = false := by
  rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil bottomCount (bottomCount + 1)
    (bottomCount + 2)
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 probeIndex)]
  have eventDiffersFromValue : isSameComponent [] (bottomCount + 2)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeIndex) = false :=
    arcCupHeadReindex_missesEventNode bottomCount windowPosition probeIndex windowFits
  have leftLegDiffersFromEvent : isSameComponent [] bottomCount (bottomCount + 2) = false :=
    decide_eq_false (fun legHitsEvent => Nat.lt_irrefl bottomCount
      (Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) (Nat.le_succ (bottomCount + 1)))
        (Nat.le_of_eq legHitsEvent.symm)))
  have eventDiffersFromRightLeg :
      isSameComponent [] (bottomCount + 2) (bottomCount + 1) = false :=
    decide_eq_false (fun eventHitsLeg => Nat.lt_irrefl (bottomCount + 1)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (bottomCount + 1))
        (Nat.le_of_eq eventHitsLeg)))
  rw [eventDiffersFromValue, leftLegDiffersFromEvent, eventDiffersFromRightLeg]
  cases hLeftLegQuery : isSameComponent [] bottomCount
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeIndex) with
  | true => rfl
  | false => rfl

/-- ★ **The component correspondence at the cup-head seed.**  The composite links (peeled cup
fired at the canonical seed) answer every `sigma`-image query exactly as the fresh tail run's
empty links with the window pair joined — the fold kit's `corr` premise at the cup head. -/
theorem arcComponentShiftCorr_cupHeadSeed (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      windowPosition (windowPosition + 1) []
      (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
        (bottomCount + 2) bottomCount) := by
  intro probeLeft probeRight
  have innerTransport : isSameComponent
      (unionFindJoin []
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 windowPosition)
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 (windowPosition + 1)))
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight)
    = isSameComponent (unionFindJoin [] windowPosition (windowPosition + 1))
        probeLeft probeRight :=
    isSameComponent_unionFindJoin_mapTransport
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      [] [] isUnionFindForest_nil isUnionFindForest_nil
      (fun leftProbe rightProbe =>
        arcCupHeadReindex_beqCorr bottomCount windowPosition leftProbe rightProbe windowFits)
      windowPosition (windowPosition + 1) probeLeft probeRight
  rw [arcCupHeadReindex_leftLeg bottomCount windowPosition windowFits,
    arcCupHeadReindex_rightLeg bottomCount windowPosition windowFits] at innerTransport
  rw [isSameComponent_unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
    (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1) isUnionFindForest_nil)
    (bottomCount + 2) bottomCount
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 probeLeft)
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 probeRight),
    cupSeedEventNodeMissesComponent bottomCount windowPosition probeLeft windowFits,
    cupSeedEventNodeMissesComponent bottomCount windowPosition probeRight windowFits,
    innerTransport]
  cases hBaseQuery : isSameComponent (unionFindJoin [] windowPosition (windowPosition + 1))
      probeLeft probeRight with
  | true => rfl
  | false => rfl

/-- The seed correspondence restated at the concrete head pair's STATES — the exact spelling
the fold consumes alongside `arcPositionalShiftSim_cupHeadSeed` (both link projections reduce
definitionally). -/
theorem arcComponentShiftCorr_cupHeadSeedState (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      windowPosition (windowPosition + 1)
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []).links
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition).links :=
  arcComponentShiftCorr_cupHeadSeed bottomCount windowPosition windowFits

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled component correspondence at the cup-head seed (peel
campaign H, seed rung, LINKS leg CLOSED at the cup).**  The event-node component-avoidance
helper (the direct atom plus two literal leg mismatches through the Boolean join
characterization), the assembled `ArcComponentShiftCorr` at the cup seed (inner leg-join by
the empty-links transport with the beq correspondence as its pointwise hypothesis, outer
event join absorbed disjunct-by-disjunct), and the state-spelled restatement the fold
consumes.  What this marker does NOT claim: the cap-head seed correspondence (its window legs
are range reads, not fresh literals, and its extra join is leg-internal), and the extract
correspondence the cancellation ultimately consumes.  `= true`. -/
def fxMode_hasArcCupHeadSeedCorr : Bool := true

end FX1Poly.Polygraph
