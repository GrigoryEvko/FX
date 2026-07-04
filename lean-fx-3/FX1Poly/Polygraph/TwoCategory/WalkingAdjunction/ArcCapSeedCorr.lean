import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapReindexInjectivity

/-! # ArcCapSeedCorr — the assembled component correspondence at the cap-head seed

The cap mirror of the cup seed correspondence, with one structural difference: the cap
CONSUMES the window pair, so the fresh tail run has NO corresponding join — the invariant's
legs are DEGENERATE (`0, 0`), and the degenerate leg-join over empty links vanishes by
computation.  Firing the peeled cap at the canonical seed joins the two window wires and
absorbs the event node `bottomCount` into their component; under the cap-head reindexing no
probe image ever meets that component (the two avoidance atoms), so both join layers strip
off and the correspondence reduces to the beq atom.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## The degenerate leg-join -/

/-- The degenerate leg-join vanishes: joining the literal node `0` with itself over empty
links finds equal roots and adds no edge. -/
private theorem degenerateLegJoin : unionFindJoin ([] : List (Nat × Nat)) 0 0 = [] := rfl

/-! ## The event-node component avoidance over the joined window pair -/

/-- The cap's event node `bottomCount` shares no component of the joined window pair with
any reindexed probe: the direct query is the event-node-avoidance atom, and the two
wire-routed disjuncts are literal mismatches. -/
private theorem capSeedEventNodeMissesComponent
    (bottomCount windowPosition tailBoundary probeIndex : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    isSameComponent (unionFindJoin [] windowPosition (windowPosition + 1)) bottomCount
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeIndex) = false := by
  rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
    (windowPosition + 1) bottomCount
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      probeIndex)]
  have eventDiffersFromValue : isSameComponent [] bottomCount
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeIndex) = false :=
    arcCapHeadReindex_missesEventNode bottomCount windowPosition tailBoundary probeIndex
      windowFits tailBoundaryFits
  have leftWireDiffersFromEvent :
      isSameComponent [] windowPosition bottomCount = false :=
    decide_eq_false (fun wireHitsEvent => Nat.lt_irrefl windowPosition
      (Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
          (Nat.le_trans (Nat.le_succ (windowPosition + 1)) windowFits))
        (Nat.le_of_eq wireHitsEvent.symm)))
  have eventDiffersFromRightWire :
      isSameComponent [] bottomCount (windowPosition + 1) = false :=
    decide_eq_false (fun eventHitsWire => Nat.lt_irrefl (windowPosition + 1)
      (Nat.lt_of_lt_of_le windowFits (Nat.le_of_eq eventHitsWire)))
  rw [eventDiffersFromValue, leftWireDiffersFromEvent, eventDiffersFromRightWire]
  cases hLeftWireQuery : isSameComponent [] windowPosition
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeIndex) with
  | true => rfl
  | false => rfl

/-! ## The assembled cap-seed correspondence -/

/-- ★ **The component correspondence at the cap-head seed.**  The composite links (peeled
cap fired at the canonical seed) answer every `sigma`-image query exactly as the fresh tail
run's empty links — degenerate legs, since the cap consumed the pair the tail never sees. -/
theorem arcComponentShiftCorr_capHeadSeed (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      0 0 []
      (unionFindJoin (unionFindJoin [] windowPosition (windowPosition + 1))
        bottomCount windowPosition) := by
  intro probeLeft probeRight
  rw [degenerateLegJoin]
  have innerReduction : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1))
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeLeft)
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeRight)
    = isSameComponent [] probeLeft probeRight := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
      (windowPosition + 1)
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeLeft)
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        probeRight)]
    have leftWireMissesLeft : isSameComponent [] windowPosition
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          probeLeft) = false :=
      arcCapHeadReindex_missesLeftWire bottomCount windowPosition tailBoundary probeLeft
        windowFits tailBoundaryFits
    have leftWireMissesRight : isSameComponent [] windowPosition
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          probeRight) = false :=
      arcCapHeadReindex_missesLeftWire bottomCount windowPosition tailBoundary probeRight
        windowFits tailBoundaryFits
    have probeCorr : isSameComponent []
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          probeLeft)
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          probeRight)
      = isSameComponent [] probeLeft probeRight :=
      arcCapHeadReindex_beqCorr bottomCount windowPosition tailBoundary probeLeft
        probeRight windowFits tailBoundaryFits
    rw [leftWireMissesLeft, leftWireMissesRight, probeCorr]
    cases hBaseQuery : isSameComponent [] probeLeft probeRight with
    | true => rfl
    | false => rfl
  rw [isSameComponent_unionFindJoin (unionFindJoin [] windowPosition (windowPosition + 1))
    (isUnionFindForest_unionFindJoin [] windowPosition (windowPosition + 1)
      isUnionFindForest_nil)
    bottomCount windowPosition
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      probeLeft)
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      probeRight),
    capSeedEventNodeMissesComponent bottomCount windowPosition tailBoundary probeLeft
      windowFits tailBoundaryFits,
    capSeedEventNodeMissesComponent bottomCount windowPosition tailBoundary probeRight
      windowFits tailBoundaryFits,
    innerReduction]
  cases hBaseQuery : isSameComponent [] probeLeft probeRight with
  | true => rfl
  | false => rfl

/-- The seed correspondence restated at the concrete head pair's STATES — the exact spelling
the fold consumes alongside `arcPositionalShiftSim_capHeadSeed`.  The cap state's joined
wires are stored range READS; pinning them with the below-boundary range read bridges to the
literal-legged core statement. -/
theorem arcComponentShiftCorr_capHeadSeedState (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      0 0
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []).links
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition).links := by
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition
      = windowPosition :=
    rangeGetAt_below bottomCount windowPosition
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
        (Nat.le_trans (Nat.le_succ (windowPosition + 1)) windowFits))
  have rightWireRead : natListGetAt (List.range bottomCount) (windowPosition + 1)
      = windowPosition + 1 :=
    rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  show ArcComponentShiftCorr
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    0 0 []
    (unionFindJoin
      (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) (windowPosition + 1)))
      bottomCount (natListGetAt (List.range bottomCount) windowPosition))
  rw [leftWireRead, rightWireRead]
  exact arcComponentShiftCorr_capHeadSeed bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled component correspondence at the cap-head seed (peel
campaign H, seed rung, LINKS leg CLOSED at BOTH heads).**  The degenerate leg-join
computation, the event-node component avoidance over the joined window pair, the assembled
`ArcComponentShiftCorr` at the cap seed (both join layers stripped by the avoidance atoms,
the residue closed by the beq correspondence, degenerate legs `0, 0`), and the state-spelled
restatement with the stored range reads pinned.  What this marker does NOT claim: the fold
assembly (threading both heads' seeds through the component fold) and the extract
correspondence the cancellation ultimately consumes.  `= true`. -/
def fxMode_hasArcCapHeadSeedCorr : Bool := true

end FX1Poly.Polygraph
