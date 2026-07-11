import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentPersistence
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity

/-! # WalkingString/StringArcComponentPersistence — component monotonicity + head-seed joins, ported
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE substrate)

Colour-blind two-token clone of the walking-adjunction `ArcComponentPersistence`'s locked set, re-plumbed onto the
FOUR-generator seed.  The arc fold only JOINS components, so any same-component fact persists to every later state;
the peeled head's seed joins survive to the folded end state.  The generic per-step siblings
(`isSameComponent_stepArcAtom_ofBase`/`stepCupArc`/`stepCapArc`, `isSameComponent_congrOfLinked`) and the union-find
join kit are `{signature}`-generic and REUSED by import; only the whole-spine persistence and the four folded joins
carry the seed classification `adjointTripleSpineAtom_hasCupOrCapArity` and so clone.

  * ★ `stringIsSameComponent_processArcSpine_ofBase` — same-component persists through the whole spine fold;
  * `stringArcCupHeadFolded_eventLegLinked` / `stringArcCupHeadFolded_legsLinked` — the cup head's seed joins;
  * ★ `stringArcCapHeadFolded_eventWireLinked` / `stringArcCapHeadFolded_consumedPairLinked` — the cap head's seed
    joins (event-to-consumed-wire, consumed pair) at the folded end state.

Raw Lean 4 + Init; structural recursion only; no `omega` / `simp`-AC / `WellFounded.fix`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

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

/-! ## Whole-spine persistence -/

/-- ★ **Same-component persists through the whole spine fold** (four-generator port): a fact linking two probes at
a forest state survives to the folded end state, because every atom's step only joins.  The three-generator analog
of `isSameComponent_processArcSpine_ofBase`. -/
theorem stringIsSameComponent_processArcSpine_ofBase
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : ArcWireState) →
    (forest : isUnionFindForest state.links) →
    (probeOne probeTwo : Nat) →
    isSameComponent state.links probeOne probeTwo = true →
    isSameComponent (processArcSpine state atoms).links probeOne probeTwo = true
  | [], _, _, _, _, base => base
  | headAtom :: restAtoms, state, forest, probeOne, probeTwo, base => by
      show isSameComponent
        (processArcSpine (stepArcAtom state headAtom) restAtoms).links probeOne probeTwo
          = true
      exact stringIsSameComponent_processArcSpine_ofBase restAtoms (stepArcAtom state headAtom)
        (isUnionFindForest_stepArcAtom state headAtom forest) probeOne probeTwo
        (isSameComponent_stepArcAtom_ofBase state headAtom
          (adjointTripleSpineAtom_hasCupOrCapArity headAtom) forest probeOne probeTwo base)

/-! ## The persistent head-seed joins at the folded end states -/

/-- Under a cup head, the head's event node stays linked to its left leg at the end state. -/
theorem stringArcCupHeadFolded_eventLegLinked
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (bottomCount + 2) bottomCount = true :=
  stringIsSameComponent_processArcSpine_ofBase atoms
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (isUnionFindForest_unionFindJoin
      (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil))
    (bottomCount + 2) bottomCount
    (isSameComponent_unionFindJoin_joined
      (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil)
      (bottomCount + 2) bottomCount)

/-- Under a cup head, the two legs stay linked at the end state. -/
theorem stringArcCupHeadFolded_legsLinked
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount (bottomCount + 1) = true :=
  stringIsSameComponent_processArcSpine_ofBase atoms
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (isUnionFindForest_unionFindJoin
      (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil))
    bottomCount (bottomCount + 1)
    (isSameComponent_unionFindJoin_ofBase
      (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil)
      (bottomCount + 2) bottomCount bottomCount (bottomCount + 1)
      (isSameComponent_unionFindJoin_joined [] isUnionFindForest_nil bottomCount
        (bottomCount + 1)))

/-- Under a cap head, the head's event node stays linked to the consumed left wire at the end state (stated at the
pinned read: the seed's wire at the window IS `windowPosition`). -/
theorem stringArcCapHeadFolded_eventWireLinked
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount windowPosition = true := by
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition = windowPosition :=
    rangeGetAt_below bottomCount windowPosition
      (Nat.lt_of_lt_of_le
        (Nat.lt_trans (Nat.lt_succ_self windowPosition)
          (Nat.lt_succ_self (windowPosition + 1)))
        windowFits)
  have persisted : isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount (natListGetAt (List.range bottomCount) windowPosition) = true :=
    stringIsSameComponent_processArcSpine_ofBase atoms
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition)
      (isUnionFindForest_unionFindJoin
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        bottomCount (natListGetAt (List.range bottomCount) windowPosition)
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil))
      bottomCount (natListGetAt (List.range bottomCount) windowPosition)
      (isSameComponent_unionFindJoin_joined
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil)
        bottomCount (natListGetAt (List.range bottomCount) windowPosition))
  rw [leftWireRead] at persisted
  exact persisted

/-- Under a cap head, the two consumed wires stay linked at the end state (stated at the pinned reads: the seed's
wires at the window ARE `windowPosition`/`windowPosition + 1`). -/
theorem stringArcCapHeadFolded_consumedPairLinked
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      windowPosition (windowPosition + 1) = true := by
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition = windowPosition :=
    rangeGetAt_below bottomCount windowPosition
      (Nat.lt_of_lt_of_le
        (Nat.lt_trans (Nat.lt_succ_self windowPosition)
          (Nat.lt_succ_self (windowPosition + 1)))
        windowFits)
  have rightWireRead : natListGetAt (List.range bottomCount) (windowPosition + 1)
      = windowPosition + 1 :=
    rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  have persisted : isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt (List.range bottomCount) windowPosition)
      (natListGetAt (List.range bottomCount) (windowPosition + 1)) = true :=
    stringIsSameComponent_processArcSpine_ofBase atoms
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition)
      (isUnionFindForest_unionFindJoin
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        bottomCount (natListGetAt (List.range bottomCount) windowPosition)
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil))
      (natListGetAt (List.range bottomCount) windowPosition)
      (natListGetAt (List.range bottomCount) (windowPosition + 1))
      (isSameComponent_unionFindJoin_ofBase
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil)
        bottomCount (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) (windowPosition + 1))
        (isSameComponent_unionFindJoin_joined [] isUnionFindForest_nil
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))))
  rw [leftWireRead, rightWireRead] at persisted
  exact persisted

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — component monotonicity + head-seed joins ported to the adjoint-triple seed (FC-3 r19).**
`stringIsSameComponent_processArcSpine_ofBase` (whole-spine persistence) and the four folded head-seed joins
(`stringArcCupHeadFolded_eventLegLinked`/`_legsLinked`, `stringArcCapHeadFolded_eventWireLinked`/`_consumedPairLinked`)
— colour-blind two-token clones of `ArcComponentPersistence`, riding `adjointTripleSpineAtom_hasCupOrCapArity` and
the `{signature}`-generic per-step siblings + union-find join kit (reused, never cloned).  `= true`. -/
def fxString_hasArcComponentPersistence : Bool := true

end FX1Poly.Polygraph
