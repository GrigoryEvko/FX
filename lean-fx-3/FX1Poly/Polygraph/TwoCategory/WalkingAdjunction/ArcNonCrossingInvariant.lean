import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryCensus

/-! # ArcNonCrossingInvariant — the state-level planarity invariant of the arc fold (cup rung D2a-ii)

The census (`ArcBoundaryCensus`) says every union-find component of an arc-fold state has at most
two boundary ends — so same-component IS a matching on the boundary.  This file adds the ORDER
that makes the matching PLANAR: reading the boundary around the rectangle (bottom left-to-right,
then the open frontier right-to-left), no two matched arcs interleave.

`arcEndTokenPosition` places each boundary end token on that cyclic boundary: a bottom port keeps
its value, an open slot is reversed past the bottom block (the last slot first).  `ArcNonCrossing`
then forbids the interleaved quadruple — four valid tokens at strictly increasing positions whose
first-and-third and second-and-fourth reads share a component.

This brick ships the STATEMENT layer plus its truth at the fresh seed: there every component is a
single straight wire `{bottom port v, open slot v}`, whose two boundary positions are `v` and
`seedBoundary + (seedBoundary - 1 - v)` — a nested family ordered by `v`, never interleaved.  The
cup/cap step PRESERVATION and the extract translation to `IsNonCrossing` are the next rungs.

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

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

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

/-! ## Empty-link component plumbing (per-file copy) -/

/-- With no links, every node is its own root. -/
private theorem unionFindRootOf_nil (node : Nat) : unionFindRootOf [] node = node := rfl

/-- Over the empty link list, same-component is node equality. -/
private theorem seedNodesEqual_ofSameComponent (leftNode rightNode : Nat)
    (sameComponentHolds : isSameComponent [] leftNode rightNode = true) :
    leftNode = rightNode := by
  have rootsEqualTrue : (unionFindRootOf [] leftNode == unionFindRootOf [] rightNode) = true :=
    sameComponentHolds
  rw [unionFindRootOf_nil leftNode, unionFindRootOf_nil rightNode] at rootsEqualTrue
  have nodesDecideTrue : decide (leftNode = rightNode) = true := rootsEqualTrue
  exact of_decide_eq_true nodesDecideTrue

/-- Subtraction from a fixed minuend is antitone in the subtrahend, proved propext-free by
induction on the gap (`Nat.sub_le_sub_left` and `Nat.sub_sub` both leak `propext`). -/
private theorem subLeftAntitone : (minuend gap start : Nat) →
    minuend - (start + gap) ≤ minuend - start
  | minuend, 0, start => Nat.le_refl (minuend - start)
  | minuend, gap + 1, start => by
      rw [Nat.add_succ, Nat.sub_succ]
      exact Nat.le_trans (Nat.pred_le (minuend - (start + gap)))
        (subLeftAntitone minuend gap start)

/-! ## The cyclic boundary position of an end token -/

/-- Where an end token sits on the rectangle's cyclic boundary: bottom ports keep their
left-to-right value; open slots are reversed past the bottom block, the last slot placed first
(`seedBoundary + (openWires.length - 1 - slotPosition)`).  This is the token-side rendering of
`boundaryPosition`, the linearization under which the identity diagram reads as nested. -/
def arcEndTokenPosition (seedBoundary : Nat) (state : ArcWireState) : ArcEndToken → Nat
  | ArcEndToken.bottomPort portValue => portValue
  | ArcEndToken.openSlot slotPosition =>
      seedBoundary + (state.openWires.length - 1 - slotPosition)

/-! ## The planarity invariant -/

/-- ★ **The state-level non-crossing (planarity) invariant.**  No four valid boundary end tokens
sit at strictly increasing cyclic positions with the first paired to the third and the second to
the fourth in the union-find — i.e. no two matched arcs interleave on the rectangle boundary. -/
def ArcNonCrossing (seedBoundary : Nat) (state : ArcWireState) : Prop :=
  ∀ tokenA tokenB tokenC tokenD : ArcEndToken,
    isValidArcEndToken seedBoundary state tokenA →
    isValidArcEndToken seedBoundary state tokenB →
    isValidArcEndToken seedBoundary state tokenC →
    isValidArcEndToken seedBoundary state tokenD →
    arcEndTokenPosition seedBoundary state tokenA
        < arcEndTokenPosition seedBoundary state tokenB →
    arcEndTokenPosition seedBoundary state tokenB
        < arcEndTokenPosition seedBoundary state tokenC →
    arcEndTokenPosition seedBoundary state tokenC
        < arcEndTokenPosition seedBoundary state tokenD →
    isSameComponent state.links (arcEndTokenNode state tokenA)
        (arcEndTokenNode state tokenC) = true →
    isSameComponent state.links (arcEndTokenNode state tokenB)
        (arcEndTokenNode state tokenD) = true →
    False

/-! ## The invariant at the fresh seed -/

/-- At the fresh seed, a same-component pair of tokens with the lower at the smaller cyclic
position IS a straight seed wire read bottom-then-top: the low token is a bottom port and the
high token is the open slot of the SAME value.  The other three shape combinations contradict
either the shared node (two ports / two slots force equal tokens, equal positions) or the order
(a slot always sits past every bottom port, so slot-then-port cannot be increasing). -/
private theorem arcSeedArcBottomTop (seedBoundary : Nat)
    (tokenLow tokenHigh : ArcEndToken)
    (validLow : isValidArcEndToken seedBoundary
      (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) tokenLow)
    (validHigh : isValidArcEndToken seedBoundary
      (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) tokenHigh)
    (positionsOrdered : arcEndTokenPosition seedBoundary
        (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) tokenLow
      < arcEndTokenPosition seedBoundary
        (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) tokenHigh)
    (sameComponent : isSameComponent
        (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []).links
        (arcEndTokenNode
          (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) tokenLow)
        (arcEndTokenNode
          (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) tokenHigh)
      = true) :
    ∃ portValue : Nat, portValue < seedBoundary
      ∧ tokenLow = ArcEndToken.bottomPort portValue
      ∧ tokenHigh = ArcEndToken.openSlot portValue := by
  have openLength : (List.range seedBoundary).length = seedBoundary := rangeLength seedBoundary
  cases tokenLow with
  | bottomPort valueLow =>
      cases tokenHigh with
      | bottomPort valueHigh =>
          have valuesEqual : valueLow = valueHigh :=
            seedNodesEqual_ofSameComponent valueLow valueHigh sameComponent
          subst valuesEqual
          exact absurd positionsOrdered (Nat.lt_irrefl _)
      | openSlot slotHigh =>
          have validHighBelow : slotHigh < seedBoundary := by
            have raw : slotHigh < (List.range seedBoundary).length := validHigh
            rw [openLength] at raw
            exact raw
          have highNodeIsSlot : natListGetAt (List.range seedBoundary) slotHigh = slotHigh :=
            rangeGetAt_below seedBoundary slotHigh validHighBelow
          have valueEqualsSlot : valueLow = slotHigh := by
            have raw : valueLow = natListGetAt (List.range seedBoundary) slotHigh :=
              seedNodesEqual_ofSameComponent valueLow
                (natListGetAt (List.range seedBoundary) slotHigh) sameComponent
            rw [highNodeIsSlot] at raw
            exact raw
          exact ⟨valueLow, validLow, rfl, by rw [valueEqualsSlot]⟩
  | openSlot slotLow =>
      have lowPositionAtLeast : seedBoundary ≤ arcEndTokenPosition seedBoundary
          (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] [])
          (ArcEndToken.openSlot slotLow) :=
        Nat.le_add_right seedBoundary _
      cases tokenHigh with
      | bottomPort valueHigh =>
          have highBelow : valueHigh < seedBoundary := validHigh
          have lowBelow : arcEndTokenPosition seedBoundary
              (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] [])
              (ArcEndToken.openSlot slotLow) < seedBoundary :=
            Nat.lt_trans positionsOrdered highBelow
          exact absurd (Nat.lt_of_lt_of_le lowBelow lowPositionAtLeast)
            (Nat.lt_irrefl _)
      | openSlot slotHigh =>
          have lowNodeIsSlot : natListGetAt (List.range seedBoundary) slotLow = slotLow :=
            rangeGetAt_below seedBoundary slotLow (openLength ▸ validLow)
          have highNodeIsSlot : natListGetAt (List.range seedBoundary) slotHigh = slotHigh :=
            rangeGetAt_below seedBoundary slotHigh (openLength ▸ validHigh)
          have slotsEqual : slotLow = slotHigh := by
            have raw : natListGetAt (List.range seedBoundary) slotLow
                = natListGetAt (List.range seedBoundary) slotHigh :=
              seedNodesEqual_ofSameComponent _ _ sameComponent
            rw [lowNodeIsSlot, highNodeIsSlot] at raw
            exact raw
          exact absurd (slotsEqual ▸ positionsOrdered) (Nat.lt_irrefl _)

/-- ★ **The fresh seed state is non-crossing.**  Every component is a single straight wire, so a
matched arc is a bottom port paired with the open slot of the same value; two such arcs at values
`portA < portB` occupy nested position intervals `[portA, sb+(sb-1-portA)]` ⊇ `[portB,
sb+(sb-1-portB)]`, never the interleaving `posA < posB < posC < posD`. -/
theorem arcNonCrossing_initial (seedBoundary : Nat) :
    ArcNonCrossing seedBoundary
      (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) := by
  intro tokenA tokenB tokenC tokenD validA validB validC validD
    positionsAB positionsBC positionsCD sameAC sameBD
  have openLength : (List.range seedBoundary).length = seedBoundary := rangeLength seedBoundary
  have positionsAC := Nat.lt_trans positionsAB positionsBC
  have positionsBD := Nat.lt_trans positionsBC positionsCD
  obtain ⟨portAC, portACBelow, tokenAisPort, tokenCisSlot⟩ :=
    arcSeedArcBottomTop seedBoundary tokenA tokenC validA validC positionsAC sameAC
  obtain ⟨portBD, portBDBelow, tokenBisPort, tokenDisSlot⟩ :=
    arcSeedArcBottomTop seedBoundary tokenB tokenD validB validD positionsBD sameBD
  subst tokenAisPort tokenCisSlot tokenBisPort tokenDisSlot
  have portsOrdered : portAC < portBD := positionsAB
  have slotsOrdered : seedBoundary + ((List.range seedBoundary).length - 1 - portAC)
      < seedBoundary + ((List.range seedBoundary).length - 1 - portBD) := positionsCD
  rw [openLength] at slotsOrdered
  have gapOrdered : seedBoundary - 1 - portAC < seedBoundary - 1 - portBD :=
    Nat.lt_of_add_lt_add_left slotsOrdered
  obtain ⟨gap, gapEq⟩ := Nat.le.dest (Nat.le_of_lt portsOrdered)
  have gapAntitone : seedBoundary - 1 - portBD ≤ seedBoundary - 1 - portAC := by
    have base := subLeftAntitone (seedBoundary - 1) gap portAC
    rw [gapEq] at base
    exact base
  exact absurd (Nat.lt_of_lt_of_le gapOrdered gapAntitone) (Nat.lt_irrefl _)

/-! ## Honesty marker -/

/-- **Honesty marker — the state-level planarity invariant is DEFINED and TRUE AT THE FRESH SEED
(cup rung D2a-ii).**  `arcEndTokenPosition` (the token-side cyclic boundary linearization),
`ArcNonCrossing` (no interleaved same-component quadruple), and `arcNonCrossing_initial` (the
identity diagram is nested, hence non-crossing).  What this marker does NOT claim: the stepCupArc
and stepCapArc preservation of `ArcNonCrossing` (D2a-iii/iv), the whole-spine fold, and the
extract translation to `IsNonCrossing bottomCount (…).diagram.partner` via the census partner
uniqueness.  `= true`. -/
def fxMode_hasArcNonCrossingInvariant : Bool := true

end FX1Poly.Polygraph
