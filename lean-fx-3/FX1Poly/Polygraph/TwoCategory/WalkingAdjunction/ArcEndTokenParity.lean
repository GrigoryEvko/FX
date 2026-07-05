import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryCensus
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionModeParity

/-! # ArcEndTokenParity — the opposite-class strand-endpoint invariant (peel campaign H, parity rung P-1)

Every strand of an arc-fold state carries its two boundary end tokens at OPPOSITE parity
classes: a bottom port's class is its position parity in the source mode word, an open
slot's class is the FLIP of its position parity (the top boundary traverses the disk edge
in the opposite direction).  The class function is state-independent data of the token —
bottom ports are keyed by their seed node value, and an open slot's position only ever
shifts by two (cups insert two wires, caps remove two), so its parity is stable along the
whole fold.

This invariant is what pins the cup partner matching: the leg-swap scenario (re-attaching
the cup's left-leg strand to the right leg) would join tokens of EQUAL class, so on the
disciplined fragment the fresh partner data at the window legs is forced — the
parity-gated half of the cup partial cancel.  It is also strictly stronger than the
boundary census: three pairwise-opposite tokens are impossible in a two-class system.

This brick ships the STATEMENT layer: the token class function, the pairwise
opposite-class invariant, and its truth at the fresh seed state, where every component is
a single straight wire whose two tokens sit at one position's two ends.  The cup/cap step
preservation and the fold transport are the campaign's next rungs.

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

/-! ## The token parity class -/

/-- **The parity class of a boundary end token** — state-independent data of the token
itself.  A bottom port's class is its position parity in the source mode word (its seed
node value IS its bottom position).  An open slot's class is the FLIP of its position
parity: the top boundary traverses the disk edge in the opposite direction, and the flip
is exactly what makes a straight seed wire's two tokens opposite.  An open slot's position
only ever shifts by two along the fold, so its class is stable. -/
def arcEndTokenClass (sourceMode : AdjunctionMode) : ArcEndToken → AdjunctionMode
  | ArcEndToken.bottomPort portValue => adjunctionModeAtDistance sourceMode portValue
  | ArcEndToken.openSlot slotPosition =>
      adjunctionOppositeMode (adjunctionModeAtDistance sourceMode slotPosition)

/-! ## The opposite-class invariant -/

/-- ★ **The opposite-class strand-endpoint invariant.**  Any two distinct valid boundary
end tokens of the SAME union-find component sit at OPPOSITE parity classes.  This is the
parity refinement of the boundary census (three pairwise-opposite tokens are impossible in
a two-class system), and it is the fact that forces the cup partner matching: a token of
one class can only strand-connect to a window leg of the opposite class. -/
def ArcEndTokenParity (sourceMode : AdjunctionMode) (seedBoundary : Nat)
    (state : ArcWireState) : Prop :=
  ∀ tokenOne tokenTwo : ArcEndToken,
    isValidArcEndToken seedBoundary state tokenOne →
    isValidArcEndToken seedBoundary state tokenTwo →
    tokenOne ≠ tokenTwo →
    isSameComponent state.links (arcEndTokenNode state tokenOne)
        (arcEndTokenNode state tokenTwo) = true →
    arcEndTokenClass sourceMode tokenOne
      = adjunctionOppositeMode (arcEndTokenClass sourceMode tokenTwo)

/-! ## The invariant at the fresh seed -/

/-- With no links, every node is its own root. -/
private theorem unionFindRootOf_nil (node : Nat) : unionFindRootOf [] node = node := rfl

/-- Over the empty link list, same-component is node equality. -/
private theorem arcSeedNodesEqual_ofSameComponent (leftNode rightNode : Nat)
    (sameComponentHolds : isSameComponent [] leftNode rightNode = true) :
    leftNode = rightNode := by
  have rootsEqualTrue : (unionFindRootOf [] leftNode == unionFindRootOf [] rightNode) = true :=
    sameComponentHolds
  rw [unionFindRootOf_nil leftNode, unionFindRootOf_nil rightNode] at rootsEqualTrue
  have nodesDecideTrue : decide (leftNode = rightNode) = true := rootsEqualTrue
  exact of_decide_eq_true nodesDecideTrue

/-- At the seed, an in-range open slot reads its own position: the seed `openWires` is the
range list. -/
private theorem arcSeedSlotRead (seedBoundary slotPosition : Nat)
    (slotBelowLength : slotPosition < (List.range seedBoundary).length) :
    natListGetAt (List.range seedBoundary) slotPosition = slotPosition := by
  rw [rangeLength seedBoundary] at slotBelowLength
  exact rangeGetAt_below seedBoundary slotPosition slotBelowLength

/-- ★ The fresh seed state satisfies the opposite-class invariant: every component is a
single straight wire, its bottom port and open slot share one position, and the slot's
class is by definition the flip of the port's. -/
theorem arcEndTokenParity_initial (sourceMode : AdjunctionMode) (seedBoundary : Nat) :
    ArcEndTokenParity sourceMode seedBoundary
      (ArcWireState.mk (List.range seedBoundary) [] seedBoundary 0 [] []) := by
  intro tokenOne tokenTwo validOne validTwo oneNeTwo sameComponentHolds
  cases tokenOne with
  | bottomPort valueOne =>
      cases tokenTwo with
      | bottomPort valueTwo =>
          exact absurd (congrArg ArcEndToken.bottomPort
              (arcSeedNodesEqual_ofSameComponent valueOne valueTwo sameComponentHolds))
            oneNeTwo
      | openSlot slotTwo =>
          have readSlotTwo : natListGetAt (List.range seedBoundary) slotTwo = slotTwo :=
            arcSeedSlotRead seedBoundary slotTwo validTwo
          have valuesEqual : valueOne = slotTwo :=
            (arcSeedNodesEqual_ofSameComponent valueOne
              (natListGetAt (List.range seedBoundary) slotTwo) sameComponentHolds).trans
              readSlotTwo
          show adjunctionModeAtDistance sourceMode valueOne
            = adjunctionOppositeMode
                (adjunctionOppositeMode (adjunctionModeAtDistance sourceMode slotTwo))
          rw [adjunctionOppositeMode_isInvolutive
            (adjunctionModeAtDistance sourceMode slotTwo), valuesEqual]
  | openSlot slotOne =>
      have readSlotOne : natListGetAt (List.range seedBoundary) slotOne = slotOne :=
        arcSeedSlotRead seedBoundary slotOne validOne
      cases tokenTwo with
      | bottomPort valueTwo =>
          have valuesEqual : slotOne = valueTwo :=
            readSlotOne.symm.trans
              (arcSeedNodesEqual_ofSameComponent
                (natListGetAt (List.range seedBoundary) slotOne) valueTwo
                sameComponentHolds)
          show adjunctionOppositeMode (adjunctionModeAtDistance sourceMode slotOne)
            = adjunctionOppositeMode (adjunctionModeAtDistance sourceMode valueTwo)
          rw [valuesEqual]
      | openSlot slotTwo =>
          have readSlotTwo : natListGetAt (List.range seedBoundary) slotTwo = slotTwo :=
            arcSeedSlotRead seedBoundary slotTwo validTwo
          have slotsEqual : slotOne = slotTwo :=
            readSlotOne.symm.trans
              ((arcSeedNodesEqual_ofSameComponent
                (natListGetAt (List.range seedBoundary) slotOne)
                (natListGetAt (List.range seedBoundary) slotTwo)
                sameComponentHolds).trans readSlotTwo)
          exact absurd (congrArg ArcEndToken.openSlot slotsEqual) oneNeTwo

/-! ## Honesty marker -/

/-- **Honesty marker — the opposite-class invariant STATEMENT layer is SHIPPED (peel
campaign H, parity rung P-1).**  The state-independent token class function (bottom port =
position parity, open slot = flipped position parity), the pairwise opposite-class
invariant `ArcEndTokenParity`, and its truth at the fresh seed state.  What this marker
does NOT claim: preservation of the invariant through `stepCupArc` / `stepCapArc` (rungs
P-2/P-3 — the token surgery riding the cup/cap window parity pins), the fold transport to
chained spines (rung P-4), and the cup partner-matching cancel it gates (rung P-5).
`= true`. -/
def fxMode_hasArcEndTokenParitySeed : Bool := true

end FX1Poly.Polygraph
