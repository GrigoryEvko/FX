import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim

/-! # MatchingLeftPadSim — the left-padded matching simulation (whisker-left leg)

The whisker-LEFT matching congruence compares `matchingOf (whiskerLeft oneCell alpha)` — run
from the canonical seed over `pad + bottomCount` wires — with `matchingOf alpha` run from the
canonical seed over `bottomCount` wires.  Unlike the right whisker, a LEFT whisker is NOT
action-invisible: every atom's left accumulator grows by the whiskering 1-cell, so every
window position SHIFTS by the pad.  The simulation therefore pairs a base step at `position`
with a padded step at `delta + position`, and the pad sits as a constant PREFIX of the wire
list — the mirror of `MatchingRightPadSim`'s constant suffix.

Because the pad occupies the identifiers `[0, delta)`, the wire rename is the UNIFORM shift
`freshShiftAbove 0 delta` (every base identifier is at or above threshold `0`), the pad zone
is `[0, delta)`, and the two join-inertness lemmas from the right-pad file apply verbatim at
`threshold := 0` — only the trivial `0 ≤ node` / `node < 0` legs need adapting, which the two
private zone adapters below do once.

This brick installs the structure and both step preservations (cup splices past the prefix
via `natListInsertAt_append_right`, cap reads/removes past the prefix via
`natListGetAt_append_atLength` / `natListRemoveTwoAt_append_right`, with the component view
carried by a two-position cap lemma).  The shifted spine correspondence, the
boundary-disciplined fold, the left seed instance, and the whiskerLeft assembly are the next
bricks. -/

namespace FX1Poly.Polygraph

/-! ## List-surgery plumbing: reading/splicing/removing PAST a constant prefix -/

/-- Reading past a block reads the tail: the read at `blockLength + offset` lands at `offset`
of the second list.  The block length is threaded as an EQUATION so callers can supply the
pad width `delta` directly. -/
private theorem natListGetAt_append_atLength : (block : List Nat) → (wires : List Nat) →
    (blockLength offset : Nat) → block.length = blockLength →
    natListGetAt (block ++ wires) (blockLength + offset) = natListGetAt wires offset
  | [], wires, blockLength, offset, lengthEq => by
      rw [← lengthEq]
      show natListGetAt wires (0 + offset) = natListGetAt wires offset
      rw [Nat.zero_add]
  | head :: blockRest, wires, blockLength, offset, lengthEq => by
      rw [← lengthEq]
      show natListGetAt (head :: (blockRest ++ wires)) (blockRest.length + 1 + offset)
        = natListGetAt wires offset
      rw [Nat.add_right_comm blockRest.length 1 offset]
      exact natListGetAt_append_atLength blockRest wires blockRest.length offset rfl

/-- Splicing past a block ignores the block: insertion at `blockLength + position` carries the
block unchanged and inserts into the tail at `position`. -/
private theorem natListInsertAt_append_right : (block wires insertedBlock : List Nat) →
    (blockLength position : Nat) → block.length = blockLength →
    natListInsertAt (block ++ wires) (blockLength + position) insertedBlock
      = block ++ natListInsertAt wires position insertedBlock
  | [], wires, insertedBlock, blockLength, position, lengthEq => by
      rw [← lengthEq]
      show natListInsertAt wires (0 + position) insertedBlock
        = natListInsertAt wires position insertedBlock
      rw [Nat.zero_add]
  | head :: blockRest, wires, insertedBlock, blockLength, position, lengthEq => by
      rw [← lengthEq]
      show natListInsertAt (head :: (blockRest ++ wires)) (blockRest.length + 1 + position)
          insertedBlock
        = head :: (blockRest ++ natListInsertAt wires position insertedBlock)
      rw [Nat.add_right_comm blockRest.length 1 position]
      exact congrArg (head :: ·)
        (natListInsertAt_append_right blockRest wires insertedBlock blockRest.length
          position rfl)

/-- The cons-successor unfolding of the two-wire removal, valid for an ARBITRARY tail (the
match compiler only reduces it definitionally once the tail's shape is known). -/
private theorem natListRemoveTwoAt_cons_succ (head : Nat) :
    (tail : List Nat) → (position : Nat) →
    natListRemoveTwoAt (head :: tail) (position + 1)
      = head :: natListRemoveTwoAt tail position
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- Two-wire removal past a block ignores the block: removal at `blockLength + position`
carries the block unchanged and removes from the tail at `position`. -/
private theorem natListRemoveTwoAt_append_right : (block wires : List Nat) →
    (blockLength position : Nat) → block.length = blockLength →
    natListRemoveTwoAt (block ++ wires) (blockLength + position)
      = block ++ natListRemoveTwoAt wires position
  | [], wires, blockLength, position, lengthEq => by
      rw [← lengthEq]
      show natListRemoveTwoAt wires (0 + position) = natListRemoveTwoAt wires position
      rw [Nat.zero_add]
  | head :: blockRest, wires, blockLength, position, lengthEq => by
      rw [← lengthEq]
      show natListRemoveTwoAt (head :: (blockRest ++ wires)) (blockRest.length + 1 + position)
        = head :: (blockRest ++ natListRemoveTwoAt wires position)
      rw [Nat.add_right_comm blockRest.length 1 position,
        natListRemoveTwoAt_cons_succ head (blockRest ++ wires) (blockRest.length + position),
        natListRemoveTwoAt_append_right blockRest wires blockRest.length position rfl]

/-! ## The left-pad zone `[0, delta)` through the shared join-inertness lemmas -/

/-- Adapt the left-pad lower-bound avoidance to the `[0, 0 + delta)` zone form the shared
join-inertness lemmas consume: the below-zero leg is vacuous. -/
private theorem leftPadZoneAvoidance (delta : Nat) (links : List (Nat × Nat))
    (rootStaysHigh : ∀ node, delta ≤ node → delta ≤ unionFindRootOf links node) :
    ∀ node, node < 0 ∨ 0 + delta ≤ node →
      unionFindRootOf links node < 0 ∨ 0 + delta ≤ unionFindRootOf links node := by
  intro node zoneAvoids
  apply Or.inr
  rw [Nat.zero_add]
  cases zoneAvoids with
  | inl impossible => exact absurd impossible (Nat.not_lt_zero node)
  | inr nodeHigh =>
      rw [Nat.zero_add] at nodeHigh
      exact rootStaysHigh node nodeHigh

/-- Adapt the left-pad below-threshold root fixing to the `[0, 0 + delta)` zone form: the
`0 ≤ node` leg is trivial. -/
private theorem leftPadZoneFixed (delta : Nat) (links : List (Nat × Nat))
    (padStaysPut : ∀ node, node < delta → unionFindRootOf links node = node) :
    ∀ node, 0 ≤ node → node < 0 + delta → unionFindRootOf links node = node := by
  intro node _ nodeBelowZoneEnd
  rw [Nat.zero_add] at nodeBelowZoneEnd
  exact padStaysPut node nodeBelowZoneEnd

/-! ## The two-position cap component view -/

/-- A CAP step preserves the component view when the two runs fire at DIFFERENT positions —
provided the window reads correspond under `sigma`.  The same-component test agrees directly
from the component view, so both take the same branch: unchanged links carry the input, the
join branch carries `componentView_unionFindJoin`.  (The one-position
`stepCap_componentComm` cannot express the left pad's `delta`-offset window.) -/
private theorem stepCap_componentComm_ofShiftedWindow (sigma : Nat → Nat)
    (stateS stateT : WireState)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (positionS positionT : Nat)
    (leftReadCorr : natListGetAt stateT.openWires positionT
      = sigma (natListGetAt stateS.openWires positionS))
    (rightReadCorr : natListGetAt stateT.openWires (positionT + 1)
      = sigma (natListGetAt stateS.openWires (positionS + 1)))
    (a b : Nat) :
    (unionFindRootOf (stepCap stateT positionT).links (sigma a)
        == unionFindRootOf (stepCap stateT positionT).links (sigma b))
      = (unionFindRootOf (stepCap stateS positionS).links a
        == unionFindRootOf (stepCap stateS positionS).links b) := by
  rw [stepCap_links, stepCap_links]
  have testCorr : isSameComponent stateT.links (natListGetAt stateT.openWires positionT)
        (natListGetAt stateT.openWires (positionT + 1))
      = isSameComponent stateS.links (natListGetAt stateS.openWires positionS)
        (natListGetAt stateS.openWires (positionS + 1)) := by
    show (unionFindRootOf stateT.links (natListGetAt stateT.openWires positionT)
            == unionFindRootOf stateT.links (natListGetAt stateT.openWires (positionT + 1)))
       = (unionFindRootOf stateS.links (natListGetAt stateS.openWires positionS)
            == unionFindRootOf stateS.links (natListGetAt stateS.openWires (positionS + 1)))
    rw [leftReadCorr, rightReadCorr]
    exact componentComm (natListGetAt stateS.openWires positionS)
      (natListGetAt stateS.openWires (positionS + 1))
  rw [testCorr]
  split
  · exact componentComm a b
  · rw [leftReadCorr, rightReadCorr]
    exact componentView_unionFindJoin sigma stateS.links stateT.links forestS forestT
      (natListGetAt stateS.openWires positionS) (natListGetAt stateS.openWires (positionS + 1))
      componentComm a b

/-! ## The left-padded simulation invariant -/

/-- ★ **The left-padded matching simulation** — the whisker-LEFT mirror of
`MatchingRightPadSim`: the padded state's wires are a CONSTANT pad prefix (the whiskering
1-cell's untouched boundary wires, identifiers `[0, delta)`) followed by the uniform-shift
images of the base state's wires, the counter runs `delta` ahead, the partition views
correspond under the shift, and the pad zone `[0, delta)` stays inert: pad ids are their own
roots and no shifted node's root ever drops into the zone.  The padded run steps at the
prefix-offset window `delta + position` wherever the base run steps at `position`. -/
structure MatchingLeftPadSim (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState) : Prop where
  /-- The padded wires are the constant prefix plus the shift-images of the base wires. -/
  openMap : stateT.openWires
    = padPrefix ++ stateS.openWires.map (freshShiftAbove 0 delta)
  /-- The pad prefix carries exactly `delta` wires (the window-offset arithmetic anchor). -/
  prefixCount : padPrefix.length = delta
  /-- The padded counter runs exactly `delta` ahead. -/
  nfShift : stateT.nextFresh = stateS.nextFresh + delta
  /-- The same-component booleans correspond under the uniform shift. -/
  componentComm : ∀ a b,
    (unionFindRootOf stateT.links (freshShiftAbove 0 delta a)
        == unionFindRootOf stateT.links (freshShiftAbove 0 delta b))
      = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b)
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The base links form a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The padded links form a forest. -/
  forestT : isUnionFindForest stateT.links
  /-- Every pad-zone id (below `delta`) is its own root in the padded links. -/
  padRootsFixed : ∀ node, node < delta → unionFindRootOf stateT.links node = node
  /-- No at-or-above-`delta` node's root drops below `delta` in the padded links. -/
  rootAvoidsPad : ∀ node, delta ≤ node → delta ≤ unionFindRootOf stateT.links node

/-! ## Step preservation: the cup -/

/-- ★ **A CUP step preserves the left-padded simulation.**  The padded splice happens past the
untouched prefix (`natListInsertAt_append_right` at the `delta`-offset window) and the legs
are exactly the shift-images of the base legs; the component view is the counter-shift cup
lemma at threshold `0`; the joined fresh legs sit past the pad zone, so the zone stays
inert. -/
theorem matchingLeftPadSim_stepCup (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState) (position : Nat)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT) :
    MatchingLeftPadSim delta padPrefix
      (stepCup stateS position) (stepCup stateT (delta + position)) := by
  have freshLegHigh : delta ≤ stateT.nextFresh := by
    rw [sim.nfShift]
    exact Nat.le_add_left delta stateS.nextFresh
  have openMapAfter : (stepCup stateT (delta + position)).openWires
      = padPrefix ++ (stepCup stateS position).openWires.map (freshShiftAbove 0 delta) := by
    rw [stepCup_openWires stateT (delta + position), stepCup_openWires stateS position,
      sim.openMap,
      natListInsertAt_append_right padPrefix
        (stateS.openWires.map (freshShiftAbove 0 delta))
        [stateT.nextFresh, stateT.nextFresh + 1] delta position sim.prefixCount,
      natListInsertAt_map (freshShiftAbove 0 delta) stateS.openWires position
        [stateS.nextFresh, stateS.nextFresh + 1],
      sim.nfShift]
    show padPrefix ++ natListInsertAt (stateS.openWires.map (freshShiftAbove 0 delta)) position
          [stateS.nextFresh + delta, stateS.nextFresh + delta + 1]
      = padPrefix ++ natListInsertAt (stateS.openWires.map (freshShiftAbove 0 delta)) position
          [freshShiftAbove 0 delta stateS.nextFresh,
            freshShiftAbove 0 delta (stateS.nextFresh + 1)]
    rw [freshShiftAbove_ofLe 0 delta stateS.nextFresh (Nat.zero_le stateS.nextFresh),
      freshShiftAbove_ofLe 0 delta (stateS.nextFresh + 1) (Nat.zero_le (stateS.nextFresh + 1)),
      Nat.add_right_comm stateS.nextFresh 1 delta]
  have nfShiftAfter : (stepCup stateT (delta + position)).nextFresh
      = (stepCup stateS position).nextFresh + delta := by
    rw [stepCup_nextFresh stateT (delta + position), stepCup_nextFresh stateS position,
      sim.nfShift, Nat.add_right_comm stateS.nextFresh delta 2]
  have padRootsAfter : ∀ node, node < delta →
      unionFindRootOf (stepCup stateT (delta + position)).links node = node := by
    intro node nodeBelowPad
    exact padRootsFixed_unionFindJoin 0 delta stateT.links sim.forestT
      stateT.nextFresh (stateT.nextFresh + 1)
      (Or.inr (by rw [Nat.zero_add]; exact freshLegHigh))
      (leftPadZoneAvoidance delta stateT.links sim.rootAvoidsPad)
      (leftPadZoneFixed delta stateT.links sim.padRootsFixed)
      node (Nat.zero_le node) (by rw [Nat.zero_add]; exact nodeBelowPad)
  have rootAvoidsAfter : ∀ node, delta ≤ node →
      delta ≤ unionFindRootOf (stepCup stateT (delta + position)).links node := by
    intro node nodeHigh
    cases rootAvoidsPadZone_unionFindJoin 0 delta stateT.links sim.forestT
        stateT.nextFresh (stateT.nextFresh + 1)
        (Or.inr (by rw [Nat.zero_add]; exact Nat.le_succ_of_le freshLegHigh))
        (leftPadZoneAvoidance delta stateT.links sim.rootAvoidsPad)
        node (Or.inr (by rw [Nat.zero_add]; exact nodeHigh)) with
    | inl rootBelowZero => exact absurd rootBelowZero (Nat.not_lt_zero _)
    | inr rootHigh =>
        rw [Nat.zero_add] at rootHigh
        exact rootHigh
  exact
    { openMap := openMapAfter
      prefixCount := sim.prefixCount
      nfShift := nfShiftAfter
      componentComm := fun a b =>
        stepCup_componentComm_ofShift 0 delta stateS stateT sim.forestS sim.forestT
          sim.nfShift (Nat.zero_le stateS.nextFresh) sim.componentComm position a b
      loopsEq := sim.loopsEq
      forestS := isUnionFindForest_stepCup stateS position sim.forestS
      forestT := isUnionFindForest_stepCup stateT (delta + position) sim.forestT
      padRootsFixed := padRootsAfter
      rootAvoidsPad := rootAvoidsAfter }

/-! ## Step preservation: the cap -/

/-- ★ **A CAP step preserves the left-padded simulation.**  The two `delta`-offset window
reads land past the prefix (`natListGetAt_append_atLength`) and are shift-images of the base
reads (`natListGetAt_map_inRange`), so the component view is the two-position cap lemma, the
loop increments agree through the corresponding same-component test, the removal happens past
the untouched prefix (`natListRemoveTwoAt_append_right`), and any join is between two
shift-images — which the shift keeps out of the pad zone. -/
theorem matchingLeftPadSim_stepCap (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState) (position : Nat)
    (windowLt : position + 1 < stateS.openWires.length)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT) :
    MatchingLeftPadSim delta padPrefix
      (stepCap stateS position) (stepCap stateT (delta + position)) := by
  have positionLt : position < stateS.openWires.length := Nat.lt_of_succ_lt windowLt
  have leftReadCorr : natListGetAt stateT.openWires (delta + position)
      = freshShiftAbove 0 delta (natListGetAt stateS.openWires position) := by
    rw [sim.openMap,
      natListGetAt_append_atLength padPrefix
        (stateS.openWires.map (freshShiftAbove 0 delta)) delta position sim.prefixCount,
      natListGetAt_map_inRange (freshShiftAbove 0 delta) stateS.openWires position positionLt]
  have rightReadCorr : natListGetAt stateT.openWires (delta + position + 1)
      = freshShiftAbove 0 delta (natListGetAt stateS.openWires (position + 1)) := by
    rw [Nat.add_assoc delta position 1, sim.openMap,
      natListGetAt_append_atLength padPrefix
        (stateS.openWires.map (freshShiftAbove 0 delta)) delta (position + 1)
        sim.prefixCount,
      natListGetAt_map_inRange (freshShiftAbove 0 delta) stateS.openWires (position + 1)
        windowLt]
  have sameComponentCorr : isSameComponent stateT.links
        (natListGetAt stateT.openWires (delta + position))
        (natListGetAt stateT.openWires (delta + position + 1))
      = isSameComponent stateS.links (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)) := by
    rw [leftReadCorr, rightReadCorr]
    exact sim.componentComm (natListGetAt stateS.openWires position)
      (natListGetAt stateS.openWires (position + 1))
  have openMapAfter : (stepCap stateT (delta + position)).openWires
      = padPrefix ++ (stepCap stateS position).openWires.map (freshShiftAbove 0 delta) := by
    rw [stepCap_openWires stateT (delta + position), stepCap_openWires stateS position,
      sim.openMap,
      natListRemoveTwoAt_append_right padPrefix
        (stateS.openWires.map (freshShiftAbove 0 delta)) delta position sim.prefixCount,
      natListRemoveTwoAt_map (freshShiftAbove 0 delta) stateS.openWires position]
  have nfShiftAfter : (stepCap stateT (delta + position)).nextFresh
      = (stepCap stateS position).nextFresh + delta := by
    rw [stepCap_nextFresh stateT (delta + position), stepCap_nextFresh stateS position]
    exact sim.nfShift
  have loopsAfter : (stepCap stateT (delta + position)).loops
      = (stepCap stateS position).loops := by
    rw [stepCap_loops stateT (delta + position), stepCap_loops stateS position,
      sameComponentCorr, sim.loopsEq]
  have padRootsAfter : ∀ node, node < delta →
      unionFindRootOf (stepCap stateT (delta + position)).links node = node := by
    rw [stepCap_links stateT (delta + position), leftReadCorr, rightReadCorr]
    cases capTest : isSameComponent stateT.links
        (freshShiftAbove 0 delta (natListGetAt stateS.openWires position))
        (freshShiftAbove 0 delta (natListGetAt stateS.openWires (position + 1))) with
    | true => exact sim.padRootsFixed
    | false =>
        intro node nodeBelowPad
        exact padRootsFixed_unionFindJoin 0 delta stateT.links sim.forestT
          (freshShiftAbove 0 delta (natListGetAt stateS.openWires position))
          (freshShiftAbove 0 delta (natListGetAt stateS.openWires (position + 1)))
          (freshShiftAbove_avoidsPadZone 0 delta (natListGetAt stateS.openWires position))
          (leftPadZoneAvoidance delta stateT.links sim.rootAvoidsPad)
          (leftPadZoneFixed delta stateT.links sim.padRootsFixed)
          node (Nat.zero_le node) (by rw [Nat.zero_add]; exact nodeBelowPad)
  have rootAvoidsAfter : ∀ node, delta ≤ node →
      delta ≤ unionFindRootOf (stepCap stateT (delta + position)).links node := by
    rw [stepCap_links stateT (delta + position), leftReadCorr, rightReadCorr]
    cases capTest : isSameComponent stateT.links
        (freshShiftAbove 0 delta (natListGetAt stateS.openWires position))
        (freshShiftAbove 0 delta (natListGetAt stateS.openWires (position + 1))) with
    | true => exact sim.rootAvoidsPad
    | false =>
        intro node nodeHigh
        cases rootAvoidsPadZone_unionFindJoin 0 delta stateT.links sim.forestT
            (freshShiftAbove 0 delta (natListGetAt stateS.openWires position))
            (freshShiftAbove 0 delta (natListGetAt stateS.openWires (position + 1)))
            (freshShiftAbove_avoidsPadZone 0 delta
              (natListGetAt stateS.openWires (position + 1)))
            (leftPadZoneAvoidance delta stateT.links sim.rootAvoidsPad)
            node (Or.inr (by rw [Nat.zero_add]; exact nodeHigh)) with
        | inl rootBelowZero => exact absurd rootBelowZero (Nat.not_lt_zero _)
        | inr rootHigh =>
            rw [Nat.zero_add] at rootHigh
            exact rootHigh
  exact
    { openMap := openMapAfter
      prefixCount := sim.prefixCount
      nfShift := nfShiftAfter
      componentComm := fun a b =>
        stepCap_componentComm_ofShiftedWindow (freshShiftAbove 0 delta) stateS stateT
          sim.forestS sim.forestT sim.componentComm position (delta + position)
          leftReadCorr rightReadCorr a b
      loopsEq := loopsAfter
      forestS := isUnionFindForest_stepCap stateS position sim.forestS
      forestT := isUnionFindForest_stepCap stateT (delta + position) sim.forestT
      padRootsFixed := padRootsAfter
      rootAvoidsPad := rootAvoidsAfter }

/-! ## Honesty marker -/

/-- **Honesty marker — the left-padded matching simulation is INSTALLED with both step
preservations.**  `MatchingLeftPadSim` relates a base run to a run padded on the LEFT
(constant prefix wires `[0, delta)`, uniform shift `freshShiftAbove 0 delta`), with the padded
side stepping at the prefix-offset window `delta + position`.  The shifted spine
correspondence, the boundary-disciplined fold, the left seed instance, and the whiskerLeft
assembly are the next bricks.  `= true`. -/
def fxMode_hasMatchingLeftPadSim : Bool := true

end FX1Poly.Polygraph
