import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCounterShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable

/-! # MatchingRightPadSim — the right-padded matching simulation (whisker-right leg)

The whisker-right matching congruence (`MatchingSaturatedCongruence.whiskerRightCongruent`)
compares `matchingOf (whiskerRight oneCell alpha)` — run from the canonical seed over
`bottomCount + pad` wires — with `matchingOf alpha` run from the canonical seed over
`bottomCount` wires.  The whiskered spine fires the SAME cup/cap atoms at the SAME positions
(a right whisker only re-anchors the right accumulator, which no atom position reads), so the
two runs stay related by a `freshShiftAbove`-style simulation — except the padded run carries
`pad` EXTRA boundary wires as a constant suffix, which `MatchingShiftSim`'s equal-length
`openMap` cannot express.

This file installs the suffix-aware clone: `MatchingRightPadSim` relates the padded run to
the base run by (wires = shift-image ++ constant pad suffix, counter `delta` ahead, component
views correspond under the shift) PLUS the pad-zone inertness the boundary read-off will
need — pad ids `[threshold, threshold + delta)` are their own union-find roots and no
pad-avoiding node's root ever enters the zone (both consequences of the join-root
characterization `unionFindRootOf_unionFindJoin`; no fuel induction).  The per-atom steps:
a cup splices the two shifted fresh legs left of the untouched suffix
(`natListInsertAt_append_left`), a cap reads and removes the window pair inside the mapped
prefix (`natListRemoveTwoAt_append_left`), and both joins involve only pad-avoiding nodes
(fresh legs past the zone; reads are shift-images, which the shift routes around the zone).

The boundary-disciplined fold and the padded-boundary view read-off are the next bricks. -/

namespace FX1Poly.Polygraph

/-! ## List-surgery plumbing: insertion/removal left of a constant suffix -/

/-- Concatenation is associative (hand-rolled — `List.append_assoc` leaks `propext`). -/
private theorem natListAppendAssoc :
    (first second third : List Nat) →
    (first ++ second) ++ third = first ++ (second ++ third)
  | [], _, _ => rfl
  | head :: firstRest, second, third =>
      congrArg (head :: ·) (natListAppendAssoc firstRest second third)

/-- ★ **Insertion left of a suffix ignores the suffix**: splicing a block at a position at or
inside the left part of a concatenation inserts into the left part and carries the suffix
unchanged. -/
theorem natListInsertAt_append_left :
    (wires suffix block : List Nat) → (position : Nat) → position ≤ wires.length →
    natListInsertAt (wires ++ suffix) position block
      = natListInsertAt wires position block ++ suffix
  | wires, suffix, block, 0, _ => by
      simp only [natListInsertAt]
      exact (natListAppendAssoc block wires suffix).symm
  | [], _, _, position + 1, positionLe => absurd positionLe (Nat.not_succ_le_zero position)
  | head :: wiresRest, suffix, block, position + 1, positionLe =>
      congrArg (head :: ·)
        (natListInsertAt_append_left wiresRest suffix block position
          (Nat.le_of_succ_le_succ positionLe))

/-- ★ **Two-wire removal left of a suffix ignores the suffix**: dropping the pair at a window
strictly inside the left part of a concatenation removes from the left part and carries the
suffix unchanged. -/
theorem natListRemoveTwoAt_append_left :
    (wires suffix : List Nat) → (position : Nat) → position + 1 < wires.length →
    natListRemoveTwoAt (wires ++ suffix) position
      = natListRemoveTwoAt wires position ++ suffix
  | [], _, position, windowLt => absurd windowLt (Nat.not_succ_le_zero (position + 1))
  | _ :: _ :: _, _, 0, _ => rfl
  | [_], _, 0, windowLt => absurd windowLt (Nat.lt_irrefl 1)
  | [_], _, position + 1, windowLt =>
      absurd (Nat.le_of_succ_le_succ windowLt) (Nat.not_succ_le_zero (position + 1))
  | head :: secondWire :: wiresRest, suffix, position + 1, windowLt =>
      congrArg (head :: ·)
        (natListRemoveTwoAt_append_left (secondWire :: wiresRest) suffix position
          (Nat.lt_of_succ_lt_succ windowLt))

/-! ## Pad-zone inertness under a join -/

/-- The shift-image of ANY wire avoids the pad zone `[threshold, threshold + delta)`: below
the threshold the shift fixes it (still below), at or above it jumps past the zone. -/
theorem freshShiftAbove_avoidsPadZone (threshold delta identifier : Nat) :
    freshShiftAbove threshold delta identifier < threshold
      ∨ threshold + delta ≤ freshShiftAbove threshold delta identifier := by
  cases Nat.decLe threshold identifier with
  | isTrue isAtOrAboveThreshold =>
      rw [freshShiftAbove_ofLe threshold delta identifier isAtOrAboveThreshold]
      exact Or.inr (Nat.add_le_add_right isAtOrAboveThreshold delta)
  | isFalse isBelowThreshold =>
      rw [freshShiftAbove_ofNotLe threshold delta identifier isBelowThreshold]
      cases Nat.lt_or_ge identifier threshold with
      | inl isStrictlyBelow => exact Or.inl isStrictlyBelow
      | inr isAtOrAbove => exact absurd isAtOrAbove isBelowThreshold

/-- ★ **A join whose FIRST node avoids the pad zone keeps pad roots fixed.**  The join-root
characterization only reroutes nodes rooted at the first argument's root — which avoids the
zone by the root-avoidance hypothesis, so a pad node (its own root, inside the zone) keeps
its root. -/
theorem padRootsFixed_unionFindJoin (threshold delta : Nat) (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstNode secondNode : Nat)
    (firstAvoidsPad : firstNode < threshold ∨ threshold + delta ≤ firstNode)
    (rootAvoidsPad : ∀ node, node < threshold ∨ threshold + delta ≤ node →
      unionFindRootOf links node < threshold ∨ threshold + delta ≤ unionFindRootOf links node)
    (padRootsFixed : ∀ node, threshold ≤ node → node < threshold + delta →
      unionFindRootOf links node = node) :
    ∀ node, threshold ≤ node → node < threshold + delta →
      unionFindRootOf (unionFindJoin links firstNode secondNode) node = node := by
  intro node nodeAtOrAboveThreshold nodeBelowZoneEnd
  rw [unionFindRootOf_unionFindJoin links firstNode secondNode node forest,
    padRootsFixed node nodeAtOrAboveThreshold nodeBelowZoneEnd]
  cases rerouteTest : (unionFindRootOf links firstNode == node) with
  | true =>
      have firstRootEq : unionFindRootOf links firstNode = node :=
        of_decide_eq_true rerouteTest
      cases rootAvoidsPad firstNode firstAvoidsPad with
      | inl firstRootBelow =>
          exact absurd
            (Nat.lt_of_le_of_lt nodeAtOrAboveThreshold (firstRootEq ▸ firstRootBelow))
            (Nat.lt_irrefl threshold)
      | inr firstRootPastZone =>
          exact absurd
            (Nat.lt_of_lt_of_le nodeBelowZoneEnd (firstRootEq ▸ firstRootPastZone))
            (Nat.lt_irrefl node)
  | false => rfl

/-- ★ **A join whose SECOND node avoids the pad zone keeps pad-avoiding roots pad-avoiding.**
The join reroutes a node's root either to the second argument's root (pad-avoiding by the
hypotheses) or leaves it (pad-avoiding by the induction hypothesis). -/
theorem rootAvoidsPadZone_unionFindJoin (threshold delta : Nat) (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstNode secondNode : Nat)
    (secondAvoidsPad : secondNode < threshold ∨ threshold + delta ≤ secondNode)
    (rootAvoidsPad : ∀ node, node < threshold ∨ threshold + delta ≤ node →
      unionFindRootOf links node < threshold ∨ threshold + delta ≤ unionFindRootOf links node) :
    ∀ node, node < threshold ∨ threshold + delta ≤ node →
      unionFindRootOf (unionFindJoin links firstNode secondNode) node < threshold
        ∨ threshold + delta
            ≤ unionFindRootOf (unionFindJoin links firstNode secondNode) node := by
  intro node nodeAvoidsPad
  rw [unionFindRootOf_unionFindJoin links firstNode secondNode node forest]
  cases rerouteTest : (unionFindRootOf links firstNode == unionFindRootOf links node) with
  | true => exact rootAvoidsPad secondNode secondAvoidsPad
  | false => exact rootAvoidsPad node nodeAvoidsPad

/-! ## The right-padded simulation invariant -/

/-- ★ **The right-padded matching simulation** — the whisker-RIGHT clone of
`MatchingShiftSim`: the padded state's wires are the shift-images of the base state's wires
followed by a CONSTANT pad suffix (the whiskered 1-cell's untouched boundary wires), the
counter runs `delta` ahead with the shift threshold at or below the base counter, the
partition views correspond under the shift, and the pad zone `[threshold, threshold + delta)`
stays inert: pad ids are their own roots and no pad-avoiding node's root enters the zone. -/
structure MatchingRightPadSim (threshold delta : Nat) (padSuffix : List Nat)
    (stateS stateT : WireState) : Prop where
  /-- The padded wires are the shift-images of the base wires plus the constant suffix. -/
  openMap : stateT.openWires
    = stateS.openWires.map (freshShiftAbove threshold delta) ++ padSuffix
  /-- The padded counter runs exactly `delta` ahead. -/
  nfShift : stateT.nextFresh = stateS.nextFresh + delta
  /-- The shift threshold stays at or below the base counter. -/
  thresholdLe : threshold ≤ stateS.nextFresh
  /-- The same-component booleans correspond under the shift. -/
  componentComm : ∀ a b,
    (unionFindRootOf stateT.links (freshShiftAbove threshold delta a)
        == unionFindRootOf stateT.links (freshShiftAbove threshold delta b))
      = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b)
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The base links form a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The padded links form a forest. -/
  forestT : isUnionFindForest stateT.links
  /-- Every pad-zone id is its own root in the padded links. -/
  padRootsFixed : ∀ node, threshold ≤ node → node < threshold + delta →
    unionFindRootOf stateT.links node = node
  /-- No pad-avoiding node's root enters the pad zone in the padded links. -/
  rootAvoidsPad : ∀ node, node < threshold ∨ threshold + delta ≤ node →
    unionFindRootOf stateT.links node < threshold
      ∨ threshold + delta ≤ unionFindRootOf stateT.links node

/-! ## Step preservation: the cup -/

/-- ★ **A CUP step preserves the right-padded simulation.**  Both sides splice their two
fresh legs at the same in-window position: the padded splice happens left of the untouched
suffix (`natListInsertAt_append_left`) and the legs are exactly the shift-images of the base
legs; the component view is the counter-shift cup lemma verbatim; the joined fresh legs sit
past the pad zone, so the zone stays inert. -/
theorem matchingRightPadSim_stepCup (threshold delta : Nat) (padSuffix : List Nat)
    (stateS stateT : WireState) (position : Nat)
    (positionLe : position ≤ stateS.openWires.length)
    (sim : MatchingRightPadSim threshold delta padSuffix stateS stateT) :
    MatchingRightPadSim threshold delta padSuffix
      (stepCup stateS position) (stepCup stateT position) := by
  have freshLegAvoidsPad : threshold + delta ≤ stateT.nextFresh := by
    rw [sim.nfShift]
    exact Nat.add_le_add_right sim.thresholdLe delta
  have openMapAfter : (stepCup stateT position).openWires
      = (stepCup stateS position).openWires.map (freshShiftAbove threshold delta)
        ++ padSuffix := by
    rw [stepCup_openWires stateT position, stepCup_openWires stateS position, sim.openMap,
      natListInsertAt_append_left (stateS.openWires.map (freshShiftAbove threshold delta))
        padSuffix [stateT.nextFresh, stateT.nextFresh + 1] position
        (by rw [mapLength]; exact positionLe),
      natListInsertAt_map (freshShiftAbove threshold delta) stateS.openWires position
        [stateS.nextFresh, stateS.nextFresh + 1],
      sim.nfShift]
    show natListInsertAt (stateS.openWires.map (freshShiftAbove threshold delta)) position
          [stateS.nextFresh + delta, stateS.nextFresh + delta + 1] ++ padSuffix
        = natListInsertAt (stateS.openWires.map (freshShiftAbove threshold delta)) position
          [freshShiftAbove threshold delta stateS.nextFresh,
            freshShiftAbove threshold delta (stateS.nextFresh + 1)] ++ padSuffix
    rw [freshShiftAbove_ofLe threshold delta stateS.nextFresh sim.thresholdLe,
      freshShiftAbove_ofLe threshold delta (stateS.nextFresh + 1)
        (Nat.le_succ_of_le sim.thresholdLe),
      Nat.add_right_comm stateS.nextFresh 1 delta]
  have nfShiftAfter : (stepCup stateT position).nextFresh
      = (stepCup stateS position).nextFresh + delta := by
    rw [stepCup_nextFresh stateT position, stepCup_nextFresh stateS position, sim.nfShift,
      Nat.add_right_comm stateS.nextFresh delta 2]
  have padRootsAfter : ∀ node, threshold ≤ node → node < threshold + delta →
      unionFindRootOf (stepCup stateT position).links node = node :=
    padRootsFixed_unionFindJoin threshold delta stateT.links sim.forestT
      stateT.nextFresh (stateT.nextFresh + 1) (Or.inr freshLegAvoidsPad)
      sim.rootAvoidsPad sim.padRootsFixed
  have rootAvoidsAfter : ∀ node, node < threshold ∨ threshold + delta ≤ node →
      unionFindRootOf (stepCup stateT position).links node < threshold
        ∨ threshold + delta ≤ unionFindRootOf (stepCup stateT position).links node :=
    rootAvoidsPadZone_unionFindJoin threshold delta stateT.links sim.forestT
      stateT.nextFresh (stateT.nextFresh + 1)
      (Or.inr (Nat.le_succ_of_le freshLegAvoidsPad)) sim.rootAvoidsPad
  exact
    { openMap := openMapAfter
      nfShift := nfShiftAfter
      thresholdLe := Nat.le_trans sim.thresholdLe (Nat.le_add_right stateS.nextFresh 2)
      componentComm := fun a b =>
        stepCup_componentComm_ofShift threshold delta stateS stateT sim.forestS sim.forestT
          sim.nfShift sim.thresholdLe sim.componentComm position a b
      loopsEq := sim.loopsEq
      forestS := isUnionFindForest_stepCup stateS position sim.forestS
      forestT := isUnionFindForest_stepCup stateT position sim.forestT
      padRootsFixed := padRootsAfter
      rootAvoidsPad := rootAvoidsAfter }

/-! ## Step preservation: the cap -/

/-- ★ **A CAP step preserves the right-padded simulation.**  The two window reads land inside
the mapped prefix (`natListGetAt_append_inside`) and are shift-images of the base reads
(`natListGetAt_map_inRange`), so the component view is the rename-generic cap lemma verbatim,
the loop increments agree through the corresponding same-component test, the removal happens
left of the untouched suffix (`natListRemoveTwoAt_append_left`), and any join is between two
shift-images — which the shift routes around the pad zone. -/
theorem matchingRightPadSim_stepCap (threshold delta : Nat) (padSuffix : List Nat)
    (stateS stateT : WireState) (position : Nat)
    (windowLt : position + 1 < stateS.openWires.length)
    (sim : MatchingRightPadSim threshold delta padSuffix stateS stateT) :
    MatchingRightPadSim threshold delta padSuffix
      (stepCap stateS position) (stepCap stateT position) := by
  have positionLt : position < stateS.openWires.length := Nat.lt_of_succ_lt windowLt
  have leftReadCorr : natListGetAt stateT.openWires position
      = freshShiftAbove threshold delta (natListGetAt stateS.openWires position) := by
    rw [sim.openMap,
      natListGetAt_append_inside (stateS.openWires.map (freshShiftAbove threshold delta))
        padSuffix position (by rw [mapLength]; exact positionLt),
      natListGetAt_map_inRange (freshShiftAbove threshold delta) stateS.openWires position
        positionLt]
  have rightReadCorr : natListGetAt stateT.openWires (position + 1)
      = freshShiftAbove threshold delta (natListGetAt stateS.openWires (position + 1)) := by
    rw [sim.openMap,
      natListGetAt_append_inside (stateS.openWires.map (freshShiftAbove threshold delta))
        padSuffix (position + 1) (by rw [mapLength]; exact windowLt),
      natListGetAt_map_inRange (freshShiftAbove threshold delta) stateS.openWires
        (position + 1) windowLt]
  have sameComponentCorr : isSameComponent stateT.links
        (natListGetAt stateT.openWires position)
        (natListGetAt stateT.openWires (position + 1))
      = isSameComponent stateS.links (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)) := by
    rw [leftReadCorr, rightReadCorr]
    exact sim.componentComm (natListGetAt stateS.openWires position)
      (natListGetAt stateS.openWires (position + 1))
  have openMapAfter : (stepCap stateT position).openWires
      = (stepCap stateS position).openWires.map (freshShiftAbove threshold delta)
        ++ padSuffix := by
    rw [stepCap_openWires stateT position, stepCap_openWires stateS position, sim.openMap,
      natListRemoveTwoAt_append_left (stateS.openWires.map (freshShiftAbove threshold delta))
        padSuffix position (by rw [mapLength]; exact windowLt),
      natListRemoveTwoAt_map (freshShiftAbove threshold delta) stateS.openWires position]
  have nfShiftAfter : (stepCap stateT position).nextFresh
      = (stepCap stateS position).nextFresh + delta := by
    rw [stepCap_nextFresh stateT position, stepCap_nextFresh stateS position]
    exact sim.nfShift
  have thresholdAfter : threshold ≤ (stepCap stateS position).nextFresh := by
    rw [stepCap_nextFresh stateS position]
    exact sim.thresholdLe
  have loopsAfter : (stepCap stateT position).loops = (stepCap stateS position).loops := by
    rw [stepCap_loops stateT position, stepCap_loops stateS position, sameComponentCorr,
      sim.loopsEq]
  have padRootsAfter : ∀ node, threshold ≤ node → node < threshold + delta →
      unionFindRootOf (stepCap stateT position).links node = node := by
    rw [stepCap_links stateT position, leftReadCorr, rightReadCorr]
    cases capTest : isSameComponent stateT.links
        (freshShiftAbove threshold delta (natListGetAt stateS.openWires position))
        (freshShiftAbove threshold delta (natListGetAt stateS.openWires (position + 1))) with
    | true => exact sim.padRootsFixed
    | false =>
        exact padRootsFixed_unionFindJoin threshold delta stateT.links sim.forestT
          (freshShiftAbove threshold delta (natListGetAt stateS.openWires position))
          (freshShiftAbove threshold delta (natListGetAt stateS.openWires (position + 1)))
          (freshShiftAbove_avoidsPadZone threshold delta
            (natListGetAt stateS.openWires position))
          sim.rootAvoidsPad sim.padRootsFixed
  have rootAvoidsAfter : ∀ node, node < threshold ∨ threshold + delta ≤ node →
      unionFindRootOf (stepCap stateT position).links node < threshold
        ∨ threshold + delta ≤ unionFindRootOf (stepCap stateT position).links node := by
    rw [stepCap_links stateT position, leftReadCorr, rightReadCorr]
    cases capTest : isSameComponent stateT.links
        (freshShiftAbove threshold delta (natListGetAt stateS.openWires position))
        (freshShiftAbove threshold delta (natListGetAt stateS.openWires (position + 1))) with
    | true => exact sim.rootAvoidsPad
    | false =>
        exact rootAvoidsPadZone_unionFindJoin threshold delta stateT.links sim.forestT
          (freshShiftAbove threshold delta (natListGetAt stateS.openWires position))
          (freshShiftAbove threshold delta (natListGetAt stateS.openWires (position + 1)))
          (freshShiftAbove_avoidsPadZone threshold delta
            (natListGetAt stateS.openWires (position + 1)))
          sim.rootAvoidsPad
  exact
    { openMap := openMapAfter
      nfShift := nfShiftAfter
      thresholdLe := thresholdAfter
      componentComm := fun a b =>
        stepCap_componentComm (freshShiftAbove threshold delta) stateS stateT sim.forestS
          sim.forestT sim.componentComm position leftReadCorr rightReadCorr a b
      loopsEq := loopsAfter
      forestS := isUnionFindForest_stepCap stateS position sim.forestS
      forestT := isUnionFindForest_stepCap stateT position sim.forestT
      padRootsFixed := padRootsAfter
      rootAvoidsPad := rootAvoidsAfter }

/-! ## Step dispatch and the boundary-disciplined fold -/

/-- ★ **The right-padded sim is step-stable from the window range.**  A cup's position is at
or inside the window (`dom = 0`), a cap's window pair is strictly inside it (`dom = 2`) —
each dispatches to its step lemma. -/
theorem matchingRightPadSim_step_ofInRange {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (threshold delta : Nat) (padSuffix : List Nat) (stateS stateT : WireState)
    (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ stateS.openWires.length)
    (sim : MatchingRightPadSim threshold delta padSuffix stateS stateT) :
    MatchingRightPadSim threshold delta padSuffix
      (stepAtom stateS atom) (stepAtom stateT atom) := by
  cases arity with
  | inl cupArity =>
      rw [stepAtom_ofCupArity stateS atom cupArity.1 cupArity.2,
        stepAtom_ofCupArity stateT atom cupArity.1 cupArity.2]
      rw [cupArity.1, Nat.add_zero] at windowInRange
      exact matchingRightPadSim_stepCup threshold delta padSuffix stateS stateT
        atom.leftContext.length windowInRange sim
  | inr capArity =>
      rw [stepAtom_ofCapArity stateS atom capArity.1 capArity.2,
        stepAtom_ofCapArity stateT atom capArity.1 capArity.2]
      rw [capArity.1] at windowInRange
      exact matchingRightPadSim_stepCap threshold delta padSuffix stateS stateT
        atom.leftContext.length
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) windowInRange)
        sim

/-- ★ **The right-padded sim folds under the boundary discipline** — chain + arity + tracking
thread exactly as in the counter-shift fold; the threshold bound travels INSIDE the sim (it is
a structure field here), so only the wire-count tracking needs re-establishing per step. -/
theorem matchingRightPadSim_processSpine_ofBoundaryDiscipline {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (threshold delta : Nat)
    (padSuffix : List Nat) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) →
    (stateS stateT : WireState) → (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength atoms →
    SpineHasCupCapAtoms atoms →
    stateS.openWires.length = boundaryLength →
    MatchingRightPadSim threshold delta padSuffix stateS stateT →
    MatchingRightPadSim threshold delta padSuffix
      (processSpine stateS atoms) (processSpine stateT atoms)
  | [], _, _, _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, boundaryLength, chained, arity, tracks, sim => by
      show MatchingRightPadSim threshold delta padSuffix
        (processSpine (stepAtom stateS atom) rest) (processSpine (stepAtom stateT atom) rest)
      have headAndTail := spineBoundaryChained_tail chained
      have arityParts := spineHasCupCapAtoms_tail arity
      have windowInRange : atom.leftContext.length + atom.generatorDom.length
          ≤ stateS.openWires.length := by
        rw [tracks, ← headAndTail.1]
        exact Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
          atom.rightContext.length
      exact matchingRightPadSim_processSpine_ofBoundaryDiscipline threshold delta padSuffix
        rest (stepAtom stateS atom) (stepAtom stateT atom) atom.codBoundaryLength
        headAndTail.2 arityParts.2
        (stepAtom_openWires_tracksBoundary stateS atom arityParts.1
          (tracks.trans headAndTail.1.symm))
        (matchingRightPadSim_step_ofInRange threshold delta padSuffix stateS stateT atom
          arityParts.1 windowInRange sim)

/-- **Honesty marker — the right-padded simulation steps AND fold are inhabited.**  The
`MatchingRightPadSim` relation (suffix-aware wires, shifted counter, corresponding component
views, inert pad zone) is preserved by in-window cup and cap steps and folds over any chained,
cup/cap-disciplined spine.  NOT yet shipped: the padded-boundary view read-off, the
right-accumulator invariance of the run (`stepAtom` ignores `rightContext`), and the
`whiskerRightCongruent` field assembly — the next MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingRightPadSimSteps : Bool := true

end FX1Poly.Polygraph
