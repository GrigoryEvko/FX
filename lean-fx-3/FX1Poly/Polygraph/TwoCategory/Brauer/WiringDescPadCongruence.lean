import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldRename
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRename

/-! # KEYSTONE15 — the horizontal pad/shift congruence port, spine -> Brauer engine (right pad)

The walking-adjunction spine ships the whisker-RIGHT matching congruence
`extractDiagram_ofRightPadSimPair` (`FreeTwoCell/MatchingRightPadCongruence.lean`): two runs related
by the right-padded matching simulation `MatchingRightPadSim` with equal BASE extracts have equal
PADDED extracts.  That payoff is ENGINE-AGNOSTIC — it consumes any `WireState` pair related by the
pad simulation.  What the spine builds cup/cap-only (via `matchingRightPadSim_stepCup`/`_stepCap` +
the boundary-disciplined fold) is the CONSTRUCTION of that simulation at `processSpine`.

This file ports that construction to the generic `stepWiring` engine — crossing included — landing
`processBrauer_rightPadSim`: the SAME Brauer word `atoms` fired from the seed at boundary `threshold`
and from the seed at the WIDER boundary `threshold + delta` are right-pad-simulated.  Composed with the
shipped payoff, this gives `brauerSeedExtract_ofRightPad`: an extract equality at width `threshold`
transports to width `threshold + delta` (the relation fired at offset `0` in a wider boundary).

## The port strategy — WHOLE-word, empty-base (the crossing multi-arc fold is FREE)

Rather than fold the full pad simulation step-by-step (whose `componentComm` at a non-empty mid base
would need a bespoke multi-arc `applyJoinEvents` rename lemma), the construction SPLITS:

  * A light `RightPadWireSim` (open-wire map + counter shift + threshold bound) is folded through the
    word (`processBrauer_rightPadWireSim`), giving the final `openMap` / `nfShift` / `thresholdLe`, and
    a whole-word trace correspondence `rightPadWireSim_wordJoinEvents`: the wider run's decoded trace
    is the `freshShiftAbove`-rename of the base run's trace.  The crossing needs NO special case — the
    wire plumbing (slice / fresh block / splice) ignores the arcs.
  * The LINK-level fields are then read off the WHOLE trace at the EMPTY base (both runs seed with no
    links): `componentComm` from `componentView_applyJoinEvents_ofRename` (empty-base rename
    equivariance), `loopsEq` from `countJoinEventLoops_ofRename`, and the pad-zone inertness
    (`padRootsFixed` / `rootAvoidsPad`) by folding the shipped single-join bricks
    `padRootsFixed_unionFindJoin` / `rootAvoidsPadZone_unionFindJoin` over the all-shift-image trace.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local subtraction-free arithmetic (Init's cancels leak `propext`) -/

/-- `(n + m) - m = n`, reproved by hand.  Structural on `m`. -/
private theorem padAddSubCancelRight : (value count : Nat) → (value + count) - count = value
  | value, 0 => rfl
  | value, count + 1 => by
      show (value + (count + 1)) - (count + 1) = value
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact padAddSubCancelRight value count

/-- Cancel a common right summand `a + d = b + d -> a = b`.  Structural on `d` via `Nat.succ.inj`. -/
private theorem padAddRightCancel : (leftValue rightValue count : Nat) →
    leftValue + count = rightValue + count → leftValue = rightValue
  | _, _, 0, h => h
  | leftValue, rightValue, count + 1, h =>
      padAddRightCancel leftValue rightValue count (Nat.succ.inj h)

/-- `List.map` distributes over `++` (local copy — the shipped one is private). -/
private theorem padMapAppend {Element ResultElement : Type} (mapped : Element → ResultElement) :
    (first second : List Element) → (first ++ second).map mapped = first.map mapped ++ second.map mapped
  | [], _ => rfl
  | head :: firstRest, second => congrArg (mapped head :: ·) (padMapAppend mapped firstRest second)

/-- `(List.range count).length = count` — local copy (the shipped copies are private). -/
private theorem rangeLengthPad (count : Nat) : (List.range count).length = count :=
  rangeLength_local count

/-- Reading `List.range.loop` at a past-the-front offset drops into the accumulator. -/
private theorem rangeLoopGetAtPastPad : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastPad count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

/-- Reading `List.range.loop` below its front returns the index. -/
private theorem rangeLoopGetAtBelowPad : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowPad count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastPad count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

/-- Reading `List.range count` below its length returns the index. -/
private theorem rangeGetAtBelowPad (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowPad count [] index indexBelow

/-! ## List surgery: removal / slice left of a constant suffix (block-many version) -/

/-- ★ **A block removal strictly inside the left part of a concatenation ignores the suffix.**  The
generic-width mirror of the shipped `natListRemoveTwoAt_append_left`.  Structural; `count = 0` first,
then the position / list recursion. -/
theorem natListRemoveManyAt_append_left :
    (wires suffix : List Nat) → (position count : Nat) → position + count ≤ wires.length →
    natListRemoveManyAt (wires ++ suffix) position count
      = natListRemoveManyAt wires position count ++ suffix
  | wires, suffix, position, 0, _ => by
      rw [removeManyAt_zero (wires ++ suffix) position, removeManyAt_zero wires position]
  | [], _, position, count + 1, windowLe =>
      absurd windowLe (by
        rw [Nat.add_succ]
        exact Nat.not_succ_le_zero (position + count))
  | headWire :: restWires, suffix, 0, count + 1, windowLe => by
      show natListRemoveManyAt (headWire :: (restWires ++ suffix)) 0 (count + 1)
        = natListRemoveManyAt (headWire :: restWires) 0 (count + 1) ++ suffix
      rw [removeManyAt_zero_cons headWire (restWires ++ suffix) count,
        removeManyAt_zero_cons headWire restWires count]
      have tailWindow : 0 + count ≤ restWires.length := by
        rw [Nat.zero_add]
        rw [Nat.zero_add] at windowLe
        exact Nat.le_of_succ_le_succ windowLe
      exact natListRemoveManyAt_append_left restWires suffix 0 count tailWindow
  | headWire :: restWires, suffix, position + 1, count, windowLe => by
      show natListRemoveManyAt (headWire :: (restWires ++ suffix)) (position + 1) count
        = natListRemoveManyAt (headWire :: restWires) (position + 1) count ++ suffix
      rw [removeManyAt_succ_cons headWire (restWires ++ suffix) position count,
        removeManyAt_succ_cons headWire restWires position count]
      have tailWindow : position + count ≤ restWires.length := by
        rw [Nat.succ_add] at windowLe
        exact Nat.le_of_succ_le_succ windowLe
      exact congrArg (headWire :: ·)
        (natListRemoveManyAt_append_left restWires suffix position count tailWindow)

/-- ★ **A window slice strictly inside the left part of a concatenation ignores the suffix.**
Structural; `count = 0` first, then the position / list recursion. -/
theorem natListSliceAt_append_left :
    (wires suffix : List Nat) → (position count : Nat) → position + count ≤ wires.length →
    natListSliceAt (wires ++ suffix) position count
      = natListSliceAt wires position count
  | wires, suffix, position, 0, _ => by
      rw [sliceAt_count_zero (wires ++ suffix) position, sliceAt_count_zero wires position]
  | [], _, position, count + 1, windowLe =>
      absurd windowLe (by
        rw [Nat.add_succ]
        exact Nat.not_succ_le_zero (position + count))
  | headWire :: restWires, suffix, 0, count + 1, windowLe => by
      show natListSliceAt (headWire :: (restWires ++ suffix)) 0 (count + 1)
        = natListSliceAt (headWire :: restWires) 0 (count + 1)
      rw [sliceAt_cons_zero_succ headWire (restWires ++ suffix) count,
        sliceAt_cons_zero_succ headWire restWires count]
      have tailWindow : 0 + count ≤ restWires.length := by
        rw [Nat.zero_add]
        rw [Nat.zero_add] at windowLe
        exact Nat.le_of_succ_le_succ windowLe
      exact congrArg (headWire :: ·)
        (natListSliceAt_append_left restWires suffix 0 count tailWindow)
  | headWire :: restWires, suffix, position + 1, count, windowLe => by
      show natListSliceAt (headWire :: (restWires ++ suffix)) (position + 1) count
        = natListSliceAt (headWire :: restWires) (position + 1) count
      rw [sliceAt_cons_succ headWire (restWires ++ suffix) position count,
        sliceAt_cons_succ headWire restWires position count]
      have tailWindow : position + count ≤ restWires.length := by
        rw [Nat.succ_add] at windowLe
        exact Nat.le_of_succ_le_succ windowLe
      exact natListSliceAt_append_left restWires suffix position count tailWindow

/-! ## The fresh output block re-bases under the shift -/

/-- The fresh output block at the wider counter IS the `freshShiftAbove`-image of the fresh output
block at the base counter — both blocks are at or above the threshold, so the shift adds `delta`
uniformly (which the counter shift `nfShift` records). -/
theorem rightPadOutputNodes_map (threshold delta : Nat) (stateS stateT : WireState) (outputCount : Nat)
    (nfShift : stateT.nextFresh = stateS.nextFresh + delta)
    (thresholdLe : threshold ≤ stateS.nextFresh) :
    (List.range outputCount).map (· + stateT.nextFresh)
      = ((List.range outputCount).map (· + stateS.nextFresh)).map (freshShiftAbove threshold delta) := by
  apply natListEqOfPointwiseGetAt
  · rw [mapLength, mapLength, mapLength]
  · intro index indexInRange
    have indexLt : index < outputCount := by
      have lengthEq : ((List.range outputCount).map (· + stateT.nextFresh)).length = outputCount := by
        rw [mapLength, rangeLengthPad]
      rw [lengthEq] at indexInRange
      exact indexInRange
    rw [natListGetAt_map_inRange (· + stateT.nextFresh) (List.range outputCount) index
        (by rw [rangeLengthPad]; exact indexLt),
      rangeGetAtBelowPad outputCount index indexLt,
      natListGetAt_map_inRange (freshShiftAbove threshold delta)
        ((List.range outputCount).map (· + stateS.nextFresh)) index
        (by rw [mapLength, rangeLengthPad]; exact indexLt),
      natListGetAt_map_inRange (· + stateS.nextFresh) (List.range outputCount) index
        (by rw [rangeLengthPad]; exact indexLt),
      rangeGetAtBelowPad outputCount index indexLt,
      freshShiftAbove_ofLe threshold delta (index + stateS.nextFresh)
        (Nat.le_trans thresholdLe (Nat.le_add_left stateS.nextFresh index)),
      nfShift, Nat.add_assoc index stateS.nextFresh delta]

/-! ## One decoded generator endpoint / arc list under node-wise renaming -/

/-- One decoded wiring endpoint under node-wise renaming is the renamed endpoint — an INPUT tag reads
the renamed input slice, an OUTPUT tag the renamed fresh block, both in range. -/
theorem wiringEndpointNode_mapNodes (sigma : Nat → Nat) (inputNodes outputNodes : List Nat)
    (inputCount outputCount tag : Nat)
    (inputLen : inputNodes.length = inputCount) (outputLen : outputNodes.length = outputCount)
    (tagLt : tag < inputCount + outputCount) :
    wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount tag
      = sigma (wiringEndpointNode inputNodes outputNodes inputCount tag) := by
  show (if tag < inputCount then natListGetAt (inputNodes.map sigma) tag
        else natListGetAt (outputNodes.map sigma) (tag - inputCount))
      = sigma (if tag < inputCount then natListGetAt inputNodes tag
        else natListGetAt outputNodes (tag - inputCount))
  by_cases tagBelow : tag < inputCount
  · rw [if_pos tagBelow, if_pos tagBelow,
      natListGetAt_map_inRange sigma inputNodes tag (by rw [inputLen]; exact tagBelow)]
  · rw [if_neg tagBelow, if_neg tagBelow]
    have inputLe : inputCount ≤ tag := Nat.le_of_not_lt tagBelow
    obtain ⟨offset, tagEq⟩ := Nat.le.dest inputLe
    have offsetLt : offset < outputCount := by
      rw [← tagEq] at tagLt
      exact Nat.lt_of_add_lt_add_left tagLt
    have subEq : tag - inputCount = offset := by
      rw [← tagEq, Nat.add_comm inputCount offset, padAddSubCancelRight offset inputCount]
    rw [natListGetAt_map_inRange sigma outputNodes (tag - inputCount)
      (by rw [outputLen, subEq]; exact offsetLt)]

/-- A generator's whole decoded arc trace under node-wise renaming is the renamed canonical trace.
Structural on the arcs, each endpoint via `wiringEndpointNode_mapNodes`. -/
theorem wiringArcEvents_mapNodes (sigma : Nat → Nat) (inputNodes outputNodes : List Nat)
    (inputCount outputCount : Nat)
    (inputLen : inputNodes.length = inputCount) (outputLen : outputNodes.length = outputCount) :
    (arcs : List (Nat × Nat)) →
    (∀ arc ∈ arcs, arc.1 < inputCount + outputCount ∧ arc.2 < inputCount + outputCount) →
    wiringArcEvents (inputNodes.map sigma) (outputNodes.map sigma) inputCount arcs
      = (wiringArcEvents inputNodes outputNodes inputCount arcs).map
          (fun event => (sigma event.1, sigma event.2))
  | [], _ => rfl
  | (firstTag, secondTag) :: rest, tagsOk => by
      have headTags := tagsOk (firstTag, secondTag) (List.Mem.head rest)
      have restTags : ∀ arc ∈ rest, arc.1 < inputCount + outputCount ∧ arc.2 < inputCount + outputCount :=
        fun arc arcMem => tagsOk arc (List.Mem.tail (firstTag, secondTag) arcMem)
      show (wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount firstTag,
            wiringEndpointNode (inputNodes.map sigma) (outputNodes.map sigma) inputCount secondTag)
            :: wiringArcEvents (inputNodes.map sigma) (outputNodes.map sigma) inputCount rest
          = (sigma (wiringEndpointNode inputNodes outputNodes inputCount firstTag),
             sigma (wiringEndpointNode inputNodes outputNodes inputCount secondTag))
            :: (wiringArcEvents inputNodes outputNodes inputCount rest).map
                (fun event => (sigma event.1, sigma event.2))
      rw [wiringEndpointNode_mapNodes sigma inputNodes outputNodes inputCount outputCount firstTag
            inputLen outputLen headTags.1,
        wiringEndpointNode_mapNodes sigma inputNodes outputNodes inputCount outputCount secondTag
            inputLen outputLen headTags.2,
        wiringArcEvents_mapNodes sigma inputNodes outputNodes inputCount outputCount inputLen outputLen
            rest restTags]

/-! ## `freshShiftAbove` is injective; its trace image avoids the pad zone -/

/-- ★ **`freshShiftAbove threshold delta` is injective.**  Below the threshold it fixes, at or above
it shifts up by `delta`; the two images sit in disjoint ranges, so the four threshold-comparison cases
each force equality of the arguments. -/
theorem freshShiftAbove_injective (threshold delta : Nat) :
    ∀ firstValue secondValue : Nat,
      freshShiftAbove threshold delta firstValue = freshShiftAbove threshold delta secondValue →
      firstValue = secondValue := by
  intro firstValue secondValue imagesEqual
  cases Nat.decLe threshold firstValue with
  | isTrue firstAtOrAbove =>
      cases Nat.decLe threshold secondValue with
      | isTrue secondAtOrAbove =>
          rw [freshShiftAbove_ofLe threshold delta firstValue firstAtOrAbove,
            freshShiftAbove_ofLe threshold delta secondValue secondAtOrAbove] at imagesEqual
          exact padAddRightCancel firstValue secondValue delta imagesEqual
      | isFalse secondBelow =>
          rw [freshShiftAbove_ofLe threshold delta firstValue firstAtOrAbove,
            freshShiftAbove_ofNotLe threshold delta secondValue secondBelow] at imagesEqual
          have secondLt : secondValue < threshold := Nat.lt_of_not_le secondBelow
          exact absurd (imagesEqual ▸ Nat.le_trans firstAtOrAbove (Nat.le_add_right firstValue delta))
            (Nat.not_le_of_lt secondLt)
  | isFalse firstBelow =>
      cases Nat.decLe threshold secondValue with
      | isTrue secondAtOrAbove =>
          rw [freshShiftAbove_ofNotLe threshold delta firstValue firstBelow,
            freshShiftAbove_ofLe threshold delta secondValue secondAtOrAbove] at imagesEqual
          have firstLt : firstValue < threshold := Nat.lt_of_not_le firstBelow
          exact absurd
            (imagesEqual ▸ Nat.le_trans secondAtOrAbove (Nat.le_add_right secondValue delta) :
              threshold ≤ firstValue)
            (Nat.not_le_of_lt firstLt)
      | isFalse secondBelow =>
          rw [freshShiftAbove_ofNotLe threshold delta firstValue firstBelow,
            freshShiftAbove_ofNotLe threshold delta secondValue secondBelow] at imagesEqual
          exact imagesEqual

/-- Every endpoint of a `freshShiftAbove`-renamed trace avoids the pad zone `[threshold, threshold + delta)`.
Structural on the events. -/
theorem renamedTraceAvoidsPadZone (threshold delta : Nat) :
    (events : List (Nat × Nat)) →
    ∀ event ∈ events.map (fun e => (freshShiftAbove threshold delta e.1, freshShiftAbove threshold delta e.2)),
      (event.1 < threshold ∨ threshold + delta ≤ event.1)
        ∧ (event.2 < threshold ∨ threshold + delta ≤ event.2)
  | [], event, mem => nomatch mem
  | headEvent :: restEvents, event, mem => by
      cases mem with
      | head _ =>
          exact ⟨freshShiftAbove_avoidsPadZone threshold delta headEvent.1,
            freshShiftAbove_avoidsPadZone threshold delta headEvent.2⟩
      | tail _ memRest => exact renamedTraceAvoidsPadZone threshold delta restEvents event memRest

/-! ## The pad-zone inertness of an all-avoiding event fold -/

/-- ★ **Folding joins whose endpoints all avoid the pad zone keeps pad ids self-rooted and pad-avoiding
roots pad-avoiding.**  Structural on the events, iterating the shipped single-join bricks
`padRootsFixed_unionFindJoin` / `rootAvoidsPadZone_unionFindJoin`. -/
theorem applyJoinEvents_padInert (threshold delta : Nat) :
    (events : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    (∀ event ∈ events,
      (event.1 < threshold ∨ threshold + delta ≤ event.1)
        ∧ (event.2 < threshold ∨ threshold + delta ≤ event.2)) →
    (∀ node, threshold ≤ node → node < threshold + delta → unionFindRootOf links node = node) →
    (∀ node, node < threshold ∨ threshold + delta ≤ node →
      unionFindRootOf links node < threshold ∨ threshold + delta ≤ unionFindRootOf links node) →
    (∀ node, threshold ≤ node → node < threshold + delta →
        unionFindRootOf (applyJoinEvents events links) node = node)
      ∧ (∀ node, node < threshold ∨ threshold + delta ≤ node →
        unionFindRootOf (applyJoinEvents events links) node < threshold
          ∨ threshold + delta ≤ unionFindRootOf (applyJoinEvents events links) node)
  | [], _, _, _, padFixed, rootAvoids => ⟨padFixed, rootAvoids⟩
  | (firstNode, secondNode) :: restEvents, links, forest, allAvoid, padFixed, rootAvoids => by
      have headAvoid := allAvoid (firstNode, secondNode) (List.Mem.head restEvents)
      have restAvoid : ∀ event ∈ restEvents,
          (event.1 < threshold ∨ threshold + delta ≤ event.1)
            ∧ (event.2 < threshold ∨ threshold + delta ≤ event.2) :=
        fun event eventMem => allAvoid event (List.Mem.tail (firstNode, secondNode) eventMem)
      exact applyJoinEvents_padInert threshold delta restEvents
        (unionFindJoin links firstNode secondNode)
        (isUnionFindForest_unionFindJoin links firstNode secondNode forest)
        restAvoid
        (padRootsFixed_unionFindJoin threshold delta links forest firstNode secondNode
          headAvoid.1 rootAvoids padFixed)
        (rootAvoidsPadZone_unionFindJoin threshold delta links forest firstNode secondNode
          headAvoid.2 rootAvoids)

/-! ## The light right-pad wire simulation and its fold -/

/-- ★ **The light right-pad WIRE simulation** — the wider run's open wires are the `freshShiftAbove`
image of the base run's open wires followed by the constant pad suffix, the counter runs exactly
`delta` ahead, and the shift threshold stays at or below the base counter.  (The link-level fields of
the full `MatchingRightPadSim` are read off the whole trace separately.) -/
structure RightPadWireSim (threshold delta : Nat) (stateS stateT : WireState) : Prop where
  /-- The padded wires are the shift-image of the base wires plus the constant pad suffix. -/
  openMap : stateT.openWires
    = stateS.openWires.map (freshShiftAbove threshold delta) ++ padIdentifiers threshold delta
  /-- The padded counter runs exactly `delta` ahead. -/
  nfShift : stateT.nextFresh = stateS.nextFresh + delta
  /-- The shift threshold stays at or below the base counter. -/
  thresholdLe : threshold ≤ stateS.nextFresh

/-- ★ **ONE `stepWiring` step preserves the right-pad wire simulation, for ANY generator.**  The
removal / splice happen left of the untouched pad suffix (`natListRemoveManyAt_append_left` /
`natListInsertAt_append_left`) and re-base under the shift (`natListRemoveManyAt_map` /
`rightPadOutputNodes_map` / `natListInsertAt_map`); the crossing needs no special case. -/
theorem stepWiring_rightPadWireSim (threshold delta : Nat) (stateS stateT : WireState)
    (position : Nat) (desc : WiringDesc)
    (windowFits : position + desc.inputCount ≤ stateS.openWires.length)
    (sim : RightPadWireSim threshold delta stateS stateT) :
    RightPadWireSim threshold delta (stepWiring stateS position desc) (stepWiring stateT position desc) := by
  obtain ⟨leftover, windowSum⟩ := Nat.le.dest windowFits
  have fitsWitness : stateS.openWires.length = position + desc.inputCount + leftover := windowSum.symm
  have openMapAfter : (stepWiring stateT position desc).openWires
      = (stepWiring stateS position desc).openWires.map (freshShiftAbove threshold delta)
        ++ padIdentifiers threshold delta := by
    show natListInsertAt (natListRemoveManyAt stateT.openWires position desc.inputCount) position
          ((List.range desc.outputCount).map (· + stateT.nextFresh))
        = (natListInsertAt (natListRemoveManyAt stateS.openWires position desc.inputCount) position
            ((List.range desc.outputCount).map (· + stateS.nextFresh))).map (freshShiftAbove threshold delta)
          ++ padIdentifiers threshold delta
    rw [sim.openMap,
      natListRemoveManyAt_append_left (stateS.openWires.map (freshShiftAbove threshold delta))
        (padIdentifiers threshold delta) position desc.inputCount (by rw [mapLength]; exact windowFits),
      ← natListRemoveManyAt_map (freshShiftAbove threshold delta) stateS.openWires position desc.inputCount,
      natListInsertAt_append_left
        ((natListRemoveManyAt stateS.openWires position desc.inputCount).map (freshShiftAbove threshold delta))
        (padIdentifiers threshold delta)
        ((List.range desc.outputCount).map (· + stateT.nextFresh)) position
        (by rw [mapLength,
              natListRemoveManyAt_length_fits stateS.openWires position desc.inputCount leftover fitsWitness]
            exact Nat.le_add_right position leftover),
      rightPadOutputNodes_map threshold delta stateS stateT desc.outputCount sim.nfShift sim.thresholdLe,
      ← natListInsertAt_map (freshShiftAbove threshold delta)
        (natListRemoveManyAt stateS.openWires position desc.inputCount) position
        ((List.range desc.outputCount).map (· + stateS.nextFresh))]
  exact
    { openMap := openMapAfter
      nfShift := by
        rw [stepWiring_nextFresh stateT position desc, stepWiring_nextFresh stateS position desc,
          sim.nfShift, Nat.add_right_comm stateS.nextFresh delta desc.outputCount]
      thresholdLe := by
        rw [stepWiring_nextFresh stateS position desc]
        exact Nat.le_trans sim.thresholdLe (Nat.le_add_right stateS.nextFresh desc.outputCount) }

/-- ★ **The right-pad wire simulation folds over any in-range Brauer word.**  Structural on the word,
threading the `BrauerWordInRange` window discipline and the additive length tracking. -/
theorem processBrauer_rightPadWireSim (threshold delta : Nat) :
    (atoms : List BrauerAtom) → (stateS stateT : WireState) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    stateS.openWires.length = boundaryLength →
    RightPadWireSim threshold delta stateS stateT →
    RightPadWireSim threshold delta (processBrauer stateS atoms) (processBrauer stateT atoms)
  | [], _, _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, boundaryLength, inRange, tracks, sim => by
      show RightPadWireSim threshold delta
        (processBrauer (stepWiring stateS atom.position atom.wiring) rest)
        (processBrauer (stepWiring stateT atom.position atom.wiring) rest)
      obtain ⟨leftover, fits, _, tailInRange⟩ := brauerWordInRange_tail inRange
      have lengthDecomp : stateS.openWires.length
          = atom.position + atom.wiring.inputCount + leftover := by rw [tracks]; exact fits
      have windowFits : atom.position + atom.wiring.inputCount ≤ stateS.openWires.length := by
        rw [lengthDecomp]
        exact Nat.le_add_right (atom.position + atom.wiring.inputCount) leftover
      exact processBrauer_rightPadWireSim threshold delta rest
        (stepWiring stateS atom.position atom.wiring) (stepWiring stateT atom.position atom.wiring)
        (atom.position + atom.wiring.outputCount + leftover) tailInRange
        (stepWiring_openWires_length_fits stateS atom.position leftover atom.wiring lengthDecomp)
        (stepWiring_rightPadWireSim threshold delta stateS stateT atom.position atom.wiring windowFits sim)

/-- ★ **The wider run's whole decoded trace is the `freshShiftAbove`-rename of the base run's trace.**
Structural on the word; the head arc events re-base node-wise (`wiringArcEvents_mapNodes` after the slice /
fresh-block correspondence), the tail steps the wire simulation. -/
theorem rightPadWireSim_wordJoinEvents (threshold delta : Nat) :
    (atoms : List BrauerAtom) → (stateS stateT : WireState) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    stateS.openWires.length = boundaryLength →
    RightPadWireSim threshold delta stateS stateT →
    brauerWordJoinEvents stateT atoms
      = (brauerWordJoinEvents stateS atoms).map
          (fun event => (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2))
  | [], _, _, _, _, _, _ => rfl
  | atom :: rest, stateS, stateT, boundaryLength, inRange, tracks, sim => by
      obtain ⟨leftover, fits, tagsInRange, tailInRange⟩ := brauerWordInRange_tail inRange
      have lengthDecomp : stateS.openWires.length
          = atom.position + atom.wiring.inputCount + leftover := by rw [tracks]; exact fits
      have windowFits : atom.position + atom.wiring.inputCount ≤ stateS.openWires.length := by
        rw [lengthDecomp]
        exact Nat.le_add_right (atom.position + atom.wiring.inputCount) leftover
      have inputNodesCorr :
          stepWiringInputNodes stateT atom.position atom.wiring
            = (stepWiringInputNodes stateS atom.position atom.wiring).map (freshShiftAbove threshold delta) := by
        show natListSliceAt stateT.openWires atom.position atom.wiring.inputCount
          = (natListSliceAt stateS.openWires atom.position atom.wiring.inputCount).map
              (freshShiftAbove threshold delta)
        rw [sim.openMap,
          natListSliceAt_append_left (stateS.openWires.map (freshShiftAbove threshold delta))
            (padIdentifiers threshold delta) atom.position atom.wiring.inputCount
            (by rw [mapLength]; exact windowFits),
          ← natListSliceAt_map (freshShiftAbove threshold delta) stateS.openWires atom.position
            atom.wiring.inputCount]
      have outputNodesCorr :
          stepWiringOutputNodes stateT atom.wiring
            = (stepWiringOutputNodes stateS atom.wiring).map (freshShiftAbove threshold delta) :=
        rightPadOutputNodes_map threshold delta stateS stateT atom.wiring.outputCount sim.nfShift
          sim.thresholdLe
      have sliceLenS : (stepWiringInputNodes stateS atom.position atom.wiring).length
          = atom.wiring.inputCount :=
        natListSliceAt_length_fits stateS.openWires atom.position atom.wiring.inputCount leftover
          lengthDecomp
      have outputLenS : (stepWiringOutputNodes stateS atom.wiring).length = atom.wiring.outputCount := by
        show ((List.range atom.wiring.outputCount).map (· + stateS.nextFresh)).length
          = atom.wiring.outputCount
        rw [mapLength, rangeLengthPad]
      have headCorr :
          wiringArcEvents (stepWiringInputNodes stateT atom.position atom.wiring)
              (stepWiringOutputNodes stateT atom.wiring) atom.wiring.inputCount atom.wiring.arcs
            = (wiringArcEvents (stepWiringInputNodes stateS atom.position atom.wiring)
                (stepWiringOutputNodes stateS atom.wiring) atom.wiring.inputCount atom.wiring.arcs).map
                (fun event =>
                  (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2)) := by
        rw [inputNodesCorr, outputNodesCorr]
        exact wiringArcEvents_mapNodes (freshShiftAbove threshold delta)
          (stepWiringInputNodes stateS atom.position atom.wiring)
          (stepWiringOutputNodes stateS atom.wiring) atom.wiring.inputCount atom.wiring.outputCount
          sliceLenS outputLenS atom.wiring.arcs tagsInRange
      show wiringArcEvents (stepWiringInputNodes stateT atom.position atom.wiring)
              (stepWiringOutputNodes stateT atom.wiring) atom.wiring.inputCount atom.wiring.arcs
            ++ brauerWordJoinEvents (stepWiring stateT atom.position atom.wiring) rest
          = (wiringArcEvents (stepWiringInputNodes stateS atom.position atom.wiring)
              (stepWiringOutputNodes stateS atom.wiring) atom.wiring.inputCount atom.wiring.arcs
            ++ brauerWordJoinEvents (stepWiring stateS atom.position atom.wiring) rest).map
              (fun event =>
                (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2))
      rw [padMapAppend
          (fun event : Nat × Nat =>
            (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2)),
        headCorr,
        rightPadWireSim_wordJoinEvents threshold delta rest
          (stepWiring stateS atom.position atom.wiring) (stepWiring stateT atom.position atom.wiring)
          (atom.position + atom.wiring.outputCount + leftover) tailInRange
          (stepWiring_openWires_length_fits stateS atom.position leftover atom.wiring lengthDecomp)
          (stepWiring_rightPadWireSim threshold delta stateS stateT atom.position atom.wiring
            windowFits sim)]

/-! ## The whole-word right-pad simulation and the padded extract congruence -/

/-- ★ **The two Brauer runs (base boundary vs wider boundary) are right-pad-simulated.**  The wire
fields come from folding the light wire simulation from the padded-range seed
(`processBrauer_rightPadWireSim`); the link fields are read off the whole trace at the empty base —
`componentComm` by `componentView_applyJoinEvents_ofRename`, `loopsEq` by `countJoinEventLoops_ofRename`,
the pad-zone inertness by `applyJoinEvents_padInert` over the all-shift-image trace. -/
theorem processBrauer_rightPadSim (threshold delta : Nat) (atoms : List BrauerAtom)
    (inRange : BrauerWordInRange threshold atoms) :
    MatchingRightPadSim threshold delta (padIdentifiers threshold delta)
      (processBrauer (brauerSeed threshold) atoms)
      (processBrauer (brauerSeed (threshold + delta)) atoms) := by
  have seedWireSim : RightPadWireSim threshold delta (brauerSeed threshold) (brauerSeed (threshold + delta)) :=
    { openMap := paddedRangeSplit threshold delta
      nfShift := rfl
      thresholdLe := Nat.le_refl threshold }
  have wireSim : RightPadWireSim threshold delta (processBrauer (brauerSeed threshold) atoms)
      (processBrauer (brauerSeed (threshold + delta)) atoms) :=
    processBrauer_rightPadWireSim threshold delta atoms (brauerSeed threshold)
      (brauerSeed (threshold + delta)) threshold inRange (rangeLengthPad threshold) seedWireSim
  have traceCorr : brauerWordJoinEvents (brauerSeed (threshold + delta)) atoms
      = (brauerWordJoinEvents (brauerSeed threshold) atoms).map
          (fun event => (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2)) :=
    rightPadWireSim_wordJoinEvents threshold delta atoms (brauerSeed threshold)
      (brauerSeed (threshold + delta)) threshold inRange (rangeLengthPad threshold) seedWireSim
  have linksS : (processBrauer (brauerSeed threshold) atoms).links
      = applyJoinEvents (brauerWordJoinEvents (brauerSeed threshold) atoms) [] :=
    processBrauer_links_eq_applyJoinEvents atoms (brauerSeed threshold)
  have linksT : (processBrauer (brauerSeed (threshold + delta)) atoms).links
      = applyJoinEvents ((brauerWordJoinEvents (brauerSeed threshold) atoms).map
          (fun event =>
            (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2))) [] := by
    rw [processBrauer_links_eq_applyJoinEvents atoms (brauerSeed (threshold + delta))]
    show applyJoinEvents (brauerWordJoinEvents (brauerSeed (threshold + delta)) atoms) []
        = applyJoinEvents ((brauerWordJoinEvents (brauerSeed threshold) atoms).map
            (fun event =>
              (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2))) []
    rw [traceCorr]
  have padInert := applyJoinEvents_padInert threshold delta
    ((brauerWordJoinEvents (brauerSeed threshold) atoms).map
      (fun event => (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2)))
    [] True.intro
    (renamedTraceAvoidsPadZone threshold delta (brauerWordJoinEvents (brauerSeed threshold) atoms))
    (fun _ _ _ => rfl) (fun _ avoids => avoids)
  exact
    { openMap := wireSim.openMap
      nfShift := wireSim.nfShift
      thresholdLe := wireSim.thresholdLe
      componentComm := fun firstValue secondValue => by
        show isSameComponent (processBrauer (brauerSeed (threshold + delta)) atoms).links
            (freshShiftAbove threshold delta firstValue) (freshShiftAbove threshold delta secondValue)
          = isSameComponent (processBrauer (brauerSeed threshold) atoms).links firstValue secondValue
        rw [linksS, linksT]
        exact componentView_applyJoinEvents_ofRename (freshShiftAbove threshold delta)
          (freshShiftAbove_injective threshold delta) (brauerWordJoinEvents (brauerSeed threshold) atoms)
          firstValue secondValue
      loopsEq := by
        rw [processBrauer_loops_eq_addJoinEventLoops atoms (brauerSeed (threshold + delta)),
          processBrauer_loops_eq_addJoinEventLoops atoms (brauerSeed threshold)]
        show (0 : Nat) + countJoinEventLoops (brauerWordJoinEvents (brauerSeed (threshold + delta)) atoms) []
              + brauerWordInternalLoops atoms
            = 0 + countJoinEventLoops (brauerWordJoinEvents (brauerSeed threshold) atoms) []
              + brauerWordInternalLoops atoms
        rw [traceCorr, countJoinEventLoops_ofRename (freshShiftAbove threshold delta)
          (freshShiftAbove_injective threshold delta) (brauerWordJoinEvents (brauerSeed threshold) atoms)]
      forestS := by
        rw [linksS]
        exact isUnionFindForest_applyJoinEvents (brauerWordJoinEvents (brauerSeed threshold) atoms) []
          True.intro
      forestT := by
        rw [linksT]
        exact isUnionFindForest_applyJoinEvents
          ((brauerWordJoinEvents (brauerSeed threshold) atoms).map
            (fun event =>
              (freshShiftAbove threshold delta event.1, freshShiftAbove threshold delta event.2))) []
          True.intro
      padRootsFixed := by rw [linksT]; exact padInert.1
      rootAvoidsPad := by rw [linksT]; exact padInert.2 }

/-- ★ **KEYSTONE15 — the RIGHT pad extract congruence at `processBrauer`.**  A Brauer extract equality
at boundary width `threshold` transports to boundary width `threshold + delta`: the two words fired from
the wider seed extract equally there.  This is the boundary-CHANGING (widening) direction the r14
functoriality did not supply — the relation fired at offset `0` in a wider boundary.  Composes the
whole-word right-pad simulation (`processBrauer_rightPadSim`) with the shipped engine-agnostic payoff
`extractDiagram_ofRightPadSimPair`. -/
theorem brauerSeedExtract_ofRightPad (threshold delta : Nat) (lhs rhs : List BrauerAtom)
    (inRangeLhs : BrauerWordInRange threshold lhs) (inRangeRhs : BrauerWordInRange threshold rhs)
    (baseEq : extractDiagram threshold (processBrauer (brauerSeed threshold) lhs)
            = extractDiagram threshold (processBrauer (brauerSeed threshold) rhs)) :
    extractDiagram (threshold + delta) (processBrauer (brauerSeed (threshold + delta)) lhs)
      = extractDiagram (threshold + delta) (processBrauer (brauerSeed (threshold + delta)) rhs) :=
  extractDiagram_ofRightPadSimPair threshold delta
    (processBrauer (brauerSeed threshold) lhs) (processBrauer (brauerSeed (threshold + delta)) lhs)
    (processBrauer (brauerSeed threshold) rhs) (processBrauer (brauerSeed (threshold + delta)) rhs)
    (processBrauer_rightPadSim threshold delta lhs inRangeLhs)
    (processBrauer_rightPadSim threshold delta rhs inRangeRhs)
    baseEq

/-! ## The LEFT pad — position-shifted word, prefix-skip surgery -/

/-- A block splice past a constant prefix inserts inside the suffix (local copy — the shipped generic-engine
version is private).  Structural on the prefix. -/
private theorem natListInsertAt_appendPrefixPad :
    (prefixWires wires : List Nat) → (position : Nat) → (block : List Nat) →
    natListInsertAt (prefixWires ++ wires) (prefixWires.length + position) block
      = prefixWires ++ natListInsertAt wires position block
  | [], wires, position, block => by
      show natListInsertAt wires (0 + position) block = natListInsertAt wires position block
      rw [Nat.zero_add]
  | headWire :: restPrefix, wires, position, block => by
      show natListInsertAt (headWire :: (restPrefix ++ wires)) (restPrefix.length + 1 + position) block
        = headWire :: (restPrefix ++ natListInsertAt wires position block)
      rw [Nat.add_right_comm restPrefix.length 1 position]
      show headWire :: natListInsertAt (restPrefix ++ wires) (restPrefix.length + position) block
        = headWire :: (restPrefix ++ natListInsertAt wires position block)
      exact congrArg (headWire :: ·) (natListInsertAt_appendPrefixPad restPrefix wires position block)

/-- ★ **Shift every atom's firing position by `delta`** — the left-pad word transport: the padded run fires the
same generators at the prefix-offset windows `delta + position`. -/
def shiftBrauerWord (delta : Nat) : List BrauerAtom → List BrauerAtom
  | [] => []
  | atom :: rest => { position := delta + atom.position, wiring := atom.wiring } :: shiftBrauerWord delta rest

/-- Shifting positions leaves the per-generator internal-loop total unchanged (the wirings are untouched). -/
theorem shiftBrauerWord_internalLoops (delta : Nat) :
    (atoms : List BrauerAtom) →
    brauerWordInternalLoops (shiftBrauerWord delta atoms) = brauerWordInternalLoops atoms
  | [] => rfl
  | atom :: rest => congrArg (atom.wiring.internalLoops + ·) (shiftBrauerWord_internalLoops delta rest)

/-- ★ **The firing discipline transports under the position shift.**  A word in range at boundary `boundaryLength`
is in range at `delta + boundaryLength` once every position is shifted by `delta`.  Structural on the word. -/
theorem brauerWordInRange_shift (delta : Nat) :
    (atoms : List BrauerAtom) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    BrauerWordInRange (delta + boundaryLength) (shiftBrauerWord delta atoms)
  | [], _, _ => BrauerWordInRange.nil _
  | atom :: rest, boundaryLength, inRange => by
      obtain ⟨rightLen, fits, tagsInRange, tailInRange⟩ := brauerWordInRange_tail inRange
      refine BrauerWordInRange.cons { position := delta + atom.position, wiring := atom.wiring } rightLen ?_
        tagsInRange ?_
      · show delta + boundaryLength = delta + atom.position + atom.wiring.inputCount + rightLen
        rw [fits, Nat.add_assoc delta atom.position atom.wiring.inputCount,
          Nat.add_assoc delta (atom.position + atom.wiring.inputCount) rightLen]
      · show BrauerWordInRange (delta + atom.position + atom.wiring.outputCount + rightLen)
          (shiftBrauerWord delta rest)
        have ext := brauerWordInRange_shift delta rest
          (atom.position + atom.wiring.outputCount + rightLen) tailInRange
        rw [Nat.add_assoc delta atom.position atom.wiring.outputCount,
          Nat.add_assoc delta (atom.position + atom.wiring.outputCount) rightLen]
        exact ext

/-- The firing discipline transports under widening the boundary on the RIGHT (each `rightLen` grows).  Structural. -/
theorem brauerWordInRange_rightExtend (extra : Nat) :
    (atoms : List BrauerAtom) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    BrauerWordInRange (boundaryLength + extra) atoms
  | [], _, _ => BrauerWordInRange.nil _
  | atom :: rest, boundaryLength, inRange => by
      obtain ⟨rightLen, fits, tagsInRange, tailInRange⟩ := brauerWordInRange_tail inRange
      refine BrauerWordInRange.cons atom (rightLen + extra) ?_ tagsInRange ?_
      · rw [fits, Nat.add_assoc (atom.position + atom.wiring.inputCount) rightLen extra]
      · have ext := brauerWordInRange_rightExtend extra rest
          (atom.position + atom.wiring.outputCount + rightLen) tailInRange
        rw [← Nat.add_assoc (atom.position + atom.wiring.outputCount) rightLen extra]
        exact ext

/-- ★ **The light left-pad WIRE simulation** — the padded run's open wires are a constant pad prefix `[0, delta)`
followed by the uniform-shift (`freshShiftAbove 0 delta`) image of the base wires; the counter runs `delta`
ahead.  (The link-level fields of `MatchingLeftPadSim` are read off the whole trace separately.) -/
structure LeftPadWireSim (delta : Nat) (stateS stateT : WireState) : Prop where
  /-- The padded wires are the constant pad prefix plus the shift-image of the base wires. -/
  openMap : stateT.openWires
    = padIdentifiers 0 delta ++ stateS.openWires.map (freshShiftAbove 0 delta)
  /-- The padded counter runs exactly `delta` ahead. -/
  nfShift : stateT.nextFresh = stateS.nextFresh + delta

/-- ★ **ONE `stepWiring` step preserves the left-pad wire simulation.**  The base steps at `position`, the padded
run at the prefix-offset window `delta + position`; the removal / splice happen past the untouched prefix
(`natListRemoveManyAt_appendPrefix` / `natListInsertAt_appendPrefixPad`) and re-base under the uniform shift. -/
theorem stepWiring_leftPadWireSim (delta : Nat) (stateS stateT : WireState)
    (position : Nat) (desc : WiringDesc)
    (sim : LeftPadWireSim delta stateS stateT) :
    LeftPadWireSim delta (stepWiring stateS position desc)
      (stepWiring stateT (delta + position) desc) := by
  have prefixOffset : delta + position = (padIdentifiers 0 delta).length + position := by
    rw [padIdentifiers_length]
  have openMapAfter : (stepWiring stateT (delta + position) desc).openWires
      = padIdentifiers 0 delta
        ++ (stepWiring stateS position desc).openWires.map (freshShiftAbove 0 delta) := by
    show natListInsertAt (natListRemoveManyAt stateT.openWires (delta + position) desc.inputCount)
          (delta + position) ((List.range desc.outputCount).map (· + stateT.nextFresh))
        = padIdentifiers 0 delta
          ++ (natListInsertAt (natListRemoveManyAt stateS.openWires position desc.inputCount) position
              ((List.range desc.outputCount).map (· + stateS.nextFresh))).map (freshShiftAbove 0 delta)
    rw [sim.openMap, prefixOffset,
      natListRemoveManyAt_appendPrefix (padIdentifiers 0 delta)
        (stateS.openWires.map (freshShiftAbove 0 delta)) position desc.inputCount,
      ← natListRemoveManyAt_map (freshShiftAbove 0 delta) stateS.openWires position desc.inputCount,
      natListInsertAt_appendPrefixPad (padIdentifiers 0 delta)
        ((natListRemoveManyAt stateS.openWires position desc.inputCount).map (freshShiftAbove 0 delta))
        position ((List.range desc.outputCount).map (· + stateT.nextFresh)),
      rightPadOutputNodes_map 0 delta stateS stateT desc.outputCount sim.nfShift (Nat.zero_le stateS.nextFresh),
      ← natListInsertAt_map (freshShiftAbove 0 delta)
        (natListRemoveManyAt stateS.openWires position desc.inputCount) position
        ((List.range desc.outputCount).map (· + stateS.nextFresh))]
  exact
    { openMap := openMapAfter
      nfShift := by
        rw [stepWiring_nextFresh stateT (delta + position) desc, stepWiring_nextFresh stateS position desc,
          sim.nfShift, Nat.add_right_comm stateS.nextFresh delta desc.outputCount] }

/-- ★ **The left-pad wire simulation folds over any in-range Brauer word** (the padded run over the shifted word). -/
theorem processBrauer_leftPadWireSim (delta : Nat) :
    (atoms : List BrauerAtom) → (stateS stateT : WireState) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    stateS.openWires.length = boundaryLength →
    LeftPadWireSim delta stateS stateT →
    LeftPadWireSim delta (processBrauer stateS atoms) (processBrauer stateT (shiftBrauerWord delta atoms))
  | [], _, _, _, _, _, sim => sim
  | atom :: rest, stateS, stateT, boundaryLength, inRange, tracks, sim => by
      show LeftPadWireSim delta (processBrauer (stepWiring stateS atom.position atom.wiring) rest)
        (processBrauer (stepWiring stateT (delta + atom.position) atom.wiring) (shiftBrauerWord delta rest))
      obtain ⟨leftover, fits, _, tailInRange⟩ := brauerWordInRange_tail inRange
      have lengthDecomp : stateS.openWires.length
          = atom.position + atom.wiring.inputCount + leftover := by rw [tracks]; exact fits
      exact processBrauer_leftPadWireSim delta rest (stepWiring stateS atom.position atom.wiring)
        (stepWiring stateT (delta + atom.position) atom.wiring)
        (atom.position + atom.wiring.outputCount + leftover) tailInRange
        (stepWiring_openWires_length_fits stateS atom.position leftover atom.wiring lengthDecomp)
        (stepWiring_leftPadWireSim delta stateS stateT atom.position atom.wiring sim)

/-- ★ **The padded run's whole decoded trace is the uniform-shift rename of the base run's trace.**  Structural;
the head arc events re-base node-wise after the slice-past-prefix / fresh-block correspondence. -/
theorem leftPadWireSim_wordJoinEvents (delta : Nat) :
    (atoms : List BrauerAtom) → (stateS stateT : WireState) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    stateS.openWires.length = boundaryLength →
    LeftPadWireSim delta stateS stateT →
    brauerWordJoinEvents stateT (shiftBrauerWord delta atoms)
      = (brauerWordJoinEvents stateS atoms).map
          (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2))
  | [], _, _, _, _, _, _ => rfl
  | atom :: rest, stateS, stateT, boundaryLength, inRange, tracks, sim => by
      obtain ⟨leftover, fits, tagsInRange, tailInRange⟩ := brauerWordInRange_tail inRange
      have lengthDecomp : stateS.openWires.length
          = atom.position + atom.wiring.inputCount + leftover := by rw [tracks]; exact fits
      have inputNodesCorr :
          stepWiringInputNodes stateT (delta + atom.position) atom.wiring
            = (stepWiringInputNodes stateS atom.position atom.wiring).map (freshShiftAbove 0 delta) := by
        show natListSliceAt stateT.openWires (delta + atom.position) atom.wiring.inputCount
          = (natListSliceAt stateS.openWires atom.position atom.wiring.inputCount).map (freshShiftAbove 0 delta)
        rw [sim.openMap,
          show delta + atom.position = (padIdentifiers 0 delta).length + atom.position from by
            rw [padIdentifiers_length],
          natListSliceAt_appendSkipPrefix (stateS.openWires.map (freshShiftAbove 0 delta))
            atom.position atom.wiring.inputCount (padIdentifiers 0 delta),
          ← natListSliceAt_map (freshShiftAbove 0 delta) stateS.openWires atom.position atom.wiring.inputCount]
      have outputNodesCorr :
          stepWiringOutputNodes stateT atom.wiring
            = (stepWiringOutputNodes stateS atom.wiring).map (freshShiftAbove 0 delta) :=
        rightPadOutputNodes_map 0 delta stateS stateT atom.wiring.outputCount sim.nfShift
          (Nat.zero_le stateS.nextFresh)
      have sliceLenS : (stepWiringInputNodes stateS atom.position atom.wiring).length
          = atom.wiring.inputCount :=
        natListSliceAt_length_fits stateS.openWires atom.position atom.wiring.inputCount leftover
          lengthDecomp
      have outputLenS : (stepWiringOutputNodes stateS atom.wiring).length = atom.wiring.outputCount := by
        show ((List.range atom.wiring.outputCount).map (· + stateS.nextFresh)).length
          = atom.wiring.outputCount
        rw [mapLength, rangeLengthPad]
      have headCorr :
          wiringArcEvents (stepWiringInputNodes stateT (delta + atom.position) atom.wiring)
              (stepWiringOutputNodes stateT atom.wiring) atom.wiring.inputCount atom.wiring.arcs
            = (wiringArcEvents (stepWiringInputNodes stateS atom.position atom.wiring)
                (stepWiringOutputNodes stateS atom.wiring) atom.wiring.inputCount atom.wiring.arcs).map
                (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2)) := by
        rw [inputNodesCorr, outputNodesCorr]
        exact wiringArcEvents_mapNodes (freshShiftAbove 0 delta)
          (stepWiringInputNodes stateS atom.position atom.wiring)
          (stepWiringOutputNodes stateS atom.wiring) atom.wiring.inputCount atom.wiring.outputCount
          sliceLenS outputLenS atom.wiring.arcs tagsInRange
      show wiringArcEvents (stepWiringInputNodes stateT (delta + atom.position) atom.wiring)
              (stepWiringOutputNodes stateT atom.wiring) atom.wiring.inputCount atom.wiring.arcs
            ++ brauerWordJoinEvents (stepWiring stateT (delta + atom.position) atom.wiring)
                (shiftBrauerWord delta rest)
          = (wiringArcEvents (stepWiringInputNodes stateS atom.position atom.wiring)
              (stepWiringOutputNodes stateS atom.wiring) atom.wiring.inputCount atom.wiring.arcs
            ++ brauerWordJoinEvents (stepWiring stateS atom.position atom.wiring) rest).map
              (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2))
      rw [padMapAppend
          (fun event : Nat × Nat => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2)),
        headCorr,
        leftPadWireSim_wordJoinEvents delta rest (stepWiring stateS atom.position atom.wiring)
          (stepWiring stateT (delta + atom.position) atom.wiring)
          (atom.position + atom.wiring.outputCount + leftover) tailInRange
          (stepWiring_openWires_length_fits stateS atom.position leftover atom.wiring lengthDecomp)
          (stepWiring_leftPadWireSim delta stateS stateT atom.position atom.wiring sim)]

/-- ★ **The two Brauer runs (base boundary vs LEFT-widened boundary over the shifted word) are
left-pad-simulated.**  Wire fields from the folded light wire simulation (seeded by `leftPaddedRangeSplit`); link
fields off the whole trace at the empty base, exactly as the right pad but at threshold `0`. -/
theorem processBrauer_leftPadSim (delta boundaryCount : Nat) (atoms : List BrauerAtom)
    (inRange : BrauerWordInRange boundaryCount atoms) :
    MatchingLeftPadSim delta (padIdentifiers 0 delta)
      (processBrauer (brauerSeed boundaryCount) atoms)
      (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)) := by
  have seedWireSim : LeftPadWireSim delta (brauerSeed boundaryCount) (brauerSeed (delta + boundaryCount)) :=
    { openMap := leftPaddedRangeSplit delta boundaryCount
      nfShift := Nat.add_comm delta boundaryCount }
  have wireSim : LeftPadWireSim delta (processBrauer (brauerSeed boundaryCount) atoms)
      (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)) :=
    processBrauer_leftPadWireSim delta atoms (brauerSeed boundaryCount)
      (brauerSeed (delta + boundaryCount)) boundaryCount inRange (rangeLengthPad boundaryCount) seedWireSim
  have traceCorr : brauerWordJoinEvents (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)
      = (brauerWordJoinEvents (brauerSeed boundaryCount) atoms).map
          (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2)) :=
    leftPadWireSim_wordJoinEvents delta atoms (brauerSeed boundaryCount)
      (brauerSeed (delta + boundaryCount)) boundaryCount inRange (rangeLengthPad boundaryCount) seedWireSim
  have linksS : (processBrauer (brauerSeed boundaryCount) atoms).links
      = applyJoinEvents (brauerWordJoinEvents (brauerSeed boundaryCount) atoms) [] :=
    processBrauer_links_eq_applyJoinEvents atoms (brauerSeed boundaryCount)
  have linksT : (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)).links
      = applyJoinEvents ((brauerWordJoinEvents (brauerSeed boundaryCount) atoms).map
          (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2))) [] := by
    rw [processBrauer_links_eq_applyJoinEvents (shiftBrauerWord delta atoms) (brauerSeed (delta + boundaryCount))]
    show applyJoinEvents (brauerWordJoinEvents (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)) []
        = applyJoinEvents ((brauerWordJoinEvents (brauerSeed boundaryCount) atoms).map
            (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2))) []
    rw [traceCorr]
  have padInert := applyJoinEvents_padInert 0 delta
    ((brauerWordJoinEvents (brauerSeed boundaryCount) atoms).map
      (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2)))
    [] True.intro
    (renamedTraceAvoidsPadZone 0 delta (brauerWordJoinEvents (brauerSeed boundaryCount) atoms))
    (fun _ _ _ => rfl) (fun _ avoids => avoids)
  exact
    { openMap := wireSim.openMap
      prefixCount := padIdentifiers_length 0 delta
      nfShift := wireSim.nfShift
      componentComm := fun firstValue secondValue => by
        show isSameComponent (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)).links
            (freshShiftAbove 0 delta firstValue) (freshShiftAbove 0 delta secondValue)
          = isSameComponent (processBrauer (brauerSeed boundaryCount) atoms).links firstValue secondValue
        rw [linksS, linksT]
        exact componentView_applyJoinEvents_ofRename (freshShiftAbove 0 delta)
          (freshShiftAbove_injective 0 delta) (brauerWordJoinEvents (brauerSeed boundaryCount) atoms)
          firstValue secondValue
      loopsEq := by
        rw [processBrauer_loops_eq_addJoinEventLoops (shiftBrauerWord delta atoms)
            (brauerSeed (delta + boundaryCount)),
          processBrauer_loops_eq_addJoinEventLoops atoms (brauerSeed boundaryCount)]
        show (0 : Nat)
              + countJoinEventLoops
                  (brauerWordJoinEvents (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta atoms)) []
              + brauerWordInternalLoops (shiftBrauerWord delta atoms)
            = 0 + countJoinEventLoops (brauerWordJoinEvents (brauerSeed boundaryCount) atoms) []
              + brauerWordInternalLoops atoms
        rw [traceCorr, countJoinEventLoops_ofRename (freshShiftAbove 0 delta)
            (freshShiftAbove_injective 0 delta) (brauerWordJoinEvents (brauerSeed boundaryCount) atoms),
          shiftBrauerWord_internalLoops delta atoms]
      forestS := by
        rw [linksS]
        exact isUnionFindForest_applyJoinEvents (brauerWordJoinEvents (brauerSeed boundaryCount) atoms) []
          True.intro
      forestT := by
        rw [linksT]
        exact isUnionFindForest_applyJoinEvents
          ((brauerWordJoinEvents (brauerSeed boundaryCount) atoms).map
            (fun event => (freshShiftAbove 0 delta event.1, freshShiftAbove 0 delta event.2))) [] True.intro
      padRootsFixed := by
        intro node nodeLtDelta
        rw [linksT]
        exact padInert.1 node (Nat.zero_le node) (by rw [Nat.zero_add]; exact nodeLtDelta)
      rootAvoidsPad := by
        intro node deltaLeNode
        rw [linksT]
        cases padInert.2 node (Or.inr (by rw [Nat.zero_add]; exact deltaLeNode)) with
        | inl belowZero => exact absurd belowZero (Nat.not_lt_zero _)
        | inr atOrAbove => rw [Nat.zero_add] at atOrAbove; exact atOrAbove }

/-- ★ **KEYSTONE15 — the LEFT pad extract congruence at `processBrauer`.**  A Brauer extract equality at boundary
width `boundaryCount` transports to boundary width `delta + boundaryCount` when the words fire at the offset window
`delta + position` (the relation fired at offset `delta` in a wider boundary). -/
theorem brauerSeedExtract_ofLeftPad (delta boundaryCount : Nat) (lhs rhs : List BrauerAtom)
    (inRangeLhs : BrauerWordInRange boundaryCount lhs) (inRangeRhs : BrauerWordInRange boundaryCount rhs)
    (baseEq : extractDiagram boundaryCount (processBrauer (brauerSeed boundaryCount) lhs)
            = extractDiagram boundaryCount (processBrauer (brauerSeed boundaryCount) rhs)) :
    extractDiagram (delta + boundaryCount)
        (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta lhs))
      = extractDiagram (delta + boundaryCount)
        (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta rhs)) :=
  extractDiagram_ofLeftPadSimPair delta boundaryCount
    (processBrauer (brauerSeed boundaryCount) lhs)
    (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta lhs))
    (processBrauer (brauerSeed boundaryCount) rhs)
    (processBrauer (brauerSeed (delta + boundaryCount)) (shiftBrauerWord delta rhs))
    (processBrauer_leftPadSim delta boundaryCount lhs inRangeLhs)
    (processBrauer_leftPadSim delta boundaryCount rhs inRangeRhs)
    baseEq

/-! ## The two-sided pad composition -/

/-- ★ **KEYSTONE15 — the TWO-SIDED horizontal pad congruence.**  A Brauer extract equality at boundary width
`boundaryCount` transports to any width `leftPad + (boundaryCount + rightPad)` with the words fired at offset
`leftPad`: right-pad first (`boundaryCount -> boundaryCount + rightPad`), then left-pad (shift by `leftPad`,
prefix `leftPad`).  This is exactly the `seedExtractEq` shape the r14 whisker bridge consumes for a relation in
arbitrary horizontal context. -/
theorem brauerSeedExtract_ofTwoSidedPad (leftPad boundaryCount rightPad : Nat) (lhs rhs : List BrauerAtom)
    (inRangeLhs : BrauerWordInRange boundaryCount lhs) (inRangeRhs : BrauerWordInRange boundaryCount rhs)
    (baseEq : extractDiagram boundaryCount (processBrauer (brauerSeed boundaryCount) lhs)
            = extractDiagram boundaryCount (processBrauer (brauerSeed boundaryCount) rhs)) :
    extractDiagram (leftPad + (boundaryCount + rightPad))
        (processBrauer (brauerSeed (leftPad + (boundaryCount + rightPad))) (shiftBrauerWord leftPad lhs))
      = extractDiagram (leftPad + (boundaryCount + rightPad))
        (processBrauer (brauerSeed (leftPad + (boundaryCount + rightPad))) (shiftBrauerWord leftPad rhs)) :=
  brauerSeedExtract_ofLeftPad leftPad (boundaryCount + rightPad) lhs rhs
    (brauerWordInRange_rightExtend rightPad lhs boundaryCount inRangeLhs)
    (brauerWordInRange_rightExtend rightPad rhs boundaryCount inRangeRhs)
    (brauerSeedExtract_ofRightPad boundaryCount rightPad lhs rhs inRangeLhs inRangeRhs baseEq)

/-! ## The FLIP wiring — the 5 relations close in ARBITRARY horizontal context

The two-sided pad congruence supplies the `seedExtractEq` the r14 whisker bridge
(`brauerConv_whisker_ofCanonicalExtractEq`) consumes, at BOUNDARY-CHANGING offsets.  This closes the residual the
r14 markers named: for each relation and ANY prefix / offset / right-pad, the relation whiskered in that context is
`BrauerConv`-convertible (hence diagram-sound by `brauerConv_sound`). -/

/-- ★ **KEYSTONE15 — a relation whiskered in ARBITRARY horizontal context is convertible.**  Given a prefix leaving
post-prefix width `leftPad + (relBoundary + rightPad)`, a relation diagram-sound at its own boundary `relBoundary`
(in range, zero internal loops), fired at offset `leftPad` in that wider boundary, is `BrauerConv`-convertible to its
rhs there — the two-sided pad congruence feeds the `seedExtractEq` the r14 whisker bridge consumes.  This is the
FULL-generality `relationAgrees` supplier the flag named: boundary-PRESERVING (r14) generalized to
boundary-CHANGING. -/
theorem brauerConv_relation_inContext (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (prefixInRange : BrauerWordInRange bottomCount prefixAtoms)
    (leftPad relBoundary rightPad : Nat) (relLhs relRhs : List BrauerAtom)
    (widthEq : (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
                = leftPad + (relBoundary + rightPad))
    (inRangeLhs : BrauerWordInRange relBoundary relLhs) (inRangeRhs : BrauerWordInRange relBoundary relRhs)
    (zeroLhs : brauerWordInternalLoops relLhs = 0) (zeroRhs : brauerWordInternalLoops relRhs = 0)
    (relSound : extractDiagram relBoundary (processBrauer (brauerSeed relBoundary) relLhs)
              = extractDiagram relBoundary (processBrauer (brauerSeed relBoundary) relRhs)) :
    BrauerConv bottomCount (prefixAtoms ++ shiftBrauerWord leftPad relLhs)
      (prefixAtoms ++ shiftBrauerWord leftPad relRhs) := by
  have inLeft : BrauerWordInRange (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
      (shiftBrauerWord leftPad relLhs) := by
    rw [widthEq]
    exact brauerWordInRange_shift leftPad relLhs (relBoundary + rightPad)
      (brauerWordInRange_rightExtend rightPad relLhs relBoundary inRangeLhs)
  have inRight : BrauerWordInRange (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
      (shiftBrauerWord leftPad relRhs) := by
    rw [widthEq]
    exact brauerWordInRange_shift leftPad relRhs (relBoundary + rightPad)
      (brauerWordInRange_rightExtend rightPad relRhs relBoundary inRangeRhs)
  have seedEq : extractDiagram (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
        (processBrauer (canonicalMatchingSeed
          (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length)
          (shiftBrauerWord leftPad relLhs))
      = extractDiagram (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
        (processBrauer (canonicalMatchingSeed
          (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length)
          (shiftBrauerWord leftPad relRhs)) := by
    rw [widthEq]
    exact brauerSeedExtract_ofTwoSidedPad leftPad relBoundary rightPad relLhs relRhs
      inRangeLhs inRangeRhs relSound
  exact brauerConv_whisker_ofCanonicalExtractEq bottomCount bottomPos prefixAtoms
    (shiftBrauerWord leftPad relLhs) (shiftBrauerWord leftPad relRhs) prefixInRange inLeft inRight
    (by rw [shiftBrauerWord_internalLoops]; exact zeroLhs)
    (by rw [shiftBrauerWord_internalLoops]; exact zeroRhs) seedEq

/-! ### The 5 relations in a boundary-CHANGING context (non-vacuity for the flip)

Each relation, fired at a NON-zero offset inside a boundary strictly wider than its own (empty prefix, `bottomCount`
> the relation's boundary), is `BrauerConv`-convertible via `brauerConv_relation_inContext`.  Unlike the r14
witnesses (which preserved the relation's boundary width), these are genuinely boundary-CHANGING — the pad congruence
is doing the work. -/

/-- R2 (crossing involutivity, boundary 2) fired at offset `1` in a width-4 boundary (`1 + (2 + 1)`). -/
theorem brauerConv_crossingInvolution_inWiderContext :
    BrauerConv 4 ([] ++ shiftBrauerWord 1 crossingInvolutionRelation.lhs)
      ([] ++ shiftBrauerWord 1 crossingInvolutionRelation.rhs) :=
  brauerConv_relation_inContext 4 (by decide) [] (BrauerWordInRange.nil 4) 1 2 1
    crossingInvolutionRelation.lhs crossingInvolutionRelation.rhs (by decide)
    (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))
    (BrauerWordInRange.nil 2) rfl rfl crossingInvolution_diagram_sound

/-- R3 (Yang–Baxter, boundary 3) fired at offset `1` in a width-5 boundary (`1 + (3 + 1)`). -/
theorem brauerConv_yangBaxter_inWiderContext :
    BrauerConv 5 ([] ++ shiftBrauerWord 1 yangBaxterRelation.lhs)
      ([] ++ shiftBrauerWord 1 yangBaxterRelation.rhs) :=
  brauerConv_relation_inContext 5 (by decide) [] (BrauerWordInRange.nil 5) 1 3 1
    yangBaxterRelation.lhs yangBaxterRelation.rhs (by decide)
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3))))
    (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 3))))
    rfl rfl yangBaxter_diagram_sound

/-- R1 (cap-slide, boundary 3) fired at offset `1` in a width-5 boundary. -/
theorem brauerConv_capSlide_inWiderContext :
    BrauerConv 5 ([] ++ shiftBrauerWord 1 capSlideRelation.lhs)
      ([] ++ shiftBrauerWord 1 capSlideRelation.rhs) :=
  brauerConv_relation_inContext 5 (by decide) [] (BrauerWordInRange.nil 5) 1 3 1
    capSlideRelation.lhs capSlideRelation.rhs (by decide)
    (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (capAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 1)))
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (capAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 1)))
    rfl rfl capSlide_diagram_sound

/-- S1 (snake, boundary 1) fired at offset `1` in a width-3 boundary (`1 + (1 + 1)`). -/
theorem brauerConv_snake_inWiderContext :
    BrauerConv 3 ([] ++ shiftBrauerWord 1 snakeRelation.lhs)
      ([] ++ shiftBrauerWord 1 snakeRelation.rhs) :=
  brauerConv_relation_inContext 3 (by decide) [] (BrauerWordInRange.nil 3) 1 1 1
    snakeRelation.lhs snakeRelation.rhs (by decide)
    (BrauerWordInRange.cons (cupAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (capAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 1)))
    (BrauerWordInRange.nil 1) rfl rfl snake_diagram_sound

/-- S2 (mirror snake, boundary 1) fired at offset `1` in a width-3 boundary. -/
theorem brauerConv_snakeMirror_inWiderContext :
    BrauerConv 3 ([] ++ shiftBrauerWord 1 snakeMirrorRelation.lhs)
      ([] ++ shiftBrauerWord 1 snakeMirrorRelation.rhs) :=
  brauerConv_relation_inContext 3 (by decide) [] (BrauerWordInRange.nil 3) 1 1 1
    snakeMirrorRelation.lhs snakeMirrorRelation.rhs (by decide)
    (BrauerWordInRange.cons (cupAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (capAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 1)))
    (BrauerWordInRange.nil 1) rfl rfl snakeMirror_diagram_sound

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the RIGHT horizontal pad congruence at `processBrauer` is SHIPPED.**  The
whole-word right-pad simulation (`processBrauer_rightPadSim`) is constructed on the generic `stepWiring`
engine (crossing included) — the wire plumbing folded, the link fields read off the whole trace at the
empty base via the shipped rename-equivariance / loop-invariance / pad-inertness bricks — and composed
with the engine-agnostic payoff `extractDiagram_ofRightPadSimPair` to land `brauerSeedExtract_ofRightPad`:
an extract equality at boundary width `threshold` transports to width `threshold + delta`.  This is the
boundary-WIDENING half of the residual named at `WiringDescFunctoriality.lean` r14.  `= true`. -/
def fxBrauer_hasRightPadCongruence : Bool := true

/-- ★ **Honesty marker — the LEFT horizontal pad congruence + the TWO-SIDED composition are SHIPPED.**  The
whole-word left-pad simulation (`processBrauer_leftPadSim`, over the position-shifted word `shiftBrauerWord`)
lands `brauerSeedExtract_ofLeftPad` (offset `delta`), and `brauerSeedExtract_ofTwoSidedPad` chains right-then-left
to transport an extract equality at width `boundaryCount` to any `leftPad + (boundaryCount + rightPad)` with the
words fired at offset `leftPad` — exactly the `seedExtractEq` shape the r14 whisker bridge consumes for a relation in
arbitrary horizontal context.  Both directions reuse the shipped engine-agnostic payoffs
(`extractDiagram_of{Left,Right}PadSimPair`).  `= true`. -/
def fxBrauer_hasTwoSidedPadCongruence : Bool := true

/-- ★ **Honesty marker — the 5 relations close in ARBITRARY horizontal context (the flag's owed uniform
`relationAgrees`, over ALL reachable states / offsets).**  `brauerConv_relation_inContext` produces, for a relation
diagram-sound at its own boundary, a `BrauerConv` for it whiskered after ANY prefix at ANY offset in ANY wider
boundary — the two-sided pad congruence feeds the r14 whisker bridge's `seedExtractEq`.  Non-vacuous + genuinely
boundary-CHANGING: `brauerConv_{crossingInvolution,yangBaxter,capSlide,snake,snakeMirror}_inWiderContext` each fire
the relation at offset `1` in a boundary strictly wider than the relation's own (which the r14 boundary-preserving
witnesses could not).  This closes the exact obligation the flag docstring names ("for each of the five relations,
its per-relation boundary same-component preservation, uniform over all reachable states / offsets") — see the flip
of `fxBrauer_hasBrauerSoundness` in `Brauer/WiringDesc.lean`.  `= true`. -/
def fxBrauer_hasRelationInArbitraryHorizontalContext : Bool := true

end FX1Poly.Polygraph
