import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadCongruence
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

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the RIGHT horizontal pad congruence at `processBrauer` is SHIPPED.**  The
whole-word right-pad simulation (`processBrauer_rightPadSim`) is constructed on the generic `stepWiring`
engine (crossing included) — the wire plumbing folded, the link fields read off the whole trace at the
empty base via the shipped rename-equivariance / loop-invariance / pad-inertness bricks — and composed
with the engine-agnostic payoff `extractDiagram_ofRightPadSimPair` to land `brauerSeedExtract_ofRightPad`:
an extract equality at boundary width `threshold` transports to width `threshold + delta`.  This is the
boundary-WIDENING half of the residual named at `WiringDescFunctoriality.lean` r14.  The LEFT pad
(position offset via `shiftBrauerWord`) and the two-sided composition feeding the soundness flip are the
next bricks.  `= true`. -/
def fxBrauer_hasRightPadCongruence : Bool := true

end FX1Poly.Polygraph
