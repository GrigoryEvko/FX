import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadSim

/-! # MatchingLeftPadSeed — the canonical seed pair is LEFT-pad-simulated

The whiskerLeft assembly compares `matchingOf alpha` (canonical seed over `bottomCount`
wires) with `matchingOf (whiskerLeft oneCell alpha)` (canonical seed over
`pad + bottomCount` wires, atoms firing `pad` positions later).  This brick installs the
simulation's base case: the padded canonical range splits as the pad PREFIX `[0, pad)`
followed by the uniform-shift images of the base range, and every other
`MatchingLeftPadSim` field is definitional on empty links (up to one `Nat.add_comm` on the
counter).

The pad-identifier list and its read lemmas are shared with the right seed
(`padIdentifiers` at `start := 0`); the range/append read kit is re-derived privately (the
right seed's copies are file-private). -/

namespace FX1Poly.Polygraph

/-! ## Range and append read plumbing (private copies — the right seed's kit is file-private) -/

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

private theorem natListAppendLength : (block : List Nat) → (wires : List Nat) →
    (block ++ wires).length = block.length + wires.length
  | [], wires => (Nat.zero_add wires.length).symm
  | _ :: blockRest, wires => by
      show (blockRest ++ wires).length + 1 = blockRest.length + 1 + wires.length
      rw [natListAppendLength blockRest wires,
        Nat.add_right_comm blockRest.length wires.length 1]

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

/-! ## The padded range splits as pad prefix plus shift-image -/

/-- ★ **The left-padded canonical wire list IS the pad prefix followed by the shift-image of
the base wire list** — pointwise: below the pad both sides read the index itself (the pad
prefix starts at `0`), at or past it the padded range keeps counting while the append defers
to the uniformly-shifted base range. -/
theorem leftPaddedRangeSplit (pad bottomCount : Nat) :
    List.range (pad + bottomCount)
      = padIdentifiers 0 pad
          ++ (List.range bottomCount).map (freshShiftAbove 0 pad) := by
  have mapRangeLength :
      ((List.range bottomCount).map (freshShiftAbove 0 pad)).length = bottomCount := by
    rw [mapLength, rangeLength]
  apply natListEqOfPointwiseGetAt
  · rw [rangeLength, natListAppendLength, padIdentifiers_length, mapRangeLength]
  · intro index indexInRange
    rw [rangeLength] at indexInRange
    cases Nat.lt_or_ge index pad with
    | inl belowPad =>
        rw [rangeGetAt_below (pad + bottomCount) index
            (Nat.lt_of_lt_of_le belowPad (Nat.le_add_right pad bottomCount)),
          natListGetAt_append_inside (padIdentifiers 0 pad)
            ((List.range bottomCount).map (freshShiftAbove 0 pad)) index
            (by rw [padIdentifiers_length]; exact belowPad),
          padIdentifiers_getAt 0 pad index belowPad,
          Nat.zero_add]
    | inr atOrAbovePad =>
        cases Nat.le.dest atOrAbovePad with
        | intro offset offsetEq =>
            have sumBound : pad + offset < pad + bottomCount := by
              rw [offsetEq]
              exact indexInRange
            have offsetLt : offset < bottomCount := Nat.lt_of_add_lt_add_left sumBound
            rw [← offsetEq,
              rangeGetAt_below (pad + bottomCount) (pad + offset) sumBound,
              natListGetAt_append_atLength (padIdentifiers 0 pad)
                ((List.range bottomCount).map (freshShiftAbove 0 pad)) pad offset
                (padIdentifiers_length 0 pad),
              natListGetAt_map_inRange (freshShiftAbove 0 pad) (List.range bottomCount)
                offset (by rw [rangeLength]; exact offsetLt),
              rangeGetAt_below bottomCount offset offsetLt,
              freshShiftAbove_ofLe 0 pad offset (Nat.zero_le offset),
              Nat.add_comm offset pad]

/-! ## The canonical seeds are left-pad-simulated -/

/-- ★ **The canonical seed pair is left-pad-simulated.**  Empty links make every root its own
node, so the component view is exactly the uniform shift's boolean-equality reflection at
threshold `0`, the pad zone `[0, pad)` is inert by reflexivity, the wire split is
`leftPaddedRangeSplit`, and the counter gap is one `Nat.add_comm`. -/
theorem matchingLeftPadSim_initial (pad bottomCount : Nat) :
    MatchingLeftPadSim pad (padIdentifiers 0 pad)
      (canonicalMatchingSeed bottomCount) (canonicalMatchingSeed (pad + bottomCount)) :=
  { openMap := leftPaddedRangeSplit pad bottomCount
    prefixCount := padIdentifiers_length 0 pad
    nfShift := Nat.add_comm pad bottomCount
    componentComm := fun a b => freshShiftAbove_beqCongr 0 pad a b
    loopsEq := rfl
    forestS := True.intro
    forestT := True.intro
    padRootsFixed := fun _ _ => rfl
    rootAvoidsPad := fun _ nodeHigh => nodeHigh }

/-! ## The padded boundary reads

`matchingBoundaryNodes (delta + bottomCount) stateT` decomposes into four read zones: the
PAD bottom ids below `delta`, the shift-imaged REAL bottom ids in `[delta, delta +
bottomCount)`, the pad-prefix top wires, and the shift-imaged top wires — the reads the
padded connectivity view is decided over.  (The generic boundary-node zone reads
`matchingBoundaryNodes_getAt_bottom`/`_top` are shared with the right seed.) -/

/-- The uniform shift lands at or above the pad width — every shift-image avoids the left
pad zone `[0, delta)` from above. -/
theorem freshShiftAbove_atZero_isHigh (delta identifier : Nat) :
    delta ≤ freshShiftAbove 0 delta identifier := by
  rw [freshShiftAbove_ofLe 0 delta identifier (Nat.zero_le identifier)]
  exact Nat.le_add_left delta identifier

/-- Reading the padded state's open wires INSIDE the pad prefix yields the pad identifier
itself. -/
theorem leftPadSim_wireRead_inPad (delta : Nat) (stateS stateT : WireState)
    (sim : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateS stateT)
    (offset : Nat) (offsetInPad : offset < delta) :
    natListGetAt stateT.openWires offset = offset := by
  rw [sim.openMap,
    natListGetAt_append_inside (padIdentifiers 0 delta)
      (stateS.openWires.map (freshShiftAbove 0 delta)) offset
      (by rw [padIdentifiers_length]; exact offsetInPad),
    padIdentifiers_getAt 0 delta offset offsetInPad,
    Nat.zero_add]

/-- Reading the padded state's open wires PAST the pad prefix is the shift of the base
read. -/
theorem leftPadSim_wireRead_inBase (delta : Nat) (stateS stateT : WireState)
    (sim : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateS stateT)
    (offset : Nat) (offsetInBase : offset < stateS.openWires.length) :
    natListGetAt stateT.openWires (delta + offset)
      = freshShiftAbove 0 delta (natListGetAt stateS.openWires offset) := by
  rw [sim.openMap,
    natListGetAt_append_atLength (padIdentifiers 0 delta)
      (stateS.openWires.map (freshShiftAbove 0 delta)) delta offset
      (padIdentifiers_length 0 delta),
    natListGetAt_map_inRange (freshShiftAbove 0 delta) stateS.openWires offset offsetInBase]

/-- The padded state carries exactly `delta` more open wires than the base state (the pad
sits in FRONT). -/
theorem leftPadSim_wireCount (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT) :
    stateT.openWires.length = delta + stateS.openWires.length := by
  rw [sim.openMap, natListAppendLength, sim.prefixCount, mapLength]

/-! ## The padded same-component zones

Over a left-pad-simulated state the same-component boolean is decided per zone pair: shifted
vs shifted is the base boolean (`sim.componentComm`), pad vs shifted is always `false` (the
pad root stays below `delta`, the shifted root stays at or above it), and pad vs pad is
plain equality of the pad identifiers (both are their own roots). -/

/-- A pad-zone node is never same-component with a shift-image node in the padded links. -/
theorem leftPadSim_padVsShifted_isFalse (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT)
    (padNode baseNode : Nat) (padBelow : padNode < delta) :
    (unionFindRootOf stateT.links padNode
        == unionFindRootOf stateT.links (freshShiftAbove 0 delta baseNode)) = false := by
  rw [sim.padRootsFixed padNode padBelow]
  have shiftedRootHigh : delta
      ≤ unionFindRootOf stateT.links (freshShiftAbove 0 delta baseNode) :=
    sim.rootAvoidsPad (freshShiftAbove 0 delta baseNode)
      (freshShiftAbove_atZero_isHigh delta baseNode)
  apply decide_eq_false
  intro rootsEq
  rw [← rootsEq] at shiftedRootHigh
  exact Nat.lt_irrefl padNode (Nat.lt_of_lt_of_le padBelow shiftedRootHigh)

/-- A shift-image node is never same-component with a pad-zone node in the padded links. -/
theorem leftPadSim_shiftedVsPad_isFalse (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT)
    (baseNode padNode : Nat) (padBelow : padNode < delta) :
    (unionFindRootOf stateT.links (freshShiftAbove 0 delta baseNode)
        == unionFindRootOf stateT.links padNode) = false := by
  rw [sim.padRootsFixed padNode padBelow]
  have shiftedRootHigh : delta
      ≤ unionFindRootOf stateT.links (freshShiftAbove 0 delta baseNode) :=
    sim.rootAvoidsPad (freshShiftAbove 0 delta baseNode)
      (freshShiftAbove_atZero_isHigh delta baseNode)
  apply decide_eq_false
  intro rootsEq
  rw [rootsEq] at shiftedRootHigh
  exact Nat.lt_irrefl padNode (Nat.lt_of_lt_of_le padBelow shiftedRootHigh)

/-- Two pad-zone nodes are same-component in the padded links exactly when they are EQUAL. -/
theorem leftPadSim_padVsPad (delta : Nat) (padPrefix : List Nat)
    (stateS stateT : WireState)
    (sim : MatchingLeftPadSim delta padPrefix stateS stateT)
    (firstPad secondPad : Nat)
    (firstBelow : firstPad < delta) (secondBelow : secondPad < delta) :
    (unionFindRootOf stateT.links firstPad == unionFindRootOf stateT.links secondPad)
      = (firstPad == secondPad) := by
  rw [sim.padRootsFixed firstPad firstBelow, sim.padRootsFixed secondPad secondBelow]

/-! ## Honesty markers -/

/-- **Honesty marker — the left-pad seed instance is SHIPPED.**  The padded canonical range
splits as the pad prefix `[0, pad)` plus the uniform-shift image (`leftPaddedRangeSplit`),
and the canonical seed pair inhabits `MatchingLeftPadSim` at that prefix
(`matchingLeftPadSim_initial`).  The padded-boundary read-off lives below
(`fxMode_hasMatchingLeftPadBoundaryReads`).  `= true`. -/
def fxMode_hasMatchingLeftPadSeed : Bool := true

/-- **Honesty marker — the left padded-boundary read-off toolkit is SHIPPED.**  The pad-sim
wire reads by zone (pad prefix reads its identifier, past-the-prefix reads the shifted base
wire), the wire count, and the padded same-component boolean characterized per zone pair:
shifted-vs-shifted is `sim.componentComm`, pad-vs-shifted is `false` both ways (pad roots
stay below `delta`, shifted roots at or above it), pad-vs-pad is plain identifier equality.
NOT yet shipped: the two-run padded relation agreement over these zones and the whiskerLeft
assembly — the next MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingLeftPadBoundaryReads : Bool := true

end FX1Poly.Polygraph
