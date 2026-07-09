import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityOffConfined
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConv
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCompositeExtract

/-! # KEYSTONE14 — the two-word FUNCTORIALITY port, from the walking-adjunction spine to the Brauer engine

The walking-adjunction lane ships the SAT-D5 headline `processSpine_extract_eq_ofCanonicalExtractEq`
(`FreeTwoCell/MatchingCompositeExtract.lean`): two disciplined spines whose CANONICAL runs extract identically
produce identical extracts from ANY shared disciplined mid-state.  Its proof factors through three legs that live
purely at the EVENT-LIST level (engine-agnostic, reused verbatim below):

  * `extractDiagram_eq_of_connectivityView` — the three-field reassembly (length / loop / view);
  * `compositeBoundaryView_agrees_ofExtractEq` — the VIEW leg (component reads over the renamed mid-links);
  * `countJoinEventLoops_overMidLinks_agrees_ofViewSim` — the LOOP leg (loop increments over the renamed mid-links);
  * `matchingConnectivityViewSim_ofExtractEq` — extract equality reconstructs the connectivity-view simulation.

What is engine-SPECIFIC is the RELATIVIZATION stack: expressing a run from an arbitrary mid-state as the canonical
trace renamed by the mid-state wire map (`…_ofMidState`).  This file PORTS that stack from the cup/cap-only spine to
the generic `stepWiring` engine — crossing included — and lands the Brauer headline
`processBrauer_extract_eq_ofCanonicalExtractEq`.

## The port map (source `spine` -> Brauer `wiring`)

  * `MatchingRelativeWireSim` — REUSED verbatim (a pure `WireState`/`sigma` structure, no spine).
  * `matchingRelativeWireSim_stepCup` / `_stepCap` -> `stepWiring_relativeWireSim` — ONE lemma for ANY generator
    (the wires depend only on slice + fresh + splice, the arcs never touch the open-wire plumbing, so the crossing
    needs NO special case — the transposition transports identically).
  * `spineJoinEvents_ofRelativeWireSim` -> `brauerWordJoinEvents_ofRelativeWireSim` (the whole word's decoded trace
    is the `sigma`-rename of the canonical trace, threading the `BrauerWordInRange` discipline).  The per-arc leg
    `wiringArcEvents_ofRelativeWireSim` covers the MIXED input/output arcs of the crossing (one input read via
    `openMap`, one fresh output via `freshCorr`) — strictly easier than a cup/cap because there is no merge.
  * `processSpine_{links,loops,openWires}_ofMidState` -> `processBrauer_{links,loops,openWires}_ofMidState`.
  * `processSpine_extract_eq_ofCanonicalExtractEq` -> `processBrauer_extract_eq_ofCanonicalExtractEq` (headline,
    mirroring the source three-leg assembly verbatim).

Two disciplines the Brauer engine needs that the spine got for free from its boundary chain / arity dichotomy:

  * `BrauerWordInRange` — the absolute-position firing discipline (each atom's window `[position, position+inputCount)`
    sits inside the running boundary, tracked additively through the word);
  * `WiringDescTagsInRange` — a static well-formedness (every arc endpoint tag `< inputCount + outputCount`), so the
    output reads land in the fresh block.  Both hold for `cup` / `cap` / `crossing` / `identity` by `decide`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local list primitives (subtraction-free length / slice arithmetic) -/

/-- `(List.range count).length = count` — local copy (the shipped copies are private). -/
private theorem rangeLengthLocal (count : Nat) : (List.range count).length = count :=
  rangeLength_local count

/-- Reading `List.range.loop` at a past-the-front offset drops into the accumulator. -/
private theorem rangeLoopGetAtPastLocal : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastLocal count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

/-- Reading `List.range.loop` below its front returns the index. -/
private theorem rangeLoopGetAtBelowLocal : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowLocal count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastLocal count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

/-- Reading `List.range count` below its length returns the index (local copy of the private `rangeGetAt_below`). -/
private theorem rangeGetAtBelowLocal (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowLocal count [] index indexBelow

/-- `(n + m) - m = n`, reproved by hand (Init's `Nat.add_sub_cancel` leaks `propext`).  Structural on `m`. -/
private theorem addSubCancelRightLocal : (n m : Nat) → (n + m) - m = n
  | value, 0 => rfl
  | value, count + 1 => by
      show (value + (count + 1)) - (count + 1) = value
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact addSubCancelRightLocal value count

/-- Cancel a common `+ 1` (Init's `Nat.add_right_cancel` leaks `propext`; `Nat.succ.inj` is clean). -/
private theorem addOneCancelLocal {leftValue rightValue : Nat}
    (h : leftValue + 1 = rightValue + 1) : leftValue = rightValue :=
  Nat.succ.inj h

/-! ## Slice commutes with a rename; slice / removal lengths (subtraction-free) -/

/-- ★ **`natListSliceAt` commutes with a rename.**  Mapping `sigma` over a slice equals slicing the renamed list —
unconditional (positional take is length-preserving).  Structural on the slice's own matcher (count, list, position). -/
theorem natListSliceAt_map (sigma : Nat → Nat) :
    (wires : List Nat) → (position count : Nat) →
    (natListSliceAt wires position count).map sigma
      = natListSliceAt (wires.map sigma) position count
  | wires, position, 0 => by
      rw [sliceAt_count_zero wires position, sliceAt_count_zero (wires.map sigma) position]; rfl
  | [], position, count + 1 => by
      rw [sliceAt_nil position (count + 1)]; exact (sliceAt_nil position (count + 1)).symm
  | headWire :: tailWires, 0, count + 1 => by
      rw [sliceAt_cons_zero_succ headWire tailWires count]
      show sigma headWire :: (natListSliceAt tailWires 0 count).map sigma
          = natListSliceAt (sigma headWire :: tailWires.map sigma) 0 (count + 1)
      rw [sliceAt_cons_zero_succ (sigma headWire) (tailWires.map sigma) count,
        natListSliceAt_map sigma tailWires 0 count]
  | headWire :: tailWires, position + 1, count => by
      rw [sliceAt_cons_succ headWire tailWires position count]
      show (natListSliceAt tailWires position count).map sigma
          = natListSliceAt (sigma headWire :: tailWires.map sigma) (position + 1) count
      rw [sliceAt_cons_succ (sigma headWire) (tailWires.map sigma) position count,
        natListSliceAt_map sigma tailWires position count]

/-- ★ **A slice inside the list has length exactly its count.**  Given the window fits
(`wires.length = position + count + leftover`), the slice reads a full `count` wires.  Subtraction-free, structural
on the slice's matcher. -/
theorem natListSliceAt_length_fits :
    (wires : List Nat) → (position count leftover : Nat) →
    wires.length = position + count + leftover →
    (natListSliceAt wires position count).length = count
  | wires, position, 0, _, _ =>
      (congrArg List.length (sliceAt_count_zero wires position)).trans rfl
  | [], position, count + 1, leftover, lengthEq => by
      have contra : (0 : Nat) = Nat.succ (position + count + leftover) := by
        have e : ([] : List Nat).length = position + (count + 1) + leftover := lengthEq
        rw [Nat.add_succ, Nat.succ_add] at e
        exact e
      exact Nat.noConfusion contra
  | headWire :: tailWires, 0, count + 1, leftover, lengthEq => by
      rw [sliceAt_cons_zero_succ headWire tailWires count]
      show (natListSliceAt tailWires 0 count).length + 1 = count + 1
      have tailLength : tailWires.length = 0 + count + leftover := by
        have e : tailWires.length + 1 = 0 + (count + 1) + leftover := lengthEq
        apply addOneCancelLocal
        rw [e, Nat.zero_add, Nat.zero_add, Nat.add_right_comm count 1 leftover]
      rw [natListSliceAt_length_fits tailWires 0 count leftover tailLength]
  | headWire :: tailWires, position + 1, count, leftover, lengthEq => by
      rw [sliceAt_cons_succ headWire tailWires position count]
      have tailLength : tailWires.length = position + count + leftover := by
        have e : tailWires.length + 1 = position + 1 + count + leftover := lengthEq
        apply addOneCancelLocal
        rw [e, Nat.add_right_comm position 1 count, Nat.add_right_comm (position + count) 1 leftover]
      exact natListSliceAt_length_fits tailWires position count leftover tailLength

/-- ★ **A block removal inside the list drops exactly its count (subtraction-free).**  Given the window fits
(`wires.length = position + count + leftover`), removing `count` wires at `position` leaves `position + leftover`.
Structural on the removal's own matcher. -/
theorem natListRemoveManyAt_length_fits :
    (wires : List Nat) → (position count leftover : Nat) →
    wires.length = position + count + leftover →
    (natListRemoveManyAt wires position count).length = position + leftover
  | wires, position, 0, leftover, lengthEq => by
      rw [removeManyAt_zero wires position]
      rw [Nat.add_zero] at lengthEq
      exact lengthEq
  | [], position, count + 1, leftover, lengthEq => by
      have contra : (0 : Nat) = Nat.succ (position + count + leftover) := by
        have e : ([] : List Nat).length = position + (count + 1) + leftover := lengthEq
        rw [Nat.add_succ, Nat.succ_add] at e
        exact e
      exact Nat.noConfusion contra
  | headWire :: tailWires, 0, count + 1, leftover, lengthEq => by
      rw [removeManyAt_zero_cons headWire tailWires count]
      have tailLength : tailWires.length = 0 + count + leftover := by
        have e : tailWires.length + 1 = 0 + (count + 1) + leftover := lengthEq
        apply addOneCancelLocal
        rw [e, Nat.zero_add, Nat.zero_add, Nat.add_right_comm count 1 leftover]
      rw [natListRemoveManyAt_length_fits tailWires 0 count leftover tailLength]
  | headWire :: tailWires, position + 1, count, leftover, lengthEq => by
      rw [removeManyAt_succ_cons headWire tailWires position count]
      show (natListRemoveManyAt tailWires position count).length + 1 = position + 1 + leftover
      have tailLength : tailWires.length = position + count + leftover := by
        have e : tailWires.length + 1 = position + 1 + count + leftover := lengthEq
        apply addOneCancelLocal
        rw [e, Nat.add_right_comm position 1 count, Nat.add_right_comm (position + count) 1 leftover]
      rw [natListRemoveManyAt_length_fits tailWires position count leftover tailLength,
        Nat.add_right_comm position leftover 1]

/-- Reading `((List.range count).map (· + base))` below its length returns `index + base`.  Map read-off. -/
private theorem natListGetAt_rangeMapAdd (base count index : Nat) (indexBelow : index < count) :
    natListGetAt ((List.range count).map (· + base)) index = index + base := by
  rw [natListGetAt_map_inRange (· + base) (List.range count) index
      (by rw [rangeLengthLocal]; exact indexBelow),
    rangeGetAtBelowLocal count index indexBelow]

/-! ## The static / dynamic disciplines -/

/-- ★ **`WiringDescTagsInRange`** — every arc endpoint tag of a generator sits in its port range
`[0, inputCount + outputCount)`, so an output read (`tag - inputCount`) lands in the freshly allocated block.  A
static well-formedness holding for `cup` / `cap` / `crossing` / `identity` by `decide`. -/
@[reducible] def WiringDescTagsInRange (desc : WiringDesc) : Prop :=
  ∀ arc ∈ desc.arcs, arc.1 < desc.inputCount + desc.outputCount ∧ arc.2 < desc.inputCount + desc.outputCount

/-- ★ **`BrauerWordInRange`** — the absolute-position firing discipline: each atom's input window
`[position, position + inputCount)` sits inside the running boundary (tracked additively as
`boundaryLength = position + inputCount + rightLen`, with `rightLen` the strands to the right), the generator is
tag-well-formed, and the tail is in range at the atom's cod boundary `position + outputCount + rightLen`.  The Brauer
analog of `SpineBoundaryChained`, cons-shaped for structural fold threading. -/
inductive BrauerWordInRange : Nat → List BrauerAtom → Prop where
  /-- The empty word is in range at any boundary. -/
  | nil (boundaryLength : Nat) : BrauerWordInRange boundaryLength []
  /-- A cons is in range when the head fires inside the running boundary (`fits`), is tag-well-formed
  (`tagsInRange`), and the tail is in range at the head's cod boundary. -/
  | cons {boundaryLength : Nat} (atom : BrauerAtom) {rest : List BrauerAtom} (rightLen : Nat)
      (fits : boundaryLength = atom.position + atom.wiring.inputCount + rightLen)
      (tagsInRange : WiringDescTagsInRange atom.wiring)
      (tailInRange : BrauerWordInRange (atom.position + atom.wiring.outputCount + rightLen) rest) :
      BrauerWordInRange boundaryLength (atom :: rest)

/-- Cons inversion for the firing discipline. -/
theorem brauerWordInRange_tail {boundaryLength : Nat} {atom : BrauerAtom} {rest : List BrauerAtom}
    (inRange : BrauerWordInRange boundaryLength (atom :: rest)) :
    ∃ rightLen : Nat,
      boundaryLength = atom.position + atom.wiring.inputCount + rightLen
      ∧ WiringDescTagsInRange atom.wiring
      ∧ BrauerWordInRange (atom.position + atom.wiring.outputCount + rightLen) rest := by
  cases inRange with
  | cons _ rightLen fits tagsInRange tailInRange => exact ⟨rightLen, fits, tagsInRange, tailInRange⟩

/-- The word's total internal-loop count — the closed loops the arc fold does NOT decode (all `0` for the
generators of the presentation). -/
def brauerWordInternalLoops : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => atom.wiring.internalLoops + brauerWordInternalLoops rest

/-! ## Length tracking: one `stepWiring` step preserves the additive boundary decomposition -/

/-- One `stepWiring` step's open-wire list is the splice of its fresh output block into the input-removed list
(the `stepWiring` `openWires` field, `rfl`). -/
private theorem stepWiring_openWires_rfl (state : WireState) (position : Nat) (desc : WiringDesc) :
    (stepWiring state position desc).openWires
      = natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position
          ((List.range desc.outputCount).map (· + state.nextFresh)) := rfl

/-- ★ **One `stepWiring` step tracks the boundary additively.**  If the open wires decompose as
`position + inputCount + rightLen`, the stepped open wires decompose as `position + outputCount + rightLen` — the
removal drops the input block (`natListRemoveManyAt_length_fits`), the splice adds the output block
(`natListInsertAt_length`). -/
theorem stepWiring_openWires_length_fits (state : WireState) (position rightLen : Nat) (desc : WiringDesc)
    (fits : state.openWires.length = position + desc.inputCount + rightLen) :
    (stepWiring state position desc).openWires.length
      = position + desc.outputCount + rightLen := by
  rw [stepWiring_openWires_rfl state position desc, natListInsertAt_length,
    natListRemoveManyAt_length_fits state.openWires position desc.inputCount rightLen fits,
    mapLength (· + state.nextFresh) (List.range desc.outputCount),
    rangeLengthLocal, Nat.add_right_comm position rightLen desc.outputCount]

/-! ## The relative-run WIRE simulation on the generic engine (crossing needs no special case) -/

/-- `(n + m) - n = m`, cancelling on the LEFT (via `addSubCancelRightLocal` after a commute). -/
private theorem addSubCancelLeftLocal (n m : Nat) : (n + m) - n = m := by
  rw [Nat.add_comm n m]; exact addSubCancelRightLocal m n

/-- Mapping a fresh-corresponding `sigma` over a `range`-shifted block re-bases it: the two future fresh blocks
correspond offset-for-offset (`freshCorr`).  Pointwise via `natListEqOfPointwiseGetAt`. -/
private theorem rangeMapAdd_ofFreshCorr (sigma : Nat → Nat) (canBase relBase count : Nat)
    (freshCorr : ∀ offset, sigma (canBase + offset) = relBase + offset) :
    ((List.range count).map (· + canBase)).map sigma = (List.range count).map (· + relBase) := by
  apply natListEqOfPointwiseGetAt
  · rw [mapLength sigma ((List.range count).map (· + canBase)),
      mapLength (· + canBase) (List.range count), mapLength (· + relBase) (List.range count)]
  · intro index indexInRange
    have indexBelowCount : index < count := by
      have lengthEq : (((List.range count).map (· + canBase)).map sigma).length = count := by
        rw [mapLength sigma ((List.range count).map (· + canBase)),
          mapLength (· + canBase) (List.range count), rangeLengthLocal]
      rw [lengthEq] at indexInRange
      exact indexInRange
    rw [natListGetAt_map_inRange sigma ((List.range count).map (· + canBase)) index
        (by rw [mapLength (· + canBase) (List.range count), rangeLengthLocal]; exact indexBelowCount),
      natListGetAt_rangeMapAdd canBase count index indexBelowCount,
      natListGetAt_rangeMapAdd relBase count index indexBelowCount,
      Nat.add_comm index canBase, freshCorr index, Nat.add_comm relBase index]

/-- ★ **ONE `stepWiring` step preserves the relative-run wire correspondence, for ANY generator.**  The wires depend
only on the input slice, the fresh block, and the splice — the arcs never touch the open-wire plumbing — so the
crossing (and any arbitrary-arity generator) transports identically to a cup / cap: `openMap` pushes the two splices
(`natListInsertAt_map` / `natListRemoveManyAt_map`) and re-bases the fresh block (`rangeMapAdd_ofFreshCorr`);
`freshCorr` shifts by the generator's output count. -/
theorem stepWiring_relativeWireSim (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState) (position : Nat) (desc : WiringDesc)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    MatchingRelativeWireSim sigma
      (stepWiring stateCanonical position desc) (stepWiring stateRelative position desc) := by
  have openMapAfter : (stepWiring stateRelative position desc).openWires
      = ((stepWiring stateCanonical position desc).openWires).map sigma := by
    rw [stepWiring_openWires_rfl stateRelative position desc,
      stepWiring_openWires_rfl stateCanonical position desc,
      natListInsertAt_map sigma
        (natListRemoveManyAt stateCanonical.openWires position desc.inputCount) position
        ((List.range desc.outputCount).map (· + stateCanonical.nextFresh)),
      natListRemoveManyAt_map sigma stateCanonical.openWires position desc.inputCount,
      sim.openMap,
      rangeMapAdd_ofFreshCorr sigma stateCanonical.nextFresh stateRelative.nextFresh desc.outputCount
        sim.freshCorr]
  have freshCorrAfter : ∀ offset,
      sigma ((stepWiring stateCanonical position desc).nextFresh + offset)
        = (stepWiring stateRelative position desc).nextFresh + offset := by
    intro offset
    rw [stepWiring_nextFresh stateCanonical position desc,
      stepWiring_nextFresh stateRelative position desc,
      Nat.add_assoc stateCanonical.nextFresh desc.outputCount offset,
      Nat.add_assoc stateRelative.nextFresh desc.outputCount offset]
    exact sim.freshCorr (desc.outputCount + offset)
  exact { openMap := openMapAfter, freshCorr := freshCorrAfter }

/-- ★ **The wire correspondence folds over any Brauer word** — no discipline needed (the wire plumbing is total). -/
theorem processBrauer_relativeWireSim (sigma : Nat → Nat) :
    (atoms : List BrauerAtom) → (stateCanonical stateRelative : WireState) →
    MatchingRelativeWireSim sigma stateCanonical stateRelative →
    MatchingRelativeWireSim sigma
      (processBrauer stateCanonical atoms) (processBrauer stateRelative atoms)
  | [], _, _, sim => sim
  | atom :: rest, stateCanonical, stateRelative, sim => by
      show MatchingRelativeWireSim sigma
        (processBrauer (stepWiring stateCanonical atom.position atom.wiring) rest)
        (processBrauer (stepWiring stateRelative atom.position atom.wiring) rest)
      exact processBrauer_relativeWireSim sigma rest
        (stepWiring stateCanonical atom.position atom.wiring)
        (stepWiring stateRelative atom.position atom.wiring)
        (stepWiring_relativeWireSim sigma stateCanonical stateRelative atom.position atom.wiring sim)

/-! ## The decoded arc trace is the sigma-rename (per endpoint, per arc, per word) -/

/-- ★ **One decoded wiring endpoint under the relative run is the `sigma`-image of the canonical endpoint.**  An
INPUT tag (`tag < inputCount`) reads the sliced open wires — `sigma`-imaged via `openMap` + `natListSliceAt_map` +
`natListGetAt_map_inRange` (in range by the window `fits`); an OUTPUT tag (`inputCount ≤ tag < inputCount + outputCount`)
reads the fresh block — `sigma`-imaged via `freshCorr`.  The crossing's mixed arcs (one of each) are exactly this. -/
theorem stepWiringEndpoint_ofRelativeWireSim (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState) (position inputCount outputCount leftover tag : Nat)
    (lengthDecomp : stateCanonical.openWires.length = position + inputCount + leftover)
    (tagInRange : tag < inputCount + outputCount)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    wiringEndpointNode (natListSliceAt stateRelative.openWires position inputCount)
        ((List.range outputCount).map (· + stateRelative.nextFresh)) inputCount tag
      = sigma (wiringEndpointNode (natListSliceAt stateCanonical.openWires position inputCount)
          ((List.range outputCount).map (· + stateCanonical.nextFresh)) inputCount tag) := by
  show (if tag < inputCount then
          natListGetAt (natListSliceAt stateRelative.openWires position inputCount) tag
        else natListGetAt ((List.range outputCount).map (· + stateRelative.nextFresh)) (tag - inputCount))
      = sigma (if tag < inputCount then
          natListGetAt (natListSliceAt stateCanonical.openWires position inputCount) tag
        else natListGetAt ((List.range outputCount).map (· + stateCanonical.nextFresh)) (tag - inputCount))
  by_cases tagBelow : tag < inputCount
  · rw [if_pos tagBelow, if_pos tagBelow]
    have sliceLength : (natListSliceAt stateCanonical.openWires position inputCount).length = inputCount :=
      natListSliceAt_length_fits stateCanonical.openWires position inputCount leftover lengthDecomp
    rw [sim.openMap, ← natListSliceAt_map sigma stateCanonical.openWires position inputCount,
      natListGetAt_map_inRange sigma (natListSliceAt stateCanonical.openWires position inputCount) tag
        (by rw [sliceLength]; exact tagBelow)]
  · rw [if_neg tagBelow, if_neg tagBelow]
    have inputLe : inputCount ≤ tag := Nat.le_of_not_lt tagBelow
    obtain ⟨offset, tagEq⟩ := Nat.le.dest inputLe
    have offsetLt : offset < outputCount := by
      rw [← tagEq] at tagInRange
      exact Nat.lt_of_add_lt_add_left tagInRange
    have subEq : tag - inputCount = offset := by
      rw [← tagEq, Nat.add_comm inputCount offset, addSubCancelRightLocal offset inputCount]
    rw [subEq,
      natListGetAt_rangeMapAdd stateRelative.nextFresh outputCount offset offsetLt,
      natListGetAt_rangeMapAdd stateCanonical.nextFresh outputCount offset offsetLt,
      Nat.add_comm offset stateCanonical.nextFresh, sim.freshCorr offset,
      Nat.add_comm offset stateRelative.nextFresh]

/-- ★ **A generator's whole decoded arc trace under the relative run is the `sigma`-rename of the canonical trace.**
Structural on the arcs, each endpoint via `stepWiringEndpoint_ofRelativeWireSim` (window `fits` + tag range). -/
theorem wiringArcEvents_ofRelativeWireSim (sigma : Nat → Nat)
    (stateCanonical stateRelative : WireState) (position inputCount outputCount leftover : Nat)
    (lengthDecomp : stateCanonical.openWires.length = position + inputCount + leftover)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    (arcs : List (Nat × Nat)) →
    (∀ arc ∈ arcs, arc.1 < inputCount + outputCount ∧ arc.2 < inputCount + outputCount) →
    wiringArcEvents (natListSliceAt stateRelative.openWires position inputCount)
        ((List.range outputCount).map (· + stateRelative.nextFresh)) inputCount arcs
      = (wiringArcEvents (natListSliceAt stateCanonical.openWires position inputCount)
          ((List.range outputCount).map (· + stateCanonical.nextFresh)) inputCount arcs).map
          (fun event => (sigma event.1, sigma event.2))
  | [], _ => rfl
  | (firstTag, secondTag) :: rest, tagsOk => by
      have headTags := tagsOk (firstTag, secondTag) (List.Mem.head rest)
      have restTags : ∀ arc ∈ rest, arc.1 < inputCount + outputCount ∧ arc.2 < inputCount + outputCount :=
        fun arc arcMem => tagsOk arc (List.Mem.tail (firstTag, secondTag) arcMem)
      show (wiringEndpointNode (natListSliceAt stateRelative.openWires position inputCount)
              ((List.range outputCount).map (· + stateRelative.nextFresh)) inputCount firstTag,
            wiringEndpointNode (natListSliceAt stateRelative.openWires position inputCount)
              ((List.range outputCount).map (· + stateRelative.nextFresh)) inputCount secondTag)
            :: wiringArcEvents (natListSliceAt stateRelative.openWires position inputCount)
                ((List.range outputCount).map (· + stateRelative.nextFresh)) inputCount rest
          = (sigma (wiringEndpointNode (natListSliceAt stateCanonical.openWires position inputCount)
              ((List.range outputCount).map (· + stateCanonical.nextFresh)) inputCount firstTag),
            sigma (wiringEndpointNode (natListSliceAt stateCanonical.openWires position inputCount)
              ((List.range outputCount).map (· + stateCanonical.nextFresh)) inputCount secondTag))
            :: (wiringArcEvents (natListSliceAt stateCanonical.openWires position inputCount)
                ((List.range outputCount).map (· + stateCanonical.nextFresh)) inputCount rest).map
                (fun event => (sigma event.1, sigma event.2))
      rw [stepWiringEndpoint_ofRelativeWireSim sigma stateCanonical stateRelative position inputCount
            outputCount leftover firstTag lengthDecomp headTags.1 sim,
        stepWiringEndpoint_ofRelativeWireSim sigma stateCanonical stateRelative position inputCount
            outputCount leftover secondTag lengthDecomp headTags.2 sim,
        wiringArcEvents_ofRelativeWireSim sigma stateCanonical stateRelative position inputCount outputCount
            leftover lengthDecomp sim rest restTags]

/-- A `List.map` distributes over `++` (local copy — the shipped one is private). -/
private theorem listMapAppendLocal {Element ResultElement : Type} (mapped : Element → ResultElement) :
    (first second : List Element) → (first ++ second).map mapped = first.map mapped ++ second.map mapped
  | [], _ => rfl
  | head :: firstRest, second => congrArg (mapped head :: ·) (listMapAppendLocal mapped firstRest second)

/-- ★ **The whole Brauer word's decoded trace under the relative run is the `sigma`-rename of the canonical trace.**
Structural on the word, threading the `BrauerWordInRange` discipline (which supplies each atom's window `fits` and
tag range) and stepping the wire simulation along both runs.  The port of `spineJoinEvents_ofRelativeWireSim`. -/
theorem brauerWordJoinEvents_ofRelativeWireSim (sigma : Nat → Nat) :
    (atoms : List BrauerAtom) → (stateCanonical stateRelative : WireState) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    stateCanonical.openWires.length = boundaryLength →
    MatchingRelativeWireSim sigma stateCanonical stateRelative →
    brauerWordJoinEvents stateRelative atoms
      = (brauerWordJoinEvents stateCanonical atoms).map (fun event => (sigma event.1, sigma event.2))
  | [], _, _, _, _, _, _ => rfl
  | atom :: rest, stateCanonical, stateRelative, boundaryLength, inRange, tracks, sim => by
      obtain ⟨leftover, fits, tagsInRange, tailInRange⟩ := brauerWordInRange_tail inRange
      show wiringArcEvents (natListSliceAt stateRelative.openWires atom.position atom.wiring.inputCount)
              ((List.range atom.wiring.outputCount).map (· + stateRelative.nextFresh))
              atom.wiring.inputCount atom.wiring.arcs
            ++ brauerWordJoinEvents (stepWiring stateRelative atom.position atom.wiring) rest
          = (wiringArcEvents (natListSliceAt stateCanonical.openWires atom.position atom.wiring.inputCount)
              ((List.range atom.wiring.outputCount).map (· + stateCanonical.nextFresh))
              atom.wiring.inputCount atom.wiring.arcs
            ++ brauerWordJoinEvents (stepWiring stateCanonical atom.position atom.wiring) rest).map
              (fun event => (sigma event.1, sigma event.2))
      have lengthDecomp : stateCanonical.openWires.length
          = atom.position + atom.wiring.inputCount + leftover := by rw [tracks]; exact fits
      rw [listMapAppendLocal (fun event : Nat × Nat => (sigma event.1, sigma event.2)),
        wiringArcEvents_ofRelativeWireSim sigma stateCanonical stateRelative atom.position
          atom.wiring.inputCount atom.wiring.outputCount leftover lengthDecomp sim atom.wiring.arcs tagsInRange,
        brauerWordJoinEvents_ofRelativeWireSim sigma rest
          (stepWiring stateCanonical atom.position atom.wiring)
          (stepWiring stateRelative atom.position atom.wiring)
          (atom.position + atom.wiring.outputCount + leftover) tailInRange
          (stepWiring_openWires_length_fits stateCanonical atom.position leftover atom.wiring lengthDecomp)
          (stepWiring_relativeWireSim sigma stateCanonical stateRelative atom.position atom.wiring sim)]

/-! ## The whole word's loop reification (UNCONDITIONAL — the arc fold accumulates the count by construction) -/

/-- The five-term commutative-monoid rearrangement the loop fold bottoms out in. -/
private theorem loopsRearrange (l1 arc internal tail rest : Nat) :
    l1 + arc + internal + tail + rest = l1 + (arc + tail) + (internal + rest) := by
  rw [Nat.add_right_comm (l1 + arc) internal tail,
    Nat.add_assoc (l1 + arc + tail) internal rest, Nat.add_assoc l1 arc tail]

/-- ★ **The whole `processBrauer` fold's loop total reified.**  UNCONDITIONALLY (no freshness): each step's
`stepWiring_loops_eq` already reads the arc loops as `countJoinEventLoops`, so the fold's total is the state's plus
the flat trace's count plus the word's internal loops.  The Brauer analog of `processSpine_loops_eq_addJoinEventLoops`
(which the spine needed freshness for — the generic arc fold does not). -/
theorem processBrauer_loops_eq_addJoinEventLoops :
    (atoms : List BrauerAtom) → (state : WireState) →
    (processBrauer state atoms).loops
      = state.loops + countJoinEventLoops (brauerWordJoinEvents state atoms) state.links
        + brauerWordInternalLoops atoms
  | [], _ => rfl
  | atom :: rest, state => by
      show (processBrauer (stepWiring state atom.position atom.wiring) rest).loops
          = state.loops
            + countJoinEventLoops
                (wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
                    (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs
                  ++ brauerWordJoinEvents (stepWiring state atom.position atom.wiring) rest)
                state.links
            + (atom.wiring.internalLoops + brauerWordInternalLoops rest)
      rw [processBrauer_loops_eq_addJoinEventLoops rest (stepWiring state atom.position atom.wiring),
        stepWiring_loops_eq state atom.position atom.wiring,
        stepWiring_links_eq_applyJoinEvents state atom.position atom.wiring,
        countJoinEventLoops_append
          (wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
            (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs)
          (brauerWordJoinEvents (stepWiring state atom.position atom.wiring) rest) state.links]
      exact loopsRearrange state.loops
        (countJoinEventLoops (wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
          (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs) state.links)
        atom.wiring.internalLoops
        (countJoinEventLoops (brauerWordJoinEvents (stepWiring state atom.position atom.wiring) rest)
          (applyJoinEvents (wiringArcEvents (stepWiringInputNodes state atom.position atom.wiring)
            (stepWiringOutputNodes state atom.wiring) atom.wiring.inputCount atom.wiring.arcs) state.links))
        (brauerWordInternalLoops rest)

/-! ## The generic-sigma read-offs -/

/-- ★ **The relative run's `links` are the renamed canonical trace folded over the relative links.** -/
theorem processBrauer_links_ofRelativeSim (sigma : Nat → Nat)
    (atoms : List BrauerAtom) (stateCanonical stateRelative : WireState) (boundaryLength : Nat)
    (inRange : BrauerWordInRange boundaryLength atoms)
    (tracks : stateCanonical.openWires.length = boundaryLength)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    (processBrauer stateRelative atoms).links
      = applyJoinEvents
          ((brauerWordJoinEvents stateCanonical atoms).map (fun event => (sigma event.1, sigma event.2)))
          stateRelative.links := by
  rw [processBrauer_links_eq_applyJoinEvents atoms stateRelative,
    brauerWordJoinEvents_ofRelativeWireSim sigma atoms stateCanonical stateRelative boundaryLength
      inRange tracks sim]

/-- ★ **The relative run's `loops` are the relative state's plus the renamed trace's already-connected count** —
provided the word carries no internal loops (which all presentation generators satisfy). -/
theorem processBrauer_loops_ofRelativeSim (sigma : Nat → Nat)
    (atoms : List BrauerAtom) (stateCanonical stateRelative : WireState) (boundaryLength : Nat)
    (inRange : BrauerWordInRange boundaryLength atoms)
    (tracks : stateCanonical.openWires.length = boundaryLength)
    (zeroInternal : brauerWordInternalLoops atoms = 0)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    (processBrauer stateRelative atoms).loops
      = stateRelative.loops
        + countJoinEventLoops
            ((brauerWordJoinEvents stateCanonical atoms).map (fun event => (sigma event.1, sigma event.2)))
            stateRelative.links := by
  rw [processBrauer_loops_eq_addJoinEventLoops atoms stateRelative,
    brauerWordJoinEvents_ofRelativeWireSim sigma atoms stateCanonical stateRelative boundaryLength
      inRange tracks sim, zeroInternal, Nat.add_zero]

/-- The relative run's final wires are the `sigma`-image of the canonical run's final wires. -/
theorem processBrauer_openWires_ofRelativeSim (sigma : Nat → Nat)
    (atoms : List BrauerAtom) (stateCanonical stateRelative : WireState)
    (sim : MatchingRelativeWireSim sigma stateCanonical stateRelative) :
    (processBrauer stateRelative atoms).openWires
      = (processBrauer stateCanonical atoms).openWires.map sigma :=
  (processBrauer_relativeWireSim sigma atoms stateCanonical stateRelative sim).openMap

/-! ## The mid-state instantiations (at the concrete `relativeWireMap`, over the canonical seed) -/

/-- ★ **Mid-state links read-off** — the port of `processSpine_links_ofMidState`. -/
theorem processBrauer_links_ofMidState (midState : WireState) (boundaryLength : Nat)
    (atoms : List BrauerAtom)
    (inRange : BrauerWordInRange boundaryLength atoms)
    (midTracks : midState.openWires.length = boundaryLength) :
    (processBrauer midState atoms).links
      = applyJoinEvents
          ((brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atoms).map
            (fun event =>
              (relativeWireMap midState.openWires midState.nextFresh event.1,
                relativeWireMap midState.openWires midState.nextFresh event.2)))
          midState.links :=
  processBrauer_links_ofRelativeSim
    (relativeWireMap midState.openWires midState.nextFresh) atoms
    (canonicalMatchingSeed boundaryLength) midState boundaryLength inRange
    (canonicalMatchingSeed_wireCount boundaryLength)
    (matchingRelativeWireSim_initial_ofTracks midState boundaryLength midTracks)

/-- ★ **Mid-state loops read-off** — the port of `processSpine_loops_ofMidState` (no freshness needed). -/
theorem processBrauer_loops_ofMidState (midState : WireState) (boundaryLength : Nat)
    (atoms : List BrauerAtom)
    (inRange : BrauerWordInRange boundaryLength atoms)
    (zeroInternal : brauerWordInternalLoops atoms = 0)
    (midTracks : midState.openWires.length = boundaryLength) :
    (processBrauer midState atoms).loops
      = midState.loops
        + countJoinEventLoops
            ((brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atoms).map
              (fun event =>
                (relativeWireMap midState.openWires midState.nextFresh event.1,
                  relativeWireMap midState.openWires midState.nextFresh event.2)))
            midState.links :=
  processBrauer_loops_ofRelativeSim
    (relativeWireMap midState.openWires midState.nextFresh) atoms
    (canonicalMatchingSeed boundaryLength) midState boundaryLength inRange
    (canonicalMatchingSeed_wireCount boundaryLength) zeroInternal
    (matchingRelativeWireSim_initial_ofTracks midState boundaryLength midTracks)

/-- **Mid-state wires read-off** — the port of `processSpine_openWires_ofMidState`. -/
theorem processBrauer_openWires_ofMidState (midState : WireState) (boundaryLength : Nat)
    (atoms : List BrauerAtom)
    (midTracks : midState.openWires.length = boundaryLength) :
    (processBrauer midState atoms).openWires
      = (processBrauer (canonicalMatchingSeed boundaryLength) atoms).openWires.map
          (relativeWireMap midState.openWires midState.nextFresh) :=
  processBrauer_openWires_ofRelativeSim
    (relativeWireMap midState.openWires midState.nextFresh) atoms
    (canonicalMatchingSeed boundaryLength) midState
    (matchingRelativeWireSim_initial_ofTracks midState boundaryLength midTracks)

/-! ## Reachable-state open-wire distinctness (to construct the zone discipline)

The zone `discipline` (`RelativeWireZoneDiscipline`) the headline consumes is `relativeWireZoneDiscipline_ofState`
applied to freshness + open-wire distinctness.  Freshness is the shipped Brauer invariant; distinctness needs the
generic-width analog of the spine's `processSpine_fromSeed_wireListDistinct`, built here from two positional read
lemmas over `natListRemoveManyAt` (in range) plus the shipped fresh-block distinctness kit. -/

/-- Below the removed window a block removal reads the original positionally.  Structural on the removal's matcher. -/
theorem natListGetAt_removeManyAt_below :
    (wires : List Nat) → (position count index : Nat) → index < position →
    natListGetAt (natListRemoveManyAt wires position count) index = natListGetAt wires index
  | wires, position, 0, _, _ => by rw [removeManyAt_zero wires position]
  | [], _, _ + 1, _, _ => rfl
  | _ :: _, 0, _ + 1, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | headWire :: rest, position + 1, count, index, indexBelow => by
      rw [removeManyAt_succ_cons headWire rest position count]
      cases index with
      | zero => rfl
      | succ innerIndex =>
          show natListGetAt (natListRemoveManyAt rest position count) innerIndex = natListGetAt rest innerIndex
          exact natListGetAt_removeManyAt_below rest position count innerIndex
            (Nat.lt_of_succ_lt_succ indexBelow)

/-- At or above the removed window (in range) a block removal reads the original shifted up by the removed count. -/
theorem natListGetAt_removeManyAt_atOrAbove :
    (wires : List Nat) → (position count index : Nat) → position ≤ index →
    (∃ leftover, wires.length = position + count + leftover) →
    index < (natListRemoveManyAt wires position count).length →
    natListGetAt (natListRemoveManyAt wires position count) index = natListGetAt wires (index + count)
  | wires, position, 0, index, _, _, _ => by
      rw [removeManyAt_zero wires position, Nat.add_zero]
  | [], position, count + 1, index, _, fitsWitness, _ => by
      obtain ⟨leftover, lengthEq⟩ := fitsWitness
      have contra : (0 : Nat) = Nat.succ (position + count + leftover) := by
        have e : ([] : List Nat).length = position + (count + 1) + leftover := lengthEq
        rw [Nat.add_succ, Nat.succ_add] at e
        exact e
      exact Nat.noConfusion contra
  | headWire :: rest, 0, count + 1, index, _, fitsWitness, indexInRange => by
      rw [removeManyAt_zero_cons headWire rest count]
      obtain ⟨leftover, lengthEq⟩ := fitsWitness
      have tailFits : ∃ leftoverTail, rest.length = 0 + count + leftoverTail := by
        refine ⟨leftover, ?_⟩
        have e : rest.length + 1 = 0 + (count + 1) + leftover := lengthEq
        apply addOneCancelLocal
        rw [e, Nat.zero_add, Nat.zero_add, Nat.add_right_comm count 1 leftover]
      have tailInRange : index < (natListRemoveManyAt rest 0 count).length := by
        rw [removeManyAt_zero_cons headWire rest count] at indexInRange
        exact indexInRange
      rw [natListGetAt_removeManyAt_atOrAbove rest 0 count index (Nat.zero_le index) tailFits tailInRange]
      rfl
  | headWire :: rest, position + 1, count, index, positionLe, fitsWitness, indexInRange => by
      rw [removeManyAt_succ_cons headWire rest position count]
      cases index with
      | zero => exact absurd positionLe (Nat.not_succ_le_zero position)
      | succ innerIndex =>
          obtain ⟨leftover, lengthEq⟩ := fitsWitness
          have tailFits : ∃ leftoverTail, rest.length = position + count + leftoverTail := by
            refine ⟨leftover, ?_⟩
            have e : rest.length + 1 = position + 1 + count + leftover := lengthEq
            apply addOneCancelLocal
            rw [e, Nat.add_right_comm position 1 count, Nat.add_right_comm (position + count) 1 leftover]
          have tailInRange : innerIndex < (natListRemoveManyAt rest position count).length := by
            rw [removeManyAt_succ_cons headWire rest position count] at indexInRange
            exact Nat.lt_of_succ_lt_succ indexInRange
          show natListGetAt (natListRemoveManyAt rest position count) innerIndex
            = natListGetAt (headWire :: rest) (innerIndex + 1 + count)
          rw [natListGetAt_removeManyAt_atOrAbove rest position count innerIndex
              (Nat.le_of_succ_le_succ positionLe) tailFits tailInRange,
            Nat.add_right_comm innerIndex 1 count]
          rfl

/-- ★ **A generic-width block removal preserves positional distinctness (in range).**  The result is a positional
subsequence via the two read lemmas (monotone index injection), so distinctness transports from the original. -/
theorem wireListDistinct_natListRemoveManyAt (wires : List Nat) (position count leftover : Nat)
    (lengthDecomp : wires.length = position + count + leftover)
    (distinct : WireListDistinct wires) :
    WireListDistinct (natListRemoveManyAt wires position count) := by
  have removedLength : (natListRemoveManyAt wires position count).length = position + leftover :=
    natListRemoveManyAt_length_fits wires position count leftover lengthDecomp
  intro indexOne indexTwo oneLtTwo twoInRange
  have twoBelowRemoved : indexTwo < position + leftover := by rw [removedLength] at twoInRange; exact twoInRange
  have oneBelowRemoved : indexOne < position + leftover := Nat.lt_trans oneLtTwo twoBelowRemoved
  have shiftOneLt : position + leftover ≤ wires.length := by
    rw [lengthDecomp, Nat.add_right_comm position count leftover]
    exact Nat.le_add_right (position + leftover) count
  cases Nat.lt_or_ge indexOne position with
  | inl oneBelow =>
      rw [natListGetAt_removeManyAt_below wires position count indexOne oneBelow]
      cases Nat.lt_or_ge indexTwo position with
      | inl twoBelow =>
          rw [natListGetAt_removeManyAt_below wires position count indexTwo twoBelow]
          exact distinct indexOne indexTwo oneLtTwo (Nat.lt_of_lt_of_le twoBelowRemoved shiftOneLt)
      | inr twoAtOrAbove =>
          rw [natListGetAt_removeManyAt_atOrAbove wires position count indexTwo twoAtOrAbove
              ⟨leftover, lengthDecomp⟩ (by rw [removedLength]; exact twoBelowRemoved)]
          have oneLtShift : indexOne < indexTwo + count :=
            Nat.lt_of_lt_of_le oneLtTwo (Nat.le_add_right indexTwo count)
          have shiftInRange : indexTwo + count < wires.length := by
            rw [lengthDecomp, Nat.add_right_comm position count leftover, Nat.add_comm (position + leftover) count,
              Nat.add_comm indexTwo count]
            exact Nat.add_lt_add_left twoBelowRemoved count
          exact distinct indexOne (indexTwo + count) oneLtShift shiftInRange
  | inr oneAtOrAbove =>
      have twoAtOrAbove : position ≤ indexTwo := Nat.le_of_lt (Nat.lt_of_le_of_lt oneAtOrAbove oneLtTwo)
      rw [natListGetAt_removeManyAt_atOrAbove wires position count indexOne oneAtOrAbove
          ⟨leftover, lengthDecomp⟩ (by rw [removedLength]; exact oneBelowRemoved),
        natListGetAt_removeManyAt_atOrAbove wires position count indexTwo twoAtOrAbove
          ⟨leftover, lengthDecomp⟩ (by rw [removedLength]; exact twoBelowRemoved)]
      have shiftLt : indexOne + count < indexTwo + count := Nat.add_lt_add_right oneLtTwo count
      have shiftInRange : indexTwo + count < wires.length := by
        rw [lengthDecomp, Nat.add_right_comm position count leftover, Nat.add_comm (position + leftover) count,
          Nat.add_comm indexTwo count]
        exact Nat.add_lt_add_left twoBelowRemoved count
      exact distinct (indexOne + count) (indexTwo + count) shiftLt shiftInRange

/-- ★ **One in-range `stepWiring` step preserves open-wire distinctness.**  The surviving old wires (distinct, all
below `nextFresh`) are spliced with the fresh output block (distinct, all at or above `nextFresh`) via the shipped
`wireListDistinct_insertFreshBlockAnyPosition`. -/
theorem stepWiring_wireListDistinct (state : WireState) (position rightLen : Nat) (desc : WiringDesc)
    (fits : state.openWires.length = position + desc.inputCount + rightLen)
    (fresh : WiringDescStateFresh state) (distinct : WireListDistinct state.openWires) :
    WireListDistinct (stepWiring state position desc).openWires := by
  rw [stepWiring_openWires_rfl state position desc]
  refine wireListDistinct_insertFreshBlockAnyPosition
    (natListRemoveManyAt state.openWires position desc.inputCount) position
    ((List.range desc.outputCount).map (· + state.nextFresh)) state.nextFresh
    (wireListDistinct_natListRemoveManyAt state.openWires position desc.inputCount rightLen fits distinct)
    (wireListDistinct_freshBlock state.nextFresh desc.outputCount)
    (fun wire wireMem => fresh.1 wire (mem_natListRemoveManyAt state.openWires position desc.inputCount wire wireMem))
    ?_
  intro leg legMem
  exact mem_mapAdd_ge state.nextFresh (List.range desc.outputCount) leg legMem

/-- ★ **The whole in-range `processBrauer` fold preserves open-wire distinctness.**  Structural on the word, threading
the `BrauerWordInRange` discipline (each atom's window fits) alongside freshness / positivity / distinctness. -/
theorem processBrauer_wireListDistinct :
    (atoms : List BrauerAtom) → (state : WireState) → (boundaryLength : Nat) →
    BrauerWordInRange boundaryLength atoms →
    state.openWires.length = boundaryLength →
    WiringDescStateFresh state → 0 < state.nextFresh → WireListDistinct state.openWires →
    WireListDistinct (processBrauer state atoms).openWires
  | [], state, _, _, _, _, _, distinct => distinct
  | atom :: rest, state, boundaryLength, inRange, tracks, fresh, nfPos, distinct => by
      obtain ⟨rightLen, fits, _, tailInRange⟩ := brauerWordInRange_tail inRange
      have fitsLength : state.openWires.length
          = atom.position + atom.wiring.inputCount + rightLen := by rw [tracks]; exact fits
      show WireListDistinct (processBrauer (stepWiring state atom.position atom.wiring) rest).openWires
      exact processBrauer_wireListDistinct rest (stepWiring state atom.position atom.wiring)
        (atom.position + atom.wiring.outputCount + rightLen) tailInRange
        (stepWiring_openWires_length_fits state atom.position rightLen atom.wiring fitsLength)
        (wiringDescStateFresh_stepWiring state atom.position atom.wiring fresh nfPos)
        (Nat.lt_of_lt_of_le nfPos (Nat.le_add_right state.nextFresh atom.wiring.outputCount))
        (stepWiring_wireListDistinct state atom.position rightLen atom.wiring fitsLength fresh distinct)

/-- ★ **Every in-range reachable diagram state has positionally distinct open wires.** -/
theorem brauerReachable_wireListDistinct (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (inRange : BrauerWordInRange bottomCount prefixAtoms) :
    WireListDistinct (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires :=
  processBrauer_wireListDistinct prefixAtoms (brauerSeed bottomCount) bottomCount inRange
    (rangeLengthLocal bottomCount)
    ⟨fun _ wireInRange => mem_range_imp_lt wireInRange, fun _ edgeInNil => by cases edgeInNil⟩
    bottomPos (canonicalMatchingSeed_wireListDistinct bottomCount)

/-- ★ **The zone discipline at every in-range reachable diagram state.**  `relativeWireZoneDiscipline_ofState`
applied to the shipped freshness invariant + the distinctness invariant above. -/
theorem relativeWireZoneDiscipline_ofBrauerReachable (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (inRange : BrauerWordInRange bottomCount prefixAtoms) :
    RelativeWireZoneDiscipline (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires
      (processBrauer (brauerSeed bottomCount) prefixAtoms).nextFresh :=
  relativeWireZoneDiscipline_ofState (processBrauer (brauerSeed bottomCount) prefixAtoms)
    (brauerReachable_conditions bottomCount bottomPos prefixAtoms).fresh
    (brauerReachable_wireListDistinct bottomCount bottomPos prefixAtoms inRange)

/-! ## The headline — two words with equal canonical extracts extract equally from any shared mid-state -/

/-- ★ **KEYSTONE14 — the two-word functoriality at `processBrauer`.**  Two Brauer words whose CANONICAL runs (from the
seed of width `boundaryLength`) extract to the SAME `DiagramType` extract identically from ANY shared disciplined
mid-state — crossing included.  This is the port of `processSpine_extract_eq_ofCanonicalExtractEq`; the proof mirrors
the source's three-leg assembly verbatim, reusing the engine-agnostic event-list gluings
(`extractDiagram_eq_of_connectivityView`, `compositeBoundaryView_agrees_ofExtractEq`,
`countJoinEventLoops_overMidLinks_agrees_ofViewSim`, `matchingConnectivityViewSim_ofExtractEq`) and the Brauer
relativization stack (`processBrauer_{links,loops,openWires}_ofMidState`).  The mid-state provenance is exactly the
reachable-state invariants (`WiringDescStateFresh` / forest / zone discipline / base bound) the Brauer engine
propagates.  No freshness is needed for the loop leg (the arc fold accumulates the count by construction), and the
crossing needs no special case (the wire simulation ignores the arcs). -/
theorem processBrauer_extract_eq_ofCanonicalExtractEq
    (baseCount boundaryLength : Nat) (midState : WireState)
    (atomsAlpha atomsBeta : List BrauerAtom)
    (inRangeAlpha : BrauerWordInRange boundaryLength atomsAlpha)
    (inRangeBeta : BrauerWordInRange boundaryLength atomsBeta)
    (zeroInternalAlpha : brauerWordInternalLoops atomsAlpha = 0)
    (zeroInternalBeta : brauerWordInternalLoops atomsBeta = 0)
    (midTracks : midState.openWires.length = boundaryLength)
    (fresh : WiringDescStateFresh midState)
    (forest : isUnionFindForest midState.links)
    (discipline : RelativeWireZoneDiscipline midState.openWires midState.nextFresh)
    (baseBelow : baseCount ≤ midState.nextFresh)
    (extractsEqual :
      extractDiagram boundaryLength (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha)
        = extractDiagram boundaryLength (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta)) :
    extractDiagram baseCount (processBrauer midState atomsAlpha)
      = extractDiagram baseCount (processBrauer midState atomsBeta) := by
  have linksAlpha : (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).links
      = applyJoinEvents (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha) [] :=
    processBrauer_links_eq_applyJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength)
  have linksBeta : (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta).links
      = applyJoinEvents (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta) [] :=
    processBrauer_links_eq_applyJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength)
  have loopsAlpha : (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).loops
      = countJoinEventLoops (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha) [] := by
    rw [processBrauer_loops_eq_addJoinEventLoops atomsAlpha (canonicalMatchingSeed boundaryLength),
      zeroInternalAlpha]
    show (0 : Nat)
        + countJoinEventLoops (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha) [] + 0
      = countJoinEventLoops (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha) []
    rw [Nat.add_zero, Nat.zero_add]
  have loopsBeta : (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta).loops
      = countJoinEventLoops (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta) [] := by
    rw [processBrauer_loops_eq_addJoinEventLoops atomsBeta (canonicalMatchingSeed boundaryLength),
      zeroInternalBeta]
    show (0 : Nat)
        + countJoinEventLoops (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta) [] + 0
      = countJoinEventLoops (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta) []
    rw [Nat.add_zero, Nat.zero_add]
  have viewSim : MatchingConnectivityViewSim boundaryLength
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta) :=
    matchingConnectivityViewSim_ofExtractEq boundaryLength
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta) extractsEqual
  have baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midState.links →
      leftNode < midState.nextFresh ∧ rightNode < midState.nextFresh :=
    fun leftNode rightNode membership => fresh.2 (leftNode, rightNode) membership
  have compositeLengthAlpha : (processBrauer midState atomsAlpha).openWires.length
      = (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length := by
    rw [processBrauer_openWires_ofMidState midState boundaryLength atomsAlpha midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  have compositeLengthBeta : (processBrauer midState atomsBeta).openWires.length
      = (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta).openWires.length := by
    rw [processBrauer_openWires_ofMidState midState boundaryLength atomsBeta midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  apply extractDiagram_eq_of_connectivityView
  · rw [compositeLengthAlpha, compositeLengthBeta]
    exact viewSim.lengthEq
  · rw [processBrauer_loops_ofMidState midState boundaryLength atomsAlpha inRangeAlpha zeroInternalAlpha
        midTracks,
      processBrauer_loops_ofMidState midState boundaryLength atomsBeta inRangeBeta zeroInternalBeta
        midTracks,
      countJoinEventLoops_overMidLinks_agrees_ofViewSim midState.openWires midState.nextFresh discipline
        boundaryLength midTracks
        (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha)
        (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta)
        (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha)
        (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta)
        midState.links linksAlpha linksBeta loopsAlpha loopsBeta viewSim forest baseBounded]
  · intro firstIndex secondIndex firstBound secondBound
    have firstBoundCanonical : firstIndex < baseCount
        + (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length := by
      rw [← compositeLengthAlpha]
      exact firstBound
    have secondBoundCanonical : secondIndex < baseCount
        + (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length := by
      rw [← compositeLengthAlpha]
      exact secondBound
    show isSameComponent (processBrauer midState atomsAlpha).links
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsAlpha).openWires) firstIndex)
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsAlpha).openWires) secondIndex)
      = isSameComponent (processBrauer midState atomsBeta).links
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsBeta).openWires) firstIndex)
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsBeta).openWires) secondIndex)
    rw [processBrauer_links_ofMidState midState boundaryLength atomsAlpha inRangeAlpha midTracks,
      processBrauer_openWires_ofMidState midState boundaryLength atomsAlpha midTracks,
      processBrauer_links_ofMidState midState boundaryLength atomsBeta inRangeBeta midTracks,
      processBrauer_openWires_ofMidState midState boundaryLength atomsBeta midTracks]
    exact compositeBoundaryView_agrees_ofExtractEq midState.openWires midState.nextFresh discipline
      boundaryLength midTracks baseCount baseBelow
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta)
      (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta)
      midState.links linksAlpha linksBeta extractsEqual forest baseBounded
      firstIndex secondIndex firstBoundCanonical secondBoundCanonical

/-! ## The whisker bridge — feed the functoriality into the shipped `BrauerConv.whisker` move -/

/-- ★ **KEYSTONE14 — the two-word functoriality DISCHARGES the contextual whisker.**  For any in-range prefix and two
in-range zero-internal words whose CANONICAL runs (at the post-prefix boundary width) extract equally, the two words
fired after the prefix are `BrauerConv`-convertible.  The three whisker legs (equal length / loops / boundary
same-component view) come out of `matchingConnectivityViewSim_ofExtractEq` on the port's output; the reachable-state
provenance (freshness / forest / zone discipline / base bound) is fully discharged from the shipped Brauer invariants
plus the distinctness invariant.  This is the direct supplier of `relationAgrees` the r13 markers named — it BYPASSES
the H1/H2 boundary-reconnection assembler, producing the whisker's boundary view straight from the extract equality. -/
theorem brauerConv_whisker_ofCanonicalExtractEq (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms wordLeft wordRight : List BrauerAtom)
    (prefixInRange : BrauerWordInRange bottomCount prefixAtoms)
    (inRangeLeft :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length wordLeft)
    (inRangeRight :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length wordRight)
    (zeroInternalLeft : brauerWordInternalLoops wordLeft = 0)
    (zeroInternalRight : brauerWordInternalLoops wordRight = 0)
    (seedExtractEq :
      extractDiagram (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
          (processBrauer (canonicalMatchingSeed
            (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordLeft)
        = extractDiagram (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
          (processBrauer (canonicalMatchingSeed
            (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordRight)) :
    BrauerConv bottomCount (prefixAtoms ++ wordLeft) (prefixAtoms ++ wordRight) := by
  have conditions := brauerReachable_conditions bottomCount bottomPos prefixAtoms
  have extractEq := processBrauer_extract_eq_ofCanonicalExtractEq bottomCount
    (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
    (processBrauer (brauerSeed bottomCount) prefixAtoms)
    wordLeft wordRight inRangeLeft inRangeRight zeroInternalLeft zeroInternalRight rfl
    conditions.fresh conditions.forest
    (relativeWireZoneDiscipline_ofBrauerReachable bottomCount bottomPos prefixAtoms prefixInRange)
    conditions.bottomLe seedExtractEq
  have viewSim := matchingConnectivityViewSim_ofExtractEq bottomCount
    (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordLeft)
    (processBrauer (processBrauer (brauerSeed bottomCount) prefixAtoms) wordRight) extractEq
  exact BrauerConv.whisker bottomCount prefixAtoms wordLeft wordRight
    viewSim.lengthEq viewSim.loopsEq
    (fun firstIndex secondIndex firstBound secondBound =>
      viewSim.viewAgrees firstIndex secondIndex
        (viewSim.lengthEq ▸ firstBound) (viewSim.lengthEq ▸ secondBound))

/-! ## Non-vacuity — the 5 relations whiskered after a NON-trivial boundary-preserving prefix, via the FUNCTORIALITY

Each relation, whiskered after a prefix that preserves its own boundary width, is `BrauerConv`-convertible by the
port — the seed-extract premise is the shipped `*_diagram_sound` (the prefix keeps the boundary at the relation's
width, so no horizontal pad/shift is needed).  Unlike the r13 `decide` witnesses, these are the FUNCTORIAL supply:
the same bridge closes the relation after EVERY boundary-preserving prefix (a crossing / identity chain), demonstrated
here on a representative.  The `BrauerWordInRange` derivations are `rfl`/`decide` (concrete words). -/

/-- R2 (crossing involutivity) whiskered after a prefix crossing, via the FUNCTORIALITY port (not `decide`): the seed
premise is `crossingInvolution_diagram_sound`.  Boundary 2 is preserved by the prefix crossing. -/
theorem brauerConv_whisker_crossingInvolution_functorial :
    BrauerConv 2 ([crossingAt 0] ++ [crossingAt 0, crossingAt 0]) ([crossingAt 0] ++ ([] : List BrauerAtom)) :=
  brauerConv_whisker_ofCanonicalExtractEq 2 (by decide) [crossingAt 0] [crossingAt 0, crossingAt 0] []
    (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))
    (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))
      : BrauerWordInRange 2 [crossingAt 0, crossingAt 0])
    (BrauerWordInRange.nil _) rfl rfl crossingInvolution_diagram_sound

/-- R3 (Yang–Baxter) whiskered after a prefix crossing (boundary 3 preserved), via the port: the seed premise is
`yangBaxter_diagram_sound`. -/
theorem brauerConv_whisker_yangBaxter_functorial :
    BrauerConv 3 ([crossingAt 0] ++ yangBaxterLhsWord) ([crossingAt 0] ++ yangBaxterRhsWord) :=
  brauerConv_whisker_ofCanonicalExtractEq 3 (by decide) [crossingAt 0] yangBaxterLhsWord yangBaxterRhsWord
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3))
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3)))
      : BrauerWordInRange 3 yangBaxterLhsWord)
    (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
        (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 3)))
      : BrauerWordInRange 3 yangBaxterRhsWord)
    rfl rfl yangBaxter_diagram_sound

/-- R1 (cap slides past a crossing) whiskered after a prefix crossing (boundary 3 preserved), via the port: the seed
premise is `capSlide_diagram_sound`. -/
theorem brauerConv_whisker_capSlide_functorial :
    BrauerConv 3 ([crossingAt 0] ++ capSlideRelation.lhs) ([crossingAt 0] ++ capSlideRelation.rhs) :=
  brauerConv_whisker_ofCanonicalExtractEq 3 (by decide) [crossingAt 0] capSlideRelation.lhs capSlideRelation.rhs
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3))
    (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (capAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 1))
      : BrauerWordInRange 3 capSlideRelation.lhs)
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (capAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 1))
      : BrauerWordInRange 3 capSlideRelation.rhs)
    rfl rfl capSlide_diagram_sound

/-- S1 (snake) whiskered after a prefix identity strand (boundary 1 preserved), via the port: the seed premise is
`snake_diagram_sound`. -/
theorem brauerConv_whisker_snake_functorial :
    BrauerConv 1 ([identityStrandAt 0] ++ snakeRelation.lhs) ([identityStrandAt 0] ++ snakeRelation.rhs) :=
  brauerConv_whisker_ofCanonicalExtractEq 1 (by decide) [identityStrandAt 0] snakeRelation.lhs snakeRelation.rhs
    (BrauerWordInRange.cons (identityStrandAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))
    (BrauerWordInRange.cons (cupAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (capAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 1))
      : BrauerWordInRange 1 snakeRelation.lhs)
    (BrauerWordInRange.nil _) rfl rfl snake_diagram_sound

/-- S2 (mirror snake) whiskered after a prefix identity strand (boundary 1 preserved), via the port: the seed premise
is `snakeMirror_diagram_sound`. -/
theorem brauerConv_whisker_snakeMirror_functorial :
    BrauerConv 1 ([identityStrandAt 0] ++ snakeMirrorRelation.lhs) ([identityStrandAt 0] ++ snakeMirrorRelation.rhs) :=
  brauerConv_whisker_ofCanonicalExtractEq 1 (by decide) [identityStrandAt 0]
    snakeMirrorRelation.lhs snakeMirrorRelation.rhs
    (BrauerWordInRange.cons (identityStrandAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))
    (BrauerWordInRange.cons (cupAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (capAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 1))
      : BrauerWordInRange 1 snakeMirrorRelation.lhs)
    (BrauerWordInRange.nil _) rfl rfl snakeMirror_diagram_sound

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the two-word FUNCTORIALITY at `processBrauer` is SHIPPED (the r13-named missing piece).**
`processBrauer_extract_eq_ofCanonicalExtractEq`: two Brauer words whose canonical runs extract equally extract
identically from ANY shared disciplined mid-state — crossing included.  It is the exact port of the walking-adjunction
SAT-D5 headline `processSpine_extract_eq_ofCanonicalExtractEq`, reusing the engine-agnostic event-list gluings
(VIEW / LOOP legs + reassembly) verbatim and supplying the Brauer relativization stack
(`stepWiring_relativeWireSim`, `brauerWordJoinEvents_ofRelativeWireSim`,
`processBrauer_{links,loops,openWires}_ofMidState`), the `BrauerWordInRange` discipline, the unconditional loop
reification `processBrauer_loops_eq_addJoinEventLoops`, and the reachable-state distinctness invariant discharging the
zone discipline.  The crossing needs NO special case (the wire simulation ignores arcs).  `= true`. -/
def fxBrauer_hasTwoWordFunctorialityPort : Bool := true

/-- ★ **Honesty marker — the functoriality DISCHARGES the contextual whisker, off the H1/H2 assembler.**
`brauerConv_whisker_ofCanonicalExtractEq` produces `BrauerConv (prefix ++ wordLeft) (prefix ++ wordRight)` from the
seed-extract equality alone (the three whisker legs come from `matchingConnectivityViewSim_ofExtractEq` on the port's
output), bypassing the r13 boundary-reconnection (H1) + boundary-two-sided (H2) route entirely.  `= true`. -/
def fxBrauer_hasWhiskerFromFunctoriality : Bool := true

/-- ★ **Honesty marker — the 5 relations close FUNCTORIALLY in NON-trivial boundary-preserving context (5/5).**
`brauerConv_whisker_{crossingInvolution,yangBaxter,capSlide,snake,snakeMirror}_functorial`: each of the five Brauer
relations, whiskered after a NON-trivial prefix that preserves its own boundary width (a prefix crossing for R1 / R2 /
R3, a prefix identity strand for the snakes), is `BrauerConv`-convertible via the functoriality port, with the
seed-extract premise supplied by the shipped `*_diagram_sound`.  Unlike the r13 `decide` witnesses, this is the
FUNCTORIAL supply of `relationAgrees`: the SAME bridge closes each relation after every boundary-preserving prefix.
`= true`. -/
def fxBrauer_hasFunctorialRelationAgreesFiveOfFive : Bool := true

/-- **Honesty marker — `fxBrauer_hasBrauerSoundness` STAYS `false`; the residual is now EXACTLY the horizontal
pad/shift congruence.**  The functoriality port supplies `relationAgrees` (hence the whisker, hence `BrauerConv`) for
every relation after any BOUNDARY-PRESERVING prefix — the vertical-composition (whiskerLeft) direction, closed here
5/5.  The FULL soundness flip additionally needs the BOUNDARY-CHANGING (horizontal tensor / pad + offset) direction:
the relation word fired at an offset in a WIDER boundary must extract equally to its rhs there — the Brauer analog of
the spine's `MatchingLeftPadCongruence` / `MatchingRightPadCongruence`, which is genuinely UNBUILT (not refuted;
Selinger arXiv:0908.3347 Thm 3.12 / 4.33 and Lehrer–Zhang arXiv:1207.5889 Thm 3.4 confirm the mathematics).  The port
does NOT supply this (it transports a fixed word from the seed to a mid-state; it neither widens the seed nor shifts
positions).  So `fxBrauer_hasBrauerSoundness` stays `false`, its residual sharpened from "the five relations' uniform
`relationAgrees`" to precisely "the horizontal pad/shift congruence feeding `extractsEqual` at boundary-changing
prefixes".  `= false`. -/
def fxBrauer_hasBrauerSoundnessResidualIsPadShift : Bool := false

end FX1Poly.Polygraph
