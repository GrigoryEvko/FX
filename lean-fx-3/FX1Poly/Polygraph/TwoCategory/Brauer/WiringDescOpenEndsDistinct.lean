import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCircleLoops
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # BRAUER r30 B2 (cap side) — THE ZERO-LOOPS INVARIANT `BrauerOpenEndsDistinct`, seed + the cap side

The r29 loops wall named the boundary-word-adds-0-loops leg: `(processBrauer (brauerSeed bc) boundaryWord).loops = 0`,
which needs a FRESH connectivity invariant — no cap in the corrected fold ever fires on a pre-connected pair, so no
cap ever closes a loop.  This file ships the invariant itself and the CAP side of its evolution, a direct port of the
FC-3 pure-cap route (`WalkingString/StringArcCapHeadLoops.lean`) from `ArcWireState`/`stepCapArc` to the generic
`WireState`/`stepWiring … capWiring` engine.

## The invariant

`BrauerOpenEndsDistinct state := ∀ lo < hi < openWires.length, isSameComponent links openWires[lo] openWires[hi] =
false` — component-level distinctness, strictly stronger than node-id distinctness.  A cap fires at position `0` on
`openWires[0], openWires[1]`, which the invariant makes DISTINCT, so it closes NO loop
(`stepWiring_cap_loops_ofDistinct`) and merges only that consumed pair — leaving every SURVIVING pair distinct
(`brauerOpenEndsDistinct_stepWiringCap`, a cap never joins two survivors).

## Ships here (the CAP side)

  * ★ `BrauerOpenEndsDistinct` + `brauerOpenEndsDistinct_seed` (S): the fresh seed is distinct (empty links ⟹ every
    node its own root; distinct range positions read distinct values).
  * ★ `stepWiring_cap_links`: a cap's link update is the unconditional join of its two read wires (the no-op bridge).
  * ★ `stepWiring_cap_loops_ofDistinct` (C1): a cap on a distinct head pair closes NO loop.
  * ★ `brauerOpenEndsDistinct_stepWiringCap` (C2): a cap at position `0` preserves the invariant.

## Honest scope

This is the CAP side only.  The full `(processBrauer (brauerSeed bc) boundaryWord).loops = 0` additionally needs the
CROSSING-preserves-distinctness lemma (the heaviest, via the shipped transposition view) and the phase-fold assembly;
those stay the named r31 residual, so `fxBrauer_hasFoldLoopsCorrectness` (the loops wall) stays `false` and NO master
flips this round.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Section 0 — local range + `Bool`-beq plumbing (propext-free, per-file copy) -/

private theorem rangeLoopLengthOED : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      rw [show List.range.loop (count + 1) accumulated = List.range.loop count (count :: accumulated) from rfl,
        rangeLoopLengthOED count (count :: accumulated)]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [Nat.add_succ, Nat.succ_add]

private theorem rangeLengthOED (count : Nat) : (List.range count).length = count :=
  (rangeLoopLengthOED count []).trans (Nat.add_zero count)

private theorem rangeLoopGetPastOED : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetPastOED count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetBelowOED : (count : Nat) → (accumulated : List Nat) → (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, index, h => absurd h (Nat.not_lt_zero index)
  | count + 1, accumulated, index, h => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetBelowOED count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ h) atLeast
          have past := rangeLoopGetPastOED count (count :: accumulated) 0
          rw [Nat.zero_add] at past
          rw [indexEq]; exact past

private theorem rangeGetBelowOED (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetBelowOED count [] index indexBelow

private theorem neOfLtLeftOED {smaller larger : Nat} (isSmaller : smaller < larger) : smaller ≠ larger :=
  fun valuesEqual => Nat.lt_irrefl smaller (Nat.lt_of_lt_of_le isSmaller (Nat.le_of_eq valuesEqual.symm))

private theorem natBeqFalseOED (leftNode rightNode : Nat) (notEqual : leftNode ≠ rightNode) :
    (leftNode == rightNode) = false := by
  cases beqCase : leftNode == rightNode with
  | true => exact absurd (of_decide_eq_true beqCase) notEqual
  | false => rfl

/-! ## Section 1 — the invariant + the fresh seed -/

/-- ★ **The open-ends distinctness invariant** — every two DISTINCT open positions read wires in DIFFERENT union-find
components.  The Brauer (`WireState`) port of the FC-3 `ArcOpenEndsDistinct`; component-level distinctness, strictly
stronger than node-id distinctness (two distinct ids can share a component). -/
def BrauerOpenEndsDistinct (state : WireState) : Prop :=
  ∀ lowPosition highPosition : Nat,
    lowPosition < highPosition → highPosition < state.openWires.length →
    isSameComponent state.links (natListGetAt state.openWires lowPosition)
        (natListGetAt state.openWires highPosition) = false

/-- ★ **(S) The fresh seed satisfies the invariant.**  At `brauerSeed bottomCount` the links are empty (every node is
its own root) and the open wires are `List.range bottomCount`, so distinct positions read distinct values — no
same-component open pair exists. -/
theorem brauerOpenEndsDistinct_seed (bottomCount : Nat) : BrauerOpenEndsDistinct (brauerSeed bottomCount) := by
  intro lowPosition highPosition lowLtHigh highInRange
  show isSameComponent [] (natListGetAt (List.range bottomCount) lowPosition)
      (natListGetAt (List.range bottomCount) highPosition) = false
  have highBelow : highPosition < bottomCount := by
    have hlen : highPosition < (List.range bottomCount).length := highInRange
    rwa [rangeLengthOED bottomCount] at hlen
  rw [rangeGetBelowOED bottomCount lowPosition (Nat.lt_trans lowLtHigh highBelow),
    rangeGetBelowOED bottomCount highPosition highBelow]
  show (lowPosition == highPosition) = false
  exact natBeqFalseOED lowPosition highPosition (neOfLtLeftOED lowLtHigh)

/-! ## Section 2 — the cap's link update is an unconditional join -/

/-- ★ **A cap at position `0`'s link update is the UNCONDITIONAL join of its two read wires.**  Via the link
reification `stepWiring_links_eq_applyJoinEvents`: the cap's decoded trace is `[(firstWire, secondWire)]`, whose event
fold is exactly `unionFindJoin links firstWire secondWire` (the outer same-component test that drives the loop count is
redundant for links). -/
theorem stepWiring_cap_links (state : WireState) (firstWire secondWire : Nat) (rest : List Nat)
    (hopen : state.openWires = firstWire :: secondWire :: rest) :
    (stepWiring state 0 capWiring).links = unionFindJoin state.links firstWire secondWire := by
  rw [stepWiring_links_eq_applyJoinEvents state 0 capWiring]
  have htrace : wiringArcEvents (stepWiringInputNodes state 0 capWiring) (stepWiringOutputNodes state capWiring)
        capWiring.inputCount capWiring.arcs
      = [(firstWire, secondWire)] := by
    show wiringArcEvents (natListSliceAt state.openWires 0 2) [] 2 [(0, 1)] = [(firstWire, secondWire)]
    rw [hopen]
    rfl
  rw [htrace]
  rfl

/-! ## Section 3 — (C1) a cap on a distinct pair closes no loop -/

/-- ★ **(C1) A cap at position `0`, fired on a DISTINCT head pair, closes NO loop.**  Via `stepWiring_loops_eq`: the
cap's single-arc trace `(firstWire, secondWire)` is NOT already connected (`distinct`), so `countJoinEventLoops`
contributes `0`.  The distinctness-driven mirror of `stepWiring_cap_loops_ofConnected`. -/
theorem stepWiring_cap_loops_ofDistinct (state : WireState) (firstWire secondWire : Nat) (rest : List Nat)
    (hopen : state.openWires = firstWire :: secondWire :: rest)
    (distinct : isSameComponent state.links firstWire secondWire = false) :
    (stepWiring state 0 capWiring).loops = state.loops := by
  rw [stepWiring_loops_eq state 0 capWiring]
  have htrace : wiringArcEvents (stepWiringInputNodes state 0 capWiring) (stepWiringOutputNodes state capWiring)
        capWiring.inputCount capWiring.arcs
      = [(firstWire, secondWire)] := by
    show wiringArcEvents (natListSliceAt state.openWires 0 2) [] 2 [(0, 1)] = [(firstWire, secondWire)]
    rw [hopen]
    rfl
  rw [htrace]
  show state.loops
      + ((isSameComponent state.links firstWire secondWire).toNat
          + countJoinEventLoops [] (unionFindJoin state.links firstWire secondWire))
      + capWiring.internalLoops = state.loops
  rw [distinct]
  rfl

/-! ## Section 4 — (C2) a cap preserves distinctness -/

/-- After a cap's merge `unionFindJoin links leftWire rightWire`, two probes SEPARATE from each other and from the LEFT
consumed wire stay in distinct components — the flat-disjunction characterization collapses on the two window misses.
The Brauer copy of the FC-3 `capMergedSurvivingSeparate` (generic on `links`). -/
private theorem capMergedSurvivingSeparateBrauer (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (leftWire rightWire probeOne probeTwo : Nat)
    (baseProbes : isSameComponent links probeOne probeTwo = false)
    (baseLeftOne : isSameComponent links leftWire probeOne = false)
    (baseLeftTwo : isSameComponent links leftWire probeTwo = false) :
    isSameComponent (unionFindJoin links leftWire rightWire) probeOne probeTwo = false := by
  rw [isSameComponent_unionFindJoin links forest leftWire rightWire probeOne probeTwo,
    baseProbes, baseLeftOne, baseLeftTwo]
  rfl

/-- ★ **(C2) A cap at position `0` preserves the distinctness invariant.**  The cap consumes `openWires[0]`,
`openWires[1]` (leaving `rest`) and merges them; every surviving pair `rest[lo], rest[hi]` reads `openWires[lo+2],
openWires[hi+2]`, both off the window `{0, 1}`, so they were distinct (invariant) and each is distinct from the
merged pair's left wire `openWires[0]` (invariant) — `capMergedSurvivingSeparateBrauer` keeps them distinct after the
join.  A cap never merges two survivors. -/
theorem brauerOpenEndsDistinct_stepWiringCap (state : WireState) (forest : isUnionFindForest state.links)
    (firstWire secondWire : Nat) (rest : List Nat)
    (hopen : state.openWires = firstWire :: secondWire :: rest)
    (distinct : BrauerOpenEndsDistinct state) :
    BrauerOpenEndsDistinct (stepWiring state 0 capWiring) := by
  intro lowPosition highPosition lowLtHigh highInRange
  have hCapOpen : (stepWiring state 0 capWiring).openWires = rest :=
    (stepWiring_cap_head state firstWire secondWire rest hopen forest).1
  have hCapLinks : (stepWiring state 0 capWiring).links = unionFindJoin state.links firstWire secondWire :=
    stepWiring_cap_links state firstWire secondWire rest hopen
  rw [hCapOpen] at highInRange
  have hlen : state.openWires.length = rest.length + 2 := by rw [hopen]; rfl
  have highPlusTwoBelow : highPosition + 2 < state.openWires.length :=
    hlen.symm ▸ Nat.add_lt_add_right highInRange 2
  have lowPlusTwoBelow : lowPosition + 2 < state.openWires.length :=
    hlen.symm ▸ Nat.add_lt_add_right (Nat.lt_trans lowLtHigh highInRange) 2
  have lowRead : natListGetAt rest lowPosition = natListGetAt state.openWires (lowPosition + 2) := by
    rw [hopen]; rfl
  have highRead : natListGetAt rest highPosition = natListGetAt state.openWires (highPosition + 2) := by
    rw [hopen]; rfl
  have firstRead : firstWire = natListGetAt state.openWires 0 := by rw [hopen]; rfl
  rw [hCapOpen, hCapLinks, lowRead, highRead]
  exact capMergedSurvivingSeparateBrauer state.links forest firstWire secondWire
    (natListGetAt state.openWires (lowPosition + 2)) (natListGetAt state.openWires (highPosition + 2))
    (distinct (lowPosition + 2) (highPosition + 2) (Nat.add_lt_add_right lowLtHigh 2) highPlusTwoBelow)
    (by rw [firstRead]; exact distinct 0 (lowPosition + 2) (Nat.succ_pos _) lowPlusTwoBelow)
    (by rw [firstRead]; exact distinct 0 (highPosition + 2) (Nat.succ_pos _) highPlusTwoBelow)

/-! ## Section 5 — the honesty marker -/

/-- ★★ **Honesty marker — the zero-loops invariant `BrauerOpenEndsDistinct` and its CAP side are SHIPPED (r30 B2).**
The invariant (`BrauerOpenEndsDistinct`, the FC-3 port to the generic `WireState`/`stepWiring` engine) holds at the
seed (`brauerOpenEndsDistinct_seed`, S), a cap on a distinct pair closes no loop (`stepWiring_cap_loops_ofDistinct`,
C1) via the unconditional-join link update (`stepWiring_cap_links`), and a cap at position `0` preserves the invariant
(`brauerOpenEndsDistinct_stepWiringCap`, C2) — a cap never merges two survivors.  This is the CAP side ONLY; the full
`(processBrauer (brauerSeed bc) boundaryWord).loops = 0` still needs the CROSSING-preserves-distinctness lemma and the
phase-fold assembly, the named r31 residual, so the loops wall `fxBrauer_hasFoldLoopsCorrectness` stays `false` and NO
master flips this round.  `= true`. -/
def fxBrauer_hasOpenEndsDistinctCapSide : Bool := true

end FX1Poly.Polygraph
