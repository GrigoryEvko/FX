import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCoreSwapBundle

/-! # KEYSTONE5 — the `openMap` four-zone wire correspondence + the in-range disjoint-window interchange

The block-swap `MatchingComponentSim` bundle (`Brauer/WiringDescCoreSwapBundle.lean`) reads the two
window-disjoint firing orders off to the boundary-diagram commutation modulo ONE explicit hypothesis: `openMap`,
the four-zone open-wire correspondence

  `BA.openWires = AB.openWires.map (blockRotate lo wA wB)`

(fixed prefix / A-window rotated up by `wB` / middle / B-window rotated down by `wA` / fixed suffix).  Every other
field — `nfEq`, `componentComm`, `loopsEq`, the two forests — is already banked (KEYSTONE1/3/4).  This file DISCHARGES
`openMap` and reads the whole surgery off to the freshness-and-forest-conditioned IN-RANGE disjoint-window
interchange.

## What this file SHIPS (each zero-axiom, structural on the wire list)

  * ★ **`natListRemoveManyAt_map`** — a generic-width block removal commutes with a renaming (the mirror of the
    shipped `natListInsertAt_map`, generalizing `natListRemoveTwoAt_map` off arity `2`).
  * ★ **`natListRemoveManyAt_appendPrefix`** — a removal at a position past a prefix removes inside the suffix (the
    generic-width mirror of `natListInsertAt_appendPrefix`).
  * ★ **`frontRemoveMany_splice_shift`** — a front removal (`natListRemoveManyAt _ 0 k`) passes THROUGH a disjoint
    higher splice, shifting the splice down by `k`.  The residual list-surgery interaction the four-zone
    correspondence bottoms out in; a structural induction on the removed count under a window-in-range discipline.
  * ★ **`spliceDisjointCommute`** — the FULL disjoint-window splice commutation over the nested
    `natListInsertAt ∘ natListRemoveManyAt`: firing the LOW window's splice and a disjoint HIGH window's splice
    commute, with the high position shifted by the low block's net width.  RANGE-CONDITIONED — the out-of-range
    degeneracy (a splice past the end of an exhausted list) genuinely breaks it (a concrete counterexample:
    `wires = []`, `lowPos = 1`).  Structural induction on the wire list threading the low position.
  * ★ **`wiringDescCoreSwap_openMap`** — the `openMap` field: mapping `blockRotate` over the AB order pushes through
    the two splices (`natListInsertAt_map` / `natListRemoveManyAt_map`), fixes the original wires (freshness +
    `blockRotate_below`), sends the two fresh output blocks to their BA-order images (the shipped
    `rangeMapAdd_map_blockRotate_first` / `_second`), and lands on the BA-order splices via `spliceDisjointCommute`.
  * ★ **`wiringDescCoreSwap_extract`** — the boundary-diagram commutation, `openMap` discharged, feeding
    `wiringDescCoreSwap_extract_ofOpenMap`.
  * ★ **`WiringDescDisjointWindowFreshInRange` + `wiringDescDisjointWindowFreshInRange_proof`** — the honestly-
    provable freshness-and-forest-conditioned IN-RANGE disjoint-window interchange, now CLOSED zero-axiom over the
    generic `stepWiring` engine (crossing included).  Every concrete Godement smoke (incl.
    `disjointWindow_crossingCup_commute`) is an instance.

## The residual that remains (NOT flipped)

The literally-stated `WiringDescDisjointWindowFresh` (`Brauer/WiringDescGodement.lean`) quantifies `positionB` with
ONLY `fresh + bottomBound + disjoint` — it omits three invariants the disjoint-window surgery genuinely consumes:

  1. `windowB : positionB + descB.inputCount ≤ state.openWires.length` — WITHOUT it `openMap` is FALSE (the
     out-of-range splice snaps the fresh block to the list end at an order-dependent offset — the `wires = []`,
     `lowPos = 1` counterexample);
  2. `isUnionFindForest state.links` — the `componentComm` root-after-join characterization needs it;
  3. `0 < state.nextFresh` — the `blockRotate` boundary-fixing sentinel `sigma 0 = 0` needs it.

All three hold along every reachable diagram state (the seed is fresh, positive, a forest, and every generator
fires in range; `stepWiring_links_isUnionFindForest` propagates the forest).  So the in-range version below is the
genuine interchange law; the unconditional flag stays `false` with the exact residual = extending it past those
reachable-state invariants (the out-of-range `windowsInRange` degeneracy plus the invariant-threading).  This does
NOT flip `fxBrauer_hasBrauerSoundness`, which additionally rides an unbuilt convertibility-congruence-closure layer
(a `BrauerConv` inductive + positional per-relation soundness + the closure induction) strictly beyond interchange.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Two generic-width list-surgery helpers -/

/-- ★ **A generic-width block removal commutes with a renaming.**  Mapping `sigma` over a `natListRemoveManyAt`
equals removing on the renamed list — the mirror of the shipped `natListInsertAt_map`, generalizing
`natListRemoveTwoAt_map` off arity `2`.  Structural on the wire list, dispatched exactly as the removal's own
matcher (list / count before position). -/
theorem natListRemoveManyAt_map (sigma : Nat → Nat) :
    (wires : List Nat) → (position count : Nat) →
    (natListRemoveManyAt wires position count).map sigma
      = natListRemoveManyAt (wires.map sigma) position count
  | wires, position, 0 => by
      rw [removeManyAt_zero wires position, removeManyAt_zero (wires.map sigma) position]
  | [], _, _ + 1 => rfl
  | headWire :: restWires, 0, count + 1 => by
      rw [removeManyAt_zero_cons headWire restWires count]
      show (natListRemoveManyAt restWires 0 count).map sigma
          = natListRemoveManyAt (sigma headWire :: restWires.map sigma) 0 (count + 1)
      rw [removeManyAt_zero_cons (sigma headWire) (restWires.map sigma) count]
      exact natListRemoveManyAt_map sigma restWires 0 count
  | headWire :: restWires, position + 1, count => by
      rw [removeManyAt_succ_cons headWire restWires position count]
      show sigma headWire :: (natListRemoveManyAt restWires position count).map sigma
          = natListRemoveManyAt (sigma headWire :: restWires.map sigma) (position + 1) count
      rw [removeManyAt_succ_cons (sigma headWire) (restWires.map sigma) position count]
      exact congrArg (sigma headWire :: ·) (natListRemoveManyAt_map sigma restWires position count)

/-- ★ **A block removal past a prefix removes inside the suffix.**  Removing `count` wires at a position shifted
past `prefixWires` leaves the prefix untouched — the generic-width mirror of `natListInsertAt_appendPrefix`.
Structural on the prefix. -/
theorem natListRemoveManyAt_appendPrefix :
    (prefixWires : List Nat) → (wires : List Nat) → (position count : Nat) →
    natListRemoveManyAt (prefixWires ++ wires) (prefixWires.length + position) count
      = prefixWires ++ natListRemoveManyAt wires position count
  | [], wires, position, count => by
      show natListRemoveManyAt wires (0 + position) count = natListRemoveManyAt wires position count
      rw [Nat.zero_add]
  | headWire :: restPrefix, wires, position, count => by
      show natListRemoveManyAt (headWire :: (restPrefix ++ wires)) (restPrefix.length + 1 + position) count
          = headWire :: (restPrefix ++ natListRemoveManyAt wires position count)
      rw [Nat.add_right_comm restPrefix.length 1 position,
        removeManyAt_succ_cons headWire (restPrefix ++ wires) (restPrefix.length + position) count]
      exact congrArg (headWire :: ·) (natListRemoveManyAt_appendPrefix restPrefix wires position count)

/-! ## The front-removal / higher-splice interaction -/

/-- ★ **A front removal passes through a disjoint higher splice.**  Removing the first `removeLow` wires of a list
that has already been spliced (`natListInsertAt ∘ natListRemoveManyAt`) at the strictly-higher position
`removeLow + extra` equals splicing at the position shifted DOWN by `removeLow` of the front-removed list.
Structural induction on `removeLow`, threading a window-in-range discipline (the exhausted-list past-end arm dies
by the range bound). -/
theorem frontRemoveMany_splice_shift (removeHigh : Nat) (blockHigh : List Nat) (extra : Nat) :
    (wires : List Nat) → (removeLow : Nat) →
    removeLow + extra + removeHigh ≤ wires.length →
    natListRemoveManyAt
        (natListInsertAt (natListRemoveManyAt wires (removeLow + extra) removeHigh) (removeLow + extra) blockHigh)
        0 removeLow
      = natListInsertAt
        (natListRemoveManyAt (natListRemoveManyAt wires 0 removeLow) extra removeHigh) extra blockHigh
  | wires, 0, _ => by
      rw [removeManyAt_zero
            (natListInsertAt (natListRemoveManyAt wires (0 + extra) removeHigh) (0 + extra) blockHigh) 0,
        Nat.zero_add extra, removeManyAt_zero wires 0]
  | [], removeLow + 1, rangeLe => by
      rw [Nat.add_right_comm removeLow 1 extra, Nat.add_right_comm (removeLow + extra) 1 removeHigh] at rangeLe
      exact absurd rangeLe (Nat.not_succ_le_zero (removeLow + extra + removeHigh))
  | headWire :: tailWires, removeLow + 1, rangeLe => by
      rw [Nat.add_right_comm removeLow 1 extra,
        removeManyAt_succ_cons headWire tailWires (removeLow + extra) removeHigh,
        insertAt_succ_cons headWire
          (natListRemoveManyAt tailWires (removeLow + extra) removeHigh) (removeLow + extra) blockHigh,
        removeManyAt_zero_cons headWire
          (natListInsertAt (natListRemoveManyAt tailWires (removeLow + extra) removeHigh)
            (removeLow + extra) blockHigh) removeLow,
        removeManyAt_zero_cons headWire tailWires removeLow]
      exact frontRemoveMany_splice_shift removeHigh blockHigh extra tailWires removeLow
        (Nat.le_of_succ_le_succ (by
          rw [Nat.add_right_comm removeLow 1 extra, Nat.add_right_comm (removeLow + extra) 1 removeHigh] at rangeLe
          exact rangeLe))

/-- A block splice past a prefix inserts inside the suffix — the shipped `natListInsertAt_appendPrefix`
(`WalkingAdjunction/ArcWindowCommutation`) reproved locally to keep the Brauer lane import-closed.  Structural on
the prefix. -/
private theorem natListInsertAt_appendPrefixLocal :
    (prefixWires : List Nat) → (wires : List Nat) → (position : Nat) → (block : List Nat) →
    natListInsertAt (prefixWires ++ wires) (prefixWires.length + position) block
      = prefixWires ++ natListInsertAt wires position block
  | [], wires, position, block => by
      show natListInsertAt wires (0 + position) block = natListInsertAt wires position block
      rw [Nat.zero_add]
  | headWire :: restPrefix, wires, position, block => by
      show natListInsertAt (headWire :: (restPrefix ++ wires)) (restPrefix.length + 1 + position) block
          = headWire :: (restPrefix ++ natListInsertAt wires position block)
      rw [Nat.add_right_comm restPrefix.length 1 position,
        insertAt_succ_cons headWire (restPrefix ++ wires) (restPrefix.length + position) block]
      exact congrArg (headWire :: ·) (natListInsertAt_appendPrefixLocal restPrefix wires position block)

/-! ## The full disjoint-window splice commutation -/

/-- ★ **Disjoint-window splices commute.**  Firing the LOW window's splice (remove `removeLow`, insert `blockLow`
at `lowPos`) and a disjoint HIGH window's splice (remove `removeHigh`, insert `blockHigh`) in either order produces
the same open-wire list, with the high position shifted by the low block's net width (`blockLow.length` on the
low-first side, `removeLow` on the high-first side; written subtraction-free as `+ extra`).  RANGE-CONDITIONED —
the out-of-range degeneracy genuinely breaks it (`wires = []`, `lowPos = 1`, `blockLow ≠ blockHigh` is a
counterexample).  Structural on the wire list, threading the low position; the base case is the front-removal /
higher-splice interaction, the step peels a common head. -/
theorem spliceDisjointCommute (removeLow removeHigh : Nat) (blockLow blockHigh : List Nat) (extra : Nat) :
    (wires : List Nat) → (lowPos : Nat) →
    lowPos + removeLow + extra + removeHigh ≤ wires.length →
    natListInsertAt
        (natListRemoveManyAt
          (natListInsertAt (natListRemoveManyAt wires (lowPos + removeLow + extra) removeHigh)
            (lowPos + removeLow + extra) blockHigh)
          lowPos removeLow)
        lowPos blockLow
      = natListInsertAt
        (natListRemoveManyAt
          (natListInsertAt (natListRemoveManyAt wires lowPos removeLow) lowPos blockLow)
          (lowPos + blockLow.length + extra) removeHigh)
        (lowPos + blockLow.length + extra) blockHigh
  | wires, 0, rangeLe => by
      have rangeLe' : removeLow + extra + removeHigh ≤ wires.length := by
        rw [Nat.zero_add removeLow] at rangeLe; exact rangeLe
      rw [Nat.zero_add removeLow, Nat.zero_add blockLow.length,
        insertAt_zero
          (natListRemoveManyAt
            (natListInsertAt (natListRemoveManyAt wires (removeLow + extra) removeHigh) (removeLow + extra)
              blockHigh)
            0 removeLow) blockLow,
        frontRemoveMany_splice_shift removeHigh blockHigh extra wires removeLow rangeLe',
        insertAt_zero (natListRemoveManyAt wires 0 removeLow) blockLow,
        natListRemoveManyAt_appendPrefix blockLow (natListRemoveManyAt wires 0 removeLow) extra removeHigh,
        natListInsertAt_appendPrefixLocal blockLow
          (natListRemoveManyAt (natListRemoveManyAt wires 0 removeLow) extra removeHigh) extra blockHigh]
  | [], lowPos + 1, rangeLe => by
      rw [Nat.add_right_comm lowPos 1 removeLow, Nat.add_right_comm (lowPos + removeLow) 1 extra,
        Nat.add_right_comm (lowPos + removeLow + extra) 1 removeHigh] at rangeLe
      exact absurd rangeLe (Nat.not_succ_le_zero (lowPos + removeLow + extra + removeHigh))
  | headWire :: tailWires, lowPos + 1, rangeLe => by
      rw [Nat.add_right_comm lowPos 1 removeLow, Nat.add_right_comm (lowPos + removeLow) 1 extra,
        Nat.add_right_comm lowPos 1 blockLow.length, Nat.add_right_comm (lowPos + blockLow.length) 1 extra,
        splice_succ_cons removeHigh blockHigh headWire tailWires (lowPos + removeLow + extra),
        splice_succ_cons removeLow blockLow headWire
          (natListInsertAt (natListRemoveManyAt tailWires (lowPos + removeLow + extra) removeHigh)
            (lowPos + removeLow + extra) blockHigh)
          lowPos,
        splice_succ_cons removeLow blockLow headWire tailWires lowPos,
        splice_succ_cons removeHigh blockHigh headWire
          (natListInsertAt (natListRemoveManyAt tailWires lowPos removeLow) lowPos blockLow)
          (lowPos + blockLow.length + extra)]
      exact congrArg (headWire :: ·)
        (spliceDisjointCommute removeLow removeHigh blockLow blockHigh extra tailWires lowPos
          (Nat.le_of_succ_le_succ (by
            rw [Nat.add_right_comm lowPos 1 removeLow, Nat.add_right_comm (lowPos + removeLow) 1 extra,
              Nat.add_right_comm (lowPos + removeLow + extra) 1 removeHigh] at rangeLe
            exact rangeLe)))

/-! ## The `openMap` field -/

/-- One `stepWiring` step's open-wire list is the splice of its fresh output block into the input-block-removed
list — the `stepWiring` `openWires` field, read off by `rfl`. -/
private theorem stepWiring_openWires (state : WireState) (position : Nat) (desc : WiringDesc) :
    (stepWiring state position desc).openWires
      = natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position
          ((List.range desc.outputCount).map (· + state.nextFresh)) := rfl

/-- ★ **The `openMap` four-zone open-wire correspondence.**  Over a fresh state (`nfPos` for the `sigma 0 = 0`
sentinel) with `descA`'s window disjointly left of `descB`'s and in range, the BA-order open wires are the
`blockRotate`-image of the AB-order open wires.  Mapping `blockRotate` over AB pushes through the two splices
(`natListInsertAt_map` / `natListRemoveManyAt_map`), fixes the original wires (`mapFixedOn` + `blockRotate_below`
under freshness), sends the two fresh output blocks to their BA images (`rangeMapAdd_map_blockRotate_first` /
`_second`), and lands on the BA-order splices via the disjoint-window commutation `spliceDisjointCommute`. -/
theorem wiringDescCoreSwap_openMap (state : WireState) (positionA positionB : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length) :
    (stepWiring (stepWiring state positionB descB) positionA descA).openWires
      = ((stepWiring (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB).openWires).map
        (blockRotate state.nextFresh descA.outputCount descB.outputCount) := by
  obtain ⟨extra, extraEq⟩ := Nat.le.dest disjoint
  have blockLen :
      ((List.range descA.outputCount).map (· + (state.nextFresh + descB.outputCount))).length
        = descA.outputCount := by rw [mapLength, rangeLength_local]
  have posBEq : positionB = positionA + descA.inputCount + extra := extraEq.symm
  have posB'Eq : positionB - descA.inputCount + descA.outputCount
      = positionA + ((List.range descA.outputCount).map (· + (state.nextFresh + descB.outputCount))).length
          + extra := by
    have subEq : positionB - descA.inputCount = positionA + extra := by
      rw [← extraEq, Nat.add_right_comm positionA descA.inputCount extra,
        addSubCancelRight (positionA + extra) descA.inputCount]
    rw [blockLen, subEq, Nat.add_right_comm positionA extra descA.outputCount]
  -- expand both open-wire lists to nested splices
  rw [stepWiring_openWires (stepWiring state positionB descB) positionA descA,
    stepWiring_openWires state positionB descB, stepWiring_nextFresh state positionB descB,
    stepWiring_openWires (stepWiring state positionA descA)
      (positionB - descA.inputCount + descA.outputCount) descB,
    stepWiring_openWires state positionA descA, stepWiring_nextFresh state positionA descA]
  -- push blockRotate through the AB-order splices
  rw [natListInsertAt_map (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      (natListRemoveManyAt
        (natListInsertAt (natListRemoveManyAt state.openWires positionA descA.inputCount) positionA
          ((List.range descA.outputCount).map (· + state.nextFresh)))
        (positionB - descA.inputCount + descA.outputCount) descB.inputCount)
      (positionB - descA.inputCount + descA.outputCount)
      ((List.range descB.outputCount).map (· + (state.nextFresh + descA.outputCount))),
    natListRemoveManyAt_map (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      (natListInsertAt (natListRemoveManyAt state.openWires positionA descA.inputCount) positionA
        ((List.range descA.outputCount).map (· + state.nextFresh)))
      (positionB - descA.inputCount + descA.outputCount) descB.inputCount,
    natListInsertAt_map (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      (natListRemoveManyAt state.openWires positionA descA.inputCount) positionA
      ((List.range descA.outputCount).map (· + state.nextFresh)),
    natListRemoveManyAt_map (blockRotate state.nextFresh descA.outputCount descB.outputCount)
      state.openWires positionA descA.inputCount]
  -- resolve the three renamed pieces: original wires fixed, the two fresh blocks rotated to their BA images
  rw [mapFixedOn (blockRotate state.nextFresh descA.outputCount descB.outputCount) state.openWires
      (fun wire wireInOpen =>
        blockRotate_below state.nextFresh descA.outputCount descB.outputCount wire (fresh.1 wire wireInOpen)),
    rangeMapAdd_map_blockRotate_first state.nextFresh descA.outputCount descB.outputCount
      (List.range descA.outputCount) (fun index indexMem => mem_range_imp_lt indexMem),
    rangeMapAdd_map_blockRotate_second state.nextFresh descA.outputCount descB.outputCount
      (List.range descB.outputCount) (fun index indexMem => mem_range_imp_lt indexMem)]
  -- bridge the two positions to the disjoint-window commutation form, then discharge
  rw [posB'Eq, posBEq]
  exact spliceDisjointCommute descA.inputCount descB.inputCount
    ((List.range descA.outputCount).map (· + (state.nextFresh + descB.outputCount)))
    ((List.range descB.outputCount).map (· + state.nextFresh)) extra state.openWires positionA
    (by rw [extraEq]; exact windowB)

/-! ## The boundary-diagram commutation (the freshness-and-forest-conditioned in-range interchange) -/

/-- ★ **The boundary diagram commutes across the two window-disjoint firing orders — `openMap` discharged.**  Feeds
`wiringDescCoreSwap_openMap` into the shipped `wiringDescCoreSwap_extract_ofOpenMap`; the remaining hypotheses
(`fresh`, `nfPos`, `forest`, `bottomBound`, `disjoint`, `windowB`) are the reachable-state invariants. -/
theorem wiringDescCoreSwap_extract (state : WireState) (positionA positionB bottomCount : Nat)
    (descA descB : WiringDesc)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links)
    (bottomBound : bottomCount ≤ state.nextFresh)
    (disjoint : positionA + descA.inputCount ≤ positionB)
    (windowB : positionB + descB.inputCount ≤ state.openWires.length) :
    extractDiagram bottomCount
        (stepWiring (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
      = extractDiagram bottomCount
        (stepWiring (stepWiring state positionB descB) positionA descA) :=
  wiringDescCoreSwap_extract_ofOpenMap state positionA positionB bottomCount descA descB fresh nfPos forest
    bottomBound disjoint windowB
    (wiringDescCoreSwap_openMap state positionA positionB descA descB fresh disjoint windowB)

/-- ★ **The freshness-and-forest-conditioned IN-RANGE disjoint-window interchange.**  The honestly-provable
strengthening of `WiringDescDisjointWindowFresh`: it carries the three reachable-state invariants the
disjoint-window surgery genuinely consumes (`windowB` — without it `openMap` is FALSE; `isUnionFindForest`; and
`0 < nextFresh`).  Every concrete Godement smoke (incl. the crossing pairs) is an instance. -/
def WiringDescDisjointWindowFreshInRange : Prop :=
  ∀ (state : WireState) (positionA positionB bottomCount : Nat) (descA descB : WiringDesc),
    WiringDescStateFresh state → 0 < state.nextFresh → isUnionFindForest state.links →
    bottomCount ≤ state.nextFresh →
    positionA + descA.inputCount ≤ positionB →
    positionB + descB.inputCount ≤ state.openWires.length →
    extractDiagram bottomCount
        (stepWiring (stepWiring state positionA descA)
          (positionB - descA.inputCount + descA.outputCount) descB)
      = extractDiagram bottomCount
        (stepWiring (stepWiring state positionB descB) positionA descA)

/-- ★ **The in-range disjoint-window interchange is CLOSED zero-axiom.**  Directly `wiringDescCoreSwap_extract`,
over the generic `stepWiring` engine (crossing included). -/
theorem wiringDescDisjointWindowFreshInRange_proof : WiringDescDisjointWindowFreshInRange :=
  fun state positionA positionB bottomCount descA descB fresh nfPos forest bottomBound disjoint windowB =>
    wiringDescCoreSwap_extract state positionA positionB bottomCount descA descB fresh nfPos forest bottomBound
      disjoint windowB

/-- The four-wire seed's crossing-over-cup interchange smoke is an instance of the general in-range proof — the
concrete `disjointWindow_crossingCup_commute` recovered from the general theorem (seed is fresh, positive, a
forest; the crossing window is in range). -/
theorem disjointWindow_crossingCup_commute_ofGeneral :
    extractDiagram 4 (stepWiring (stepWiring fourWireSeed 0 cupWiring) 4 crossingWiring)
      = extractDiagram 4 (stepWiring (stepWiring fourWireSeed 2 crossingWiring) 0 cupWiring) :=
  wiringDescDisjointWindowFreshInRange_proof fourWireSeed 0 2 4 cupWiring crossingWiring
    (by dsimp only [WiringDescStateFresh, fourWireSeed]; decide) (by decide) isUnionFindForest_nil (by decide)
    (by decide) (by decide)

/-! ## Honesty markers -/

/-- **Honesty marker — the `openMap` four-zone wire correspondence is SHIPPED.**  `wiringDescCoreSwap_openMap`
discharges the last field of the block-swap `MatchingComponentSim` bundle: the BA-order open wires are the
`blockRotate`-image of the AB-order open wires, via the generic-width list-surgery kit
(`natListRemoveManyAt_map` / `_appendPrefix`, `frontRemoveMany_splice_shift`, and the RANGE-CONDITIONED
`spliceDisjointCommute`) plus the shipped fresh-block images.  `= true`. -/
def fxBrauer_hasWiringDescCoreSwapOpenMap : Bool := true

/-- **Honesty marker — the IN-RANGE disjoint-window interchange is CLOSED.**  `wiringDescCoreSwap_extract` reads the
whole disjoint-window surgery off to the boundary-diagram commutation (`openMap` discharged), and
`wiringDescDisjointWindowFreshInRange_proof` packages it as the freshness-and-forest-conditioned in-range
interchange over the generic `stepWiring` engine (crossing included) — every Godement smoke an instance.  `= true`. -/
def fxBrauer_hasWiringDescDisjointWindowFreshInRangeProof : Bool := true

/-- **Honesty marker — the UNCONDITIONAL `WiringDescDisjointWindowFresh` stays open on the reachable-state
invariant threading.**  The literally-stated residual omits three invariants the surgery consumes: `windowB`
(without it `openMap` is FALSE — the out-of-range splice snaps the fresh block to the list end at an order-dependent
offset), `isUnionFindForest state.links`, and `0 < state.nextFresh`.  The in-range version carrying all three is
now CLOSED (`wiringDescDisjointWindowFreshInRange_proof`); the exact residual to flip the shipped
`fxBrauer_hasWiringDescDisjointWindowFreshProof` (in `WiringDescGodement`) is showing the soundness chain only ever
consumes the interchange at reachable states (which are fresh, positive, forests, in range) — the
boundary-discipline / out-of-range brick.  This marker records that the residual is precisely named (it does NOT
redefine the shipped flag).  `= true`. -/
def fxBrauer_hasWiringDescDisjointWindowFreshResidualNamed : Bool := true

end FX1Poly.Polygraph
