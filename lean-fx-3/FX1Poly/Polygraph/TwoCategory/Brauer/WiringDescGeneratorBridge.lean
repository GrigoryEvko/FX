import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadback
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents

/-! # BRAUER-MIDDLE r10 B1 — the generator bridges: routing `stepWiring` at `cupWiring` / `capWiring` to the
shipped `stepCup` / `stepCap`

`processBrauer` fires the GENERIC engine `stepWiring state atom.position atom.wiring` at each atom (via
`stepBrauerAtom`), while the shipped T-DISJOINT per-atom preservations
(`boundedBoundaryComponents_stepCap` / `_stepCup`) are stated over the HARDCODED `stepCap` / `stepCup`.  The
crossing preservation is already in generic `stepWiring` form (no bridge); the cup / cap preservations are not.
This file supplies the two missing bridges so the fold lift can route cup / cap atoms to their shipped
preservations:

  * ★ **`stepWiring_capWiring_eq_stepCap`** — `stepWiring state position capWiring = stepCap state position`,
    under the window-fit `position + 2 ≤ state.openWires.length` (genuinely load-bearing: the two removal
    functions `natListRemoveManyAt _ _ 2` and `natListRemoveTwoAt` DIVERGE past the end of the list, agreeing
    only when the two consumed wires actually sit in the window).
  * ★ **`stepWiring_cupWiring_eq_stepCup`** — `stepWiring state position cupWiring = stepCup state position`,
    under freshness (`WiringDescStateFresh state`): the cup's arc fold is stuck on
    `isSameComponent links nextFresh (nextFresh + 1)`, which freshness pins to `false`, matching `stepCup`'s
    unconditional join branch.

Both are gated by two small structural plumbing lemmas — `natListRemoveManyAt_two_eq_removeTwoAt` (the
two-removal / two-remove agreement under window-fit) and `natListInsertAt_nil` (splicing an empty block is a
no-op) — plus the two arc-fold reductions `stepWiringArcs_cup_eq` / `stepWiringArcs_cap_eq_{same,diff}`.  The
discipline mirrors the shipped propext-clean crossing proof `stepWiring_crossing_links`: pure `rw` over NAMED
equation lemmas, never `simp only` on a raw recursive matcher (the `natListRemoveTwoAt` singleton arm would leak
`propext` through its splitter).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two structural plumbing lemmas -/

/-- The shipped `natListRemoveTwoAt` peels a head at a nonzero position (its matcher splits the list deeply to
handle the singleton arm, so this is not `rfl` at a variable tail — one `cases` on the tail resolves it). -/
theorem removeTwoAt_succ_cons (headWire : Nat) (tailWires : List Nat) (position : Nat) :
    natListRemoveTwoAt (headWire :: tailWires) (position + 1)
      = headWire :: natListRemoveTwoAt tailWires position := by
  cases tailWires with
  | nil => rfl
  | cons _ _ => rfl

/-- ★ **The two-wide block removal equals the shipped two-remove, under window-fit.**  `natListRemoveManyAt _ _ 2`
and `natListRemoveTwoAt` agree exactly when the two consumed wires sit inside the list (`position + 2 ≤ length`);
the range bound rules out the past-end singleton divergence.  Structural on the position, then the list; per-arm
`rw` only (no `simp only` on the `natListRemoveTwoAt` matcher). -/
theorem natListRemoveManyAt_two_eq_removeTwoAt :
    (position : Nat) → (wires : List Nat) → position + 2 ≤ wires.length →
    natListRemoveManyAt wires position 2 = natListRemoveTwoAt wires position
  | 0, [], hle => absurd hle (Nat.not_succ_le_zero 1)
  | 0, [_single], hle => absurd hle (Nat.not_succ_le_self 1)
  | 0, first :: second :: rest, _ => by
      show natListRemoveManyAt (first :: second :: rest) 0 2 = rest
      rw [removeManyAt_zero_cons, removeManyAt_zero_cons, removeManyAt_zero]
  | _position + 1, [], hle => absurd hle (Nat.not_succ_le_zero _)
  | position + 1, firstWire :: rest, hle => by
      rw [removeManyAt_succ_cons firstWire rest position 2, removeTwoAt_succ_cons firstWire rest position]
      have hle' : position + 2 ≤ rest.length := by
        have expanded : position + 2 + 1 ≤ rest.length + 1 := by
          rw [Nat.add_right_comm position 2 1]; exact hle
        exact Nat.le_of_succ_le_succ expanded
      rw [natListRemoveManyAt_two_eq_removeTwoAt position rest hle']

/-- ★ **Splicing an empty block is a no-op.**  `natListInsertAt wires position [] = wires` — the cap produces zero
output wires, so its splice restores the input-removed list.  Structural on the position then the list. -/
theorem natListInsertAt_nil :
    (wires : List Nat) → (position : Nat) → natListInsertAt wires position [] = wires
  | wires, 0 => by rw [insertAt_zero wires []]; rfl
  | [], _position + 1 => rfl
  | headWire :: rest, position + 1 => by
      rw [insertAt_succ_cons headWire rest position []]
      show headWire :: natListInsertAt rest position [] = headWire :: rest
      rw [natListInsertAt_nil rest position]

/-! ## The arc-fold reductions -/

/-- The cup's one-arc fold on two DISCONNECTED fresh legs: the join branch, no loop.  Mirrors the shipped
`stepWiringArcs_crossing_eq` discipline — pure `rw` over the named endpoint reductions, then `if_neg` on the
freshness discriminator. -/
theorem stepWiringArcs_cup_eq (leftLeg rightLeg : Nat) (links : List (Nat × Nat))
    (disc : isSameComponent links leftLeg rightLeg = false) :
    stepWiringArcs [] [leftLeg, rightLeg] 0 [(0, 1)] 0 links = (unionFindJoin links leftLeg rightLeg, 0) := by
  have e0 : wiringEndpointNode [] [leftLeg, rightLeg] 0 0 = leftLeg := rfl
  have e1 : wiringEndpointNode [] [leftLeg, rightLeg] 0 1 = rightLeg := rfl
  show (if isSameComponent links (wiringEndpointNode [] [leftLeg, rightLeg] 0 0)
          (wiringEndpointNode [] [leftLeg, rightLeg] 0 1)
        then stepWiringArcs [] [leftLeg, rightLeg] 0 [] (0 + 1) links
        else stepWiringArcs [] [leftLeg, rightLeg] 0 [] 0
          (unionFindJoin links (wiringEndpointNode [] [leftLeg, rightLeg] 0 0)
            (wiringEndpointNode [] [leftLeg, rightLeg] 0 1))) = (unionFindJoin links leftLeg rightLeg, 0)
  rw [e0, e1, disc, if_neg (fun eq => Bool.noConfusion eq)]
  rfl

/-- The cap's one-arc fold on two ALREADY-connected wires: the loop branch, `links` untouched, one loop. -/
theorem stepWiringArcs_cap_eq_same (leftWire rightWire : Nat) (links : List (Nat × Nat))
    (disc : isSameComponent links leftWire rightWire = true) :
    stepWiringArcs [leftWire, rightWire] [] 2 [(0, 1)] 0 links = (links, 1) := by
  have e0 : wiringEndpointNode [leftWire, rightWire] [] 2 0 = leftWire := rfl
  have e1 : wiringEndpointNode [leftWire, rightWire] [] 2 1 = rightWire := rfl
  show (if isSameComponent links (wiringEndpointNode [leftWire, rightWire] [] 2 0)
          (wiringEndpointNode [leftWire, rightWire] [] 2 1)
        then stepWiringArcs [leftWire, rightWire] [] 2 [] (0 + 1) links
        else stepWiringArcs [leftWire, rightWire] [] 2 [] 0
          (unionFindJoin links (wiringEndpointNode [leftWire, rightWire] [] 2 0)
            (wiringEndpointNode [leftWire, rightWire] [] 2 1))) = (links, 1)
  rw [e0, e1, disc, if_pos rfl]
  rfl

/-- The cap's one-arc fold on two DISCONNECTED wires: the join branch, no loop. -/
theorem stepWiringArcs_cap_eq_diff (leftWire rightWire : Nat) (links : List (Nat × Nat))
    (disc : isSameComponent links leftWire rightWire = false) :
    stepWiringArcs [leftWire, rightWire] [] 2 [(0, 1)] 0 links = (unionFindJoin links leftWire rightWire, 0) := by
  have e0 : wiringEndpointNode [leftWire, rightWire] [] 2 0 = leftWire := rfl
  have e1 : wiringEndpointNode [leftWire, rightWire] [] 2 1 = rightWire := rfl
  show (if isSameComponent links (wiringEndpointNode [leftWire, rightWire] [] 2 0)
          (wiringEndpointNode [leftWire, rightWire] [] 2 1)
        then stepWiringArcs [leftWire, rightWire] [] 2 [] (0 + 1) links
        else stepWiringArcs [leftWire, rightWire] [] 2 [] 0
          (unionFindJoin links (wiringEndpointNode [leftWire, rightWire] [] 2 0)
            (wiringEndpointNode [leftWire, rightWire] [] 2 1))) = (unionFindJoin links leftWire rightWire, 0)
  rw [e0, e1, disc, if_neg (fun eq => Bool.noConfusion eq)]
  rfl

/-! ## The two bridges -/

/-- ★ **The CAP bridge.**  `stepWiring state position capWiring = stepCap state position` under the window-fit
`position + 2 ≤ state.openWires.length`.  The generic engine slices the two consumed wires
(`natListSliceAt_two`), folds the single arc (`stepWiringArcs_cap_eq_{same,diff}`), and splices back the empty
output block (`natListInsertAt_nil` after `natListRemoveManyAt_two_eq_removeTwoAt`), reproducing `stepCap`'s two
branches exactly. -/
theorem stepWiring_capWiring_eq_stepCap (state : WireState) (position : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length) :
    stepWiring state position capWiring = stepCap state position := by
  have sliceEq : natListSliceAt state.openWires position 2
      = [natListGetAt state.openWires position, natListGetAt state.openWires (position + 1)] :=
    natListSliceAt_two state.openWires position windowInRange
  have removeEq : natListInsertAt (natListRemoveManyAt state.openWires position 2) position ([] : List Nat)
      = natListRemoveTwoAt state.openWires position := by
    rw [natListInsertAt_nil (natListRemoveManyAt state.openWires position 2) position,
      natListRemoveManyAt_two_eq_removeTwoAt position state.openWires windowInRange]
  show { openWires := natListInsertAt (natListRemoveManyAt state.openWires position 2) position [],
         links := (stepWiringArcs (natListSliceAt state.openWires position 2) [] 2 [(0, 1)] 0 state.links).fst,
         nextFresh := state.nextFresh + 0,
         loops := state.loops
           + (stepWiringArcs (natListSliceAt state.openWires position 2) [] 2 [(0, 1)] 0 state.links).snd + 0 }
       = stepCap state position
  rw [sliceEq, removeEq]
  dsimp only [stepCap]
  cases hbranch : isSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) with
  | true =>
      rw [stepWiringArcs_cap_eq_same (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) state.links hbranch]
      rfl
  | false =>
      rw [stepWiringArcs_cap_eq_diff (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) state.links hbranch]
      rfl

/-- ★ **The CUP bridge.**  `stepWiring state position cupWiring = stepCup state position` under freshness.  The
generic engine allocates the two fresh legs `nextFresh`, `nextFresh + 1` (`(List.range 2).map (· + nextFresh)`),
folds the single arc on them — freshness (`isSameComponent_freshPair_eq_false`) forcing the join branch — and
splices them in, reproducing `stepCup` exactly. -/
theorem stepWiring_cupWiring_eq_stepCup (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) :
    stepWiring state position cupWiring = stepCup state position := by
  have disc : isSameComponent state.links state.nextFresh (state.nextFresh + 1) = false :=
    isSameComponent_freshPair_eq_false state.nextFresh state.links
      (fun edge edgeMem => (fresh.2 edge edgeMem).1) state.nextFresh (Nat.le_refl state.nextFresh)
  have outputEq : (List.range 2).map (· + state.nextFresh) = [state.nextFresh, state.nextFresh + 1] := by
    show [0 + state.nextFresh, 1 + state.nextFresh] = [state.nextFresh, state.nextFresh + 1]
    rw [Nat.zero_add, Nat.add_comm 1 state.nextFresh]
  show { openWires := natListInsertAt (natListRemoveManyAt state.openWires position 0) position
           ((List.range 2).map (· + state.nextFresh)),
         links := (stepWiringArcs (natListSliceAt state.openWires position 0)
           ((List.range 2).map (· + state.nextFresh)) 0 [(0, 1)] 0 state.links).fst,
         nextFresh := state.nextFresh + 2,
         loops := state.loops
           + (stepWiringArcs (natListSliceAt state.openWires position 0)
             ((List.range 2).map (· + state.nextFresh)) 0 [(0, 1)] 0 state.links).snd + 0 }
       = stepCup state position
  rw [removeManyAt_zero state.openWires position, sliceAt_count_zero state.openWires position, outputEq,
    stepWiringArcs_cup_eq state.nextFresh (state.nextFresh + 1) state.links disc]
  rfl

/-! ## Honesty marker -/

/-- **Honesty marker — the two generator bridges are SHIPPED.**  `stepWiring_capWiring_eq_stepCap` (window-fit)
and `stepWiring_cupWiring_eq_stepCup` (freshness) route the generic engine's cap / cup firings to the shipped
`stepCap` / `stepCup`, so the fold lift can dispatch cup / cap atoms to their shipped T-DISJOINT preservations.
Both propext-clean (the shipped crossing-proof discipline: named `rw` reductions, never `simp only` on a raw
recursive matcher).  `= true`. -/
def fxBrauer_hasGeneratorBridge : Bool := true

end FX1Poly.Polygraph
