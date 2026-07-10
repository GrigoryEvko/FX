import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhases

/-! # BRAUER-MIDDLE r5 B1 — R3-A-INTERIOR: the interior-offset cup PHASE FOLD (the generalization the corrected
extractor's `throughBottoms.length`-offset cup block needs)

The r4 cup phase fold `cupFold_creates` (`Brauer/WiringDescStandardFoldPhases.lean`) handles ONLY the position-`0`
cup block `cupWord (natReplicate cupCount 0)` — directly load-bearing for the through-strand-free subclass, where
the standard-form cup block sits at position `0`.  But the corrected extractor
`reconstructStandardFormExt5Corrected` (`Brauer/WiringDescArcExtractorRec.lean:79`) sets
`cupBlock := natReplicate … throughBottoms.length` — it fires the cups at the INTERIOR offset
`throughBottoms.length` (after the through-strand wires) whenever through-strands are present.  So the R3-A roundtrip
needs the offset-generalized cup fold: firing `cupWord (natReplicate cupCount offset)` on a state whose open wires
split as `front ++ back` with `front.length = offset` prepends `cupCount` fresh CONNECTED pairs RIGHT AFTER the
`front` block, leaving `front` (the through wires) untouched in place.

This is the recon's R3-A-INTERIOR leg.  The wall shape the recon predicted was "none of substance" — `natListInsertAt`
at a nonzero position is structural, and the arc-connection lemma `stepWiring_connects_arc` is already position-generic
(it takes `position` as a parameter).  The only genuinely new ingredient is the append-at-front computation
(`natListInsertAtFront`), replacing the position-`0`-specialized `simp only … rfl` closer of `stepWiring_cup_head`.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`natListInsertAtFront`** — `natListInsertAt (front ++ back) front.length block = front ++ (block ++ back)`:
    inserting a block at the length of a prefix splices it right after that prefix.  Structural on `front`.
  * **`natListRemoveManyAt_zero`** — removing `0` wires at any position is a no-op (the cup consumes no input ports).
  * **`stepWiring_cup_interior`** — one `cupAt offset` at position `offset = front.length` inserts a fresh CONNECTED
    pair right after `front`, leaving `front ++ (freshLeft :: freshRight :: back)` (the offset generalization of the
    shipped position-`0` `stepWiring_cup_head`; the connection arc is the SAME `stepWiring_connects_arc`, unchanged).
  * ★ **`cupFold_creates_atOffset`** — the interior CUP-creation phase fold: firing `cupWord (natReplicate cupCount
    offset)` prepends exactly `cupCount` fresh CONNECTED pairs right after `front`, each still same-component in the
    resulting links, with `front` (the through wires) preserved in place.  Structural on `cupCount`; the offset
    generalization of `cupFold_creates`.
  * non-vacuity at a NONZERO offset (`cupFold_creates_atOffset_throughOne`, `cupFold_atOffset_throughOne_diagram`):
    one cup fired at offset `1` behind one through wire realizes the straddle-shaped through+cup matching `[1,0,3,2]`.

## Honest scope — this is the R3-A-INTERIOR leg, NOT the roundtrip

This is the interior-offset cup fold the recon named as R3-A-INTERIOR — the prerequisite the six-phase glue
(R3-A-CROSSING-GLUE) threads the cup phase through.  The crossing-phase composition and above all the TAG
CORRESPONDENCE (R3-A-TAGCORR) remain the standing R3-A residual.  So `fxBrauer_hasExt5CorrectedRoundtripProof` /
`fxBrauer_hasExt5TotalExtractorRoundtrip` STAY `false` (no flip is fabricated); #2013 does not close.

Raw Lean 4 + Init.  The list arithmetic uses only structural recursion + `List.Mem` constructor case analysis
(propext-free).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The append-at-front computation for `natListInsertAt` -/

/-- Inserting a block at position `0` prepends it to the whole list — the `natListInsertAt` clause-1 equation,
proven by cases on the list (the matcher splits on the list before the position, so a bare `rfl` at a variable list
does not fire).  Propext-free. -/
theorem natListInsertAt_zero : (wires block : List Nat) →
    natListInsertAt wires 0 block = block ++ wires
  | [], _ => rfl
  | _ :: _, _ => rfl

/-- ★ **Inserting a block at the length of a prefix splices it right after that prefix.**
`natListInsertAt (front ++ back) front.length block = front ++ (block ++ back)`.  Structural on `front`
(propext-free): the position `front.length` counts exactly past the `front` cons cells. -/
theorem natListInsertAtFront : (front back block : List Nat) →
    natListInsertAt (front ++ back) front.length block = front ++ (block ++ back)
  | [], back, block => natListInsertAt_zero back block
  | headNode :: rest, back, block => by
      show headNode :: natListInsertAt (rest ++ back) rest.length block
          = headNode :: (rest ++ (block ++ back))
      rw [natListInsertAtFront rest back block]

/-- Removing `0` wires at any position is a no-op — the cup consumes no input ports, so its
`natListRemoveManyAt … 0` leaves the open wires untouched.  Full case split (propext-free). -/
theorem natListRemoveManyAt_zero : (wires : List Nat) → (position : Nat) →
    natListRemoveManyAt wires position 0 = wires
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: _, _ + 1 => rfl

/-! ## The interior cup phase-atom lemma -/

/-- ★ **One cup at the interior offset prepends a fresh connected pair right after `front`.**  On a state whose open
wires split as `front ++ back` with `front.length = offset`, `stepWiring … cupWiring` at position `offset` leaves
open wires `front ++ (freshLeft :: freshRight :: back)` and connects the two fresh wires.  The offset generalization
of `stepWiring_cup_head` (which is the `front = []` case); the connection is the arc `(0, 1)` of `cupWiring` through
the position-generic `stepWiring_connects_arc`. -/
theorem stepWiring_cup_interior (state : WireState) (offset : Nat) (front back : List Nat)
    (hopen : state.openWires = front ++ back) (hlen : front.length = offset)
    (forest : isUnionFindForest state.links) :
    (stepWiring state offset cupWiring).openWires
        = front ++ ((0 + state.nextFresh) :: (1 + state.nextFresh) :: back)
      ∧ isSameComponent (stepWiring state offset cupWiring).links
          (0 + state.nextFresh) (1 + state.nextFresh) = true := by
  refine ⟨?_, ?_⟩
  · show natListInsertAt (natListRemoveManyAt state.openWires offset 0) offset
        ((List.range 2).map (· + state.nextFresh))
        = front ++ ((0 + state.nextFresh) :: (1 + state.nextFresh) :: back)
    rw [natListRemoveManyAt_zero state.openWires offset, hopen, ← hlen,
      natListInsertAtFront front back ((List.range 2).map (· + state.nextFresh))]
    rfl
  · exact stepWiring_connects_arc state offset cupWiring forest (0, 1) (List.Mem.head [])

/-! ## The interior CUP-creation phase fold -/

/-- ★ **The interior cup phase prepends fresh connected pairs right after `front`.**  Firing `cupWord (natReplicate
cupCount offset)` — one cup at position `offset = front.length` per count — on a state whose open wires are
`front ++ back` prepends exactly `cupCount` fresh pairs (returned as `freshFeet`) right after `front`, each still
same-component in the resulting links, and `front` (the through wires) stays in place.  Structural on `cupCount`; the
offset generalization of `cupFold_creates` (the `front = []` case).  Each already-placed pair's connection survives
the later cups by the inductive hypothesis (over the final links directly), and the newly placed pair survives by
connectivity monotonicity `processBrauer_isSameComponent_ofBase`. -/
theorem cupFold_creates_atOffset (offset : Nat) :
    (cupCount : Nat) → (state : WireState) → (front back : List Nat) →
    state.openWires = front ++ back → front.length = offset →
    isUnionFindForest state.links →
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = cupCount
      ∧ (processBrauer state (cupWord (natReplicate cupCount offset))).openWires
          = front ++ (flattenNatPairs freshFeet ++ back)
      ∧ ∀ pair, pair ∈ freshFeet →
          isSameComponent (processBrauer state (cupWord (natReplicate cupCount offset))).links
            pair.1 pair.2 = true
  | 0, state, front, back, hopen, _hlen, _forest => by
      refine ⟨[], rfl, ?_, ?_⟩
      · show state.openWires = front ++ back
        exact hopen
      · intro pair hmem; nomatch hmem
  | cupCount + 1, state, front, back, hopen, hlen, forest => by
      obtain ⟨hStepOpen, hStepConn⟩ := stepWiring_cup_interior state offset front back hopen hlen forest
      have forest1 : isUnionFindForest (stepWiring state offset cupWiring).links :=
        stepWiring_links_isUnionFindForest state offset cupWiring forest
      obtain ⟨freshFeet', hLen', hOpen', hConn'⟩ :=
        cupFold_creates_atOffset offset cupCount (stepWiring state offset cupWiring)
          front ((0 + state.nextFresh) :: (1 + state.nextFresh) :: back) hStepOpen hlen forest1
      refine ⟨freshFeet' ++ [(0 + state.nextFresh, 1 + state.nextFresh)], ?_, ?_, ?_⟩
      · rw [lengthAppendSingleton freshFeet' (0 + state.nextFresh, 1 + state.nextFresh), hLen']
      · show (processBrauer (stepWiring state offset cupWiring)
              (cupWord (natReplicate cupCount offset))).openWires
            = front ++ (flattenNatPairs (freshFeet' ++ [(0 + state.nextFresh, 1 + state.nextFresh)]) ++ back)
        rw [hOpen', flattenNatPairs_appendSingleton freshFeet' (0 + state.nextFresh, 1 + state.nextFresh)]
        exact congrArg (front ++ ·)
          (appendPairRegroup (flattenNatPairs freshFeet') (0 + state.nextFresh) (1 + state.nextFresh) back).symm
      · intro pair hmem
        cases natPairMemAppendSingleton freshFeet' (0 + state.nextFresh, 1 + state.nextFresh) pair hmem with
        | inl hin =>
            show isSameComponent (processBrauer (stepWiring state offset cupWiring)
                (cupWord (natReplicate cupCount offset))).links pair.1 pair.2 = true
            exact hConn' pair hin
        | inr heq =>
            show isSameComponent (processBrauer (stepWiring state offset cupWiring)
                (cupWord (natReplicate cupCount offset))).links pair.1 pair.2 = true
            rw [heq]
            exact processBrauer_isSameComponent_ofBase (cupWord (natReplicate cupCount offset))
              (stepWiring state offset cupWiring) forest1 (0 + state.nextFresh) (1 + state.nextFresh) hStepConn

/-! ## Non-vacuity — the interior cup fold FIRES at a NONZERO offset -/

/-- ★ **The interior cup fold fires at offset `1` behind one through wire.**  Firing `cupWord (natReplicate 1 1)`
(one cup at position `1`) on the one-bottom-wire seed prepends a single fresh pair AFTER the through wire `0` — the
general `cupFold_creates_atOffset` at the nonzero offset the position-`0` `cupFold_creates` could not reach. -/
theorem cupFold_creates_atOffset_throughOne :
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = 1
      ∧ (processBrauer (brauerSeed 1) (cupWord (natReplicate 1 1))).openWires
          = [0] ++ (flattenNatPairs freshFeet ++ []) := by
  obtain ⟨freshFeet, hLen, hOpen, _⟩ :=
    cupFold_creates_atOffset 1 1 (brauerSeed 1) [0] [] rfl rfl isUnionFindForest_nil
  exact ⟨freshFeet, hLen, hOpen⟩

/-- Cross-check: the interior cup at offset `1` behind one through wire realizes the straddle-shaped through+cup
matching `[1, 0, 3, 2]` — bottom `0` runs to top port `0` (the through strand), and the cup's two legs surface at top
ports `1`, `2`.  Decided directly; the concrete witness the general `cupFold_creates_atOffset` covers at a nonzero
offset. -/
theorem cupFold_atOffset_throughOne_diagram :
    brauerDiagramOf 1 (cupWord (natReplicate 1 1))
      = { bottomCount := 1, topCount := 3, partner := [1, 0, 3, 2], loops := 0 } := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the interior-offset cup PHASE FOLD is SHIPPED (R3-A-INTERIOR).**  `stepWiring_cup_interior`
and `cupFold_creates_atOffset` generalize the shipped position-`0` `stepWiring_cup_head` / `cupFold_creates` to the
`throughBottoms.length`-offset cup block the corrected extractor `reconstructStandardFormExt5Corrected` fires when
through-strands are present, via the append-at-front computation `natListInsertAtFront` (the position-generic
`stepWiring_connects_arc` supplies the arc connection unchanged), cross-checked FIRING at the nonzero offset `1`
behind one through wire (`cupFold_creates_atOffset_throughOne`, `cupFold_atOffset_throughOne_diagram`).  `= true`. -/
def fxBrauer_hasInteriorCupFold : Bool := true

/-- **Honesty WALL marker — R3-A-INTERIOR shipped does NOT close the roundtrip (the standing residual).**  The
interior cup fold is one of the three R3-A legs (R3-A-INTERIOR); the crossing-phase composition (R3-A-CROSSING-GLUE)
and above all the TAG CORRESPONDENCE (R3-A-TAGCORR — the read-off enumeration + the forest-cardinality disjointness
invariant + the target-closure lemma) remain unbuilt.  So `fxBrauer_hasExt5CorrectedRoundtripProof` /
`fxBrauer_hasExt5TotalExtractorRoundtrip` stay `false` (no flip fabricated); #2013 does not close.  `= false`. -/
def fxBrauer_hasInteriorCupFoldRoundtrip : Bool := false

end FX1Poly.Polygraph
