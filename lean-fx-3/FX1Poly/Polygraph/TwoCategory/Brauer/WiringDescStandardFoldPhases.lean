import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusConnectivityInduction
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractorRec
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerCompleteness

/-! # BRAUER-MIDDLE r4 R3-A machinery — the cup / cap PHASE-FOLD connectivity inductions (the FROB-shaped
new atoms the corrected-extractor roundtrip needs)

The R3-A roundtrip PROOF (`standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d`) reduces — exactly
as the FROB spider realization reduced to `spiderPartition_of_allConnected` — to a `stepWiring`-connectivity
structural induction over the six-phase standard-form fold (three crossing phases + cap + cup + circle).  The three
crossing phases are already a solved permutation/connectivity induction (`stateIsPermGraph`,
`extractDiagram_eq_permutationDiagram_ofPermGraph`).  The CAP-consumption and CUP-creation phases are the two
genuinely NEW inductions with no FROB analog: FROB's comb had `μ` (a `2 ⇒ 1` multiplication) and `δ` (a `1 ⇒ 2`
comultiplication), whereas the Brauer standard form uses the `2 ⇒ 0` CAP and the `0 ⇒ 2` CUP.

This file builds those two phase folds as the reusable atoms, zero-axiom, in the FROB style — reusing the shipped
crossing-inclusive arc-connection lemma `stepWiring_connects_arc`, the connectivity monotonicity
`processBrauer_isSameComponent_ofBase`, and the forest preservation `stepWiring_links_isUnionFindForest`.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`stepWiring_cup_head`** — one `cupAt 0` prepends a fresh CONNECTED pair `(nextFresh, nextFresh+1)` to the open
    wires (the `0 ⇒ 2` analog of FROB's `stepWiring_comult_head`).
  * **`stepWiring_cap_head`** — one `capAt 0` on `firstWire :: secondWire :: rest` connects the two head wires and
    drops them, leaving `rest` (the `2 ⇒ 0` analog of FROB's `stepWiring_mult_head`).
  * **`capFold_consumes`** — the CAP-consumption phase: firing `capWord (natReplicate feetPairs.length 0)` on a
    state whose open wires are `flattenNatPairs feetPairs ++ tail` consumes every front pair, leaving `tail`, and
    connects each consumed pair (the Brauer analog of FROB's `mergeFold_connects_all`).
  * **`cupFold_creates`** — the CUP-creation phase: firing `cupWord (natReplicate cupCount 0)` prepends `cupCount`
    fresh CONNECTED pairs, all still connected after the whole fold (the Brauer analog of FROB's `fanFold_connects`).

## Honest scope — this is the R3-A phase machinery, NOT the roundtrip

These are the position-0 cup / cap phase folds — directly load-bearing for the through-strand-free (pure cup / pure
cap) subclass, where the standard-form cup/cap blocks sit at position `0` (`throughBottoms.length = 0`).  The general
INTERIOR-position fold, the crossing-phase composition (`processBrauer_append`), and above all the TAG CORRESPONDENCE
(that `capArcFeet` / `throughStrandPerm` / `cupArcTops` / `permInverse` actually enumerate `d`'s arcs in fold order —
the read-off-correctness long pole with no FROB analog) remain the standing R3-A residual.  So
`fxBrauer_hasExt5CorrectedRoundtripProof` / `fxBrauer_hasExt5TotalExtractorRoundtrip` STAY `false` (no flip is
fabricated); `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` stay `false`; #2013 does not
close.

Raw Lean 4 + Init.  The Nat/list arithmetic uses only structural recursion + `List.Mem` constructor case analysis
(propext-free).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free list helper kit (structural, re-derived locally) -/

/-- Flatten a list of node-id pairs into the front-to-back open-wire order the cap / cup blocks act on:
`[(a, b), (c, d)] ↦ [a, b, c, d]`.  Structural, propext-free. -/
def flattenNatPairs : List (Nat × Nat) → List Nat
  | [] => []
  | (first, second) :: rest => first :: second :: flattenNatPairs rest

/-- `flattenNatPairs` commutes with a single-element append: the appended pair's two feet land at the back.
Structural on the pair list. -/
theorem flattenNatPairs_appendSingleton :
    (list : List (Nat × Nat)) → (extra : Nat × Nat) →
    flattenNatPairs (list ++ [extra]) = flattenNatPairs list ++ [extra.1, extra.2]
  | [], _ => rfl
  | (headFirst, headSecond) :: rest, extra => by
      show headFirst :: headSecond :: flattenNatPairs (rest ++ [extra])
          = headFirst :: headSecond :: (flattenNatPairs rest ++ [extra.1, extra.2])
      rw [flattenNatPairs_appendSingleton rest extra]

/-- Regroup a two-element tail append past a front list: `(front ++ [a, b]) ++ tail = front ++ (a :: b :: tail)`.
The targeted append-associativity the cup fold needs, structural on `front` (propext-free). -/
theorem appendPairRegroup : (front : List Nat) → (firstNode secondNode : Nat) → (tailList : List Nat) →
    (front ++ [firstNode, secondNode]) ++ tailList = front ++ (firstNode :: secondNode :: tailList)
  | [], _, _, _ => rfl
  | headNode :: rest, firstNode, secondNode, tailList => by
      show headNode :: ((rest ++ [firstNode, secondNode]) ++ tailList)
          = headNode :: (rest ++ (firstNode :: secondNode :: tailList))
      rw [appendPairRegroup rest firstNode secondNode tailList]

/-- Length after a single-element append: `(list ++ [extra]).length = list.length + 1`.  Structural, propext-free. -/
theorem lengthAppendSingleton {alpha : Type} : (list : List alpha) → (extra : alpha) →
    (list ++ [extra]).length = list.length + 1
  | [], _ => rfl
  | _ :: rest, extra => by
      show (rest ++ [extra]).length + 1 = (rest.length + 1) + 1
      rw [lengthAppendSingleton rest extra]

/-- Membership over a single-element append, decomposed by the `List.Mem` constructors (propext-free — no iff
lemma): an element of `list ++ [extra]` is either in `list` or equal to `extra`.  Structural on `list`. -/
theorem natPairMemAppendSingleton :
    (list : List (Nat × Nat)) → (extra elem : Nat × Nat) → elem ∈ list ++ [extra] →
    elem ∈ list ∨ elem = extra
  | [], _, _, hmem => by
      cases hmem with
      | head => exact Or.inr rfl
      | tail _ hrest => nomatch hrest
  | headPair :: rest, extra, elem, hmem => by
      cases hmem with
      | head => exact Or.inl (List.Mem.head rest)
      | tail _ hrest =>
          cases natPairMemAppendSingleton rest extra elem hrest with
          | inl hin => exact Or.inl (List.Mem.tail headPair hin)
          | inr heq => exact Or.inr heq

/-! ## The two new phase-atom lemmas — the Brauer cup (`0 ⇒ 2`) and cap (`2 ⇒ 0`) heads -/

/-- ★ **One cup at the head prepends a fresh connected pair.**  On any (forest) state, `stepWiring … cupWiring` at
position `0` leaves open wires `(0 + nextFresh) :: (1 + nextFresh) :: openWires` and connects the two fresh wires.
The `0 ⇒ 2` analog of FROB's `stepWiring_comult_head`; the connection is the arc `(0, 1)` of `cupWiring` through
`stepWiring_connects_arc`. -/
theorem stepWiring_cup_head (state : WireState) (forest : isUnionFindForest state.links) :
    (stepWiring state 0 cupWiring).openWires
        = (0 + state.nextFresh) :: (1 + state.nextFresh) :: state.openWires
      ∧ isSameComponent (stepWiring state 0 cupWiring).links
          (0 + state.nextFresh) (1 + state.nextFresh) = true := by
  refine ⟨?_, ?_⟩
  · show natListInsertAt (natListRemoveManyAt state.openWires 0 0) 0 ((List.range 2).map (· + state.nextFresh))
        = (0 + state.nextFresh) :: (1 + state.nextFresh) :: state.openWires
    simp only [natListRemoveManyAt, natListInsertAt, List.range, List.range.loop, List.map]; rfl
  · exact stepWiring_connects_arc state 0 cupWiring forest (0, 1) (List.Mem.head [])

/-- ★ **One cap at the head connects and drops the two head wires.**  On a state whose open wires are
`firstWire :: secondWire :: rest`, `stepWiring … capWiring` at position `0` leaves open wires `rest` and connects
`firstWire` with `secondWire`.  The `2 ⇒ 0` analog of FROB's `stepWiring_mult_head`; the connection is the arc
`(0, 1)` of `capWiring` through `stepWiring_connects_arc`. -/
theorem stepWiring_cap_head (state : WireState) (firstWire secondWire : Nat) (rest : List Nat)
    (hopen : state.openWires = firstWire :: secondWire :: rest) (forest : isUnionFindForest state.links) :
    (stepWiring state 0 capWiring).openWires = rest
      ∧ isSameComponent (stepWiring state 0 capWiring).links firstWire secondWire = true := by
  refine ⟨?_, ?_⟩
  · show natListInsertAt (natListRemoveManyAt state.openWires 0 2) 0 ((List.range 0).map (· + state.nextFresh))
        = rest
    rw [hopen]
    simp only [natListRemoveManyAt, natListInsertAt, List.range, List.range.loop, List.map]; rfl
  · have hconn := stepWiring_connects_arc state 0 capWiring forest (0, 1) (List.Mem.head [])
    rw [hopen] at hconn
    exact hconn

/-! ## The CAP-consumption phase fold -/

/-- ★ **The cap phase consumes every front pair and connects each.**  Firing `capWord (natReplicate
feetPairs.length 0)` — one cap at position `0` per listed pair — on a state whose open wires are
`flattenNatPairs feetPairs ++ tail` leaves exactly `tail` open, and every listed pair is same-component in the
resulting links.  Structural on `feetPairs`; the FROB `mergeFold_connects_all` analog for the `2 ⇒ 0` cap
(consuming pairs rather than merging to a hub).  The head pair is connected by `stepWiring_cap_head` and survives
the remaining caps by connectivity monotonicity `processBrauer_isSameComponent_ofBase`. -/
theorem capFold_consumes :
    (feetPairs : List (Nat × Nat)) → (state : WireState) → (tail : List Nat) →
    state.openWires = flattenNatPairs feetPairs ++ tail →
    isUnionFindForest state.links →
    (processBrauer state (capWord (natReplicate feetPairs.length 0))).openWires = tail
      ∧ ∀ pair, pair ∈ feetPairs →
          isSameComponent (processBrauer state (capWord (natReplicate feetPairs.length 0))).links
            pair.1 pair.2 = true
  | [], state, tail, hopen, _forest => by
      refine ⟨hopen, ?_⟩
      intro pair hmem; nomatch hmem
  | (firstFoot, secondFoot) :: rest, state, tail, hopen, forest => by
      have hopen' : state.openWires = firstFoot :: secondFoot :: (flattenNatPairs rest ++ tail) := hopen
      obtain ⟨hStepOpen, hStepConn⟩ :=
        stepWiring_cap_head state firstFoot secondFoot (flattenNatPairs rest ++ tail) hopen' forest
      have forest1 : isUnionFindForest (stepWiring state 0 capWiring).links :=
        stepWiring_links_isUnionFindForest state 0 capWiring forest
      have hStepOpen' : (stepWiring state 0 capWiring).openWires = flattenNatPairs rest ++ tail := hStepOpen
      obtain ⟨hIHOpen, hIHConn⟩ :=
        capFold_consumes rest (stepWiring state 0 capWiring) tail hStepOpen' forest1
      refine ⟨hIHOpen, ?_⟩
      intro pair hmem
      cases hmem with
      | head =>
          exact processBrauer_isSameComponent_ofBase (capWord (natReplicate rest.length 0))
            (stepWiring state 0 capWiring) forest1 firstFoot secondFoot hStepConn
      | tail _ hrest => exact hIHConn pair hrest

/-! ## The CUP-creation phase fold -/

/-- ★ **The cup phase prepends fresh connected pairs.**  Firing `cupWord (natReplicate cupCount 0)` — one cup at
position `0` per count — prepends exactly `cupCount` fresh pairs to the open wires (returned as `freshFeet`), each
still same-component in the resulting links.  Structural on `cupCount`; the FROB `fanFold_connects` analog for the
`0 ⇒ 2` cup.  Each already-placed pair's connection survives the later cups by the inductive hypothesis (it is over
the final links directly), and the newly placed pair survives by connectivity monotonicity
`processBrauer_isSameComponent_ofBase`. -/
theorem cupFold_creates :
    (cupCount : Nat) → (state : WireState) → isUnionFindForest state.links →
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = cupCount
      ∧ (processBrauer state (cupWord (natReplicate cupCount 0))).openWires
          = flattenNatPairs freshFeet ++ state.openWires
      ∧ ∀ pair, pair ∈ freshFeet →
          isSameComponent (processBrauer state (cupWord (natReplicate cupCount 0))).links
            pair.1 pair.2 = true
  | 0, state, _forest => by
      refine ⟨[], rfl, rfl, ?_⟩
      intro pair hmem; nomatch hmem
  | cupCount + 1, state, forest => by
      obtain ⟨hStepOpen, hStepConn⟩ := stepWiring_cup_head state forest
      have forest1 : isUnionFindForest (stepWiring state 0 cupWiring).links :=
        stepWiring_links_isUnionFindForest state 0 cupWiring forest
      obtain ⟨freshFeet', hLen', hOpen', hConn'⟩ :=
        cupFold_creates cupCount (stepWiring state 0 cupWiring) forest1
      refine ⟨freshFeet' ++ [(0 + state.nextFresh, 1 + state.nextFresh)], ?_, ?_, ?_⟩
      · rw [lengthAppendSingleton freshFeet' (0 + state.nextFresh, 1 + state.nextFresh), hLen']
      · show (processBrauer (stepWiring state 0 cupWiring) (cupWord (natReplicate cupCount 0))).openWires
            = flattenNatPairs (freshFeet' ++ [(0 + state.nextFresh, 1 + state.nextFresh)]) ++ state.openWires
        rw [hOpen', flattenNatPairs_appendSingleton freshFeet' (0 + state.nextFresh, 1 + state.nextFresh),
          hStepOpen]
        exact (appendPairRegroup (flattenNatPairs freshFeet') (0 + state.nextFresh) (1 + state.nextFresh)
          state.openWires).symm
      · intro pair hmem
        cases natPairMemAppendSingleton freshFeet' (0 + state.nextFresh, 1 + state.nextFresh) pair hmem with
        | inl hin =>
            show isSameComponent (processBrauer (stepWiring state 0 cupWiring)
                (cupWord (natReplicate cupCount 0))).links pair.1 pair.2 = true
            exact hConn' pair hin
        | inr heq =>
            show isSameComponent (processBrauer (stepWiring state 0 cupWiring)
                (cupWord (natReplicate cupCount 0))).links pair.1 pair.2 = true
            rw [heq]
            exact processBrauer_isSameComponent_ofBase (cupWord (natReplicate cupCount 0))
              (stepWiring state 0 cupWiring) forest1 (0 + state.nextFresh) (1 + state.nextFresh) hStepConn

/-! ## Non-vacuity — the phase folds FIRE on concrete pure-cup / pure-cap instances -/

/-- The cap phase consumes the two-cap front block `[(0, 1), (2, 3)]` over four bottom wires down to the empty
tail — the concrete pure-cap instance the general `capFold_consumes` covers. -/
theorem capFold_consumes_twoCaps :
    (processBrauer (brauerSeed 4) (capWord (natReplicate 2 0))).openWires = [] := by
  have result := capFold_consumes [(0, 1), (2, 3)] (brauerSeed 4) [] rfl isUnionFindForest_nil
  exact result.1

/-- The cup phase prepends exactly two fresh pairs from the empty seed — the concrete pure-cup instance the general
`cupFold_creates` covers: the general theorem instantiates with a two-pair `freshFeet` list that realizes the
open-wire prefix. -/
theorem cupFold_creates_twoCups :
    ∃ freshFeet : List (Nat × Nat),
      freshFeet.length = 2
      ∧ (processBrauer (brauerSeed 0) (cupWord (natReplicate 2 0))).openWires
          = flattenNatPairs freshFeet ++ (brauerSeed 0).openWires := by
  obtain ⟨freshFeet, hLen, hOpen, _⟩ := cupFold_creates 2 (brauerSeed 0) isUnionFindForest_nil
  exact ⟨freshFeet, hLen, hOpen⟩

/-- Cross-check: the concrete two-cup fold over the empty seed computes the ADJACENT-cups matching `[1, 0, 3, 2]`
(two fresh connected pairs, front-inserted at position `0`), decided directly.  Position-0 cups produce adjacent
arcs; the NESTED `[3, 2, 1, 0]` needs the top crossing staircase the corrected extractor adds — exactly the
recon's point that all reordering rides the crossing phases, which this cup fold deliberately does not. -/
theorem cupFold_twoCups_diagram :
    brauerDiagramOf 0 (cupWord (natReplicate 2 0))
      = { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 } := by decide

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the two NEW Brauer phase-fold connectivity inductions are SHIPPED (R3-A machinery).**
`stepWiring_cup_head` / `stepWiring_cap_head` are the `0 ⇒ 2` / `2 ⇒ 0` phase-atom lemmas FROB's comb lacked
(FROB has only the `2 ⇒ 1` `μ` and `1 ⇒ 2` `δ`), and `capFold_consumes` / `cupFold_creates` fold them into the
cap-consumption and cup-creation phase inductions — the Brauer analogs of FROB's `mergeFold_connects_all` /
`fanFold_connects`, each zero-axiom and structural, cross-checked FIRING on the concrete pure-cap
(`capFold_consumes_twoCaps`) and pure-cup / nested-cups-front (`cupFold_creates_twoCups`) instances.  `= true`. -/
def fxBrauer_hasCupCapPhaseFolds : Bool := true

/-- **Honesty WALL marker — the R3-A roundtrip is NOT closed by the phase folds (the standing residual).**  The
two phase folds are the position-0 cup / cap atoms — directly load-bearing for the through-strand-free subclass
(`throughBottoms.length = 0`), but the general interior-position fold, the crossing-phase composition, and above
all the TAG CORRESPONDENCE (that `capArcFeet` / `throughStrandPerm` / `cupArcTops` / `permInverse` actually
enumerate `d`'s arcs in the order the phases consume / produce them — the read-off-correctness long pole with no
FROB analog) remain unbuilt.  So `fxBrauer_hasExt5CorrectedRoundtripProof` /
`fxBrauer_hasExt5TotalExtractorRoundtrip` stay `false` (no flip fabricated), and
`fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` stay `false`; #2013 does not close.
`= false`. -/
def fxBrauer_hasExt5CorrectedRoundtripFromPhaseFolds : Bool := false

end FX1Poly.Polygraph
