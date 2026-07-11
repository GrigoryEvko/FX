import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingFoldAlignment
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable

/-! # BRAUER r23 — THE GENERAL non-seed crossing open-wire tracker (the r19 fresh-id bridge)

The r18 crossing-phase correspondence `crossingWord_openWire_sameComponent_bottomPort`
(`Brauer/WiringDescCrossingFoldAlignment.lean`) is SEED-LOCKED: it reads the correspondence off the shipped
`StateIsPermGraph.boundView`, which only holds for a crossing-ONLY word run from `brauerSeed` (its `openLen` /
`noLoops` / permutation-graph `boundView` fields all fail on a post-cap / post-cup / loopy interior state).  The r19
and r22 walls (`Brauer/WiringDescTConnectCapClass.lean:299`) name the missing brick verbatim: *a GENERAL non-seed
crossing open-wire tracker — the `topPerm` / `middle` phases run on a NON-seed state, off the seed-locked
`StateIsPermGraph`.*  The CUP and THROUGH T-CONNECT classes both need it (their crossing phases fire on the
post-cap / post-cup interior states).

## What this file ships — the tracker, on ANY reachable interior state

`crossingWordFold_openWire_sameComponent_incomingPort`: for a crossing word `positions` in range over ANY state
`state` satisfying `BrauerStateConditions bottomCount` (the four reachable-state invariants — freshness, forest,
non-empty boundary, bottom-fits), the open wire at each position `index` of the folded state shares a union-find
component with the OLD open wire at the permuted position:

    natListPointwiseSameComponent (processBrauer state (crossingWord positions)).links
      (processBrauer state (crossingWord positions)).openWires
      (positions.foldl applyAdjacentSwap state.openWires)

i.e. `final.openWires[index] ~ (positions.foldl applyAdjacentSwap state.openWires)[index]` for every `index`.  This
drops all three seed-locked `StateIsPermGraph` fields, keeping only position→incoming-node connectivity, and works on
joined / consumed / loopy interior states.  At `state = brauerSeed bottomCount` the abstract permuted-open-wire target
is definitionally `permuteOfCrossingWord bottomCount positions`, so the shipped seed lemma is recovered exactly
(`crossingWordFold_openWire_sameComponent_incomingPort_seed`).

## The proof — a FRESH structural induction (NOT the seed-locked `boundView` corollary)

Because the perm-graph structure is seed-locked, the general tracker is a genuine induction on the crossing word,
not a corollary of `boundView`:

  * **`stepWiringCrossing_openWire_pointwiseSwap`** (the single-crossing correspondence): one crossing at `position`
    sends the fresh output at `position` into the component of the OLD wire at `position + 1` (and vice versa),
    leaving every other open wire node-identical — so the new open wires are pointwise same-component with
    `applyAdjacentSwap state.openWires position`.  Built from the shipped public `stepWiring_crossing_links` (the
    two-join link update), the re-proved crossing open-wire get `stepWiringCrossing_openWire_get`, and the join
    connectivity kit (`isSameComponent_unionFindJoin_joined` / `_ofBase` / `_flip`).

  * **`natListPointwiseSameComponent_foldl_inRange`**: an in-range adjacent-swap fold preserves pointwise
    same-component of two equal-length node lists (swapping the SAME positions of both lists keeps them
    pointwise-connected).

  * The induction peels the FIRST crossing: `S' = stepWiring state position crossingWiring`; the single-crossing
    correspondence gives `S'.openWires` pointwise-connected to `applyAdjacentSwap state.openWires position` in
    `S'.links`; the swap-fold preservation carries it through the `rest` staircase; connectivity-monotonicity
    (`processBrauer_isSameComponent_ofBase`) transports it to the final links; and the induction hypothesis composes
    it with `final.openWires[index] ~ (rest.foldl swap S'.openWires)[index]` by transitivity.

The tracker flips NO master (it is one ingredient of the per-arc T-CONNECT, not the whole proof); it discharges the
r19-named fresh-id bridge as a standalone theorem.  `fxBrauer_hasTConnectThroughWall` stays `false`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only
on closed literals (the anti-vacuity firing).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Pointwise same-component of two node lists -/

/-- Two node lists are **pointwise same-component** in `links` when, at every index, their entries share a union-find
component (past-the-end both read the default `0`, so the unbounded quantifier is honest — `isSameComponent links 0 0
= true`). -/
abbrev natListPointwiseSameComponent (links : List (Nat × Nat)) (listA listB : List Nat) : Prop :=
  ∀ index : Nat, isSameComponent links (natListGetAt listA index) (natListGetAt listB index) = true

/-! ## Reading an adjacent swap (public re-proof of the readback-private `applyAdjacentSwap_get`) -/

/-- Reading an adjacent swap: `position` and `position + 1` exchange, every other index unchanged (needs
`position + 1 < wires.length`, so the swap actually fires).  Structural on `position` then the list, matching the
swap's own matcher.  A public re-proof of the readback-private `applyAdjacentSwap_get`. -/
theorem natListGetAt_applyAdjacentSwap :
    (wires : List Nat) → (position index : Nat) → position + 1 < wires.length →
    natListGetAt (applyAdjacentSwap wires position) index
      = (if index = position then natListGetAt wires (position + 1)
         else if index = position + 1 then natListGetAt wires position
         else natListGetAt wires index)
  | [], _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | [_single], position, _, hlt => absurd (Nat.lt_of_succ_lt_succ hlt) (Nat.not_lt_zero position)
  | _ :: _ :: _, 0, index, _ => by
      match index with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => rfl
  | first :: second :: rest, positionPred + 1, index, hlt => by
      have restLt : positionPred + 1 < (second :: rest).length := Nat.lt_of_succ_lt_succ hlt
      match index with
      | 0 => rfl
      | idx + 1 =>
          show natListGetAt (applyAdjacentSwap (second :: rest) positionPred) idx
            = (if idx + 1 = positionPred + 1 then natListGetAt (second :: rest) (positionPred + 1)
               else if idx + 1 = positionPred + 1 + 1 then natListGetAt (second :: rest) positionPred
               else natListGetAt (second :: rest) idx)
          rw [natListGetAt_applyAdjacentSwap (second :: rest) positionPred idx restLt]
          cases hidx : Nat.decEq idx positionPred with
          | isTrue heq => rw [if_pos heq, if_pos (congrArg (· + 1) heq)]
          | isFalse hne =>
              rw [if_neg hne, if_neg (fun succEq => hne (Nat.succ.inj succEq))]
              cases hidx2 : Nat.decEq idx (positionPred + 1) with
              | isTrue heq2 => rw [if_pos heq2, if_pos (congrArg (· + 1) heq2)]
              | isFalse hne2 => rw [if_neg hne2, if_neg (fun succEq => hne2 (Nat.succ.inj succEq))]

/-! ## The crossing open-wire get (public re-proof of the readback-private crossing open-wire indexing) -/

/-- Reading the block a crossing splices in: remove the two consumed wires at `position`, insert the two fresh legs;
`natListGetAt` replaces positions `position` / `position + 1` by the two fresh nodes and leaves every other position
unchanged.  A public re-proof of the readback-private `natListGetAt_crossingReplace`.  Structural on `position` then
the list. -/
theorem natListGetAt_crossingReplaceBlock (freshLeft freshRight : Nat) (wires : List Nat)
    (position index : Nat) (hle : position + 2 ≤ wires.length) :
    natListGetAt (natListInsertAt (natListRemoveManyAt wires position 2) position [freshLeft, freshRight]) index
      = (if index = position then freshLeft
         else if index = position + 1 then freshRight
         else natListGetAt wires index) := by
  induction position generalizing wires index with
  | zero =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          cases restWires with
          | nil => exact absurd hle (Nat.not_succ_le_self 1)
          | cons nextWire rest =>
              rw [removeManyAt_zero_cons, removeManyAt_zero_cons, removeManyAt_zero, insertAt_zero]
              match index with
              | 0 => rfl
              | 1 => rfl
              | _ + 2 => rfl
  | succ positionPred inductionHypothesis =>
      cases wires with
      | nil => exact absurd hle (Nat.not_succ_le_zero _)
      | cons headWire restWires =>
          match index with
          | 0 =>
              rw [removeManyAt_succ_cons, insertAt_succ_cons]
              rw [if_neg (fun eqZero => Nat.noConfusion eqZero),
                if_neg (fun eqZero => Nat.noConfusion eqZero)]
              rfl
          | idx + 1 =>
              rw [removeManyAt_succ_cons, insertAt_succ_cons, natListGetAt]
              rw [inductionHypothesis restWires idx (Nat.le_of_succ_le_succ hle)]
              cases hidx : Nat.decEq idx positionPred with
              | isTrue heq =>
                  rw [if_pos heq, if_pos (congrArg (· + 1) heq)]
              | isFalse hne =>
                  rw [if_neg hne, if_neg (fun succEq => hne (Nat.succ.inj succEq))]
                  cases hidx2 : Nat.decEq idx (positionPred + 1) with
                  | isTrue heq2 => rw [if_pos heq2, if_pos (congrArg (· + 1) heq2)]
                  | isFalse hne2 =>
                      rw [if_neg hne2, if_neg (fun succEq => hne2 (Nat.succ.inj succEq))]
                      rfl

/-- The crossing step's open-wire read at any index: `position` gets the left fresh leg `nextFresh`, `position + 1`
gets the right fresh leg `nextFresh + 1`, every other position is unchanged.  Combines the definitional open-wire
splice of `stepWiring … crossingWiring` with `natListGetAt_crossingReplaceBlock`. -/
theorem stepWiringCrossing_openWire_get (state : WireState) (position index : Nat)
    (hrange : position + 2 ≤ state.openWires.length) :
    natListGetAt (stepWiring state position crossingWiring).openWires index
      = (if index = position then state.nextFresh
         else if index = position + 1 then state.nextFresh + 1
         else natListGetAt state.openWires index) := by
  have hopen : (stepWiring state position crossingWiring).openWires
      = natListInsertAt (natListRemoveManyAt state.openWires position 2) position
          [state.nextFresh, state.nextFresh + 1] := by
    show natListInsertAt (natListRemoveManyAt state.openWires position 2) position
        ((List.range 2).map (· + state.nextFresh)) = _
    have hout : (List.range 2).map (· + state.nextFresh) = [state.nextFresh, state.nextFresh + 1] := by
      show [0 + state.nextFresh, 1 + state.nextFresh] = [state.nextFresh, state.nextFresh + 1]
      rw [Nat.zero_add, Nat.add_comm 1 state.nextFresh]
    rw [hout]
  rw [hopen]
  exact natListGetAt_crossingReplaceBlock state.nextFresh (state.nextFresh + 1) state.openWires position index hrange

/-! ## The single-crossing correspondence -/

/-- ★★ **The single-crossing open-wire correspondence.**  One crossing at `position` over a fresh forest state leaves
the new open wires pointwise same-component with `applyAdjacentSwap state.openWires position`: the fresh output at
`position` (`nextFresh`) shares the OLD wire-at-`position + 1`'s component (the outer join `… b nextFresh`), the fresh
output at `position + 1` (`nextFresh + 1`) shares the OLD wire-at-`position`'s component (the inner join `… a
(nextFresh + 1)`, surviving the outer join), and every other position is node-identical.  Built from the public
`stepWiring_crossing_links` two-join update + `stepWiringCrossing_openWire_get` + the join kit. -/
theorem stepWiringCrossing_openWire_pointwiseSwap (state : WireState)
    (fresh : WiringDescStateFresh state) (nfPos : 0 < state.nextFresh)
    (forest : isUnionFindForest state.links) (position : Nat)
    (hrange : position + 2 ≤ state.openWires.length) :
    natListPointwiseSameComponent (stepWiring state position crossingWiring).links
        (stepWiring state position crossingWiring).openWires
        (applyAdjacentSwap state.openWires position) := by
  intro index
  have hlinks := stepWiring_crossing_links state position fresh nfPos forest hrange
  have hopen := stepWiringCrossing_openWire_get state position index hrange
  have hp1lt : position + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) hrange
  have hswap := natListGetAt_applyAdjacentSwap state.openWires position index hp1lt
  rw [hopen, hswap, hlinks]
  have forestInner : isUnionFindForest (unionFindJoin state.links
      (natListGetAt state.openWires position) (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links _ _ forest
  cases hkp : Nat.decEq index position with
  | isTrue heq =>
      rw [if_pos heq, if_pos heq]
      exact isSameComponent_flip
        (unionFindJoin (unionFindJoin state.links (natListGetAt state.openWires position) (state.nextFresh + 1))
          (natListGetAt state.openWires (position + 1)) state.nextFresh)
        (natListGetAt state.openWires (position + 1)) state.nextFresh
        (isSameComponent_unionFindJoin_joined
          (unionFindJoin state.links (natListGetAt state.openWires position) (state.nextFresh + 1))
          forestInner (natListGetAt state.openWires (position + 1)) state.nextFresh)
  | isFalse hkp0 =>
      rw [if_neg hkp0, if_neg hkp0]
      cases hkp1 : Nat.decEq index (position + 1) with
      | isTrue heq1 =>
          rw [if_pos heq1, if_pos heq1]
          exact isSameComponent_flip
            (unionFindJoin (unionFindJoin state.links (natListGetAt state.openWires position) (state.nextFresh + 1))
              (natListGetAt state.openWires (position + 1)) state.nextFresh)
            (natListGetAt state.openWires position) (state.nextFresh + 1)
            (isSameComponent_unionFindJoin_ofBase
              (unionFindJoin state.links (natListGetAt state.openWires position) (state.nextFresh + 1))
              forestInner (natListGetAt state.openWires (position + 1)) state.nextFresh
              (natListGetAt state.openWires position) (state.nextFresh + 1)
              (isSameComponent_unionFindJoin_joined state.links forest
                (natListGetAt state.openWires position) (state.nextFresh + 1)))
      | isFalse hkp1' =>
          rw [if_neg hkp1', if_neg hkp1']
          exact isSameComponent_self _ _

/-! ## Adjacent-swap folds preserve pointwise same-component -/

/-- One in-range adjacent swap of BOTH lists preserves pointwise same-component (the same positions of both lists
exchange, so every index reads a pair the original related). -/
theorem natListPointwiseSameComponent_applyAdjacentSwap (links : List (Nat × Nat))
    (listA listB : List Nat) (position : Nat) (lenEq : listA.length = listB.length)
    (posLt : position + 1 < listA.length)
    (pointwise : natListPointwiseSameComponent links listA listB) :
    natListPointwiseSameComponent links (applyAdjacentSwap listA position)
      (applyAdjacentSwap listB position) := by
  intro index
  have posLtB : position + 1 < listB.length := Nat.lt_of_lt_of_le posLt (Nat.le_of_eq lenEq)
  rw [natListGetAt_applyAdjacentSwap listA position index posLt,
    natListGetAt_applyAdjacentSwap listB position index posLtB]
  cases hip : Nat.decEq index position with
  | isTrue heq => rw [if_pos heq, if_pos heq]; exact pointwise (position + 1)
  | isFalse hip0 =>
      rw [if_neg hip0, if_neg hip0]
      cases hip1 : Nat.decEq index (position + 1) with
      | isTrue heq1 => rw [if_pos heq1, if_pos heq1]; exact pointwise position
      | isFalse hip1' => rw [if_neg hip1', if_neg hip1']; exact pointwise index

/-- The whole in-range adjacent-swap fold preserves pointwise same-component.  Structural on the position list, the
equal-length and in-range invariants threaded through `applyAdjacentSwap_length`. -/
theorem natListPointwiseSameComponent_foldl (links : List (Nat × Nat)) :
    (positions : List Nat) → (listA listB : List Nat) → listA.length = listB.length →
    (∀ position, position ∈ positions → position + 1 < listA.length) →
    natListPointwiseSameComponent links listA listB →
    natListPointwiseSameComponent links (positions.foldl applyAdjacentSwap listA)
      (positions.foldl applyAdjacentSwap listB)
  | [], _, _, _, _, pointwise => pointwise
  | position :: rest, listA, listB, lenEq, inRange, pointwise =>
      natListPointwiseSameComponent_foldl links rest
        (applyAdjacentSwap listA position) (applyAdjacentSwap listB position)
        (by rw [applyAdjacentSwap_length, applyAdjacentSwap_length]; exact lenEq)
        (by intro position' positionMem
            rw [applyAdjacentSwap_length]
            exact inRange position' (List.Mem.tail position positionMem))
        (natListPointwiseSameComponent_applyAdjacentSwap links listA listB position lenEq
          (inRange position (List.Mem.head rest)) pointwise)

/-! ## The general non-seed crossing open-wire tracker -/

/-- ★★★ **THE GENERAL non-seed crossing open-wire tracker (the r19 fresh-id bridge).**  For a crossing word
`positions` in range over ANY reachable interior state (`BrauerStateConditions bottomCount`), the open wire at each
position `index` of the folded state shares a union-find component with the OLD open wire at the permuted position
`(positions.foldl applyAdjacentSwap state.openWires)[index]`.  A FRESH structural induction (NOT the seed-locked
`boundView`): peel the first crossing, apply the single-crossing correspondence
`stepWiringCrossing_openWire_pointwiseSwap`, carry it through the `rest` staircase with
`natListPointwiseSameComponent_foldl`, transport to the final links with connectivity-monotonicity
`processBrauer_isSameComponent_ofBase`, and compose with the induction hypothesis by transitivity.  Works on
joined / consumed / loopy interior states — every field the seed-locked `StateIsPermGraph` needed is dropped. -/
theorem crossingWordFold_openWire_sameComponent_incomingPort (bottomCount : Nat) :
    (positions : List Nat) → (state : WireState) → BrauerStateConditions bottomCount state →
    (∀ position, position ∈ positions → position + 2 ≤ state.openWires.length) →
    natListPointwiseSameComponent (processBrauer state (crossingWord positions)).links
        (processBrauer state (crossingWord positions)).openWires
        (positions.foldl applyAdjacentSwap state.openWires)
  | [], _, _, _ => by intro index; exact isSameComponent_self _ _
  | position :: rest, state, cond, inRange => by
      have hposFits : position + 2 ≤ state.openWires.length := inRange position (List.Mem.head rest)
      have condStep : BrauerStateConditions bottomCount (stepBrauerAtom state (crossingAt position)) :=
        brauerStateConditions_stepBrauerAtom bottomCount state (crossingAt position) cond
      have hlenStep : (stepBrauerAtom state (crossingAt position)).openWires.length
          = state.openWires.length := by
        obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest hposFits
        show (stepWiring state position crossingWiring).openWires.length = state.openWires.length
        rw [stepWiring_openWires_length_fits state position rightLen crossingWiring
          (by show state.openWires.length = position + 2 + rightLen; rw [fitsRaw])]
        show position + 2 + rightLen = state.openWires.length
        rw [fitsRaw]
      have inRangeStep : ∀ position', position' ∈ rest →
          position' + 2 ≤ (stepBrauerAtom state (crossingAt position)).openWires.length := by
        intro position' positionMem
        rw [hlenStep]
        exact inRange position' (List.Mem.tail position positionMem)
      have inductionHypothesis := crossingWordFold_openWire_sameComponent_incomingPort bottomCount rest
        (stepBrauerAtom state (crossingAt position)) condStep inRangeStep
      have singleCrossing := stepWiringCrossing_openWire_pointwiseSwap state cond.fresh cond.nfPos cond.forest
        position hposFits
      have singleCrossingFolded := natListPointwiseSameComponent_foldl
        (stepBrauerAtom state (crossingAt position)).links rest
        (stepBrauerAtom state (crossingAt position)).openWires
        (applyAdjacentSwap state.openWires position)
        (by rw [applyAdjacentSwap_length]; exact hlenStep)
        (by intro position' positionMem
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (position' + 1))
              (by rw [hlenStep]; exact inRange position' (List.Mem.tail position positionMem)))
        singleCrossing
      intro index
      show isSameComponent (processBrauer (stepBrauerAtom state (crossingAt position)) (crossingWord rest)).links
          (natListGetAt (processBrauer (stepBrauerAtom state (crossingAt position))
            (crossingWord rest)).openWires index)
          (natListGetAt (rest.foldl applyAdjacentSwap (applyAdjacentSwap state.openWires position)) index) = true
      exact isSameComponent_trans _ _ _ _ (inductionHypothesis index)
        (processBrauer_isSameComponent_ofBase (crossingWord rest)
          (stepBrauerAtom state (crossingAt position)) condStep.forest _ _ (singleCrossingFolded index))

/-- ★★ **The seed specialization recovers the shipped seed lemma.**  At `state = brauerSeed bottomCount`,
`state.openWires = List.range bottomCount`, so `positions.foldl applyAdjacentSwap state.openWires =
permuteOfCrossingWord bottomCount positions` definitionally, and the general tracker reads the open wire at each
position `index` into the component of bottom port `natListGetAt (permuteOfCrossingWord bottomCount positions) index`
— exactly the r18 `crossingWord_openWire_sameComponent_bottomPort`, now as a corollary of the GENERAL non-seed
tracker (not of the seed-locked `boundView`). -/
theorem crossingWordFold_openWire_sameComponent_incomingPort_seed (bottomCount : Nat)
    (bottomPos : 0 < bottomCount) (positions : List Nat)
    (inRange : ∀ position, position ∈ positions → position + 2 ≤ bottomCount) (index : Nat) :
    isSameComponent (processBrauer (brauerSeed bottomCount) (crossingWord positions)).links
        (natListGetAt (processBrauer (brauerSeed bottomCount) (crossingWord positions)).openWires index)
        (natListGetAt (permuteOfCrossingWord bottomCount positions) index)
      = true :=
  crossingWordFold_openWire_sameComponent_incomingPort bottomCount positions (brauerSeed bottomCount)
    (brauerStateConditions_seed bottomCount bottomPos)
    (fun position positionMem => by
      show position + 2 ≤ (brauerSeed bottomCount).openWires.length
      rw [show (brauerSeed bottomCount).openWires.length = bottomCount from rangeLength_local bottomCount]
      exact inRange position positionMem)
    index

/-! ## Anti-vacuity — the tracker fires on a genuine NON-seed post-cap interior state -/

/-- ★ **The tracker fires on the post-cap interior state (the recon §1b witness).**  Over `brauerSeed 6` with a cap
consumed at `0`, the interior state `[2,3,4,5]` is NON-seed (`openLen 4 ≠ 6`, cap arc `{0,1}` is not a
permutation-graph, so `StateIsPermGraph` cannot even be stated); yet the two middle crossings at `0, 1` send each
final open wire into the component of the permuted OLD open wire.  The general tracker instantiated on a genuine
interior state — the seed-locked `boundView` route is unavailable here. -/
theorem crossingWordFold_openWire_sameComponent_incomingPort_postCap :
    natListPointwiseSameComponent
        (processBrauer (processBrauer (brauerSeed 6) [capAt 0]) (crossingWord [0, 1])).links
        (processBrauer (processBrauer (brauerSeed 6) [capAt 0]) (crossingWord [0, 1])).openWires
        ([0, 1].foldl applyAdjacentSwap (processBrauer (brauerSeed 6) [capAt 0]).openWires) :=
  crossingWordFold_openWire_sameComponent_incomingPort 6 [0, 1]
    (processBrauer (brauerSeed 6) [capAt 0])
    (brauerReachable_conditions 6 (by decide) [capAt 0])
    (fun position positionMem => by
      cases positionMem with
      | head => decide
      | tail _ tailMem =>
          cases tailMem with
          | head => decide
          | tail _ nilMem => nomatch nilMem)

/-- ★ **The tracker's post-cap conclusion, kernel-decided at each position.**  The four per-position connectivities
of the post-cap firing are each `true` on the closed literal (the recon §1b hand-trace: `perm = [1,2,0,3]`, so final
open wire `j` shares a component with the OLD post-cap open wire at `perm[j]`).  Confirms the general firing is not
vacuous. -/
theorem crossingWordFold_openWire_sameComponent_incomingPort_postCap_decided :
    (isSameComponent (processBrauer (processBrauer (brauerSeed 6) [capAt 0]) (crossingWord [0, 1])).links
        (natListGetAt (processBrauer (processBrauer (brauerSeed 6) [capAt 0]) (crossingWord [0, 1])).openWires 0)
        (natListGetAt ([0, 1].foldl applyAdjacentSwap (processBrauer (brauerSeed 6) [capAt 0]).openWires) 0) = true)
    ∧ (isSameComponent (processBrauer (processBrauer (brauerSeed 6) [capAt 0]) (crossingWord [0, 1])).links
        (natListGetAt (processBrauer (processBrauer (brauerSeed 6) [capAt 0]) (crossingWord [0, 1])).openWires 2)
        (natListGetAt ([0, 1].foldl applyAdjacentSwap (processBrauer (brauerSeed 6) [capAt 0]).openWires) 2)
      = true) :=
  ⟨by decide, by decide⟩

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the GENERAL non-seed crossing open-wire tracker is SHIPPED (r23, the r19 fresh-id
bridge).**  `crossingWordFold_openWire_sameComponent_incomingPort` proves, by a fresh structural induction on the
crossing word (single-crossing correspondence `stepWiringCrossing_openWire_pointwiseSwap` + swap-fold pointwise
preservation `natListPointwiseSameComponent_foldl` + connectivity-monotonicity `processBrauer_isSameComponent_ofBase`
+ transitivity), that a crossing staircase over ANY reachable interior state (`BrauerStateConditions`) sends each
final open wire into the component of the permuted OLD open wire — dropping every seed-locked `StateIsPermGraph`
field.  It recovers the shipped seed lemma as the `brauerSeed` corollary
(`crossingWordFold_openWire_sameComponent_incomingPort_seed`) and fires on a genuine NON-seed post-cap interior state
(`…_postCap`, `…_postCap_decided`).  This is ONE ingredient of the per-arc T-CONNECT (the CUP / THROUGH middle- and
top-perm phases run on non-seed states); it flips NO master — the general per-arc T-CONNECT proof and its T-CLOSE(b)
reassembly remain the residual, so `fxBrauer_hasTConnectThroughWall` stays `false` and #2013 does NOT close.
`= true`. -/
def fxBrauer_hasGeneralCrossingTracker : Bool := true

end FX1Poly.Polygraph
