import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapPreserves

/-! # WalkingString — the CAP non-crossing infrastructure + the LOOP-branch preservation (FC-4, P1)

The CUP non-crossing preservation (`stringNonCrossing_stepCup`, in `StringFussCatalanNonCrossing`) is CLOSED.  Its dual
`stringNonCrossing_stepCap` — a cap step preserves planarity — is the FC-4 P1 leg.  `stepCap` at `position` REMOVES the
two window wires `(position, position+1)`; the new open-wire list is a two-drop of the old, so every surviving wire is
an OLD wire read at the shifted index `capRemap` (below the window unmoved, at/above the window shifted UP by 2 — the
mirror of the cup's `cupUnmap`).  This file ships:

  * ★ `capRemap` (below ↦ self, at/above ↦ `+2`) + `capRemap_strictMono` — the de-drop index map and its strict
    monotonicity on the new indices, the CAP analog of `cupUnmap` / `cupUnmap_strictMono`.  Purely additive (`+2`), so
    it is CLEANER than the cup case (no `Nat` subtraction);
  * ★ `stringStepCap_read_oldIndex` — a new open-wire index reads the OLD wire at `capRemap position index`, and the
    unmapped index stays in the old range (via the shipped L4/L5 remove-shift kit);
  * ★ `stringStepCap_links_loopBranch` — in the LOOP branch (the cap fires on a same-component window) the links are
    UNCHANGED;
  * ★★ `stringNonCrossing_stepCap_loopBranch` — the LOOP-branch case of the CAP non-crossing fold invariance: with the
    links unchanged and the surviving wires a monotone re-index of the old wires, any post-cap interleaving pulls back
    to a pre-cap interleaving, refuted by the OLD non-crossing.  UNCONDITIONAL, zero-axiom.

## The JOIN branch — the honest wall (the ported perfect-matching CENSUS + the survivor analysis)

`stringNonCrossing_stepCap` in the JOIN branch (the cap fires on a DISTINCT-component window, `links` gains one edge
`(rootLeft, rootRight)`) is genuinely harder — the string port of the shipped `arcNonCrossing_stepCapArc`
(`ArcNonCrossingCapMain`), a ~230-line survivor analysis whose FIVE surviving join-dispatch combos each exhibit an OLD
crossing quadruple, while the FOUR "two survivors reach the same window end" combos are refuted by a BOUNDARY CENSUS
(`ArcBoundaryCensus`: every union-find component carries at most two OPEN-wire ends — the perfect-matching structure
of a planar cup/cap diagram).  That census is a genuine NEW fold invariant with its own seed / cup / cap preservation,
NOT yet ported over the bare `WireState`; the join-dispatch is the shipped `isSameComponent_unionFindJoin_split`
(available over the byte-identical `isUnionFindForest` via a trivial forest bridge).  So `stringNonCrossing_stepCap`
(full) STAYS a multi-round port, with the residual localized to exactly the census port + the survivor combo analysis
(see the honesty markers).  `fxString_hasNoLoopsTheorem` (in `StringFussCatalan`) stays `false`, honestly.

Raw Lean 4 + Init; the index map is a two-branch `if`, the strict monotonicity is additive `Nat` arithmetic, the reads
route through the shipped generic remove-shift kit, the loop-branch invariance is a monotone pullback.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The de-drop index map — new index below the window is unmoved, at/above shifts UP by 2 -/

/-- Send a NEW open-wire index (after a cap two-drop at `position`) back to its OLD index: below the window unmoved,
at/above the window shifted UP by 2 (the two consumed wires).  The CAP analog of `cupUnmap`; purely additive. -/
def capRemap (position index : Nat) : Nat := if index < position then index else index + 2

/-- ★ **`capRemap` is strictly monotone on the new indices.**  Below-window indices map to themselves, at/above-window
indices shift up by 2 while staying above the below-window image — so the strict order is preserved across the 2-gap.
The CAP analog of `cupUnmap_strictMono`, additive (no subtraction). -/
theorem capRemap_strictMono (position lower higher : Nat) (lowerLtHigher : lower < higher) :
    capRemap position lower < capRemap position higher := by
  show (if lower < position then lower else lower + 2) < (if higher < position then higher else higher + 2)
  cases lowerBelow : Nat.decLt lower position with
  | isTrue lowerBelowPos =>
      rw [if_pos lowerBelowPos]
      cases higherBelow : Nat.decLt higher position with
      | isTrue higherBelowPos => rw [if_pos higherBelowPos]; exact lowerLtHigher
      | isFalse higherNotBelow =>
          rw [if_neg higherNotBelow]
          exact Nat.lt_trans lowerLtHigher (Nat.lt_succ_of_lt (Nat.lt_succ_self higher))
  | isFalse lowerNotBelow =>
      have higherNotBelow : ¬ higher < position :=
        fun higherBelowPos => lowerNotBelow (Nat.lt_trans lowerLtHigher higherBelowPos)
      rw [if_neg lowerNotBelow, if_neg higherNotBelow]
      exact Nat.succ_lt_succ (Nat.succ_lt_succ lowerLtHigher)

/-! ## A new open-wire index reads the old wire under `capRemap`, staying in range -/

/-- ★ **A NEW open-wire index (after a cap) reads its OLD wire under `capRemap`, and the unmapped index stays in the
old range.**  `stepCap`'s open wires are `natListRemoveTwoAt state.openWires position` in BOTH branches, so a new index
below the window reads the old wire unmoved (L4), and at/above the window reads the old wire two slots up (L5) — either
way it reads `state.openWires` at `capRemap position index`, and the unmapped index is below the old length. -/
theorem stringStepCap_read_oldIndex (state : WireState) (position index : Nat)
    (windowInRange : position + 1 < state.openWires.length)
    (indexLt : index < (stepCap state position).openWires.length) :
    natListGetAt (stepCap state position).openWires index
        = natListGetAt state.openWires (capRemap position index)
      ∧ capRemap position index < state.openWires.length := by
  have owEq : (stepCap state position).openWires = natListRemoveTwoAt state.openWires position := by
    dsimp only [stepCap]; split <;> rfl
  have newLen : (stepCap state position).openWires.length + 2 = state.openWires.length :=
    stringStepCap_openWires_length state position windowInRange
  cases indexBelow : Nat.decLt index position with
  | isTrue below =>
      refine ⟨?_, ?_⟩
      · rw [owEq, natListGetAt_eq_listGetAtD, natListRemoveTwoAt_eq_listRemoveTwoAt,
          listGetAtD_removeTwoAt_below 0 state.openWires position index below, natListGetAt_eq_listGetAtD]
        show listGetAtD 0 state.openWires index
          = listGetAtD 0 state.openWires (if index < position then index else index + 2)
        rw [if_pos below]
      · show (if index < position then index else index + 2) < state.openWires.length
        rw [if_pos below]
        exact Nat.lt_trans below (Nat.lt_of_succ_lt windowInRange)
  | isFalse notBelow =>
      have posLeIndex : position ≤ index := Nat.le_of_not_lt notBelow
      refine ⟨?_, ?_⟩
      · rw [owEq, natListGetAt_eq_listGetAtD, natListRemoveTwoAt_eq_listRemoveTwoAt,
          listGetAtD_removeTwoAt_above 0 state.openWires position index windowInRange posLeIndex,
          natListGetAt_eq_listGetAtD]
        show listGetAtD 0 state.openWires (index + 2)
          = listGetAtD 0 state.openWires (if index < position then index else index + 2)
        rw [if_neg notBelow]
      · show (if index < position then index else index + 2) < state.openWires.length
        rw [if_neg notBelow]
        exact newLen ▸ Nat.succ_lt_succ (Nat.succ_lt_succ indexLt)

/-! ## The links are unchanged in the LOOP branch -/

/-- ★ **In the LOOP branch a cap leaves the links unchanged.**  When the window `(position, position+1)` is
same-component, `stepCap` takes the loop branch: it drops the two wires and increments `loops`, but keeps `links`
verbatim.  So the connectivity of the surviving wires is exactly the old connectivity. -/
theorem stringStepCap_links_loopBranch (state : WireState) (position : Nat)
    (windowSame : isSameComponent state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)) = true) :
    (stepCap state position).links = state.links := by
  dsimp only [stepCap]
  split
  · rfl
  · next windowDistinct => exact absurd windowSame windowDistinct

/-! ## ★★ The LOOP-branch case of the CAP non-crossing fold invariance -/

/-- ★★ **The LOOP-branch CAP non-crossing preservation.**  When the cap fires on a SAME-component window (the loop
branch), the links are UNCHANGED (`stringStepCap_links_loopBranch`) and every surviving open wire reads its old wire at
`capRemap` (`stringStepCap_read_oldIndex`).  So any post-cap interleaving `lowA < lowB < highA < highB` pulls back
under `capRemap` (strictly monotone) to an OLD interleaving of the SAME wires with the SAME links, which the OLD
non-crossing rules out.  UNCONDITIONAL for the loop branch, zero-axiom.  (The JOIN branch — where the cap adds a merge
edge — is the harder residual walled below.) -/
theorem stringNonCrossing_stepCap_loopBranch (state : WireState) (position : Nat)
    (windowInRange : position + 1 < state.openWires.length)
    (windowSame : isSameComponent state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)) = true)
    (nonCrossing : StringNonCrossing state) :
    StringNonCrossing (stepCap state position) := by
  intro lowA lowB highA highB lowALtLowB lowBLtHighA highALtHighB highBLt sameA sameB
  have linksEq : (stepCap state position).links = state.links :=
    stringStepCap_links_loopBranch state position windowSame
  have highBLtNew : highB < (stepCap state position).openWires.length := highBLt
  have highALtNew : highA < (stepCap state position).openWires.length := Nat.lt_trans highALtHighB highBLtNew
  have lowBLtNew : lowB < (stepCap state position).openWires.length := Nat.lt_trans lowBLtHighA highALtNew
  have lowALtNew : lowA < (stepCap state position).openWires.length := Nat.lt_trans lowALtLowB lowBLtNew
  obtain ⟨readLowA, _⟩ := stringStepCap_read_oldIndex state position lowA windowInRange lowALtNew
  obtain ⟨readLowB, _⟩ := stringStepCap_read_oldIndex state position lowB windowInRange lowBLtNew
  obtain ⟨readHighA, _⟩ := stringStepCap_read_oldIndex state position highA windowInRange highALtNew
  obtain ⟨readHighB, rangeHighB⟩ := stringStepCap_read_oldIndex state position highB windowInRange highBLtNew
  rw [linksEq, readLowA, readHighA] at sameA
  rw [linksEq, readLowB, readHighB] at sameB
  exact nonCrossing (capRemap position lowA) (capRemap position lowB) (capRemap position highA)
    (capRemap position highB)
    (capRemap_strictMono position lowA lowB lowALtLowB)
    (capRemap_strictMono position lowB highA lowBLtHighA)
    (capRemap_strictMono position highA highB highALtHighB)
    rangeHighB sameA sameB

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the CAP non-crossing INFRASTRUCTURE + the LOOP-branch preservation.**  The de-drop index map
`capRemap` (below the window unmoved, at/above shifted up by 2) is shipped with its strict monotonicity
(`capRemap_strictMono`, the additive CAP analog of `cupUnmap_strictMono`), the new-index-reads-old-wire lemma
(`stringStepCap_read_oldIndex`, via the shipped L4/L5 remove-shift kit), and the loop-branch links-unchanged fact
(`stringStepCap_links_loopBranch`).  On top of these, `stringNonCrossing_stepCap_loopBranch` closes the LOOP-branch case
of the CAP non-crossing fold invariance UNCONDITIONALLY: with links unchanged and survivors a monotone re-index of the
old wires, any post-cap interleaving pulls back to an OLD interleaving the old non-crossing forbids.  Zero-axiom.
`= true`. -/
def fxString_hasCapNonCrossingLoopBranch : Bool := true

/-- **OPEN (honest, LOCALIZED) — the JOIN-branch CAP non-crossing owes the ported perfect-matching CENSUS + the
survivor combo analysis.**  `stringNonCrossing_stepCap` in the JOIN branch (a DISTINCT-component window: `links` gains
one merge edge `(rootLeft, rootRight)`) is the string port of the shipped `arcNonCrossing_stepCapArc`
(`ArcNonCrossingCapMain`), which needs two ingredients over the bare `WireState`, neither yet ported:

  * **the boundary CENSUS** `StringBoundaryCensus` — every union-find component carries at most TWO open-wire ends (the
    perfect-matching structure of a planar cup/cap diagram).  As of FC-5 P1 this census is SHIPPED over the bare
    `WireState` in `StringBoundaryCensus` (statement + seed + cup + cap preservation + the whole-fold transport
    `stringBoundaryCensus_fromCell`, all zero-axiom).  It is LOAD-BEARING: the four join-dispatch combos where two
    survivors reach the SAME consumed window end are refuted precisely because that end's component would then carry
    three boundary ends;
  * **the survivor combo analysis** — the join-dispatch (`sameComponent_unionFindJoin_dispatch`, available over the
    byte-identical `isUnionFindForest` via the shipped `stringForest_toUnionFindForest` bridge) times the two paired
    components gives nine combos; the five surviving ones each exhibit an OLD crossing quadruple (from the six tokens
    `{A',B',C',D', capLeft, capRight}` by a position split), which the OLD non-crossing forbids.

So with the CENSUS now SHIPPED (FC-5 P1), the sole remaining residual of `stringNonCrossing_stepCap` (join branch) is
the survivor combo analysis — the string port of `ArcNonCrossingCapMain`; `fxString_hasNoLoopsTheorem` (in
`StringFussCatalan`) stays `false`, honestly (and additionally owes the `capPin` label-tracking, which the census does
NOT unlock — see `fxString_hasBoundaryCensusUnlocksBothResiduals`).  `= false`. -/
def fxString_hasCapNonCrossingJoinBranch : Bool := false

/-! ## Non-vacuity — the general loop-freedom reduction discharges on THREE real cells (incl. the cross-level cell) -/

/-- The lower cup `η : id ⇒ F·G` is loop-free via the general reduction (its single cap-free spine trivially satisfies
`CapsDistinctAlongFold`). -/
theorem stringUnitLower_loops_zero_viaReduction :
    (matchingOf stringUnitLower).loops = 0 :=
  stringMatchingOf_loops_zero_ofCapsDistinct stringUnitLower (by decide)

/-- ★ **The FC-0 cross-level cell `G·F ⇒ G·H` is loop-free via the general reduction** — a genuine cross-level cell (in
NEITHER single adjunction) with a real cap `ε`, loop-free because its cap fires on a distinct-component window
(`CapsDistinctAlongFold`, `decide`d). -/
theorem stringCrossLevelCell_loops_zero_viaReductionN :
    (matchingOf stringCrossLevelCell).loops = 0 :=
  stringMatchingOf_loops_zero_ofCapsDistinct stringCrossLevelCell (by decide)

/-- The `F`-snake `(left ◁ counit) ∘ (unit ▷ left)` — a cup THEN a cap — is loop-free via the general reduction: its
cap fires on a DISTINCT-component window (the through-strand), so `CapsDistinctAlongFold` holds. -/
theorem stringSnakeF_loops_zero_viaReduction :
    (matchingOf stringSnakeF).loops = 0 :=
  stringMatchingOf_loops_zero_ofCapsDistinct stringSnakeF (by decide)

-- Loop counts of three real cells (unit cup, cross-level cell, F-snake), displayed at build time — `[0, 0, 0]`.
#eval [(matchingOf stringUnitLower).loops, (matchingOf stringCrossLevelCell).loops,
       (matchingOf stringSnakeF).loops]

/-- **★ ESTABLISHED — the loop-freedom reduction is NON-VACUOUS on three real cells.**  The general no-loops reduction
`stringMatchingOf_loops_zero_ofCapsDistinct` discharges `(matchingOf cell).loops = 0` on three genuine
walking-adjoint-triple cells — the lower cup `η` (`stringUnitLower_loops_zero_viaReduction`), the FC-0 CROSS-LEVEL cell
`G·F ⇒ G·H` with a real cap (`stringCrossLevelCell_loops_zero_viaReductionN`), and the `F`-SNAKE
`(left ◁ counit) ∘ (unit ▷ left)` whose cap fires on a distinct (through-strand) window
(`stringSnakeF_loops_zero_viaReduction`) — each by `decide`-discharging `CapsDistinctAlongFold`, and the `#eval`
displays `[0, 0, 0]`.  So the reduction is a live path to loop-freedom, not a vacuous statement.  `= true`. -/
def fxString_hasCapNonCrossingNonVacuity : Bool := true

end FX1Poly.Polygraph
