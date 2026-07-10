import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapNonCrossingJoin
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanNoLoops

/-! # WalkingString — the CAP orientation-preservation heart (WALL 1, the merge-dual of the cup)

The CUP case of `preserves` (`stringOrientationDiscipline_stepCup`) is shipped as a 16-region insert-dual.  This file
ships its MERGE-dual — the CAP case `stringOrientationDiscipline_stepCap` — the last per-step orientation residual the
headline no-loops flip owes.  Unlike the cup (which splices two FRESH legs), a cap MERGES two distinct arcs and DROPS
the window, so the survivor read is a `capRemap` backmap and the same-component survivor pair DISPATCHES three ways
(`sameComponent_unionFindJoin_dispatch`) — the exact machine the shipped `stringNonCrossing_stepCap` rides, here for
ONE survivor pair rather than two arcs.

## The survivor colour dispatch

A same-component new pair `lowPos < highPos` backmaps under `capRemap` to two OLD off-window indices
`sLo < sHi` whose wires are same-component in the JOINED links.  The join membership dispatches:

  * **BASE** — the pair was already same-component in the OLD links: the OLD `orient` delivers the cup word directly
    (COVERED by the shipped invariant);
  * **LEG** — `sLo` reaches the LEFT window wire (`position`), `sHi` the RIGHT (`position+1`);
  * **SWAP** — the mirror (`sLo` reaches RIGHT, `sHi` reaches LEFT).

Each of LEG / SWAP splits on the two survivors' off-window sides.  The INTERLEAVING sub-cases are refuted by the OLD
non-crossing (`StringNonCrossing`); the NESTED sub-cases are the genuinely NEW colour reads — a finite `WireLabel`
deduction (`stringCapOrient_legStraddle` / `_swapBelow` / `_swapAbove`) fed by the two OLD survivor-to-window cup words
and the window CAP word (`windowIsCapWord`, the string content WALL 2's reachable-`capPin` supplies: a cap fires on a
genuine cap word, never a degenerate `(G,G)`).

## The window-CAP-word hypothesis is load-bearing

`windowIsCapWord` is `isCapWordOrdered ... = true` (the genuine cap word `{(G,F), (H,G)}`), NOT merely
`isCupWordOrdered ... = false`: the weaker form admits a `(G,G)` window at which the nested colour deduction FAILS
`((F,H)` is not a cup word), so the merge-dual genuinely needs the cap's two-colour chirality, exactly the letter the
single-parity walking adjunction lacks.

Raw Lean 4 + Init; the label de-splice read is the generic remove-shift kit, the colour reads are full-enum
`WireLabel` case analysis, the refutations are the OLD non-crossing on a crossing quadruple, the survivor dispatch is
the shipped join membership.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private off-window arithmetic (per-file copies; the `StringCapNonCrossingJoin` originals are `private`) -/

/-- `position < index` whenever `index` is two-or-more above the window floor. -/
private theorem capOrientPositionLtAbove (position index : Nat) (above : position + 2 ≤ index) :
    position < index :=
  Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self position) (Nat.le_succ (position + 1))) above

/-- `position + 1 < index` whenever `index` is two-or-more above the window floor. -/
private theorem capOrientPositionSuccLtAbove (position index : Nat) (above : position + 2 ≤ index) :
    position + 1 < index :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) above

/-! ## The cap-side label de-splice read (dual of the wire read) -/

/-- ★ **A NEW label index (after a cap) reads its OLD label under `capRemap`.**  `stepCap` removes the two window
labels, so a new label index below the window reads the old label unmoved (L4), and at/above the window reads the old
label two slots up (L5) — either way the old label at `capRemap position index`.  The LABEL analog of
`stringStepCap_read_oldIndex`. -/
theorem stringStepCap_labelRead (labels : List WireLabel) (position index : Nat)
    (labelWindowInRange : position + 1 < labels.length) :
    wireLabelListGetAt (wireLabelListRemoveTwoAt labels position) index
      = wireLabelListGetAt labels (capRemap position index) := by
  rw [wireLabelListGetAt_eq_listGetAtD]
  show listGetAtD WireLabel.gWire (listRemoveTwoAt labels position) index
    = wireLabelListGetAt labels (capRemap position index)
  cases indexBelow : Nat.decLt index position with
  | isTrue below =>
      rw [listGetAtD_removeTwoAt_below WireLabel.gWire labels position index below,
        wireLabelListGetAt_eq_listGetAtD]
      show listGetAtD WireLabel.gWire labels index
        = listGetAtD WireLabel.gWire labels (if index < position then index else index + 2)
      rw [if_pos below]
  | isFalse notBelow =>
      have posLe : position ≤ index := Nat.le_of_not_lt notBelow
      rw [listGetAtD_removeTwoAt_above WireLabel.gWire labels position index labelWindowInRange posLe,
        wireLabelListGetAt_eq_listGetAtD]
      show listGetAtD WireLabel.gWire labels (index + 2)
        = listGetAtD WireLabel.gWire labels (if index < position then index else index + 2)
      rw [if_neg notBelow]

/-! ## The three NEW colour deductions (finite `WireLabel` reads) -/

/-- ★★ **LEG-straddle colour read.**  In the LEG survivor case with the two survivors straddling the window
(`sLo < position`, `position+1 < sHi`), the OLD `orient` gives `(labSLo, windowLow)` and `(windowHigh, labSHi)` cup
words; with the window a genuine CAP word, the survivors `(labSLo, labSHi)` read a cup word.  Full-enum `WireLabel`. -/
theorem stringCapOrient_legStraddle (windowLow windowHigh labSLo labSHi : WireLabel)
    (windowCap : isCapWordOrdered windowLow windowHigh = true)
    (survLowCup : isCupWordOrdered labSLo windowLow = true)
    (survHighCup : isCupWordOrdered windowHigh labSHi = true) :
    isCupWordOrdered labSLo labSHi = true := by
  cases windowLow <;> cases windowHigh <;> cases labSLo <;> cases labSHi <;>
    first
    | rfl
    | exact Bool.noConfusion windowCap
    | exact Bool.noConfusion survLowCup
    | exact Bool.noConfusion survHighCup

/-- ★★ **SWAP-both-below colour read.**  In the SWAP survivor case with both survivors below the window
(`sLo < sHi < position`), the OLD `orient` gives `(labSLo, windowHigh)` and `(labSHi, windowLow)` cup words; with the
window a genuine CAP word, `(labSLo, labSHi)` read a cup word.  Full-enum `WireLabel`. -/
theorem stringCapOrient_swapBelow (windowLow windowHigh labSLo labSHi : WireLabel)
    (windowCap : isCapWordOrdered windowLow windowHigh = true)
    (survLowCup : isCupWordOrdered labSLo windowHigh = true)
    (survHighCup : isCupWordOrdered labSHi windowLow = true) :
    isCupWordOrdered labSLo labSHi = true := by
  cases windowLow <;> cases windowHigh <;> cases labSLo <;> cases labSHi <;>
    first
    | rfl
    | exact Bool.noConfusion windowCap
    | exact Bool.noConfusion survLowCup
    | exact Bool.noConfusion survHighCup

/-- ★★ **SWAP-both-above colour read.**  In the SWAP survivor case with both survivors above the window
(`position+1 < sLo < sHi`), the OLD `orient` gives `(windowHigh, labSLo)` and `(windowLow, labSHi)` cup words; with the
window a genuine CAP word, `(labSLo, labSHi)` read a cup word.  Full-enum `WireLabel`. -/
theorem stringCapOrient_swapAbove (windowLow windowHigh labSLo labSHi : WireLabel)
    (windowCap : isCapWordOrdered windowLow windowHigh = true)
    (survLowCup : isCupWordOrdered windowHigh labSLo = true)
    (survHighCup : isCupWordOrdered windowLow labSHi = true) :
    isCupWordOrdered labSLo labSHi = true := by
  cases windowLow <;> cases windowHigh <;> cases labSLo <;> cases labSHi <;>
    first
    | rfl
    | exact Bool.noConfusion windowCap
    | exact Bool.noConfusion survLowCup
    | exact Bool.noConfusion survHighCup

/-! ## ★★ The CAP case of `preserves` -/

/-- ★★ **The CAP case of the orientation-discipline fold invariance.**  After `stepCap` at `position` MERGES the two
window arcs and drops them, the strand-orientation discipline is preserved — GIVEN the state's forest + non-crossing
(census is NOT needed for orient, unlike cap non-crossing) and the WINDOW being a genuine CAP word (`windowIsCapWord`,
the WALL-2 reachable-`capPin` fact).  The `sameLengths` half is `stringAdvanceLabels_sameLengths_cap`; the `orient`
half backmaps each same-component survivor pair under `capRemap` to two OLD off-window indices, dispatches their join
membership three ways, discharges BASE by the OLD `orient`, refutes the interleaving LEG/SWAP sub-cases by the OLD
non-crossing, and reads the nested sub-cases' cup word off the three NEW colour deductions.  This is the MERGE-dual of
the shipped 16-region `stringOrientationDiscipline_stepCup`, CLOSED given the connectivity substrate + the cap word. -/
theorem stringOrientationDiscipline_stepCap (state : WireState) (labels : List WireLabel)
    (position : Nat) (capInRange : position + 2 ≤ state.openWires.length)
    (forest : stringIsUnionFindForest state.links)
    (nonCrossing : StringNonCrossing state) (discipline : StringOrientationDiscipline state labels)
    (windowIsCapWord : isCapWordOrdered (wireLabelListGetAt labels position)
        (wireLabelListGetAt labels (position + 1)) = true) :
    StringOrientationDiscipline (stepCap state position)
      (wireLabelListRemoveTwoAt labels position) := by
  have windowInRange : position + 1 < state.openWires.length := Nat.lt_of_succ_le capInRange
  have positionLt : position < state.openWires.length := Nat.lt_of_succ_lt windowInRange
  have labelWindowInRange : position + 1 < labels.length := discipline.sameLengths ▸ windowInRange
  have sharedForest : isUnionFindForest state.links := stringForest_toUnionFindForest state.links forest
  refine ⟨?_, ?_⟩
  · exact stringAdvanceLabels_sameLengths_cap state labels position windowInRange discipline.sameLengths
  · intro lowPos highPos lowLtHigh highLtNew sameTrue
    have lowLtNew : lowPos < (stepCap state position).openWires.length := Nat.lt_trans lowLtHigh highLtNew
    obtain ⟨readLow, lowOldLt⟩ := stringStepCap_read_oldIndex state position lowPos windowInRange lowLtNew
    obtain ⟨readHigh, highOldLt⟩ := stringStepCap_read_oldIndex state position highPos windowInRange highLtNew
    have survLtSurv : capRemap position lowPos < capRemap position highPos :=
      capRemap_strictMono position lowPos highPos lowLtHigh
    have offLow := capRemap_offWindow position lowPos
    have offHigh := capRemap_offWindow position highPos
    rw [stringStepCap_labelRead labels position lowPos labelWindowInRange,
      stringStepCap_labelRead labels position highPos labelWindowInRange]
    have linksEq : (stepCap state position).links
        = unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)) :=
      stepCap_links_eq_unionFindJoin state position
    rw [linksEq, readLow, readHigh] at sameTrue
    have dispatch := sameComponent_unionFindJoin_dispatch state.links sharedForest
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
      (natListGetAt state.openWires (capRemap position lowPos))
      (natListGetAt state.openWires (capRemap position highPos)) sameTrue
    rcases dispatch with base | ⟨legLeft, legRight⟩ | ⟨swapLeft, swapRight⟩
    · -- BASE: the survivor pair was already same-component in the OLD links
      exact discipline.orient (capRemap position lowPos) (capRemap position highPos) survLtSurv highOldLt base
    · -- LEG: sLo ~ position (left window wire), sHi ~ position+1 (right window wire)
      rcases offLow with lowBelow | lowAbove
      · rcases offHigh with highBelow | highAbove
        · -- both below: interleaving (sLo, sHi, position, position+1) — refuted
          exact (nonCrossing (capRemap position lowPos) (capRemap position highPos) position (position + 1)
            survLtSurv highBelow (Nat.lt_succ_self position) windowInRange
            (isSameComponent_flip state.links _ _ legLeft)
            (isSameComponent_flip state.links _ _ legRight)).elim
        · -- straddle: nested — the LEG colour read
          exact stringCapOrient_legStraddle (wireLabelListGetAt labels position)
            (wireLabelListGetAt labels (position + 1)) (wireLabelListGetAt labels (capRemap position lowPos))
            (wireLabelListGetAt labels (capRemap position highPos)) windowIsCapWord
            (discipline.orient (capRemap position lowPos) position lowBelow positionLt
              (isSameComponent_flip state.links _ _ legLeft))
            (discipline.orient (position + 1) (capRemap position highPos)
              (capOrientPositionSuccLtAbove position (capRemap position highPos) highAbove) highOldLt legRight)
      · rcases offHigh with highBelow | highAbove
        · -- sLo above, sHi below: impossible (sLo > sHi contradicts sLo < sHi)
          exact absurd survLtSurv (Nat.lt_asymm (Nat.lt_trans highBelow
            (capOrientPositionLtAbove position (capRemap position lowPos) lowAbove)))
        · -- both above: interleaving (position, position+1, sLo, sHi) — refuted
          exact (nonCrossing position (position + 1) (capRemap position lowPos) (capRemap position highPos)
            (Nat.lt_succ_self position)
            (capOrientPositionSuccLtAbove position (capRemap position lowPos) lowAbove)
            survLtSurv highOldLt legLeft legRight).elim
    · -- SWAP: sLo ~ position+1 (right window wire), sHi ~ position (left window wire)
      rcases offLow with lowBelow | lowAbove
      · rcases offHigh with highBelow | highAbove
        · -- both below: nested — the SWAP-below colour read
          exact stringCapOrient_swapBelow (wireLabelListGetAt labels position)
            (wireLabelListGetAt labels (position + 1)) (wireLabelListGetAt labels (capRemap position lowPos))
            (wireLabelListGetAt labels (capRemap position highPos)) windowIsCapWord
            (discipline.orient (capRemap position lowPos) (position + 1) (Nat.lt_succ_of_lt lowBelow)
              windowInRange swapRight)
            (discipline.orient (capRemap position highPos) position highBelow positionLt
              (isSameComponent_flip state.links _ _ swapLeft))
        · -- straddle: interleaving (sLo, position, position+1, sHi) — refuted
          exact (nonCrossing (capRemap position lowPos) position (position + 1) (capRemap position highPos)
            lowBelow (Nat.lt_succ_self position)
            (capOrientPositionSuccLtAbove position (capRemap position highPos) highAbove) highOldLt
            swapRight swapLeft).elim
      · rcases offHigh with highBelow | highAbove
        · -- sLo above, sHi below: impossible
          exact absurd survLtSurv (Nat.lt_asymm (Nat.lt_trans highBelow
            (capOrientPositionLtAbove position (capRemap position lowPos) lowAbove)))
        · -- both above: nested — the SWAP-above colour read
          exact stringCapOrient_swapAbove (wireLabelListGetAt labels position)
            (wireLabelListGetAt labels (position + 1)) (wireLabelListGetAt labels (capRemap position lowPos))
            (wireLabelListGetAt labels (capRemap position highPos)) windowIsCapWord
            (discipline.orient (position + 1) (capRemap position lowPos)
              (capOrientPositionSuccLtAbove position (capRemap position lowPos) lowAbove) lowOldLt
              (isSameComponent_flip state.links _ _ swapRight))
            (discipline.orient position (capRemap position highPos)
              (capOrientPositionLtAbove position (capRemap position highPos) highAbove) highOldLt swapLeft)

/-! ## Honesty marker (flip) -/

/-- **★ ESTABLISHED — the CAP case of `preserves` is CLOSED (WALL 1, the merge-dual of the cup).**
`stringOrientationDiscipline_stepCap` carries the strand-orientation discipline through a `stepCap`, GIVEN the joint
invariant's forest + non-crossing and the window being a genuine CAP word.  The `sameLengths` half is the
shipped cap-length lemma; the `orient` half backmaps each survivor pair under `capRemap`, dispatches the join membership
three ways (`sameComponent_unionFindJoin_dispatch`), discharges BASE by the OLD `orient`, refutes the LEG-both-below /
LEG-both-above / SWAP-straddle interleavings by the OLD non-crossing, and reads the LEG-straddle / SWAP-below /
SWAP-above nested sub-cases' cup word off the three NEW finite-`WireLabel` colour deductions
(`stringCapOrient_legStraddle` / `_swapBelow` / `_swapAbove`), fed the window CAP word.  With the shipped CUP case
`stringOrientationDiscipline_stepCup`, this is the FULL per-atom orientation preservation — the second of the two
per-step residuals the headline no-loops flip owed (the first, `capPin`, is WALL 2's reachable-`capPin` fold).  All the
regions land; the merge-dual table is COMPLETE.  Zero-axiom.  `= true`. -/
def fxString_hasOrientationCapPreserves : Bool := true

end FX1Poly.Polygraph
