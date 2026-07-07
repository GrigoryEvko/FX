import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyFloorHomogeneous
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SurvivorTopRank
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanLocalize
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCupWindowScanSplit

/-! # ValleyMatchingClassification — the survivor-top CLASSIFICATION lemma (Piece II tail crux)

The valley-append split's inversion handle is a CLASSIFICATION of the whole valley `V = capBlock ++
cupBlock`'s TOP ports over bottom count `bc`: a top port `bc + p` is a **survivor-top** (its partner is a
bottom, `partner < bc`) EXACTLY when its own wire value is a survivor value (`finalOpen[p] < bc`), and a
**cup-leg top** (its partner is another top, `partner ≥ bc`) exactly when its wire value is a cup leg
(`finalOpen[p] ≥ bc`).  This file lands that classification as an equation of `Bool`s:

  * ★ `isSurvivorTop_extractDiagram_classify` — for ANY final wire state whose links are FLOOR-SEPARATED
    (every below-`bc` node keeps its root `< bc`, every at-or-above-`bc` node keeps its root `≥ bc`), a top
    port `bc + topOffset` is a survivor-top iff its own open-wire value is `< bc`:
    `isSurvivorTop (extractDiagram bc finalState) (bc + topOffset)
        = decide (natListGetAt finalState.openWires topOffset < bc)`.

  * ★ `isSurvivorTop_matchingValley_classify` — the whole-valley instance, discharging the floor-separation
    hypotheses from the shipped N1/N2 root facts (`valleyRootBelowFloor` / `valleyCupLegRootAboveFloor`).

The proof is a clean bounded composition of the shipped kernel: the boundary reads
(`matchingBoundaryNodes_getAt_bottom` / `_top`), the partner-scan localization duals N3a/N3b
(`findPartnerScan_result_passes_of_exists` / `_result_ge_of_all_ge`), the first-hit / front-miss split
(`findPartnerScan_append_ofFoundInFront` / `findPartnerScan_range_frontSegmentMisses`, `rangeSplit`), and
the two whole-valley root facts N1/N2.  The survivor direction's witness is the top port's OWN wire value
`v` (which, being `< bc`, IS a bottom boundary index sharing its component), so no phi-surjectivity input is
needed — the classification is unconditional on the two root facts.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local range plumbing (propext-free) -/

private theorem rangeLoopLenLocal : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenLocal count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenLocal (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenLocal count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastLocal : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastLocal count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowLocal : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowLocal count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastLocal count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowLocal (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowLocal count [] index indexBelow

/-- Reading `(List.range total).map mappedFunction` at an in-range index is `mappedFunction index`. -/
private theorem natRangeMapGetAtLocal (total : Nat) (mappedFunction : Nat → Nat) (index : Nat)
    (indexInRange : index < total) :
    natListGetAt ((List.range total).map mappedFunction) index = mappedFunction index := by
  rw [natListGetAt_map_inRange mappedFunction (List.range total) index
      (by rw [rangeLenLocal total]; exact indexInRange),
    rangeGetAtBelowLocal total index indexInRange]

/-- Every member of `(List.range count).map (base + ·)` is at or above `base`. -/
private theorem le_of_mem_mapAdd (base : Nat) :
    (values : List Nat) → ∀ x, x ∈ values.map (fun offset => base + offset) → base ≤ x
  | [], _, xMem => nomatch xMem
  | head :: rest, x, xMem => by
      have xMem' : x ∈ (base + head) :: rest.map (fun offset => base + offset) := xMem
      cases xMem' with
      | head => exact Nat.le_add_right base head
      | tail _ xInRest => exact le_of_mem_mapAdd base rest x xInRest

/-! ## `Nat.blt` against `decide` on the partner value -/

private theorem natBltEqTrueOfLt {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

private theorem natBltEqFalseOfGe {bound value : Nat} (isGe : bound ≤ value) :
    Nat.blt value bound = false := by
  cases hble : Nat.blt value bound with
  | false => rfl
  | true =>
      exact absurd (Nat.le_of_ble_eq_true hble) (Nat.not_le.mpr (Nat.lt_succ_of_le isGe))

/-! ## The classification lemma -/

/-- ★ **The survivor-top classification, over a floor-separated final state.**  For any wire state whose
links never cross the floor `bottomCount` (every below-floor node keeps its root `< bottomCount`, every
at-or-above-floor node keeps its root `≥ bottomCount`), a top port `bottomCount + topOffset` is a
survivor-top iff its own open-wire value is a survivor value (`< bottomCount`).

Proof (two directions on `natListGetAt finalState.openWires topOffset <? bottomCount`):

  * **below-floor** (`v < bc`): the port's own wire value `v` is a bottom boundary index sharing its
    component (`matchingBoundaryNodes_getAt_bottom`, self-root), so it PASSES the front test; the first-hit
    discipline (`findPartnerScan_result_passes_of_exists` on the front, then
    `findPartnerScan_append_ofFoundInFront`) lands the partner on a below-floor bottom candidate.

  * **cup-leg** (`bc ≤ v`): the root here is `≥ bc` (N2), every bottom candidate's root is `< bc` (N1) so
    the whole front misses (`findPartnerScan_range_frontSegmentMisses`), and the surviving top segment plus
    the exclude are all `≥ bc` (`findPartnerScan_result_ge_of_all_ge`), so the partner is a top. -/
theorem isSurvivorTop_extractDiagram_classify
    (bottomCount : Nat) (finalState : WireState) (topOffset : Nat)
    (topInRange : topOffset < finalState.openWires.length)
    (rootBelowFloor : ∀ node, node < bottomCount →
        unionFindRootOf finalState.links node < bottomCount)
    (rootAboveFloor : ∀ node, bottomCount ≤ node →
        bottomCount ≤ unionFindRootOf finalState.links node) :
    isSurvivorTop (extractDiagram bottomCount finalState) (bottomCount + topOffset)
      = decide (natListGetAt finalState.openWires topOffset < bottomCount) := by
  have totalBound : bottomCount + topOffset < bottomCount + finalState.openWires.length :=
    Nat.add_lt_add_left topInRange bottomCount
  -- Reduce the LHS to a single `Nat.blt` on the partner index.
  have lhsReduce :
      isSurvivorTop (extractDiagram bottomCount finalState) (bottomCount + topOffset)
        = Nat.blt (partnerIndexOf finalState.links (matchingBoundaryNodes bottomCount finalState)
            (bottomCount + finalState.openWires.length) (bottomCount + topOffset)) bottomCount := by
    show (Nat.ble bottomCount (bottomCount + topOffset)
        && Nat.blt (natListGetAt ((List.range (bottomCount + finalState.openWires.length)).map
            (partnerIndexOf finalState.links (matchingBoundaryNodes bottomCount finalState)
              (bottomCount + finalState.openWires.length))) (bottomCount + topOffset)) bottomCount)
      = Nat.blt (partnerIndexOf finalState.links (matchingBoundaryNodes bottomCount finalState)
          (bottomCount + finalState.openWires.length) (bottomCount + topOffset)) bottomCount
    rw [Nat.ble_eq_true_of_le (Nat.le_add_right bottomCount topOffset), Bool.true_and,
      natRangeMapGetAtLocal (bottomCount + finalState.openWires.length)
        (partnerIndexOf finalState.links (matchingBoundaryNodes bottomCount finalState)
          (bottomCount + finalState.openWires.length)) (bottomCount + topOffset) totalBound]
  rw [lhsReduce]
  -- The boundary read of the port's own wire.
  have vRead : natListGetAt (matchingBoundaryNodes bottomCount finalState) (bottomCount + topOffset)
      = natListGetAt finalState.openWires topOffset :=
    matchingBoundaryNodes_getAt_top bottomCount finalState topOffset
  -- Unfold `partnerIndexOf` and substitute the wire read for the root argument.
  have partnerUnfold :
      partnerIndexOf finalState.links (matchingBoundaryNodes bottomCount finalState)
          (bottomCount + finalState.openWires.length) (bottomCount + topOffset)
        = findPartnerScan finalState.links (matchingBoundaryNodes bottomCount finalState)
            (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
            (bottomCount + topOffset) (List.range (bottomCount + finalState.openWires.length)) := by
    show findPartnerScan finalState.links (matchingBoundaryNodes bottomCount finalState)
        (unionFindRootOf finalState.links (natListGetAt (matchingBoundaryNodes bottomCount finalState)
          (bottomCount + topOffset))) (bottomCount + topOffset)
        (List.range (bottomCount + finalState.openWires.length))
      = findPartnerScan finalState.links (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset) (List.range (bottomCount + finalState.openWires.length))
    rw [vRead]
  rw [partnerUnfold]
  cases Nat.lt_or_ge (natListGetAt finalState.openWires topOffset) bottomCount with
  | inl vLt =>
      -- Survivor direction: the port's own wire is the passing front witness.
      have vLtExclude : natListGetAt finalState.openWires topOffset < bottomCount + topOffset :=
        Nat.lt_of_lt_of_le vLt (Nat.le_add_right bottomCount topOffset)
      have vNeExclude :
          (natListGetAt finalState.openWires topOffset != bottomCount + topOffset) = true := by
        show (!(natListGetAt finalState.openWires topOffset == bottomCount + topOffset)) = true
        cases hEq : (natListGetAt finalState.openWires topOffset == bottomCount + topOffset) with
        | true => exact absurd (of_decide_eq_true hEq) (fun eq => Nat.lt_irrefl _ (eq ▸ vLtExclude))
        | false => rfl
      have selfRoot : (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)
          == unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)) = true := by
        cases hp : (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)
            == unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)) with
        | true => rfl
        | false => exact absurd rfl (of_decide_eq_false hp)
      have vPasses : (natListGetAt finalState.openWires topOffset != bottomCount + topOffset
          && unionFindRootOf finalState.links
              (natListGetAt (matchingBoundaryNodes bottomCount finalState)
                (natListGetAt finalState.openWires topOffset))
            == unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)) = true := by
        rw [matchingBoundaryNodes_getAt_bottom bottomCount finalState
            (natListGetAt finalState.openWires topOffset) vLt, vNeExclude, selfRoot]
        rfl
      obtain ⟨_, frontMem⟩ := findPartnerScan_result_passes_of_exists finalState.links
        (matchingBoundaryNodes bottomCount finalState)
        (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
        (bottomCount + topOffset) (List.range bottomCount)
        ⟨natListGetAt finalState.openWires topOffset, mem_range_of_lt vLt, vPasses⟩
      have frontLt : findPartnerScan finalState.links (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset) (List.range bottomCount) < bottomCount :=
        mem_range_imp_lt frontMem
      have frontNeExclude : findPartnerScan finalState.links (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset) (List.range bottomCount) ≠ bottomCount + topOffset :=
        fun eq => Nat.lt_irrefl _
          (eq ▸ Nat.lt_of_lt_of_le frontLt (Nat.le_add_right bottomCount topOffset))
      rw [rangeSplit bottomCount finalState.openWires.length,
        findPartnerScan_append_ofFoundInFront finalState.links (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset) (List.range bottomCount)
          ((List.range finalState.openWires.length).map (fun offset => bottomCount + offset))
          frontNeExclude,
        natBltEqTrueOfLt frontLt, decide_eq_true vLt]
  | inr vGe =>
      -- Cup-leg direction: the whole bottom front misses, the top segment lands `≥ bc`.
      have frontFails : ∀ candidate, candidate ∈ List.range bottomCount →
          (candidate != bottomCount + topOffset
              && unionFindRootOf finalState.links
                  (natListGetAt (matchingBoundaryNodes bottomCount finalState) candidate)
                == unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)) = false := by
        intro candidate candMem
        have candLt : candidate < bottomCount := mem_range_imp_lt candMem
        rw [matchingBoundaryNodes_getAt_bottom bottomCount finalState candidate candLt]
        have rootCandLt : unionFindRootOf finalState.links candidate < bottomCount :=
          rootBelowFloor candidate candLt
        have rootVGe : bottomCount ≤ unionFindRootOf finalState.links
            (natListGetAt finalState.openWires topOffset) := rootAboveFloor _ vGe
        have rootNe : (unionFindRootOf finalState.links candidate
            == unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)) = false := by
          cases hp : (unionFindRootOf finalState.links candidate
              == unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset)) with
          | false => rfl
          | true =>
              exact absurd (of_decide_eq_true hp)
                (fun eq => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (eq ▸ rootCandLt) rootVGe))
        rw [rootNe]; exact Bool.and_false _
      have topResultGe : bottomCount ≤ findPartnerScan finalState.links
          (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset)
          ((List.range finalState.openWires.length).map (fun offset => bottomCount + offset)) :=
        findPartnerScan_result_ge_of_all_ge finalState.links
          (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset) bottomCount
          ((List.range finalState.openWires.length).map (fun offset => bottomCount + offset))
          (Nat.le_add_right bottomCount topOffset)
          (le_of_mem_mapAdd bottomCount (List.range finalState.openWires.length))
      rw [findPartnerScan_range_frontSegmentMisses finalState.links
          (matchingBoundaryNodes bottomCount finalState)
          (unionFindRootOf finalState.links (natListGetAt finalState.openWires topOffset))
          (bottomCount + topOffset) bottomCount finalState.openWires.length frontFails,
        natBltEqFalseOfGe topResultGe, decide_eq_false (Nat.not_lt.mpr vGe)]

/-! ## The whole-valley instance -/

/-- ★ **The survivor-top classification for a whole valley.**  Instantiates
`isSurvivorTop_extractDiagram_classify` at the whole valley `V = capBlock ++ cupBlock` run from the
canonical seed, discharging the floor-separation hypotheses from the shipped whole-valley root facts N1
(`valleyRootBelowFloor`) and N2 (`valleyCupLegRootAboveFloor`).  So a whole-valley top port `bc + topOffset`
is a survivor-top iff its own final open-wire value is `< bc`. -/
theorem isSurvivorTop_matchingValley_classify
    {overallSource overallMiddle overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capAtoms : List (SpineAtom adjunctionModeSignature overallSource overallMiddle))
    (cupAtoms : List (SpineAtom adjunctionModeSignature overallMiddle overallTarget))
    (pureCap : AllCapArity capAtoms) (pureCup : AllCupArity cupAtoms) (topOffset : Nat)
    (topInRange : topOffset < (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        capAtoms) cupAtoms).openWires.length) :
    isSurvivorTop (extractDiagram bottomCount
        (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms) cupAtoms))
        (bottomCount + topOffset)
      = decide (natListGetAt (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
          capAtoms) cupAtoms).openWires topOffset < bottomCount) :=
  isSurvivorTop_extractDiagram_classify bottomCount
    (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms) cupAtoms)
    topOffset topInRange
    (fun node nodeBelow =>
      valleyRootBelowFloor bottomCount bottomPositive capAtoms cupAtoms pureCap pureCup node nodeBelow)
    (fun node nodeAbove =>
      valleyCupLegRootAboveFloor bottomCount bottomPositive capAtoms cupAtoms pureCap pureCup node nodeAbove)

/-! ## Honesty marker -/

/-- **Honesty marker — the survivor-top CLASSIFICATION lemma is SHIPPED (both the abstract floor-separated
form and the whole-valley instance).**  Landed here, all zero-axiom:

  * `isSurvivorTop_extractDiagram_classify` — a top port `bc + topOffset` of a floor-separated final state is
    a survivor-top iff its own open-wire value is `< bc`.  A clean bounded composition of the shipped kernel
    (boundary reads, the two scan-localization duals N3a/N3b, the first-hit / front-miss split), with the
    survivor direction witnessed by the port's OWN wire value — no phi-surjectivity input.

  * `isSurvivorTop_matchingValley_classify` — the whole-valley instance, discharging floor-separation from
    the shipped N1/N2 root facts.

This is the classification the `SurvivorTopRank` / `ValleyFloorHomogeneous` / `ValleyCupImageCover` markers
name as the still-open bridge.  It is the correct INPUT to the surjectivity of the cup embedding onto the
survivor positions (combining it with the shipped value-cover), not the surjectivity itself.  Downstream
F/G reconstruction, `valleyAppend_split`, and valley normalization remain; no gate flag is flipped.
`= true`. -/
def fxMode_hasSurvivorTopClassificationLemma : Bool := true

end FX1Poly.Polygraph
