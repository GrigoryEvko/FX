import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyMidZeroReassembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupReconstruct
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyFloorHomogeneous
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCounterShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # SpineValleyMidZeroCupReconstruct — the mid-width-`0` cup-block reconstruction (Track B LAST BRICK)

`SpineValleyMidZeroReassembly` reduced the FULL `CellValleyTraceEquiv` to the single brick
`MidZeroCupBlockReconstruct` — the mid-width-`0` mirror of the shipped `cupRestrict_reconstructs`, with
`midPositive` replaced by the witness `survivorTopTotal V = 0`.  This file DISCHARGES it, all zero-axiom.

At mid-width `0` the cup-block's own diagram is `matchingOfSpineList 0 cupBlock` (the cup run from the
from-scratch seed `⟨List.range 0, [], 0, 0⟩`), and `cupRestrict V` (`V = matchingOfSpineList bc (capBlock ++
cupBlock)`) has `bottomCount := survivorTopTotal V = 0`.  The three non-partner fields close by the shipped
`cupRestrict_bottomCount_eq` / `cupRestrict_topCount_eq` / `cupRestrict_loops_eq` (none needs `midPositive`); the
cup-BOTTOM partner case is VACUOUS (`Nat.blt index 0 = false`) and the survivor-TOP case is VACUOUS
(`survivorTopTotal V = 0` ⇒ NO survivor-top in range).  The SOLE genuine content is the top-top cup-arc partner at
floor `0`: the PURE fresh-leg shift `V.partner[bc + k] - bc ↔ (matchingOfSpineList 0 cupBlock).partner[k]`.

The shift is landed on the MATCHING carrier (NO arc bridge, NO `arcDiagram_eq_matching`, positivity-free):

  * the shipped counter-shift simulation (`MatchingShiftSim`, `MatchingCounterShift`) — folded over the pure-cup
    block from the width-`0` seed vs the whole valley's cup-part seed `capState` (fresh legs `bc + k`) — gives the
    same-component correspondence `isSameComponent whole.links (a + bc) (b + bc) = isSameComponent cupAlone.links
    a b` and the open-wire shift `whole.openWires = cupAlone.openWires.map (· + bc)` (loops-irrelevance bridges the
    proxy seed to `capState`);
  * the whole-valley boundary is `List.range bc ++ whole.openWires`; the scan over `List.range (bc + T)`
    (`rangeSplit`) SKIPS the bottom prefix `List.range bc` — every bottom root stays `< bc` (`valleyRootBelowFloor`,
    N1) while the cup-leg probe root is `≥ bc` (`valleyCupLegRootAboveFloor`, N2), so the front never matches
    (`findPartnerScan_append_ofFrontFails`) — and the remaining `(List.range T).map (· + bc)` scan corresponds
    pointwise to the cup-alone scan under the component correspondence (`findPartnerScan_mapCongr`), giving
    `partnerIndexOf whole … (bc + index) = bc + partnerIndexOf cupAlone … index`.

Raw Lean 4 + Init; structural / `AllCupArity` recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local plumbing (propext-free copies) -/

/-- `(List.range count).length = count`, propext-free (via the accumulator length). -/
private theorem rangeLoopLenMZ : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLenMZ count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLenMZ (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLenMZ count []]; exact Nat.add_zero count

private theorem rangeLoopGetPastMZ : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetPastMZ count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetBelowMZ : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetBelowMZ count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetPastMZ count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem rangeGetBelowMZ (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetBelowMZ count [] index indexBelow

private theorem listMapLenMZ {carrier : Type} (mapFn : Nat → carrier) :
    (values : List Nat) → (values.map mapFn).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (listMapLenMZ mapFn rest)

/-- Reading a `(List.range n).map f` at an in-range index. -/
private theorem rangeMapGetMZ (mapFn : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFn) index = mapFn index := by
  have inRangeList : index < (List.range total).length := by rw [rangeLenMZ]; exact inRange
  rw [natListGetAt_map_inRange mapFn (List.range total) index inRangeList,
    rangeGetBelowMZ total index inRange]

/-- `(a + delta == b + delta) = (a == b)`, propext-free (induction on `delta`). -/
private theorem natBeqAddRightMZ (a b : Nat) : (delta : Nat) → ((a + delta == b + delta) = (a == b))
  | 0 => rfl
  | delta + 1 => by
      have inner := natBeqAddRightMZ a b delta
      show (a + delta + 1 == b + delta + 1) = (a == b)
      rw [show ((a + delta + 1 == b + delta + 1) = (a + delta == b + delta)) from by
          cases Nat.decEq (a + delta) (b + delta) with
          | isTrue areEqual => rw [areEqual]; exact (decide_eq_true rfl).trans (decide_eq_true rfl).symm
          | isFalse notEqual =>
              exact (decide_eq_false (fun succEq => notEqual (Nat.succ.inj succEq))).trans
                (decide_eq_false notEqual).symm]
      exact inner

/-- `(a + delta != b + delta) = (a != b)`, propext-free. -/
private theorem natBneAddRightMZ (a b delta : Nat) : ((a + delta != b + delta) = (a != b)) := by
  show (!(a + delta == b + delta)) = (!(a == b))
  rw [natBeqAddRightMZ a b delta]

/-- `Nat.blt value 0 = false`. -/
private theorem bltZeroMZ (value : Nat) : Nat.blt value 0 = false := by
  cases probe : Nat.blt value 0 with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true probe) (Nat.not_succ_le_zero value)

/-- `Nat.blt value bound = true` when `value < bound`. -/
private theorem bltTrueMZ {value bound : Nat} (isLess : value < bound) : Nat.blt value bound = true :=
  Nat.ble_eq_true_of_le isLess

/-- `Nat.blt value bound = false` when `bound ≤ value`. -/
private theorem bltFalseMZ {value bound : Nat} (isGe : bound ≤ value) : Nat.blt value bound = false := by
  cases probe : Nat.blt value bound with
  | false => rfl
  | true => exact absurd (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true probe) isGe) (Nat.lt_irrefl value)

/-- `Nat.ble lower upper = true` when `lower ≤ upper`. -/
private theorem bleTrueMZ {lower upper : Nat} (isLe : lower ≤ upper) : Nat.ble lower upper = true :=
  Nat.ble_eq_true_of_le isLe

/-- `base + value - base = value`, propext-free (hand-rolled). -/
private theorem addSubCancelLeftMZ : (base value : Nat) → base + value - base = value
  | 0, value => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, value => by
      rw [Nat.succ_add, Nat.succ_sub_succ]; exact addSubCancelLeftMZ base value

/-- The partner list of `extractDiagram` has length `bottomCount + open-wire count`. -/
private theorem extractPartnerLenMZ (bottomCount : Nat) (state : WireState) :
    (extractDiagram bottomCount state).partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [listMapLenMZ, rangeLenMZ]

/-- The partner list of `cupRestrict` has length `survivorTopTotal + topCount`. -/
private theorem cupRestrictPartnerLenMZ (diagram : DiagramType) :
    (cupRestrict diagram).partner.length = survivorTopTotal diagram + diagram.topCount := by
  show ((List.range (survivorTopTotal diagram + diagram.topCount)).map
      (fun index =>
        if Nat.blt index (survivorTopTotal diagram) then
          survivorTopTotal diagram + (nthSurvivorTop diagram index - diagram.bottomCount)
        else
          let wholeTop := diagram.bottomCount + (index - survivorTopTotal diagram)
          let wholePartner := natListGetAt diagram.partner wholeTop
          if Nat.blt wholePartner diagram.bottomCount then survivorTopRank diagram wholeTop
          else survivorTopTotal diagram + (wholePartner - diagram.bottomCount))).length
    = survivorTopTotal diagram + diagram.topCount
  rw [listMapLenMZ, rangeLenMZ]

/-- Read the `cupRestrict` partner list at an in-range index. -/
private theorem cupRestrictPartnerGetMZ (diagram : DiagramType) (index : Nat)
    (inRange : index < survivorTopTotal diagram + diagram.topCount) :
    natListGetAt (cupRestrict diagram).partner index
      = (if Nat.blt index (survivorTopTotal diagram) then
          survivorTopTotal diagram + (nthSurvivorTop diagram index - diagram.bottomCount)
        else
          let wholeTop := diagram.bottomCount + (index - survivorTopTotal diagram)
          let wholePartner := natListGetAt diagram.partner wholeTop
          if Nat.blt wholePartner diagram.bottomCount then survivorTopRank diagram wholeTop
          else survivorTopTotal diagram + (wholePartner - diagram.bottomCount)) := by
  show natListGetAt ((List.range (survivorTopTotal diagram + diagram.topCount)).map
      (fun idx =>
        if Nat.blt idx (survivorTopTotal diagram) then
          survivorTopTotal diagram + (nthSurvivorTop diagram idx - diagram.bottomCount)
        else
          let wholeTop := diagram.bottomCount + (idx - survivorTopTotal diagram)
          let wholePartner := natListGetAt diagram.partner wholeTop
          if Nat.blt wholePartner diagram.bottomCount then survivorTopRank diagram wholeTop
          else survivorTopTotal diagram + (wholePartner - diagram.bottomCount))) index = _
  rw [rangeMapGetMZ _ (survivorTopTotal diagram + diagram.topCount) index inRange]

/-! ## Loops-irrelevance of a pure-cup run (the proxy-to-`capState` bridge) -/

/-- ★ **A pure-cup run's open wires / links / counter ignore the seed loop count.**  `stepCup`'s three
non-loop fields are computed from the state's open wires, links, and counter alone (`stepCup_openWires` /
`stepCup_links` / `stepCup_nextFresh`), so two runs from seeds agreeing on those three fields (but differing in
`loops`) stay agreed.  This bridges the proxy seed `⟨[], capState.links, bc, 0⟩` (where the shift simulation's
`loopsEq` holds) to the actual `capState` (whose loop count is generally nonzero). -/
private theorem cupRunLoopsIrrelMZ
    {overallSource overallTarget : adjunctionGraph.Mode}
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity cupBlock) :
    (stateA stateB : WireState) →
    stateA.openWires = stateB.openWires → stateA.links = stateB.links →
    stateA.nextFresh = stateB.nextFresh →
    (processSpine stateA cupBlock).openWires = (processSpine stateB cupBlock).openWires
      ∧ (processSpine stateA cupBlock).links = (processSpine stateB cupBlock).links := by
  induction pureCup with
  | nil => intro stateA stateB openEq linksEq _; exact ⟨openEq, linksEq⟩
  | cons hasCupDomArity hasCupCodArity _restAllCup restIrrel =>
      rename_i headAtom rest
      intro stateA stateB openEq linksEq nextEq
      show (processSpine (stepAtom stateA headAtom) rest).openWires
          = (processSpine (stepAtom stateB headAtom) rest).openWires
        ∧ (processSpine (stepAtom stateA headAtom) rest).links
          = (processSpine (stepAtom stateB headAtom) rest).links
      rw [stepAtom_ofCupArity stateA headAtom hasCupDomArity hasCupCodArity,
        stepAtom_ofCupArity stateB headAtom hasCupDomArity hasCupCodArity]
      refine restIrrel (stepCup stateA headAtom.leftContext.length)
        (stepCup stateB headAtom.leftContext.length) ?_ ?_ ?_
      · rw [stepCup_openWires, stepCup_openWires, openEq, nextEq]
      · rw [stepCup_links, stepCup_links, linksEq, nextEq]
      · rw [stepCup_nextFresh, stepCup_nextFresh, nextEq]

/-! ## The partner-scan is exclude when every candidate fails -/

/-- A scan over a candidate list in which EVERY candidate fails the exclude-and-root test returns the
exclude sentinel — the bottom-prefix front-fail witness `findPartnerScan_append_ofFrontFails` consumes. -/
private theorem findPartnerScan_allFailMZ (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere excludeIndex : Nat) :
    (candidates : List Nat) →
    (∀ candidate ∈ candidates,
      (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) = false) →
    findPartnerScan links boundaryNodes rootHere excludeIndex candidates = excludeIndex
  | [], _ => rfl
  | candidate :: rest, allFail => by
      rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex candidate rest
        (allFail candidate (List.Mem.head rest))]
      exact findPartnerScan_allFailMZ links boundaryNodes rootHere excludeIndex rest
        (fun later laterMem => allFail later (List.Mem.tail candidate laterMem))

/-! ## The floor-0 top-top partner shift on the matching carrier -/

/-- ★ **The floor-`0` top-top cup-arc partner shift.**  For a whole valley whose cup-part run (`whole`) is the
counter-shift image (by `bc`) of the from-scratch cup-alone run (`cupAlone`) — its open wires are the `+ bc`
images (`openMapWhole`), its same-component view corresponds under the shift (`compCommWhole`) — and whose links
are floor-`bc` homogeneous (`belowRoot`/`aboveRoot`, N1/N2), a top port `bc + index`'s whole-valley partner is
`bc +` the cup-alone partner of `index`.  The scan over `List.range (bc + T)` splits at `bc` (`rangeSplit`); the
bottom prefix `List.range bc` is SKIPPED (bottom roots stay `< bc`, the cup-leg probe root is `≥ bc`, so no bottom
matches — `findPartnerScan_allFailMZ` + `findPartnerScan_append_ofFrontFails`); the top segment
`(List.range T).map (· + bc)` corresponds pointwise to the cup-alone scan (`findPartnerScan_mapCongr` under
`compCommWhole`), returning the shifted cup-alone partner.  Positivity-free, matching carrier — no arc bridge. -/
private theorem wholeCupPartnerShiftMZ (bc : Nat) (whole cupAlone : WireState)
    (index : Nat) (indexLt : index < cupAlone.openWires.length)
    (openMapWhole : whole.openWires = cupAlone.openWires.map (freshShiftAbove 0 bc))
    (compCommWhole : ∀ a b,
      (unionFindRootOf whole.links (freshShiftAbove 0 bc a)
          == unionFindRootOf whole.links (freshShiftAbove 0 bc b))
        = (unionFindRootOf cupAlone.links a == unionFindRootOf cupAlone.links b))
    (belowRoot : ∀ node, node < bc → unionFindRootOf whole.links node < bc)
    (aboveRoot : ∀ node, bc ≤ node → bc ≤ unionFindRootOf whole.links node) :
    partnerIndexOf whole.links (List.range bc ++ whole.openWires)
        (bc + cupAlone.openWires.length) (bc + index)
      = bc + partnerIndexOf cupAlone.links (List.range 0 ++ cupAlone.openWires)
          (0 + cupAlone.openWires.length) index := by
  -- the shifted boundary read at any cup-window offset
  have readShift : ∀ offset, offset < cupAlone.openWires.length →
      natListGetAt (List.range bc ++ whole.openWires) (bc + offset)
        = freshShiftAbove 0 bc (natListGetAt cupAlone.openWires offset) := by
    intro offset offsetLt
    have offsetLtW : offset < whole.openWires.length := by
      rw [openMapWhole, listMapLenMZ]; exact offsetLt
    have pastRead : natListGetAt (List.range bc ++ whole.openWires) (offset + (List.range bc).length)
        = natListGetAt whole.openWires offset :=
      natListGetAt_append_pastBlock (List.range bc) whole.openWires offset
    rw [rangeLenMZ bc, Nat.add_comm offset bc] at pastRead
    rw [pastRead, openMapWhole,
      natListGetAt_map_inRange (freshShiftAbove 0 bc) cupAlone.openWires offset offsetLt]
  -- the probe's root, in shifted form
  have probeRead : natListGetAt (List.range bc ++ whole.openWires) (bc + index)
      = freshShiftAbove 0 bc (natListGetAt cupAlone.openWires index) := readShift index indexLt
  -- unfold the whole-side partnerIndexOf and split its candidate range at `bc`
  show findPartnerScan whole.links (List.range bc ++ whole.openWires)
      (unionFindRootOf whole.links (natListGetAt (List.range bc ++ whole.openWires) (bc + index)))
      (bc + index) (List.range (bc + cupAlone.openWires.length))
    = bc + partnerIndexOf cupAlone.links (List.range 0 ++ cupAlone.openWires)
        (0 + cupAlone.openWires.length) index
  rw [probeRead, rangeSplit bc cupAlone.openWires.length]
  -- the bottom prefix `List.range bc` all fails
  have rootHereGe : bc ≤ unionFindRootOf whole.links
      (freshShiftAbove 0 bc (natListGetAt cupAlone.openWires index)) := by
    apply aboveRoot
    rw [freshShiftAbove_ofLe 0 bc _ (Nat.zero_le _)]
    exact Nat.le_add_left bc (natListGetAt cupAlone.openWires index)
  have frontFails : findPartnerScan whole.links (List.range bc ++ whole.openWires)
      (unionFindRootOf whole.links (freshShiftAbove 0 bc (natListGetAt cupAlone.openWires index)))
      (bc + index) (List.range bc) = bc + index := by
    apply findPartnerScan_allFailMZ
    intro candidate candidateMem
    have candidateLt : candidate < bc := mem_range_imp_lt candidateMem
    have readCand : natListGetAt (List.range bc ++ whole.openWires) candidate = candidate := by
      have inside := natListGetAt_append_inside (List.range bc) whole.openWires candidate
        (by rw [rangeLenMZ bc]; exact candidateLt)
      rw [inside, rangeGetBelowMZ bc candidate candidateLt]
    rw [readCand]
    have rootCandLt : unionFindRootOf whole.links candidate < bc := belowRoot candidate candidateLt
    have rootNe : (unionFindRootOf whole.links candidate
        == unionFindRootOf whole.links (freshShiftAbove 0 bc (natListGetAt cupAlone.openWires index)))
        = false :=
      decide_eq_false (fun rootEq =>
        Nat.lt_irrefl (unionFindRootOf whole.links candidate)
          (Nat.lt_of_lt_of_le rootCandLt (rootEq ▸ rootHereGe)))
    rw [rootNe, Bool.and_false]
  rw [findPartnerScan_append_ofFrontFails whole.links (List.range bc ++ whole.openWires)
    (unionFindRootOf whole.links (freshShiftAbove 0 bc (natListGetAt cupAlone.openWires index)))
    (bc + index) (List.range bc)
    ((List.range cupAlone.openWires.length).map (fun offset => bc + offset)) frontFails]
  -- the top segment corresponds pointwise to the cup-alone scan
  have mapped := findPartnerScan_mapCongr whole.links cupAlone.links
    (List.range bc ++ whole.openWires) (List.range 0 ++ cupAlone.openWires)
    (unionFindRootOf whole.links (freshShiftAbove 0 bc (natListGetAt cupAlone.openWires index)))
    (unionFindRootOf cupAlone.links (natListGetAt (List.range 0 ++ cupAlone.openWires) index))
    index (fun offset => bc + offset) (List.range cupAlone.openWires.length)
    (by
      intro candidate candidateMem
      have candidateLt : candidate < cupAlone.openWires.length := mem_range_imp_lt candidateMem
      have freshReadCand : natListGetAt (List.range 0 ++ cupAlone.openWires) candidate
          = natListGetAt cupAlone.openWires candidate := rfl
      have freshReadIndex : natListGetAt (List.range 0 ++ cupAlone.openWires) index
          = natListGetAt cupAlone.openWires index := rfl
      rw [readShift candidate candidateLt, freshReadCand, freshReadIndex,
        show ((fun offset => bc + offset) candidate != (fun offset => bc + offset) index)
            = (candidate != index) from by
          show (bc + candidate != bc + index) = (candidate != index)
          rw [Nat.add_comm bc candidate, Nat.add_comm bc index]
          exact natBneAddRightMZ candidate index bc,
        compCommWhole (natListGetAt cupAlone.openWires candidate)
          (natListGetAt cupAlone.openWires index)])
  rw [Nat.zero_add cupAlone.openWires.length]
  exact mapped

/-! ## The cup-run counter-shift agreement (whole valley vs cup-alone) -/

/-- ★ **The whole valley's cup-part run is the `bc`-counter-shift image of the from-scratch cup-alone run.**
At mid-width `0` the cap state `capState` has empty open wires, counter `bc`, and links entirely `< bc`; the
proxy seed `⟨[], capState.links, bc, 0⟩` (loops zeroed) shift-simulates the width-`0` seed `⟨List.range 0, [], 0,
0⟩` by `freshShiftAbove 0 bc` (`MatchingShiftSim`, initial component view by `unionFindRootOf_eq_self_ofFresh` +
`natBeqAddRightMZ`), folds through the pure-cup block (`matchingShiftSim_processSpine_ofBoundaryDiscipline`), and
`cupRunLoopsIrrelMZ` transports the proxy run's links / open wires to the actual `capState`.  Delivers the open-wire
`+ bc` shift and the same-component correspondence the floor-`0` partner scan consumes. -/
private theorem cupWholeSimMZ
    {overallSource overallTarget : adjunctionGraph.Mode} (bc : Nat) (bottomPositive : 0 < bc)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained0 : SpineBoundaryChained 0 cupBlock)
    (capOWnil : (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).openWires = []) :
    (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).openWires
        = (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires.map (freshShiftAbove 0 bc)
      ∧ (∀ a b,
          (unionFindRootOf (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).links
                (freshShiftAbove 0 bc a)
              == unionFindRootOf (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).links
                (freshShiftAbove 0 bc b))
            = (unionFindRootOf (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).links a
              == unionFindRootOf (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).links b)) := by
  have capNF : (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).nextFresh = bc :=
    processSpine_nextFresh_ofAllCapArity_seed bc capBlock capPure
  have capBelow : ∀ edge ∈ (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links,
      edge.1 < bc ∧ edge.2 < bc :=
    processSpine_links_below_ofAllCapArity_seed bc bottomPositive capBlock capPure
  have capForest : isUnionFindForest (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links :=
    isUnionFindForest_processSpine capBlock ⟨List.range bc, [], bc, 0⟩ isUnionFindForest_nil
  -- the proxy seed (loops zeroed) shift-simulated by `freshShiftAbove 0 bc` from the width-0 seed
  have initialSim : MatchingShiftSim 0 bc ⟨List.range 0, [], 0, 0⟩
      ⟨[], (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links, bc, 0⟩ :=
    { openMap := rfl
      nfShift := (Nat.zero_add bc).symm
      componentComm := fun a b => by
        rw [freshShiftAbove_ofLe 0 bc a (Nat.zero_le a), freshShiftAbove_ofLe 0 bc b (Nat.zero_le b),
          unionFindRootOf_eq_self_ofFresh bc _ (fun edge edgeMem => (capBelow edge edgeMem).1)
            (a + bc) (Nat.le_add_left bc a),
          unionFindRootOf_eq_self_ofFresh bc _ (fun edge edgeMem => (capBelow edge edgeMem).1)
            (b + bc) (Nat.le_add_left bc b)]
        exact natBeqAddRightMZ a b bc
      loopsEq := rfl
      forestS := isUnionFindForest_nil
      forestT := capForest }
  have simFold : MatchingShiftSim 0 bc (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock)
      (processSpine ⟨[], (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links, bc, 0⟩ cupBlock) :=
    matchingShiftSim_processSpine_ofBoundaryDiscipline 0 bc cupBlock ⟨List.range 0, [], 0, 0⟩
      ⟨[], (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links, bc, 0⟩ 0 cupChained0
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure) rfl (Nat.le_refl 0) initialSim
  -- transport the proxy run's links / open wires to the actual `capState` (loops-irrelevance)
  have irrel := cupRunLoopsIrrelMZ cupBlock cupPure
    ⟨[], (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links, bc, 0⟩
    (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) capOWnil.symm rfl capNF.symm
  refine ⟨?_, ?_⟩
  · rw [← irrel.1]; exact simFold.openMap
  · intro a b; rw [← irrel.2]; exact simFold.componentComm a b

/-! ## The count-zero converse (case-2 vacuity) -/

/-- A count of a Bool predicate over `[0, bound)` that is zero forces the predicate false at every in-range
index (the converse of the shipped `countBelow_eq_zero_of_allFalse`). -/
private theorem allFalseCountZeroMZ (predicate : Nat → Bool) :
    (bound : Nat) → countBelow predicate bound = 0 →
    ∀ index, index < bound → predicate index = false
  | 0, _, _, indexLt => absurd indexLt (Nat.not_lt_zero _)
  | bound + 1, countZero, index, indexLt => by
      have split : countBelow predicate bound + cond (predicate bound) 1 0 = 0 := countZero
      have restZero : countBelow predicate bound = 0 := by
        cases hh : countBelow predicate bound with
        | zero => rfl
        | succ predCount =>
            rw [hh, Nat.succ_add] at split
            exact Nat.noConfusion split
      have headZero : cond (predicate bound) 1 0 = 0 := by
        rw [restZero, Nat.zero_add] at split; exact split
      cases Nat.lt_or_ge index bound with
      | inl below => exact allFalseCountZeroMZ predicate bound restZero index below
      | inr atLeast =>
          have indexEq : index = bound := Nat.le_antisymm (Nat.le_of_lt_succ indexLt) atLeast
          rw [indexEq]
          cases hp : predicate bound with
          | false => rfl
          | true => rw [hp] at headZero; exact Nat.noConfusion headZero

/-! ## The mid-width-`0` cup-block reconstruction — DISCHARGED -/

/-- ★ **`MidZeroCupBlockReconstruct` is DISCHARGED — the Track B LAST BRICK.**  At mid-width `0` the cup block's
own diagram is `cupRestrict` of the whole valley's diagram.  The three non-partner fields close by the shipped
positivity-free field lemmas; the cup-BOTTOM partner case is vacuous (`Nat.blt index 0 = false`) and the
survivor-TOP case is vacuous (`survivorTopTotal V = 0` kills every survivor-top via `allFalseCountZeroMZ`); the SOLE
content is the floor-`0` top-top cup-arc partner, the pure fresh-leg shift landed on the matching carrier by
`wholeCupPartnerShiftMZ` (shift simulation + N1/N2 floor separation + `findPartnerScan_mapCongr`), POSITIVITY-FREE
— no arc bridge, no `arcDiagram_eq_matching`. -/
theorem midZeroCupBlockReconstruct_holds : MidZeroCupBlockReconstruct := by
  intro overallSource overallTarget bc bottomPositive capBlock cupBlock capPure cupPure cupChained
    wholeChained midZero
  -- the mid-width is `0`, so the cap state's open wires are empty
  have midEq : survivorTopTotal (matchingOfSpineList bc (capBlock ++ cupBlock))
      = (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).openWires.length :=
    survivorTopTotal_eq_midWidth bc bottomPositive capBlock cupBlock capPure cupPure cupChained
  have capLen0 : (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).openWires.length = 0 :=
    midEq.symm.trans midZero
  have capOWnil : (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).openWires = [] := by
    cases hOW : (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).openWires with
    | nil => rfl
    | cons head tail =>
        rw [hOW] at capLen0
        exact Nat.noConfusion capLen0
  have cupChained0 : SpineBoundaryChained 0 cupBlock := capLen0 ▸ cupChained
  -- the whole valley diagram is the extraction of the whole run from `capState`
  have wholeSplit : matchingOfSpineList bc (capBlock ++ cupBlock)
      = extractDiagram bc (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock) := by
    show extractDiagram bc (processSpine ⟨List.range bc, [], bc, 0⟩ (capBlock ++ cupBlock))
      = extractDiagram bc (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock)
    rw [processSpine_append capBlock cupBlock ⟨List.range bc, [], bc, 0⟩]
  have vBottom : (matchingOfSpineList bc (capBlock ++ cupBlock)).bottomCount = bc :=
    congrArg DiagramType.bottomCount wholeSplit
  have vTopCount : (matchingOfSpineList bc (capBlock ++ cupBlock)).topCount
      = (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).openWires.length :=
    congrArg DiagramType.topCount wholeSplit
  -- the counter-shift agreement between the whole cup-part run and the cup-alone run
  have simFacts := cupWholeSimMZ bc bottomPositive capBlock cupBlock capPure cupPure cupChained0 capOWnil
  have openMapWhole := simFacts.1
  have compCommWhole := simFacts.2
  have topLenEq :
      (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).openWires.length
        = (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires.length := by
    rw [openMapWhole, listMapLenMZ]
  -- floor-`bc` homogeneity of the whole-valley links (mode-uniform build; N1/N2 follow)
  have capFresh : WireStateFresh (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) :=
    processSpine_wireStateFresh capBlock ⟨List.range bc, [], bc, 0⟩ (wireStateFresh_initial bc) bottomPositive
  have capNF : (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).nextFresh = bc :=
    processSpine_nextFresh_ofAllCapArity_seed bc capBlock capPure
  have capBelow : ∀ edge ∈ (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock).links,
      edge.1 < bc ∧ edge.2 < bc :=
    processSpine_links_below_ofAllCapArity_seed bc bottomPositive capBlock capPure
  have valleyHomog : ∀ edge ∈ (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).links,
      edgeFloorHomogeneous bc edge :=
    processSpine_edgesFloorHomogeneous_ofAllCupArity bc cupBlock cupPure
      (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) capFresh (Nat.le_of_eq capNF.symm)
      (fun edge edgeMem => ⟨fun floorLe => absurd floorLe (Nat.not_le.mpr (capBelow edge edgeMem).1),
        fun _ => (capBelow edge edgeMem).2⟩)
  have belowRoot : ∀ node, node < bc →
      unionFindRootOf (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).links node < bc :=
    fun node nodeLt =>
      unionFindRootOf_lt_of_edgesBelowFloor _ bc (fun edge edgeMem => (valleyHomog edge edgeMem).2) node nodeLt
  have aboveRoot : ∀ node, bc ≤ node →
      bc ≤ unionFindRootOf (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).links node :=
    fun node nodeGe =>
      unionFindRootOf_ge_of_edgesPreserveFloor _ bc (fun edge edgeMem => (valleyHomog edge edgeMem).1) node nodeGe
  -- the survivor-top count is zero, so no top port is a survivor-top in range
  have countZero : countBelow (isSurvivorTop (matchingOfSpineList bc (capBlock ++ cupBlock)))
      ((matchingOfSpineList bc (capBlock ++ cupBlock)).bottomCount
        + (matchingOfSpineList bc (capBlock ++ cupBlock)).topCount) = 0 := by
    rw [← survivorTopCount_eq_countBelow]; exact midZero
  have allFalseSurvivor : ∀ topPort,
      topPort < (matchingOfSpineList bc (capBlock ++ cupBlock)).bottomCount
          + (matchingOfSpineList bc (capBlock ++ cupBlock)).topCount →
      isSurvivorTop (matchingOfSpineList bc (capBlock ++ cupBlock)) topPort = false :=
    allFalseCountZeroMZ (isSurvivorTop (matchingOfSpineList bc (capBlock ++ cupBlock))) _ countZero
  -- assemble the `DiagramType.ext`
  apply diagramType_eq_of_fields
  · exact cupRestrict_bottomCount_eq bc bottomPositive capBlock cupBlock capPure cupPure cupChained
  · exact cupRestrict_topCount_eq bc capBlock cupBlock cupPure
  · -- partner
    rw [capLen0]
    show (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock)).partner
      = (cupRestrict (matchingOfSpineList bc (capBlock ++ cupBlock))).partner
    apply natListEqOfPointwiseGetAt
    · rw [extractPartnerLenMZ 0 (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock),
        cupRestrictPartnerLenMZ (matchingOfSpineList bc (capBlock ++ cupBlock)), midZero,
        Nat.zero_add, Nat.zero_add, vTopCount, topLenEq]
    · intro index indexRaw
      have indexLtT : index < (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires.length := by
        rw [extractPartnerLenMZ 0 (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock), Nat.zero_add] at indexRaw
        exact indexRaw
      -- the LHS partner read (cup-alone)
      have lhsRead : natListGetAt (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock)).partner index
          = partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).links
              (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires)
              (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires.length) index :=
        extractDiagram_partner_getAt 0 (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock) index
          (by rw [Nat.zero_add]; exact indexLtT)
      -- the RHS partner read (cupRestrict at mid-0)
      have indexLtRHS : index < survivorTopTotal (matchingOfSpineList bc (capBlock ++ cupBlock))
          + (matchingOfSpineList bc (capBlock ++ cupBlock)).topCount := by
        rw [midZero, Nat.zero_add, vTopCount, topLenEq]; exact indexLtT
      -- the whole-valley top partner read
      have wholeTopRead : natListGetAt (matchingOfSpineList bc (capBlock ++ cupBlock)).partner (bc + index)
          = partnerIndexOf (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).links
              (List.range bc ++ (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).openWires)
              (bc + (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock).openWires.length)
              (bc + index) := by
        rw [wholeSplit]
        exact extractDiagram_partner_getAt bc
          (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock) (bc + index)
          (Nat.add_lt_add_left (topLenEq.symm ▸ indexLtT) bc)
      -- the top partner is `bc +` the cup-alone partner (the pure fresh-leg shift)
      have shiftEq := wholeCupPartnerShiftMZ bc
        (processSpine (processSpine ⟨List.range bc, [], bc, 0⟩ capBlock) cupBlock)
        (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock) index indexLtT openMapWhole compCommWhole
        belowRoot aboveRoot
      -- the shifted cup-alone partner sits at or above `bc`, so the survivor branch is dead
      have partnerGe : bc ≤ bc + partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).links
          (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires)
          (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires.length) index :=
        Nat.le_add_right bc _
      rw [lhsRead, cupRestrictPartnerGetMZ (matchingOfSpineList bc (capBlock ++ cupBlock)) index indexLtRHS,
        midZero, if_neg (fun hh => Bool.noConfusion ((bltZeroMZ index).symm.trans hh))]
      dsimp only []
      rw [Nat.sub_zero, vBottom, wholeTopRead, topLenEq, shiftEq,
        if_neg (fun hh => Bool.noConfusion ((bltFalseMZ partnerGe).symm.trans hh))]
      generalize partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).links
          (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires)
          (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ cupBlock).openWires.length) index = cupPart
      rw [addSubCancelLeftMZ bc cupPart]
      exact (Nat.zero_add cupPart).symm
  · exact cupRestrict_loops_eq bc capBlock cupBlock cupPure

end FX1Poly.Polygraph
