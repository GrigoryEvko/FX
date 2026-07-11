import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapInternalCountsPointwise
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCounts
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapPartnerList
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort

/-! # WalkingString/StringArcCapInternalCountsPointwise — the per-port cap-count characterization,
ported (FC-3 r20, THE CLONE CAMPAIGN — Branch A)

Phantom-signature two-token clone of the walking-adjunction `ArcCapInternalCountsPointwise`, re-plumbed
onto the FOUR-generator adjoint-triple seed.  For a boundary-chained PURE-CAP spine the per-port internal
cap count is a FUNCTION of the boundary `diagram`: port `index` carries one cap-turnback iff it is a
bottom port whose partner is also a bottom port (a bottom-bottom short chord), zero otherwise.  Proved by
peel-FIRST fuel induction: the head-cap splice `[1, 1]` (the string list splice
`stringArcCapHeadFolded_internalCapCountsCorr`) lands exactly where the short chord is spliced into the
partner list (`stringArcCapHeadFolded_partnerListCorr`), and every other port shift-tracks through
`freshShiftAbove` whose `bltShiftAbove` invariance carries the verdict from the shrunk boundary.  The
purity kit `stringHeadCapArity` / `stringAllCapArity_ofCons` and the graph-neutral public
`capPortIndicator` are REUSED by import; the `~20` private Nat/list helpers are re-declared verbatim; the
two private locked stages (`stringStepPointwiseCap`, `stringPointwiseCapFueled`) are checked transitively.
The signature is a pure phantom, so ONLY the `SpineAtom`-quantified statements clone.  The fuel recursion
is STRUCTURAL on the fuel `Nat` (no `WellFounded.fix`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below =>
      natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

private theorem natListMapLength (mapFunction : Nat → Nat) :
    (list : List Nat) → (list.map mapFunction).length = list.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natListMapLength mapFunction rest)

private theorem listEqNilOfLengthZero {carrier : Type _} :
    (list : List carrier) → list.length = 0 → list = []
  | [], _ => rfl
  | _ :: _, lengthEq => Nat.noConfusion lengthEq

/-! ## The `Nat.blt`-based cap-port indicator -/

private theorem natBleEqTrueOfLe : {lowValue highValue : Nat} →
    lowValue ≤ highValue → Nat.ble lowValue highValue = true
  | 0, _, _ => rfl
  | _ + 1, 0, isImpossible => nomatch isImpossible
  | lowValue + 1, highValue + 1, isLessEqual => by
      show Nat.ble lowValue highValue = true
      exact natBleEqTrueOfLe (Nat.le_of_succ_le_succ isLessEqual)

private theorem natBleEqFalseOfLt {bound value : Nat} (lt : value < bound) :
    Nat.ble bound value = false := by
  cases hBle : Nat.ble bound value with
  | false => rfl
  | true => exact absurd (Nat.lt_of_lt_of_le lt (Nat.le_of_ble_eq_true hBle)) (Nat.lt_irrefl value)

/-- `Nat.blt smaller larger` is `true` when `smaller < larger` (it is `Nat.ble (smaller + 1) larger`). -/
private theorem natBltEqTrueOfLt {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := natBleEqTrueOfLe isLess

/-- `Nat.blt value bound` is `false` when `bound ≤ value`. -/
private theorem natBltEqFalseOfGe {bound value : Nat} (isGe : bound ≤ value) :
    Nat.blt value bound = false := natBleEqFalseOfLt (Nat.succ_le_succ isGe)


/-- The cap indicator is determined by the two `Nat.blt` verdicts — stated with independent bounds so
the peel-first step can compare the composite boundary `bottomCount` against the shrunk boundary
`tailBoundary`. -/
private theorem capPortIndicator_congr2 {bound1 partnerValue1 index1 bound2 partnerValue2 index2 : Nat}
    (indexBlt : Nat.blt index1 bound1 = Nat.blt index2 bound2)
    (partnerBlt : Nat.blt partnerValue1 bound1 = Nat.blt partnerValue2 bound2) :
    capPortIndicator bound1 partnerValue1 index1 = capPortIndicator bound2 partnerValue2 index2 := by
  show (if Nat.blt index1 bound1 && Nat.blt partnerValue1 bound1 then 1 else 0)
     = (if Nat.blt index2 bound2 && Nat.blt partnerValue2 bound2 then 1 else 0)
  rw [indexBlt, partnerBlt]

private theorem capPortIndicator_of_bothTrue {bottomCount partnerValue index : Nat}
    (indexTrue : Nat.blt index bottomCount = true) (partnerTrue : Nat.blt partnerValue bottomCount = true) :
    capPortIndicator bottomCount partnerValue index = 1 := by
  show (if Nat.blt index bottomCount && Nat.blt partnerValue bottomCount then 1 else 0) = 1
  rw [indexTrue, partnerTrue]; rfl

private theorem capPortIndicator_of_idxFalse {bottomCount partnerValue index : Nat}
    (indexFalse : Nat.blt index bottomCount = false) :
    capPortIndicator bottomCount partnerValue index = 0 := by
  show (if Nat.blt index bottomCount && Nat.blt partnerValue bottomCount then 1 else 0) = 0
  rw [indexFalse]; rfl

private theorem capPortIndicator_of_partnerFalse {bottomCount partnerValue index : Nat}
    (partnerFalse : Nat.blt partnerValue bottomCount = false) :
    capPortIndicator bottomCount partnerValue index = 0 := by
  show (if Nat.blt index bottomCount && Nat.blt partnerValue bottomCount then 1 else 0) = 0
  rw [partnerFalse, Bool.and_false]; rfl

/-- ★ **`freshShiftAbove windowPosition 2` preserves the bottom-port verdict relative to the shrunk
boundary.**  The composite boundary is `tailBoundary + 2` and the shift adds exactly `2` to at-or-above
threshold values, so `· < tailBoundary + 2` after the shift matches `· < tailBoundary` before — for any
value: below-threshold values (fixed by the shift) are already below `tailBoundary`; at-or-above values
land two higher against a boundary two higher.  The cap analogue of the cup's `bleShiftAbove`. -/
private theorem bltShiftAbove (windowPosition tailBoundary value : Nat)
    (windowLeTail : windowPosition ≤ tailBoundary) :
    Nat.blt (freshShiftAbove windowPosition 2 value) (tailBoundary + 2)
      = Nat.blt value tailBoundary := by
  cases Nat.lt_or_ge value windowPosition with
  | inl below =>
      rw [freshShiftAbove_ofNotLe windowPosition 2 value
        (fun windowLe => Nat.lt_irrefl value (Nat.lt_of_lt_of_le below windowLe))]
      have valueLtTail : value < tailBoundary := Nat.lt_of_lt_of_le below windowLeTail
      rw [natBltEqTrueOfLt (Nat.lt_of_lt_of_le valueLtTail (Nat.le_add_right tailBoundary 2)),
        natBltEqTrueOfLt valueLtTail]
  | inr atLeast =>
      rw [freshShiftAbove_ofLe windowPosition 2 value atLeast]
      cases Nat.lt_or_ge value tailBoundary with
      | inl lt => rw [natBltEqTrueOfLt (Nat.add_lt_add_right lt 2), natBltEqTrueOfLt lt]
      | inr ge => rw [natBltEqFalseOfGe (Nat.add_le_add_right ge 2), natBltEqFalseOfGe ge]

/-! ## Length reflections for the arc lists -/

private theorem extractArc_internalCapCounts_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).internalCapCounts.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
        state.capEventNodes)).length = bottomCount + state.openWires.length
  rw [natListMapLength, rangeLength]

private theorem extractArc_partner_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).diagram.partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [natListMapLength, rangeLength]

/-! ## The empty-spine base case -/

/-- The empty spine reads every internal cap count as `0` (no cap events). -/
private theorem initialInternalCapCounts_get {bottomCount k : Nat} (kRange : k < bottomCount + bottomCount) :
    natListGetAt (extractArc bottomCount
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).internalCapCounts k = 0 := by
  have lenEq : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  show natListGetAt ((List.range (bottomCount + (List.range bottomCount).length)).map
      (internalEventCountAt ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount)
        ([] : List Nat))) k = 0
  rw [natListGetAt_map_below _ (List.range (bottomCount + (List.range bottomCount).length)) k
    (by rw [rangeLength, lenEq]; exact kRange)]
  rfl

/-- Reading `List.range bottomCount ++ List.range bottomCount` below `bottomCount` returns the index. -/
private theorem doubleRangeGet_below {bottomCount index : Nat} (indexBelow : index < bottomCount) :
    natListGetAt (List.range bottomCount ++ List.range bottomCount) index = index := by
  have lenEq : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  rw [natListGetAt_append_inside (List.range bottomCount) (List.range bottomCount) index
      (by rw [lenEq]; exact indexBelow),
    rangeGetAt_below bottomCount index indexBelow]

/-- Reading `List.range bottomCount ++ List.range bottomCount` at `bottomCount + rest` (with `rest`
below `bottomCount`) returns `rest`. -/
private theorem doubleRangeGet_above {bottomCount rest : Nat} (restBelow : rest < bottomCount) :
    natListGetAt (List.range bottomCount ++ List.range bottomCount) (bottomCount + rest) = rest := by
  have lenEq : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  have idxEq : bottomCount + rest = rest + (List.range bottomCount).length := by
    rw [lenEq, Nat.add_comm rest bottomCount]
  rw [idxEq, natListGetAt_append_pastBlock (List.range bottomCount) (List.range bottomCount) rest,
    rangeGetAt_below bottomCount rest restBelow]

/-- A `findPartnerScan` result is below any bound that dominates the exclude and every scanned
candidate. -/
private theorem findPartnerScan_lt_of_scannedLt (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (rootHere excludeIndex bound : Nat) (excludeLt : excludeIndex < bound) :
    (scanned : List Nat) → (∀ candidate, candidate ∈ scanned → candidate < bound) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned < bound
  | [], _ => excludeLt
  | candidate :: rest, allLt => by
      rw [findPartnerScan_cons]
      cases hCond : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => exact allLt candidate (List.Mem.head rest)
      | false =>
          exact findPartnerScan_lt_of_scannedLt links boundaryNodes rootHere excludeIndex bound
            excludeLt rest (fun laterCandidate laterMem =>
              allLt laterCandidate (List.Mem.tail candidate laterMem))

/-- The empty spine sends every BOTTOM port to a TOP port: for `k < bottomCount` the partner is
`bottomCount + k ≥ bottomCount`.  Via the partner scan's completeness (the matching top index forces a
find) and soundness (the found node shares the root).  DUAL of the cup's `initialPartner_topPort_lt`. -/
private theorem initialPartner_bottomPort_ge {bottomCount k : Nat} (kBelow : k < bottomCount) :
    bottomCount ≤ natListGetAt (extractArc bottomCount
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner k := by
  have lenEq : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  have kRange : k < bottomCount + bottomCount :=
    Nat.lt_of_lt_of_le kBelow (Nat.le_add_left bottomCount bottomCount)
  have kTotal : k < bottomCount + (List.range bottomCount).length := by rw [lenEq]; exact kRange
  show bottomCount ≤ natListGetAt ((List.range (bottomCount + (List.range bottomCount).length)).map
      (partnerIndexOf ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount)
        (bottomCount + (List.range bottomCount).length))) k
  rw [natListGetAt_map_below _ (List.range (bottomCount + (List.range bottomCount).length)) k
      (by rw [rangeLength]; exact kTotal),
    rangeGetAt_below (bottomCount + (List.range bottomCount).length) k kTotal]
  show bottomCount ≤ findPartnerScan ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount)
      (unionFindRootOf ([] : List (Nat × Nat))
        (natListGetAt (List.range bottomCount ++ List.range bottomCount) k)) k
      (List.range (bottomCount + (List.range bottomCount).length))
  have rootAtK : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range bottomCount ++ List.range bottomCount) k) = k := by
    rw [doubleRangeGet_below kBelow]; rfl
  rw [rootAtK]
  -- the scan target: the top index `bottomCount + k`, in the same (empty-links) component, distinct
  have targetMem : bottomCount + k ∈ List.range (bottomCount + (List.range bottomCount).length) :=
    mem_range_of_lt (by rw [lenEq]; exact Nat.add_lt_add_left kBelow bottomCount)
  have kLtSum : k < bottomCount + k := Nat.lt_of_lt_of_le kBelow (Nat.le_add_right bottomCount k)
  have targetNeK : bottomCount + k ≠ k := by
    intro eqK
    rw [eqK] at kLtSum
    exact Nat.lt_irrefl k kLtSum
  have targetRoot : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range bottomCount ++ List.range bottomCount) (bottomCount + k)) = k := by
    rw [doubleRangeGet_above kBelow]; rfl
  have scanNeK : findPartnerScan ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) k k
      (List.range (bottomCount + (List.range bottomCount).length)) ≠ k :=
    findPartnerScan_neExclude_ofTarget ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) k k
      (List.range (bottomCount + (List.range bottomCount).length)) (bottomCount + k)
      targetMem targetNeK targetRoot
  have scanRoot : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range bottomCount ++ List.range bottomCount)
        (findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) k k
          (List.range (bottomCount + (List.range bottomCount).length)))) = k :=
    findPartnerScan_root_ofFound ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) k k
      (List.range (bottomCount + (List.range bottomCount).length)) scanNeK
  cases Nat.lt_or_ge (findPartnerScan ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) k k
      (List.range (bottomCount + (List.range bottomCount).length))) bottomCount with
  | inr aboveBottom => exact aboveBottom
  | inl belowBottom =>
      exfalso
      have readAtPartner : natListGetAt (List.range bottomCount ++ List.range bottomCount)
          (findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) k k
            (List.range (bottomCount + (List.range bottomCount).length))) = k := scanRoot
      have readBelow : natListGetAt (List.range bottomCount ++ List.range bottomCount)
          (findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) k k
            (List.range (bottomCount + (List.range bottomCount).length))) =
          findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) k k
            (List.range (bottomCount + (List.range bottomCount).length)) :=
        doubleRangeGet_below belowBottom
      exact scanNeK (readBelow.symm.trans readAtPartner)

/-! ## The peel-first step (mirroring the head-cap peel of `pureCapSpine_sort`) -/

/-- ★ **The peel-first step for the pointwise characterization.**  Firing the head cap at
`windowPosition` on the fresh initial state at `bottomCount`, then processing the tail `atoms`, whose
fresh run at the SHRUNK boundary `tailBoundary` (`tailBoundary + 2 = bottomCount`) already satisfies the
characterization: the composite extract satisfies it too.  The count list splices `[1, 1]` at
`windowPosition` (`stringArcCapHeadFolded_internalCapCountsCorr`) exactly where the short chord
`[windowPosition + 1, windowPosition]` is spliced into the partner list
(`stringArcCapHeadFolded_partnerListCorr`); the two window ports read a bottom-bottom chord (indicator `1`), and
every other port shift-tracks through `freshShiftAbove` — whose `bltShiftAbove` invariance carries the
verdict from the shrunk boundary to the composite one — and inherits from `tailPointwise`. -/
private theorem stringStepPointwiseCap
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms)
    (tailPointwise : ∀ j, j < tailBoundary
        + (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length →
      natListGetAt (arcStructureOfSpineList tailBoundary atoms).internalCapCounts j
        = capPortIndicator tailBoundary
            (natListGetAt (arcStructureOfSpineList tailBoundary atoms).diagram.partner j) j)
    (k : Nat)
    (kRange : k < bottomCount
      + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
          atoms).openWires.length) :
    natListGetAt (extractArc bottomCount
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
          atoms)).internalCapCounts k
      = capPortIndicator bottomCount
          (natListGetAt (extractArc bottomCount
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
              atoms)).diagram.partner k) k := by
  have windowLeTail : windowPosition ≤ tailBoundary := by
    have padded : windowPosition + 2 ≤ tailBoundary + 2 := by rw [tailBoundaryFits]; exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ padded)
  have windowLeFresh : windowPosition ≤ tailBoundary
      + (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).openWires.length :=
    Nat.le_trans windowLeTail (Nat.le_add_right _ _)
  have tailLtBc : tailBoundary < bottomCount := by
    rw [← tailBoundaryFits]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self tailBoundary)
      (Nat.add_le_add_left (Nat.le_succ 1) tailBoundary)
  have windowSuccLtBc : windowPosition + 1 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + 1)) windowFits
  have windowLtBc : windowPosition < bottomCount :=
    Nat.lt_trans (Nat.lt_succ_self windowPosition) windowSuccLtBc
  have icLen : (arcStructureOfSpineList tailBoundary atoms).internalCapCounts.length
      = tailBoundary + (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).openWires.length :=
    extractArc_internalCapCounts_length tailBoundary
      (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
  have partnerLen : (arcStructureOfSpineList tailBoundary atoms).diagram.partner.length
      = tailBoundary + (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).openWires.length :=
    extractArc_partner_length tailBoundary
      (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms)
  have countSplice : (extractArc bottomCount
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
          atoms)).internalCapCounts
      = natListInsertAt (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition
          [1, 1] :=
    stringArcCapHeadFolded_internalCapCountsCorr bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms chained
  have partnerSplice : (extractArc bottomCount
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)
          atoms)).diagram.partner
      = natListInsertAt
          ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
            (freshShiftAbove windowPosition 2))
          windowPosition [windowPosition + 1, windowPosition] :=
    stringArcCapHeadFolded_partnerListCorr bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms chained
  have kLtFreshPlus2 : k < (tailBoundary
      + (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).openWires.length) + 2 := by
    have tot := stringArcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms
    rw [tot] at kRange; exact kRange
  rw [countSplice, partnerSplice]
  have windowLeIcLen : windowPosition ≤ (arcStructureOfSpineList tailBoundary atoms).internalCapCounts.length := by
    rw [icLen]; exact windowLeFresh
  have windowLeMapLen : windowPosition
      ≤ ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
          (freshShiftAbove windowPosition 2)).length := by
    rw [natListMapLength, partnerLen]; exact windowLeFresh
  cases Nat.lt_or_ge k windowPosition with
  | inl kBelowWindow =>
      have kLtTail : k < tailBoundary := Nat.lt_of_lt_of_le kBelowWindow windowLeTail
      have kBelowIc : k < (arcStructureOfSpineList tailBoundary atoms).internalCapCounts.length := by
        rw [icLen]; exact Nat.lt_of_lt_of_le kBelowWindow windowLeFresh
      have kBelowPartner : k < (arcStructureOfSpineList tailBoundary atoms).diagram.partner.length := by
        rw [partnerLen]; exact Nat.lt_of_lt_of_le kBelowWindow windowLeFresh
      have kBelowMapped : k < ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
          (freshShiftAbove windowPosition 2)).length := by
        rw [natListMapLength]; exact kBelowPartner
      rw [natListGetAt_natListInsertAt_below (arcStructureOfSpineList tailBoundary atoms).internalCapCounts
          windowPosition [1, 1] k kBelowWindow kBelowIc,
        natListGetAt_natListInsertAt_below
          ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
            (freshShiftAbove windowPosition 2))
          windowPosition [windowPosition + 1, windowPosition] k kBelowWindow kBelowMapped,
        natListGetAt_map_below (freshShiftAbove windowPosition 2)
          (arcStructureOfSpineList tailBoundary atoms).diagram.partner k kBelowPartner,
        tailPointwise k (Nat.lt_of_lt_of_le kBelowWindow windowLeFresh)]
      refine capPortIndicator_congr2 ?_ ?_
      · exact (natBltEqTrueOfLt kLtTail).trans (natBltEqTrueOfLt (Nat.lt_trans kLtTail tailLtBc)).symm
      · rw [← tailBoundaryFits]
        exact (bltShiftAbove windowPosition tailBoundary
          (natListGetAt (arcStructureOfSpineList tailBoundary atoms).diagram.partner k) windowLeTail).symm
  | inr kAtLeastWindow =>
      obtain ⟨d, hd⟩ := Nat.le.dest kAtLeastWindow
      cases d with
      | zero =>
          have kEq : windowPosition = k := by rw [← hd, Nat.add_zero]
          subst kEq
          have icRead : natListGetAt (natListInsertAt
              (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition [1, 1])
              windowPosition = 1 := by
            have inside := natListGetAt_natListInsertAt_inside
              (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition [1, 1] 0
              (Nat.succ_pos 1) windowLeIcLen
            rw [Nat.add_zero] at inside; exact inside
          have partnerRead : natListGetAt (natListInsertAt
              ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
                (freshShiftAbove windowPosition 2))
              windowPosition [windowPosition + 1, windowPosition]) windowPosition = windowPosition + 1 := by
            have inside := natListGetAt_natListInsertAt_inside
              ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
                (freshShiftAbove windowPosition 2))
              windowPosition [windowPosition + 1, windowPosition] 0 (Nat.succ_pos 1) windowLeMapLen
            rw [Nat.add_zero] at inside; exact inside
          rw [icRead, partnerRead]
          exact (capPortIndicator_of_bothTrue (natBltEqTrueOfLt windowLtBc)
            (natBltEqTrueOfLt windowSuccLtBc)).symm
      | succ dInner =>
          cases dInner with
          | zero =>
              have kEq : windowPosition + 1 = k := by rw [← hd]
              subst kEq
              have icRead : natListGetAt (natListInsertAt
                  (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition [1, 1])
                  (windowPosition + 1) = 1 :=
                natListGetAt_natListInsertAt_inside
                  (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition [1, 1] 1
                  (Nat.lt_succ_self 1) windowLeIcLen
              have partnerRead : natListGetAt (natListInsertAt
                  ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
                    (freshShiftAbove windowPosition 2))
                  windowPosition [windowPosition + 1, windowPosition]) (windowPosition + 1) = windowPosition :=
                natListGetAt_natListInsertAt_inside
                  ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
                    (freshShiftAbove windowPosition 2))
                  windowPosition [windowPosition + 1, windowPosition] 1 (Nat.lt_succ_self 1) windowLeMapLen
              rw [icRead, partnerRead]
              exact (capPortIndicator_of_bothTrue (natBltEqTrueOfLt windowSuccLtBc)
                (natBltEqTrueOfLt windowLtBc)).symm
          | succ t =>
              have kEq : windowPosition + 2 + t = k := by
                rw [← hd, Nat.add_assoc windowPosition 2 t, Nat.add_comm 2 t]
              subst kEq
              have windowTLt : windowPosition + t < tailBoundary
                  + (processArcSpine (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires.length := by
                have reassoc : windowPosition + 2 + t = windowPosition + t + 2 := by
                  rw [Nat.add_assoc windowPosition 2 t, Nat.add_comm 2 t,
                    ← Nat.add_assoc windowPosition t 2]
                rw [reassoc] at kLtFreshPlus2
                exact Nat.lt_of_add_lt_add_right kLtFreshPlus2
              have windowTLtPartner : windowPosition + t
                  < (arcStructureOfSpineList tailBoundary atoms).diagram.partner.length := by
                rw [partnerLen]; exact windowTLt
              have icRead : natListGetAt (natListInsertAt
                  (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition [1, 1])
                  (windowPosition + 2 + t)
                  = natListGetAt (arcStructureOfSpineList tailBoundary atoms).internalCapCounts
                      (windowPosition + t) := by
                have past := natListGetAt_natListInsertAt_pastBlock
                  (arcStructureOfSpineList tailBoundary atoms).internalCapCounts windowPosition [1, 1] t
                  windowLeIcLen
                have blkLen : ([1, 1] : List Nat).length = 2 := rfl
                rw [blkLen, Nat.add_right_comm windowPosition t 2] at past
                exact past
              have partnerRead : natListGetAt (natListInsertAt
                  ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
                    (freshShiftAbove windowPosition 2))
                  windowPosition [windowPosition + 1, windowPosition]) (windowPosition + 2 + t)
                  = freshShiftAbove windowPosition 2
                      (natListGetAt (arcStructureOfSpineList tailBoundary atoms).diagram.partner
                        (windowPosition + t)) := by
                have past := natListGetAt_natListInsertAt_pastBlock
                  ((arcStructureOfSpineList tailBoundary atoms).diagram.partner.map
                    (freshShiftAbove windowPosition 2))
                  windowPosition [windowPosition + 1, windowPosition] t windowLeMapLen
                have blkLen : ([windowPosition + 1, windowPosition] : List Nat).length = 2 := rfl
                rw [blkLen, Nat.add_right_comm windowPosition t 2] at past
                rw [past, natListGetAt_map_below (freshShiftAbove windowPosition 2)
                  (arcStructureOfSpineList tailBoundary atoms).diagram.partner (windowPosition + t)
                  windowTLtPartner]
              rw [icRead, partnerRead, tailPointwise (windowPosition + t) windowTLt]
              refine capPortIndicator_congr2 ?_ ?_
              · rw [← tailBoundaryFits, Nat.add_right_comm windowPosition 2 t,
                  ← freshShiftAbove_ofLe windowPosition 2 (windowPosition + t)
                    (Nat.le_add_right windowPosition t)]
                exact (bltShiftAbove windowPosition tailBoundary (windowPosition + t) windowLeTail).symm
              · rw [← tailBoundaryFits]
                exact (bltShiftAbove windowPosition tailBoundary
                  (natListGetAt (arcStructureOfSpineList tailBoundary atoms).diagram.partner
                    (windowPosition + t)) windowLeTail).symm

/-! ## The pointwise characterization (fuel-driven peel-first induction) -/

private theorem stringPointwiseCapFueled {overallSource overallTarget : adjointTripleGraph.Mode} :
    (fuel : Nat) → (bottomCount : Nat) →
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    atoms.length ≤ fuel →
    SpineBoundaryChained bottomCount atoms →
    AllCapArity atoms →
    ∀ k, k < bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).openWires.length →
      natListGetAt (arcStructureOfSpineList bottomCount atoms).internalCapCounts k
        = capPortIndicator bottomCount
            (natListGetAt (arcStructureOfSpineList bottomCount atoms).diagram.partner k) k
  | 0, bottomCount, atoms, lenBound, _, _ => by
      match atoms, lenBound with
      | [], _ =>
          intro k kRange
          have kRange2 : k < bottomCount + bottomCount := by
            have owLen : (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).openWires.length
                = bottomCount := rangeLength bottomCount
            rw [owLen] at kRange; exact kRange
          show natListGetAt (extractArc bottomCount
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).internalCapCounts k
            = capPortIndicator bottomCount (natListGetAt (extractArc bottomCount
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner k) k
          rw [initialInternalCapCounts_get kRange2]
          cases Nat.lt_or_ge k bottomCount with
          | inl kBelow =>
              exact (capPortIndicator_of_partnerFalse
                (natBltEqFalseOfGe (initialPartner_bottomPort_ge kBelow))).symm
          | inr kAtLeast => exact (capPortIndicator_of_idxFalse (natBltEqFalseOfGe kAtLeast)).symm
      | _ :: _, lengthBound => exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, bottomCount, atoms, lenBound, chained, pureCap => by
      match atoms, lenBound, chained, pureCap with
      | [], _, _, _ =>
          intro k kRange
          have kRange2 : k < bottomCount + bottomCount := by
            have owLen : (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).openWires.length
                = bottomCount := rangeLength bottomCount
            rw [owLen] at kRange; exact kRange
          show natListGetAt (extractArc bottomCount
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).internalCapCounts k
            = capPortIndicator bottomCount (natListGetAt (extractArc bottomCount
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner k) k
          rw [initialInternalCapCounts_get kRange2]
          cases Nat.lt_or_ge k bottomCount with
          | inl kBelow =>
              exact (capPortIndicator_of_partnerFalse
                (natBltEqFalseOfGe (initialPartner_bottomPort_ge kBelow))).symm
          | inr kAtLeast => exact (capPortIndicator_of_idxFalse (natBltEqFalseOfGe kAtLeast)).symm
      | headCap :: tailAtoms, lengthBound, chained, pureCap =>
          intro k kRange
          obtain ⟨c1Dom, c1Cod⟩ := stringHeadCapArity pureCap
          have tailPure : AllCapArity tailAtoms := stringAllCapArity_ofCons pureCap
          obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
          have domExpand : headCap.leftContext.length + 2 + headCap.rightContext.length = bottomCount := by
            have raw : headCap.leftContext.length + headCap.generatorDom.length
                + headCap.rightContext.length = bottomCount := headFires
            rw [c1Dom] at raw; exact raw
          have windowFits : headCap.leftContext.length + 2 ≤ bottomCount := by
            rw [← domExpand]
            exact Nat.le_add_right (headCap.leftContext.length + 2) headCap.rightContext.length
          have tailBoundaryFits : headCap.codBoundaryLength + 2 = bottomCount := by
            have codRaw : headCap.codBoundaryLength
                = headCap.leftContext.length + headCap.rightContext.length := by
              show headCap.leftContext.length + headCap.generatorCod.length + headCap.rightContext.length
                = headCap.leftContext.length + headCap.rightContext.length
              rw [c1Cod, Nat.add_zero]
            rw [codRaw, Nat.add_right_comm headCap.leftContext.length headCap.rightContext.length 2]
            exact domExpand
          have tailLenBound : tailAtoms.length ≤ fuel := Nat.le_of_succ_le_succ lengthBound
          have tailIH := stringPointwiseCapFueled fuel headCap.codBoundaryLength tailAtoms tailLenBound
            tailChained tailPure
          have compositeEq : processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              (headCap :: tailAtoms)
              = processArcSpine (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  headCap.leftContext.length) tailAtoms := by
            show processArcSpine (stepArcAtom
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headCap) tailAtoms
              = processArcSpine (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  headCap.leftContext.length) tailAtoms
            rw [stepArcAtom_eq_stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              headCap c1Dom c1Cod]
          have goalBridge : arcStructureOfSpineList bottomCount (headCap :: tailAtoms)
              = extractArc bottomCount (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    headCap.leftContext.length) tailAtoms) := by
            show extractArc bottomCount (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) (headCap :: tailAtoms))
              = extractArc bottomCount (processArcSpine
                  (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    headCap.leftContext.length) tailAtoms)
            rw [compositeEq]
          rw [goalBridge]
          have kRangeStepped : k < bottomCount + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                headCap.leftContext.length) tailAtoms).openWires.length := by
            rw [← compositeEq]; exact kRange
          exact stringStepPointwiseCap bottomCount headCap.leftContext.length headCap.codBoundaryLength
            windowFits tailBoundaryFits tailAtoms tailChained tailIH k kRangeStepped

/-- ★ **The per-port cap-count characterization.**  For a boundary-chained pure-cap spine the internal
cap count at each in-range port `k` is `1` exactly when `k` is a bottom port whose partner is a bottom
port (a bottom-bottom short chord), and `0` otherwise — a function of the boundary `diagram` alone.  The
exact dual of `pureCup_internalCupCounts_pointwise`, proved peel-FIRST (the cap infrastructure is
arc-anchored: caps consume existing bottom ports). -/
theorem stringPureCap_internalCapCounts_pointwise {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) (chained : SpineBoundaryChained bottomCount atoms)
    (k : Nat)
    (kRange : k < bottomCount + (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length) :
    natListGetAt (arcStructureOfSpineList bottomCount atoms).internalCapCounts k
      = capPortIndicator bottomCount
          (natListGetAt (arcStructureOfSpineList bottomCount atoms).diagram.partner k) k :=
  stringPointwiseCapFueled atoms.length bottomCount atoms (Nat.le_refl atoms.length) chained pureCap k kRange

/-! ## The agreement corollary -/

/-- A list is determined by its length and its entries (structural, no `funext`). -/
private theorem natListExtByGet : (first second : List Nat) → first.length = second.length →
    (∀ index, index < first.length → natListGetAt first index = natListGetAt second index) →
    first = second
  | [], [], _, _ => rfl
  | [], _ :: _, lengthEq, _ => Nat.noConfusion lengthEq
  | _ :: _, [], lengthEq, _ => Nat.noConfusion lengthEq
  | headFirst :: restFirst, headSecond :: restSecond, lengthEq, entriesEq => by
      have headEq : headFirst = headSecond := entriesEq 0 (Nat.succ_pos _)
      have restLengthEq : restFirst.length = restSecond.length := Nat.succ.inj lengthEq
      have restEntriesEq : ∀ index, index < restFirst.length →
          natListGetAt restFirst index = natListGetAt restSecond index :=
        fun index indexBelow => entriesEq (index + 1) (Nat.succ_lt_succ indexBelow)
      rw [headEq, natListExtByGet restFirst restSecond restLengthEq restEntriesEq]

/-- ★ **The agreement corollary.**  Two pure-cap boundary-chained spines whose boundary `diagram`s agree
have equal `internalCapCounts`: each entry is `capPortIndicator` of the SHARED partner list, and the
lengths agree because the `diagram` fixes the bottom-port count.  Discharges the `capInternalCapCountsAgree`
residual of `sameMatchingValleys_spineTraceEquiv`. -/
theorem stringPureCapSpines_internalCapCountsAgree_ofDiagram {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (firstChained : SpineBoundaryChained bottomCount firstList)
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
      = (arcStructureOfSpineList bottomCount secondList).diagram) :
    (arcStructureOfSpineList bottomCount firstList).internalCapCounts
      = (arcStructureOfSpineList bottomCount secondList).internalCapCounts := by
  have topEq : (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        firstList).openWires.length
      = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondList).openWires.length :=
    congrArg DiagramType.topCount diagramAgree
  have firstIcLen : (arcStructureOfSpineList bottomCount firstList).internalCapCounts.length
      = bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        firstList).openWires.length :=
    extractArc_internalCapCounts_length bottomCount _
  have secondIcLen : (arcStructureOfSpineList bottomCount secondList).internalCapCounts.length
      = bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondList).openWires.length :=
    extractArc_internalCapCounts_length bottomCount _
  have lengthEq : (arcStructureOfSpineList bottomCount firstList).internalCapCounts.length
      = (arcStructureOfSpineList bottomCount secondList).internalCapCounts.length := by
    rw [firstIcLen, secondIcLen, topEq]
  have partnerAgree : (arcStructureOfSpineList bottomCount firstList).diagram.partner
      = (arcStructureOfSpineList bottomCount secondList).diagram.partner :=
    congrArg DiagramType.partner diagramAgree
  refine natListExtByGet _ _ lengthEq (fun index indexBelow => ?_)
  have indexFirst : index < bottomCount + (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstList).openWires.length := by
    rw [firstIcLen] at indexBelow; exact indexBelow
  have indexSecond : index < bottomCount + (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondList).openWires.length := by
    rw [← topEq]; exact indexFirst
  rw [stringPureCap_internalCapCounts_pointwise bottomCount firstList firstPureCap firstChained index indexFirst,
    stringPureCap_internalCapCounts_pointwise bottomCount secondList secondPureCap secondChained index indexSecond,
    partnerAgree]

/-! ## Honesty marker -/

/-- **Honesty marker — the per-port cap-count characterization, ported (FC-3 r20 clone campaign).**
`stringPureCap_internalCapCounts_pointwise`: on a boundary-chained pure-cap spine the internal cap count
at each port is `capPortIndicator` of the boundary partner (a bottom-bottom short chord reads `1`, all
else `0`), proved by peel-FIRST structural fuel induction.
`stringPureCapSpines_internalCapCountsAgree_ofDiagram`: equal `diagram`s force equal `internalCapCounts`.
The exact dual of the cup case.  `= true`. -/
def fxString_hasArcCapInternalCountsPointwise : Bool := true

end FX1Poly.Polygraph
