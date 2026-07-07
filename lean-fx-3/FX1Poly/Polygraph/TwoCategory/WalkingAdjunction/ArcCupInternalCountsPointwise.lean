import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDrop
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched

/-! # ArcCupInternalCountsPointwise — the per-port cup-count characterization (leaf 2a-i)

For a boundary-chained PURE-CUP spine the per-port internal cup count is a FUNCTION of the boundary
`diagram`: port `index` carries exactly one cup-turnback iff it is a top port (`bottomCount ≤ index`)
whose partner is ALSO a top port (`bottomCount ≤ partner index`) — a top-top short chord — and zero
otherwise.  Every cup event in a pure-cup spine is such a top-top short chord (both legs reach the top
boundary, nothing caps them); every pass-through strand carries no cup event and matches a bottom port.

  * ★ `pureCup_internalCupCounts_pointwise` — the pointwise characterization `Q`, by peel-last
    induction on the spine (mirroring `dropStepReduce`): the empty spine reads both sides `0`, and
    peeling the last cup splices `[1, 1]` into the count list (`internalCupCounts_stepCupArc`) exactly
    where the short chord `[bc+w+1, bc+w]` is spliced into the partner list
    (`diagramPartner_stepCupArc`), so the two spliced window ports read `1` (top-top) and every other
    port shift-tracks through `freshShiftAbove` and inherits from the induction hypothesis.
  * ★ `pureCupSpines_internalCupCountsAgree_ofDiagram` — the agreement corollary: two pure-cup spines
    whose `diagram`s agree (hence whose `partner`s agree) have equal `internalCupCounts`, since each
    entry is `Q` of the shared partner.  This discharges the `cupInternalCupCountsAgree` residual of
    `sameMatchingValleys_spineTraceEquiv`.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-
declaration `#assert_no_axioms` gated in the audit twin. -/

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

private theorem listNilOrSnoc {carrier : Type _} :
    (list : List carrier) → list = [] ∨ ∃ prefixAtoms lastAtom, list = prefixAtoms ++ [lastAtom]
  | [] => Or.inl rfl
  | headAtom :: restAtoms =>
      match listNilOrSnoc restAtoms with
      | Or.inl restNil => Or.inr ⟨[], headAtom, by subst restNil; rfl⟩
      | Or.inr ⟨prefixAtoms, lastAtom, restSnoc⟩ =>
          Or.inr ⟨headAtom :: prefixAtoms, lastAtom, by subst restSnoc; rfl⟩

private theorem lengthSnoc {carrier : Type _} :
    (prefixAtoms : List carrier) → (lastAtom : carrier) →
    (prefixAtoms ++ [lastAtom]).length = prefixAtoms.length + 1
  | [], _ => rfl
  | _ :: restAtoms, lastAtom => congrArg Nat.succ (lengthSnoc restAtoms lastAtom)

/-! ## The `Nat.ble`-based cup-port indicator -/

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

/-- The per-port cup indicator: `1` when `index` is a top port whose partner is a top port (a top-top
short chord), `0` otherwise.  Read as a pure `Bool` function so the agreement corollary is `congrArg`. -/
def cupPortIndicator (bottomCount partnerValue index : Nat) : Nat :=
  if Nat.ble bottomCount index && Nat.ble bottomCount partnerValue then 1 else 0

private theorem cupPortIndicator_congr {bottomCount partnerValue1 partnerValue2 index1 index2 : Nat}
    (indexBle : Nat.ble bottomCount index1 = Nat.ble bottomCount index2)
    (partnerBle : Nat.ble bottomCount partnerValue1 = Nat.ble bottomCount partnerValue2) :
    cupPortIndicator bottomCount partnerValue1 index1
      = cupPortIndicator bottomCount partnerValue2 index2 := by
  show (if Nat.ble bottomCount index1 && Nat.ble bottomCount partnerValue1 then 1 else 0)
     = (if Nat.ble bottomCount index2 && Nat.ble bottomCount partnerValue2 then 1 else 0)
  rw [indexBle, partnerBle]

private theorem cupPortIndicator_of_bothTrue {bottomCount partnerValue index : Nat}
    (indexTrue : Nat.ble bottomCount index = true) (partnerTrue : Nat.ble bottomCount partnerValue = true) :
    cupPortIndicator bottomCount partnerValue index = 1 := by
  show (if Nat.ble bottomCount index && Nat.ble bottomCount partnerValue then 1 else 0) = 1
  rw [indexTrue, partnerTrue]; rfl

private theorem cupPortIndicator_of_idxFalse {bottomCount partnerValue index : Nat}
    (indexFalse : Nat.ble bottomCount index = false) :
    cupPortIndicator bottomCount partnerValue index = 0 := by
  show (if Nat.ble bottomCount index && Nat.ble bottomCount partnerValue then 1 else 0) = 0
  rw [indexFalse]; rfl

private theorem cupPortIndicator_of_partnerFalse {bottomCount partnerValue index : Nat}
    (partnerFalse : Nat.ble bottomCount partnerValue = false) :
    cupPortIndicator bottomCount partnerValue index = 0 := by
  show (if Nat.ble bottomCount index && Nat.ble bottomCount partnerValue then 1 else 0) = 0
  rw [partnerFalse, Bool.and_false]; rfl

/-- `freshShiftAbove` above a threshold at or above the bound does not change the `bottomCount ≤ ·`
verdict: a below-threshold value is fixed; an at-or-above one lands even higher — both stay above the
bound once the threshold is at or above it. -/
private theorem bleShiftAbove (bound threshold delta value : Nat) (boundLe : bound ≤ threshold) :
    Nat.ble bound (freshShiftAbove threshold delta value) = Nat.ble bound value := by
  cases Nat.decLe threshold value with
  | isTrue atLeast =>
      rw [freshShiftAbove_ofLe threshold delta value atLeast,
        natBleEqTrueOfLe (Nat.le_trans boundLe atLeast),
        natBleEqTrueOfLe (Nat.le_trans (Nat.le_trans boundLe atLeast) (Nat.le_add_right value delta))]
  | isFalse below =>
      rw [freshShiftAbove_ofNotLe threshold delta value below]

/-! ## The partner-scan bound -/

/-- A `findPartnerScan` result is below any bound that dominates the exclude and every scanned
candidate: the scan returns either a scanned candidate or the exclude, and both are below the bound. -/
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
            excludeLt rest (fun laterCandidate laterMem => allLt laterCandidate (List.Mem.tail candidate laterMem))

/-! ## The empty-spine base case -/

/-- The empty spine reads every internal cup count as `0` (no cup events). -/
private theorem initialInternalCupCounts_get {bottomCount k : Nat} (kRange : k < bottomCount + bottomCount) :
    natListGetAt (extractArc bottomCount
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).internalCupCounts k = 0 := by
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

/-- The empty spine sends every TOP port to a BOTTOM port: for `bottomCount ≤ k < 2·bottomCount` the
partner is `k - bottomCount < bottomCount`.  Via the partner scan's soundness (the found node shares
the root) and completeness (the matching bottom index forces a find). -/
private theorem initialPartner_topPort_lt {bottomCount k : Nat}
    (kAtLeast : bottomCount ≤ k) (kRange : k < bottomCount + bottomCount) :
    natListGetAt (extractArc bottomCount
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner k
      < bottomCount := by
  have lenEq : (List.range bottomCount).length = bottomCount := rangeLength bottomCount
  obtain ⟨m, hm⟩ := Nat.le.dest kAtLeast
  have mLt : m < bottomCount := by
    have step : bottomCount + m < bottomCount + bottomCount := by rw [hm]; exact kRange
    exact Nat.lt_of_add_lt_add_left step
  have kTotal : k < bottomCount + (List.range bottomCount).length := by rw [lenEq]; exact kRange
  -- reduce the partner read to a `partnerIndexOf` over the double range
  show natListGetAt ((List.range (bottomCount + (List.range bottomCount).length)).map
      (partnerIndexOf ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount)
        (bottomCount + (List.range bottomCount).length))) k < bottomCount
  rw [natListGetAt_map_below _ (List.range (bottomCount + (List.range bottomCount).length)) k
      (by rw [rangeLength]; exact kTotal),
    rangeGetAt_below (bottomCount + (List.range bottomCount).length) k kTotal]
  -- unfold `partnerIndexOf` to the scan; name the root at k
  show findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount)
      (unionFindRootOf ([] : List (Nat × Nat))
        (natListGetAt (List.range bottomCount ++ List.range bottomCount) k)) k
      (List.range (bottomCount + (List.range bottomCount).length)) < bottomCount
  -- the root at k is m (empty links, second-range read)
  have rootAtK : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range bottomCount ++ List.range bottomCount) k) = m := by
    rw [← hm, doubleRangeGet_above mLt]
    rfl
  rw [rootAtK]
  -- the scan target m: a bottom index in the same component, distinct from the exclude
  have mMem : m ∈ List.range (bottomCount + (List.range bottomCount).length) :=
    mem_range_of_lt (Nat.lt_of_lt_of_le mLt (Nat.le_add_right bottomCount (List.range bottomCount).length))
  have mNeK : m ≠ k := by
    intro mEqK
    rw [mEqK] at mLt
    exact Nat.lt_irrefl k (Nat.lt_of_lt_of_le mLt kAtLeast)
  have mRoot : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range bottomCount ++ List.range bottomCount) m) = m := by
    rw [doubleRangeGet_below mLt]
    rfl
  have scanNeK : findPartnerScan ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) m k
      (List.range (bottomCount + (List.range bottomCount).length)) ≠ k :=
    findPartnerScan_neExclude_ofTarget ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) m k
      (List.range (bottomCount + (List.range bottomCount).length)) m mMem mNeK mRoot
  have scanRoot : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range bottomCount ++ List.range bottomCount)
        (findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) m k
          (List.range (bottomCount + (List.range bottomCount).length)))) = m :=
    findPartnerScan_root_ofFound ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) m k
      (List.range (bottomCount + (List.range bottomCount).length)) scanNeK
  -- the empty-links root is the node itself, so the boundary read at the result is m
  have readAtPartner : natListGetAt (List.range bottomCount ++ List.range bottomCount)
      (findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) m k
        (List.range (bottomCount + (List.range bottomCount).length))) = m := scanRoot
  -- the result is below the total
  have partnerLt : findPartnerScan ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) m k
      (List.range (bottomCount + (List.range bottomCount).length))
      < bottomCount + (List.range bottomCount).length :=
    findPartnerScan_lt_of_scannedLt ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) m k
      (bottomCount + (List.range bottomCount).length) kTotal
      (List.range (bottomCount + (List.range bottomCount).length))
      (fun candidate candidateMem => mem_range_imp_lt candidateMem)
  -- case on whether the result is a bottom or a top index
  cases Nat.lt_or_ge (findPartnerScan ([] : List (Nat × Nat))
      (List.range bottomCount ++ List.range bottomCount) m k
      (List.range (bottomCount + (List.range bottomCount).length))) bottomCount with
  | inl below => exact below
  | inr above =>
      exfalso
      obtain ⟨j, hj⟩ := Nat.le.dest above
      have jLt : j < bottomCount := by
        have step : bottomCount + j < bottomCount + (List.range bottomCount).length := by
          rw [hj]; exact partnerLt
        have jLtLen : j < (List.range bottomCount).length := Nat.lt_of_add_lt_add_left step
        rw [lenEq] at jLtLen
        exact jLtLen
      have readAbove : natListGetAt (List.range bottomCount ++ List.range bottomCount)
          (findPartnerScan ([] : List (Nat × Nat)) (List.range bottomCount ++ List.range bottomCount) m k
            (List.range (bottomCount + (List.range bottomCount).length))) = j := by
        rw [← hj, doubleRangeGet_above jLt]
      have jEqM : j = m := (readAbove.symm.trans readAtPartner)
      have partnerEqK : findPartnerScan ([] : List (Nat × Nat))
          (List.range bottomCount ++ List.range bottomCount) m k
          (List.range (bottomCount + (List.range bottomCount).length)) = k := by rw [← hj, jEqM, hm]
      exact scanNeK partnerEqK

/-! ## The peel-last step reduction (mirroring `dropStepReduce`) -/

private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget) (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue : (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

/-- Reduce a pure-cup boundary-chained spine `prefixAtoms ++ [lastCup]` to a top-of-stack cup fired
onto the processed prefix, with the prefix state's shipped invariants — the shared front matter of the
peel-last step (a copy of the private `dropStepReduce` skeleton). -/
private theorem stepReduce {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])
        = extractArc bottomCount
            (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms) lastCup.leftContext.length)
      ∧ ArcStateFresh (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms)
      ∧ isUnionFindForest (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).links
      ∧ bottomCount ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).nextFresh
      ∧ ArcBoundaryCensus bottomCount (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
      ∧ lastCup.leftContext.length ≤ (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms).openWires.length := by
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have sumZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup (addRightVanish sumZero)
  have prefixChained : SpineBoundaryChained bottomCount prefixAtoms :=
    spineBoundaryChained_prefix_ofAppend prefixAtoms [lastCup] bottomCount chained
  have freshS := arcStateFresh_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) (arcStateFresh_initial bottomCount)
  have forestS := isUnionFindForest_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) isUnionFindForest_nil
  have censusS := arcBoundaryCensus_ofChainedSpineList bottomCount prefixAtoms prefixChained
  have seedBelowS := seedBottomCount_le_processArcSpine_nextFresh bottomCount prefixAtoms
  have domLen := processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  have structEq : arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length) := by
    show extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          (prefixAtoms ++ [lastCup]))
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)
    rw [processArcSpine_append prefixAtoms [lastCup]
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
    show extractArc bottomCount
        (stepArcAtom (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup)
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)
    rw [stepArcAtom_eq_stepCupArc
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
      lastCup lastDom lastCod]
  exact ⟨structEq, freshS, forestS, seedBelowS, censusS, windowFitsS⟩

/-! ## Length reflections for the prefix arc lists -/

private theorem extractArc_internalCupCounts_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).internalCupCounts.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
        state.cupEventNodes)).length = bottomCount + state.openWires.length
  rw [natListMapLength, rangeLength]

private theorem extractArc_partner_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).diagram.partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [natListMapLength, rangeLength]


/-- ★ **The peel-last step for the pointwise characterization.**  Firing a top-of-stack cup at
`windowPos` onto a well-formed prefix state whose extract already satisfies the pointwise
characterization: the composite extract satisfies it too.  The count list splices `[1, 1]` at
`bottomCount + windowPos` (`internalCupCounts_stepCupArc`) exactly where the short chord
`[bottomCount + windowPos + 1, bottomCount + windowPos]` is spliced into the partner list
(`diagramPartner_stepCupArc`); the two window ports read a top-top chord (indicator `1`), and every
other port shift-tracks through `freshShiftAbove` and inherits from `prefixPointwise`. -/
private theorem stepPointwise (bottomCount : Nat) (prefixState : ArcWireState) (windowPos : Nat)
    (fresh : ArcStateFresh prefixState) (forest : isUnionFindForest prefixState.links)
    (seedBelow : bottomCount ≤ prefixState.nextFresh)
    (census : ArcBoundaryCensus bottomCount prefixState)
    (windowFits : windowPos ≤ prefixState.openWires.length)
    (prefixPointwise : ∀ j, j < bottomCount + prefixState.openWires.length →
      natListGetAt (extractArc bottomCount prefixState).internalCupCounts j
        = cupPortIndicator bottomCount
            (natListGetAt (extractArc bottomCount prefixState).diagram.partner j) j)
    (k : Nat) (kRange : k < bottomCount + (stepCupArc prefixState windowPos).openWires.length) :
    natListGetAt (extractArc bottomCount (stepCupArc prefixState windowPos)).internalCupCounts k
      = cupPortIndicator bottomCount
          (natListGetAt (extractArc bottomCount (stepCupArc prefixState windowPos)).diagram.partner k) k := by
  have steppedOpenLen : (stepCupArc prefixState windowPos).openWires.length
      = prefixState.openWires.length + 2 :=
    natListInsertAt_length prefixState.openWires windowPos
      [prefixState.nextFresh, prefixState.nextFresh + 1]
  have kRangeStepped : k < bottomCount + (prefixState.openWires.length + 2) := by
    rw [steppedOpenLen] at kRange; exact kRange
  have windowLe : bottomCount + windowPos ≤ bottomCount + prefixState.openWires.length :=
    Nat.add_le_add_left windowFits bottomCount
  have bottomLeWindow : bottomCount ≤ bottomCount + windowPos :=
    Nat.le_add_right bottomCount windowPos
  have icLen : (extractArc bottomCount prefixState).internalCupCounts.length
      = bottomCount + prefixState.openWires.length :=
    extractArc_internalCupCounts_length bottomCount prefixState
  have partnerLen : (extractArc bottomCount prefixState).diagram.partner.length
      = bottomCount + prefixState.openWires.length :=
    extractArc_partner_length bottomCount prefixState
  rw [internalCupCounts_stepCupArc bottomCount prefixState windowPos fresh forest seedBelow windowFits,
    diagramPartner_stepCupArc bottomCount prefixState windowPos fresh forest seedBelow census windowFits]
  cases Nat.lt_or_ge k (bottomCount + windowPos) with
  | inl kBelowWindow =>
      -- zone A: below the window
      have kBelowIc : k < (extractArc bottomCount prefixState).internalCupCounts.length := by
        rw [icLen]; exact Nat.lt_of_lt_of_le kBelowWindow windowLe
      have kBelowPartner : k < (extractArc bottomCount prefixState).diagram.partner.length := by
        rw [partnerLen]; exact Nat.lt_of_lt_of_le kBelowWindow windowLe
      have kBelowMapped : k < ((extractArc bottomCount prefixState).diagram.partner.map
          (freshShiftAbove (bottomCount + windowPos) 2)).length := by
        rw [natListMapLength]; exact kBelowPartner
      rw [natListGetAt_natListInsertAt_below (extractArc bottomCount prefixState).internalCupCounts
          (bottomCount + windowPos) [1, 1] k kBelowWindow kBelowIc,
        natListGetAt_natListInsertAt_below
          ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
          (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos] k kBelowWindow kBelowMapped,
        natListGetAt_map_below (freshShiftAbove (bottomCount + windowPos) 2)
          (extractArc bottomCount prefixState).diagram.partner k kBelowPartner,
        prefixPointwise k (by rw [icLen] at kBelowIc; exact kBelowIc)]
      exact cupPortIndicator_congr rfl
        (bleShiftAbove bottomCount (bottomCount + windowPos) 2
          (natListGetAt (extractArc bottomCount prefixState).diagram.partner k) bottomLeWindow).symm
  | inr kAtLeastWindow =>
      obtain ⟨d, hd⟩ := Nat.le.dest kAtLeastWindow
      cases d with
      | zero =>
          -- zone B: the left leg, k = window
          have kEq : k = bottomCount + windowPos := by rw [← hd, Nat.add_zero]
          subst kEq
          have windowLeIc : bottomCount + windowPos
              ≤ (extractArc bottomCount prefixState).internalCupCounts.length := by
            rw [icLen]; exact windowLe
          have windowLeMapped : bottomCount + windowPos
              ≤ ((extractArc bottomCount prefixState).diagram.partner.map
                (freshShiftAbove (bottomCount + windowPos) 2)).length := by
            rw [natListMapLength, partnerLen]; exact windowLe
          have icRead : natListGetAt (natListInsertAt
              (extractArc bottomCount prefixState).internalCupCounts (bottomCount + windowPos) [1, 1])
              (bottomCount + windowPos) = 1 := by
            have inside := natListGetAt_natListInsertAt_inside
              (extractArc bottomCount prefixState).internalCupCounts (bottomCount + windowPos) [1, 1] 0
              (Nat.succ_pos 1) windowLeIc
            rw [Nat.add_zero] at inside; exact inside
          have partnerRead : natListGetAt (natListInsertAt
              ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
              (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos])
              (bottomCount + windowPos) = bottomCount + windowPos + 1 := by
            have inside := natListGetAt_natListInsertAt_inside
              ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
              (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos] 0
              (Nat.succ_pos 1) windowLeMapped
            rw [Nat.add_zero] at inside; exact inside
          rw [icRead, partnerRead]
          exact (cupPortIndicator_of_bothTrue (natBleEqTrueOfLe bottomLeWindow)
            (natBleEqTrueOfLe (Nat.le_trans bottomLeWindow (Nat.le_succ (bottomCount + windowPos))))).symm
      | succ d' =>
          cases d' with
          | zero =>
              -- zone C: the right leg, k = window + 1
              have kEq : k = bottomCount + windowPos + 1 := by rw [← hd]
              subst kEq
              have windowLeIc : bottomCount + windowPos
                  ≤ (extractArc bottomCount prefixState).internalCupCounts.length := by
                rw [icLen]; exact windowLe
              have windowLeMapped : bottomCount + windowPos
                  ≤ ((extractArc bottomCount prefixState).diagram.partner.map
                    (freshShiftAbove (bottomCount + windowPos) 2)).length := by
                rw [natListMapLength, partnerLen]; exact windowLe
              have icRead : natListGetAt (natListInsertAt
                  (extractArc bottomCount prefixState).internalCupCounts (bottomCount + windowPos) [1, 1])
                  (bottomCount + windowPos + 1) = 1 :=
                natListGetAt_natListInsertAt_inside
                  (extractArc bottomCount prefixState).internalCupCounts (bottomCount + windowPos) [1, 1] 1
                  (Nat.lt_succ_self 1) windowLeIc
              have partnerRead : natListGetAt (natListInsertAt
                  ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
                  (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos])
                  (bottomCount + windowPos + 1) = bottomCount + windowPos :=
                natListGetAt_natListInsertAt_inside
                  ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
                  (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos] 1
                  (Nat.lt_succ_self 1) windowLeMapped
              rw [icRead, partnerRead]
              exact (cupPortIndicator_of_bothTrue
                (natBleEqTrueOfLe (Nat.le_trans bottomLeWindow (Nat.le_succ (bottomCount + windowPos))))
                (natBleEqTrueOfLe bottomLeWindow)).symm
          | succ t =>
              -- zone D: past the window, k = window + 2 + t
              have kEq : k = bottomCount + windowPos + 2 + t := by
                rw [← hd, Nat.add_assoc (bottomCount + windowPos) 2 t, Nat.add_comm 2 t]
              subst kEq
              have windowTLt : bottomCount + windowPos + t < bottomCount + prefixState.openWires.length := by
                have reassoc : bottomCount + windowPos + 2 + t = bottomCount + windowPos + t + 2 := by
                  rw [Nat.add_assoc (bottomCount + windowPos) 2 t, Nat.add_comm 2 t,
                    ← Nat.add_assoc (bottomCount + windowPos) t 2]
                rw [reassoc, ← Nat.add_assoc bottomCount prefixState.openWires.length 2] at kRangeStepped
                exact Nat.lt_of_add_lt_add_right kRangeStepped
              have windowTLtIc : bottomCount + windowPos + t
                  ≤ (extractArc bottomCount prefixState).internalCupCounts.length := by
                rw [icLen]; exact Nat.le_of_lt windowTLt
              have windowTLtPartner : bottomCount + windowPos + t
                  < (extractArc bottomCount prefixState).diagram.partner.length := by
                rw [partnerLen]; exact windowTLt
              have icRead : natListGetAt (natListInsertAt
                  (extractArc bottomCount prefixState).internalCupCounts (bottomCount + windowPos) [1, 1])
                  (bottomCount + windowPos + 2 + t)
                  = natListGetAt (extractArc bottomCount prefixState).internalCupCounts
                      (bottomCount + windowPos + t) := by
                have past := natListGetAt_natListInsertAt_pastBlock
                  (extractArc bottomCount prefixState).internalCupCounts (bottomCount + windowPos) [1, 1] t
                  (by rw [icLen]; exact windowLe)
                have blkLen : ([1, 1] : List Nat).length = 2 := rfl
                rw [blkLen, Nat.add_right_comm (bottomCount + windowPos) t 2] at past
                exact past
              have partnerRead : natListGetAt (natListInsertAt
                  ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
                  (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos])
                  (bottomCount + windowPos + 2 + t)
                  = freshShiftAbove (bottomCount + windowPos) 2
                      (natListGetAt (extractArc bottomCount prefixState).diagram.partner
                        (bottomCount + windowPos + t)) := by
                have past := natListGetAt_natListInsertAt_pastBlock
                  ((extractArc bottomCount prefixState).diagram.partner.map (freshShiftAbove (bottomCount + windowPos) 2))
                  (bottomCount + windowPos) [bottomCount + windowPos + 1, bottomCount + windowPos] t
                  (by rw [natListMapLength, partnerLen]; exact windowLe)
                have blkLen : ([bottomCount + windowPos + 1, bottomCount + windowPos] : List Nat).length = 2 := rfl
                rw [blkLen, Nat.add_right_comm (bottomCount + windowPos) t 2] at past
                rw [past, natListGetAt_map_below (freshShiftAbove (bottomCount + windowPos) 2)
                  (extractArc bottomCount prefixState).diagram.partner (bottomCount + windowPos + t) windowTLtPartner]
              rw [icRead, partnerRead, prefixPointwise (bottomCount + windowPos + t) windowTLt]
              refine cupPortIndicator_congr ?_ (bleShiftAbove bottomCount (bottomCount + windowPos) 2
                (natListGetAt (extractArc bottomCount prefixState).diagram.partner (bottomCount + windowPos + t))
                bottomLeWindow).symm
              rw [natBleEqTrueOfLe (Nat.le_trans bottomLeWindow (Nat.le_add_right (bottomCount + windowPos) t)),
                natBleEqTrueOfLe (Nat.le_trans bottomLeWindow
                  (Nat.le_trans (Nat.le_add_right (bottomCount + windowPos) 2)
                    (Nat.le_add_right (bottomCount + windowPos + 2) t)))]

/-! ## The pointwise characterization (fuel-driven peel-last induction) -/

private theorem pointwiseFueled {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat) :
    (fuel : Nat) →
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    atoms.length ≤ fuel →
    SpineBoundaryChained bottomCount atoms →
    AllCupArity atoms →
    ∀ k, k < bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms).openWires.length →
      natListGetAt (arcStructureOfSpineList bottomCount atoms).internalCupCounts k
        = cupPortIndicator bottomCount
            (natListGetAt (arcStructureOfSpineList bottomCount atoms).diagram.partner k) k
  | 0, atoms, lenBound, _, _, k, kRange => by
      have atomsNil : atoms = [] := listEqNilOfLengthZero atoms (Nat.le_antisymm lenBound (Nat.zero_le _))
      subst atomsNil
      have kRange2 : k < bottomCount + bottomCount := by
        have owLen : (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires.length
            = bottomCount := rangeLength bottomCount
        rw [owLen] at kRange; exact kRange
      show natListGetAt (extractArc bottomCount
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).internalCupCounts k
        = cupPortIndicator bottomCount (natListGetAt (extractArc bottomCount
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner k) k
      rw [initialInternalCupCounts_get kRange2]
      cases Nat.lt_or_ge k bottomCount with
      | inl kBelow => exact (cupPortIndicator_of_idxFalse (natBleEqFalseOfLt kBelow)).symm
      | inr kAtLeast =>
          exact (cupPortIndicator_of_partnerFalse
            (natBleEqFalseOfLt (initialPartner_topPort_lt kAtLeast kRange2))).symm
  | fuel + 1, atoms, lenBound, chained, pureCup, k, kRange => by
      cases listNilOrSnoc atoms with
      | inl atomsNil =>
          subst atomsNil
          have kRange2 : k < bottomCount + bottomCount := by
            have owLen : (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).openWires.length
                = bottomCount := rangeLength bottomCount
            rw [owLen] at kRange; exact kRange
          show natListGetAt (extractArc bottomCount
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).internalCupCounts k
            = cupPortIndicator bottomCount (natListGetAt (extractArc bottomCount
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])).diagram.partner k) k
          rw [initialInternalCupCounts_get kRange2]
          cases Nat.lt_or_ge k bottomCount with
          | inl kBelow => exact (cupPortIndicator_of_idxFalse (natBleEqFalseOfLt kBelow)).symm
          | inr kAtLeast =>
              exact (cupPortIndicator_of_partnerFalse
                (natBleEqFalseOfLt (initialPartner_topPort_lt kAtLeast kRange2))).symm
      | inr snocWit =>
          obtain ⟨prefixAtoms, lastCup, atomsSnoc⟩ := snocWit
          subst atomsSnoc
          obtain ⟨structEq, freshS, forestS, seedBelowS, censusS, windowFitsS⟩ :=
            stepReduce bottomCount prefixAtoms lastCup chained pureCup
          have prefixChained : SpineBoundaryChained bottomCount prefixAtoms :=
            spineBoundaryChained_prefix_ofAppend prefixAtoms [lastCup] bottomCount chained
          have prefixPure : AllCupArity prefixAtoms :=
            allCupArity_prefix_ofAppend prefixAtoms [lastCup] pureCup
          have prefixLenBound : prefixAtoms.length ≤ fuel := by
            have snocLen : (prefixAtoms ++ [lastCup]).length = prefixAtoms.length + 1 :=
              lengthSnoc prefixAtoms lastCup
            rw [snocLen] at lenBound
            exact Nat.le_of_succ_le_succ lenBound
          have inductionHypothesis := pointwiseFueled bottomCount fuel prefixAtoms prefixLenBound
            prefixChained prefixPure
          -- the composite open-wire length, so the goal's k-range matches the stepped state
          have owComposite : (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              (prefixAtoms ++ [lastCup])).openWires.length
              = (stepCupArc (processArcSpine
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
                lastCup.leftContext.length).openWires.length := by
            rw [processArcSpine_append prefixAtoms [lastCup]
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
            show (stepArcAtom (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
              lastCup).openWires.length
              = (stepCupArc (processArcSpine
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
                lastCup.leftContext.length).openWires.length
            obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup
              (addRightVanish ((capAtomCount_append prefixAtoms [lastCup]).symm.trans
                (capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup)))
            rw [stepArcAtom_eq_stepCupArc (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
              lastCup lastDom lastCod]
          have kRangeStepped : k < bottomCount + (stepCupArc (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
              lastCup.leftContext.length).openWires.length := by
            rw [owComposite] at kRange; exact kRange
          rw [structEq]
          exact stepPointwise bottomCount (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
            lastCup.leftContext.length freshS forestS seedBelowS censusS windowFitsS
            (fun j jRange => inductionHypothesis j jRange) k kRangeStepped

/-- ★ **The per-port cup-count characterization (`Q`).**  For a boundary-chained pure-cup spine the
internal cup count at each in-range port `k` is `1` exactly when `k` is a top port whose partner is a
top port (a top-top short chord), and `0` otherwise — a function of the boundary `diagram` alone. -/
theorem pureCup_internalCupCounts_pointwise {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) (chained : SpineBoundaryChained bottomCount atoms)
    (k : Nat)
    (kRange : k < bottomCount + (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length) :
    natListGetAt (arcStructureOfSpineList bottomCount atoms).internalCupCounts k
      = cupPortIndicator bottomCount
          (natListGetAt (arcStructureOfSpineList bottomCount atoms).diagram.partner k) k :=
  pointwiseFueled bottomCount atoms.length atoms (Nat.le_refl atoms.length) chained pureCup k kRange

/-! ## The agreement corollary -/

/-- A list is determined by its length and its entries, indexed by `natListGetAt` (structural, no
`funext`). -/
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

/-- ★ **The agreement corollary.**  Two pure-cup boundary-chained spines whose boundary `diagram`s
agree have equal `internalCupCounts`: each entry is `cupPortIndicator` of the SHARED partner list, and
the lengths agree because the `diagram` fixes the top-port count.  Discharges the
`cupInternalCupCountsAgree` residual of `sameMatchingValleys_spineTraceEquiv`. -/
theorem pureCupSpines_internalCupCountsAgree_ofDiagram {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCup : AllCupArity firstList) (secondPureCup : AllCupArity secondList)
    (firstChained : SpineBoundaryChained bottomCount firstList)
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
      = (arcStructureOfSpineList bottomCount secondList).diagram) :
    (arcStructureOfSpineList bottomCount firstList).internalCupCounts
      = (arcStructureOfSpineList bottomCount secondList).internalCupCounts := by
  have topEq : (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        firstList).openWires.length
      = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondList).openWires.length :=
    congrArg DiagramType.topCount diagramAgree
  have firstIcLen : (arcStructureOfSpineList bottomCount firstList).internalCupCounts.length
      = bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        firstList).openWires.length :=
    extractArc_internalCupCounts_length bottomCount _
  have secondIcLen : (arcStructureOfSpineList bottomCount secondList).internalCupCounts.length
      = bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondList).openWires.length :=
    extractArc_internalCupCounts_length bottomCount _
  have lengthEq : (arcStructureOfSpineList bottomCount firstList).internalCupCounts.length
      = (arcStructureOfSpineList bottomCount secondList).internalCupCounts.length := by
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
  rw [pureCup_internalCupCounts_pointwise bottomCount firstList firstPureCup firstChained index indexFirst,
    pureCup_internalCupCounts_pointwise bottomCount secondList secondPureCup secondChained index indexSecond,
    partnerAgree]

/-! ## Honesty marker -/

/-- **Honesty marker — the per-port cup-count characterization (leaf 2a-i) is SHIPPED.**
`pureCup_internalCupCounts_pointwise`: on a boundary-chained pure-cup spine the internal cup count at
each port is `cupPortIndicator` of the boundary partner (a top-top short chord reads `1`, all else
`0`), proved by peel-last induction (empty spine both-sides-zero; last-cup splice `[1,1]` at the same
window the short chord `[bc+w+1, bc+w]` is spliced into the partner, other ports shift-tracking through
`freshShiftAbove`).  `pureCupSpines_internalCupCountsAgree_ofDiagram`: equal `diagram`s force equal
`internalCupCounts`.  This discharges the `cupInternalCupCountsAgree` 2a residual of
`sameMatchingValleys_spineTraceEquiv`.  No gate flag is flipped.  `= true`. -/
def fxMode_hasArcCupInternalCountsPointwise : Bool := true

end FX1Poly.Polygraph
