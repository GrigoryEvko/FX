import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingStepCupOldPartner

/-! # MatchingStepCupWindowPartner — the two fresh window ports partner each other (Track B route 1, brick 3)

The arc-carrier `generalStateCupForwardPartner` reads the forward window partner off a censused arc state via the
census-backed uniqueness `partnerIndexOf_uniqueSameComponent` (which rules out a THIRD boundary node sharing a
component through the perfect-matching census).  The width-`0` plain carrier is settled MORE cheaply: brick 1's
DIRECT freshness argument (the fresh cup component's stepped root is `nextFresh + 1`, strictly above every old
port's root) pins BOTH window partners with NO census — the result of the partner scan must share the fresh root
`nextFresh + 1`, and every OLD boundary node roots below `nextFresh`, so the scan can only land on the OTHER fresh
leg.

This file lands, census-free and positivity-free:

  * ★ `partnerIndexOf_ofFreshLegPair` — the abstract fresh-leg uniqueness finisher: at a boundary where the
    exclude and target indices both read a node rooting to `freshBound + 1` and EVERY other in-range index roots
    below `freshBound`, the partner scan of the exclude returns the target.  Brick 1's uniqueness, abstracted.
  * ★ `generalStateCupForwardPartnerMatching` — the seed-general FORWARD window partner: a folded cup's left leg
    `seedBoundary + windowPosition` partners the right leg `seedBoundary + windowPosition + 1`.
  * ★ `generalStateCupBackwardPartnerMatching` — the seed-general BACKWARD window partner: the right leg
    `seedBoundary + windowPosition + 1` partners the left leg `seedBoundary + windowPosition`.  This is what the
    arc route obtained via the census involution; here it is a symmetric copy of the forward argument.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / membership plumbing (per-file copies, following the codebase pattern) -/

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
  rw [rangeLoopLength count []]; exact Nat.add_zero count

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

private theorem rangeLoopMem_ofAccumulated : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, targetMem => targetMem
  | count + 1, accumulated, target, targetMem =>
      rangeLoopMem_ofAccumulated count (count :: accumulated) target (List.Mem.tail count targetMem)

private theorem rangeLoopMem_ofLt : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target < count → target ∈ List.range.loop count accumulated
  | 0, _, target, targetBelow => absurd targetBelow (Nat.not_lt_zero target)
  | count + 1, accumulated, target, targetBelow => by
      cases Nat.lt_or_ge target count with
      | inl below => exact rangeLoopMem_ofLt count (count :: accumulated) target below
      | inr atLeast =>
          have targetEq : target = count := Nat.le_antisymm (Nat.le_of_succ_le_succ targetBelow) atLeast
          rw [targetEq]
          exact rangeLoopMem_ofAccumulated count (count :: accumulated) count (List.Mem.head accumulated)

private theorem rangeMem_ofLt (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  rangeLoopMem_ofLt count [] target targetBelow

private theorem findPartnerScan_memOrExclude (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned = excludeIndex
      ∨ findPartnerScan links boundaryNodes rootHere excludeIndex scanned ∈ scanned
  | [] => Or.inl rfl
  | candidate :: rest => by
      rw [findPartnerScan_cons]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => exact Or.inr (List.Mem.head rest)
      | false =>
          cases findPartnerScan_memOrExclude links boundaryNodes rootHere excludeIndex rest with
          | inl isExclude => exact Or.inl isExclude
          | inr isMember => exact Or.inr (List.Mem.tail candidate isMember)

private theorem natListGetAt_mem_inRange :
    (wires : List Nat) → (index : Nat) → index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The abstract fresh-leg uniqueness finisher -/

/-- ★ **The fresh-leg partner uniqueness (census-free).**  At a boundary where the `excludeIndex` and
`targetIndex` both read a node whose root is `freshBound + 1`, and EVERY other in-range index reads a node rooting
strictly BELOW `freshBound`, the canonical partner scan of `excludeIndex` returns `targetIndex`: the scan skips
`excludeIndex`, and its answer shares `excludeIndex`'s root `freshBound + 1`, so it cannot be an old index (root
`< freshBound`), leaving only the target.  Brick 1's uniqueness, abstracted over the two fresh legs. -/
theorem partnerIndexOf_ofFreshLegPair (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (total freshBound excludeIndex targetIndex : Nat)
    (targetInRange : targetIndex < total)
    (targetNeExclude : targetIndex ≠ excludeIndex)
    (rootAtExclude : unionFindRootOf links (natListGetAt boundaryNodes excludeIndex) = freshBound + 1)
    (rootAtTarget : unionFindRootOf links (natListGetAt boundaryNodes targetIndex) = freshBound + 1)
    (oldBelow : ∀ c, c < total → c ≠ excludeIndex → c ≠ targetIndex →
      unionFindRootOf links (natListGetAt boundaryNodes c) < freshBound) :
    partnerIndexOf links boundaryNodes total excludeIndex = targetIndex := by
  show findPartnerScan links boundaryNodes
      (unionFindRootOf links (natListGetAt boundaryNodes excludeIndex)) excludeIndex (List.range total)
    = targetIndex
  rw [rootAtExclude]
  have targetMem : targetIndex ∈ List.range total := rangeMem_ofLt total targetIndex targetInRange
  have resultNeExclude := findPartnerScan_neExclude_ofTarget links boundaryNodes (freshBound + 1)
    excludeIndex (List.range total) targetIndex targetMem targetNeExclude rootAtTarget
  have resultRoot := findPartnerScan_root_ofFound links boundaryNodes (freshBound + 1)
    excludeIndex (List.range total) resultNeExclude
  have resultMem : findPartnerScan links boundaryNodes (freshBound + 1) excludeIndex (List.range total)
      ∈ List.range total := by
    cases findPartnerScan_memOrExclude links boundaryNodes (freshBound + 1) excludeIndex
        (List.range total) with
    | inl isExclude => exact absurd isExclude resultNeExclude
    | inr isMember => exact isMember
  have resultInRange : findPartnerScan links boundaryNodes (freshBound + 1) excludeIndex (List.range total)
      < total := mem_range_imp_lt resultMem
  cases Nat.decEq (findPartnerScan links boundaryNodes (freshBound + 1) excludeIndex (List.range total))
      targetIndex with
  | isTrue resultEq => exact resultEq
  | isFalse resultNe =>
      exfalso
      have below := oldBelow (findPartnerScan links boundaryNodes (freshBound + 1) excludeIndex
        (List.range total)) resultInRange resultNeExclude resultNe
      rw [resultRoot] at below
      exact Nat.lt_irrefl freshBound (Nat.lt_trans (Nat.lt_succ_self freshBound) below)

/-! ## The window / old boundary reads on the stepped state -/

/-- The insert reads BELOW `nextFresh` away from the two window slots (brick 1's `oldReadBelow` body, factored). -/
private theorem insertReadBelow (state : WireState) (windowPosition : Nat)
    (openBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length) (offset : Nat)
    (offsetLt : offset < state.openWires.length + 2) (offsetNeW : offset ≠ windowPosition)
    (offsetNeW1 : offset ≠ windowPosition + 1) :
    natListGetAt (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) offset
      < state.nextFresh := by
  cases Nat.lt_or_ge offset windowPosition with
  | inl below =>
      have offsetLtLen : offset < state.openWires.length := Nat.lt_of_lt_of_le below windowFits
      rw [natListGetAt_natListInsertAt_below state.openWires windowPosition
        [state.nextFresh, state.nextFresh + 1] offset below offsetLtLen]
      exact openBelow _ (natListGetAt_mem_inRange state.openWires offset offsetLtLen)
  | inr atLeast =>
      cases Nat.lt_or_ge offset (windowPosition + 1) with
      | inl belowSucc =>
          exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) atLeast) offsetNeW
      | inr atLeastSucc =>
          have offsetGeW2 : windowPosition + 2 ≤ offset := by
            cases Nat.lt_or_ge offset (windowPosition + 2) with
            | inl ltTwo => exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ ltTwo) atLeastSucc) offsetNeW1
            | inr geTwo => exact geTwo
          obtain ⟨tail, tailEq⟩ := Nat.le.dest offsetGeW2
          have idxForm : offset = windowPosition + tail + 2 := by
            rw [← tailEq, Nat.add_right_comm windowPosition 2 tail]
          have pastRead : natListGetAt (natListInsertAt state.openWires windowPosition
                [state.nextFresh, state.nextFresh + 1]) offset
              = natListGetAt state.openWires (windowPosition + tail) := by
            rw [idxForm]
            exact natListGetAt_natListInsertAt_pastBlock state.openWires windowPosition
              [state.nextFresh, state.nextFresh + 1] tail windowFits
          have windowTailLt : windowPosition + tail < state.openWires.length := by
            have shifted : windowPosition + tail + 2 < state.openWires.length + 2 := by
              rw [← idxForm]; exact offsetLt
            exact Nat.lt_of_add_lt_add_right shifted
          rw [pastRead]
          exact openBelow _ (natListGetAt_mem_inRange state.openWires (windowPosition + tail) windowTailLt)

/-- Away from the two window slots, the stepped boundary reads BELOW `nextFresh` (seed-general). -/
private theorem stepCupWindow_oldReadBelow (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (openBelow : ∀ wire ∈ state.openWires, wire < state.nextFresh)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length) (index : Nat)
    (indexLt : index < seedBoundary + (state.openWires.length + 2))
    (neW : index ≠ seedBoundary + windowPosition) (neW1 : index ≠ seedBoundary + windowPosition + 1) :
    natListGetAt (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) index
      < state.nextFresh := by
  cases Nat.lt_or_ge index seedBoundary with
  | inl indexBelow =>
      rw [natListGetAt_append_inside (List.range seedBoundary)
          (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) index
          (by rw [rangeLength]; exact indexBelow),
        rangeGetAt_below seedBoundary index indexBelow]
      exact Nat.lt_of_lt_of_le indexBelow seedBelowFresh
  | inr indexAtLeast =>
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest indexAtLeast
      have hIdx : index = offset + (List.range seedBoundary).length := by
        rw [rangeLength, ← offsetEq, Nat.add_comm seedBoundary offset]
      have offsetLt : offset < state.openWires.length + 2 := by
        have shifted : seedBoundary + offset < seedBoundary + (state.openWires.length + 2) := by
          rw [offsetEq]; exact indexLt
        exact Nat.lt_of_add_lt_add_left shifted
      have offsetNeW : offset ≠ windowPosition := by
        intro offsetEqW
        exact neW (by rw [← offsetEq, offsetEqW])
      have offsetNeW1 : offset ≠ windowPosition + 1 := by
        intro offsetEqW1
        exact neW1 (by rw [← offsetEq, offsetEqW1, Nat.add_assoc seedBoundary windowPosition 1])
      rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary)
        (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) offset]
      exact insertReadBelow state windowPosition openBelow windowFits offset offsetLt offsetNeW offsetNeW1

/-- The left window slot reads the left fresh leg `nextFresh`. -/
private theorem stepCupWindow_legLeftRead (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (windowFits : windowPosition ≤ state.openWires.length) :
    natListGetAt (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
        (seedBoundary + windowPosition) = state.nextFresh := by
  have hIdx : seedBoundary + windowPosition = windowPosition + (List.range seedBoundary).length := by
    rw [rangeLength, Nat.add_comm seedBoundary windowPosition]
  rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary)
    (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) windowPosition]
  have inside := natListGetAt_natListInsertAt_inside state.openWires windowPosition
    [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) windowFits
  rw [Nat.add_zero] at inside
  exact inside

/-- The right window slot reads the right fresh leg `nextFresh + 1`. -/
private theorem stepCupWindow_legRightRead (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (windowFits : windowPosition ≤ state.openWires.length) :
    natListGetAt (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
        (seedBoundary + windowPosition + 1) = state.nextFresh + 1 := by
  have hIdx : seedBoundary + windowPosition + 1 = (windowPosition + 1) + (List.range seedBoundary).length := by
    rw [rangeLength, Nat.add_comm (windowPosition + 1) seedBoundary, Nat.add_assoc seedBoundary windowPosition 1]
  rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary)
    (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) (windowPosition + 1)]
  exact natListGetAt_natListInsertAt_inside state.openWires windowPosition
    [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) windowFits

/-! ## The two window partners -/

/-- Bundle the shared `oldBelow` obligation (both window partners consume the same one). -/
private theorem stepCupWindow_oldRootBelow (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh) (windowFits : windowPosition ≤ state.openWires.length)
    (index : Nat) (indexLt : index < seedBoundary + (state.openWires.length + 2))
    (neW : index ≠ seedBoundary + windowPosition) (neW1 : index ≠ seedBoundary + windowPosition + 1) :
    unionFindRootOf (stepCup state windowPosition).links
        (natListGetAt (List.range seedBoundary ++ (stepCup state windowPosition).openWires) index)
      < state.nextFresh := by
  obtain ⟨openBelow, linkBelow⟩ := fresh
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeMem => (linkBelow edge edgeMem).2
  have hStepOpen : (stepCup state windowPosition).openWires
      = natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1] := rfl
  rw [hStepOpen]
  have nodeBelow := stepCupWindow_oldReadBelow seedBoundary state windowPosition openBelow seedBelowFresh
    windowFits index indexLt neW neW1
  have baseRootBelow : unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) index)
      < state.nextFresh :=
    unionFindRootOf_lt state.nextFresh state.links parentsBelow _ nodeBelow
  rw [unionFindRootOf_stepCup_old state windowPosition ⟨openBelow, linkBelow⟩ forest _ baseRootBelow]
  exact baseRootBelow

/-- ★ **The seed-general FORWARD window partner.**  A folded cup's left leg at boundary index
`seedBoundary + windowPosition` partners the right leg at `seedBoundary + windowPosition + 1`. -/
theorem generalStateCupForwardPartnerMatching (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (forest : isUnionFindForest state.links) (fresh : WireStateFresh state)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh) (windowFits : windowPosition ≤ state.openWires.length) :
    partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length)
        (seedBoundary + windowPosition)
      = seedBoundary + windowPosition + 1 := by
  have hStepOpen : (stepCup state windowPosition).openWires
      = natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1] := rfl
  have hStepLen : (stepCup state windowPosition).openWires.length = state.openWires.length + 2 := by
    rw [hStepOpen]
    exact natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  rw [hStepLen]
  refine partnerIndexOf_ofFreshLegPair (stepCup state windowPosition).links
    (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
    (seedBoundary + (state.openWires.length + 2)) state.nextFresh
    (seedBoundary + windowPosition) (seedBoundary + windowPosition + 1)
    (Nat.succ_lt_succ (Nat.lt_succ_of_le (Nat.add_le_add_left windowFits seedBoundary)))
    (fun heq => Nat.lt_irrefl (seedBoundary + windowPosition)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (seedBoundary + windowPosition)) (Nat.le_of_eq heq)))
    ?rootExclude ?rootTarget ?oldBelow
  case rootExclude =>
    rw [hStepOpen, stepCupWindow_legLeftRead seedBoundary state windowPosition windowFits]
    exact (stepCup_freshComponentRoot state windowPosition fresh forest).1
  case rootTarget =>
    rw [hStepOpen, stepCupWindow_legRightRead seedBoundary state windowPosition windowFits]
    exact (stepCup_freshComponentRoot state windowPosition fresh forest).2
  case oldBelow =>
    intro c cLt cNeExclude cNeTarget
    exact stepCupWindow_oldRootBelow seedBoundary state windowPosition fresh forest seedBelowFresh windowFits
      c cLt cNeExclude cNeTarget

/-- ★ **The seed-general BACKWARD window partner.**  A folded cup's right leg at boundary index
`seedBoundary + windowPosition + 1` partners the left leg at `seedBoundary + windowPosition`.  The census-free
symmetric companion of the forward partner (the arc route obtained this from the census involution). -/
theorem generalStateCupBackwardPartnerMatching (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (forest : isUnionFindForest state.links) (fresh : WireStateFresh state)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh) (windowFits : windowPosition ≤ state.openWires.length) :
    partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length)
        (seedBoundary + windowPosition + 1)
      = seedBoundary + windowPosition := by
  have hStepOpen : (stepCup state windowPosition).openWires
      = natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1] := rfl
  have hStepLen : (stepCup state windowPosition).openWires.length = state.openWires.length + 2 := by
    rw [hStepOpen]
    exact natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  rw [hStepLen]
  refine partnerIndexOf_ofFreshLegPair (stepCup state windowPosition).links
    (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
    (seedBoundary + (state.openWires.length + 2)) state.nextFresh
    (seedBoundary + windowPosition + 1) (seedBoundary + windowPosition)
    (Nat.add_lt_add_left
      (Nat.lt_succ_of_le (Nat.le_trans windowFits (Nat.le_succ state.openWires.length))) seedBoundary)
    (fun heq => Nat.lt_irrefl (seedBoundary + windowPosition)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (seedBoundary + windowPosition)) (Nat.le_of_eq heq.symm)))
    ?rootExclude ?rootTarget ?oldBelow
  case rootExclude =>
    rw [hStepOpen, stepCupWindow_legRightRead seedBoundary state windowPosition windowFits]
    exact (stepCup_freshComponentRoot state windowPosition fresh forest).2
  case rootTarget =>
    rw [hStepOpen, stepCupWindow_legLeftRead seedBoundary state windowPosition windowFits]
    exact (stepCup_freshComponentRoot state windowPosition fresh forest).1
  case oldBelow =>
    intro c cLt cNeExclude cNeTarget
    exact stepCupWindow_oldRootBelow seedBoundary state windowPosition fresh forest seedBelowFresh windowFits
      c cLt cNeTarget cNeExclude

end FX1Poly.Polygraph
