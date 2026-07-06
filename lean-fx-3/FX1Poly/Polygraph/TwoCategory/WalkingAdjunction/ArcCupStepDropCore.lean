import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupScanAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisciplinePreservation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality

/-! # ArcCupStepDropCore — a TOP-OF-STACK cup leaves the old ports' matching undisturbed (S3 core)

The whole top-of-stack cup-drop cancellation (`dropLastCup_arc_injective`, S3) rests on ONE core fact: a cup
fired LAST onto an arbitrary incoming state allocates a fresh, ISOLATED 3-node component and splices its two
legs into the open-wire list — so it leaves every OLD port's connected component untouched, merely shifting the
boundary positions at or beyond the insertion window up by two and adding the two fresh legs as a new disjoint
adjacent pair.

This file assembles the freshness / disjointness core the leg rounds need:

  * `stepCupArc_freshComponentRoot` — the three fresh nodes `nextFresh, nextFresh+1, nextFresh+2` all root to
    `nextFresh + 1` under the stepped links (the fresh cup component's single root), computed from the two nested
    `unionFindJoin`s via `unionFindRootOf_unionFindJoin` and the fresh-node parentless facts.
  * `stepCupArc_freshLeg_ne_oldRoot` — hence each fresh leg's stepped root is DISTINCT from the root of every OLD
    port (any node whose base root is below `nextFresh`): the boolean-equality test is `false`, the disjointness
    the punctured scan consumes to skip the two inserted leg candidates.
  * `cupCount_stepCupArc_succ` / `capCount_stepCupArc_eq` — the two trivial count legs: a cup conses one fresh
    cup-event node (`+1`) and leaves the cap-event list untouched.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fresh cup component's single root under a top-of-stack cup -/

/-- ★ **The fresh cup component roots to `nextFresh + 1`.**  A top-of-stack cup builds
`links := unionFindJoin (unionFindJoin state.links nextFresh (nextFresh+1)) (nextFresh+2) nextFresh`.  In a fresh
forest the three legs `nextFresh, nextFresh+1, nextFresh+2` are each parentless in the base links, so the inner
join sends both `nextFresh` and `nextFresh+1` to root `nextFresh+1` and leaves `nextFresh+2` at `nextFresh+2`,
and the outer join then folds `nextFresh+2` onto `nextFresh`'s root `nextFresh+1` — so all three fresh nodes
share the single component root `nextFresh + 1`, which is at or above `nextFresh` and hence never the root of an
old port. -/
theorem stepCupArc_freshComponentRoot (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    unionFindRootOf (stepCupArc state position).links state.nextFresh = state.nextFresh + 1
      ∧ unionFindRootOf (stepCupArc state position).links (state.nextFresh + 1) = state.nextFresh + 1
      ∧ unionFindRootOf (stepCupArc state position).links (state.nextFresh + 2)
          = state.nextFresh + 1 := by
  have hLinks : (stepCupArc state position).links
      = unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2) state.nextFresh := rfl
  -- the three legs are parentless in the base links (a fresh forest keeps every child below `nextFresh`)
  have baseRootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh
      (unionFindParent_none_of_freshNode state fresh state.nextFresh (Nat.le_refl _))
  have baseRootNf1 : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 1) (Nat.le_add_right _ _))
  have baseRootNf2 : unionFindRootOf state.links (state.nextFresh + 2) = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 2)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 2) (Nat.le_add_right _ _))
  have forestL1 : isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have hNf1LtNf2 : state.nextFresh + 1 < state.nextFresh + 2 := Nat.lt_succ_self _
  -- inner-join roots of the three legs
  have l1Nf : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      state.nextFresh = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) state.nextFresh forest,
      baseRootNf, baseRootNf1]
    cases hc : (state.nextFresh == state.nextFresh) with
    | true => rfl
    | false =>
        exact Bool.noConfusion
          ((decide_eq_true (rfl : state.nextFresh = state.nextFresh)).symm.trans hc)
  have l1Nf1 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 1) = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 1) forest, baseRootNf1]
    cases hc : (unionFindRootOf state.links state.nextFresh == state.nextFresh + 1) with
    | true => rfl
    | false => rfl
  have l1Nf2 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) = state.nextFresh + 2 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 2) forest, baseRootNf, baseRootNf2]
    cases hc : (state.nextFresh == state.nextFresh + 2) with
    | true =>
        exact absurd (of_decide_eq_true hc)
          (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))
    | false => rfl
  -- outer-join roots (the `nextFresh+2 -> nextFresh` fold) of the three legs
  refine ⟨?_, ?_, ?_⟩
  · rw [hLinks,
      unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh state.nextFresh forestL1, l1Nf2, l1Nf]
    cases hc : (state.nextFresh + 2 == state.nextFresh + 1) with
    | true => rfl
    | false => rfl
  · rw [hLinks,
      unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) forestL1, l1Nf2, l1Nf1]
    cases hc : (state.nextFresh + 2 == state.nextFresh + 1) with
    | true => exact absurd (of_decide_eq_true hc) (Nat.ne_of_gt hNf1LtNf2)
    | false => rfl
  · rw [hLinks,
      unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh (state.nextFresh + 2) forestL1, l1Nf2, l1Nf]
    cases hc : (state.nextFresh + 2 == state.nextFresh + 2) with
    | true => rfl
    | false =>
        exact Bool.noConfusion
          ((decide_eq_true (rfl : state.nextFresh + 2 = state.nextFresh + 2)).symm.trans hc)

/-! ## Disjointness of the fresh legs from every old port -/

/-- ★ **A fresh leg's stepped root is distinct from every old port's root.**  For an OLD node `y` whose base root
lies below `nextFresh`, neither the left leg `nextFresh` nor the right leg `nextFresh+1` shares `y`'s component
under the stepped links: both fresh legs root to `nextFresh + 1` (`stepCupArc_freshComponentRoot`), which lies
strictly above `y`'s root, so the boolean same-root test is `false`.  This is the disjointness the punctured
scan consumes to skip the two inserted leg candidates. -/
theorem stepCupArc_freshLeg_ne_oldRoot (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) (y : Nat)
    (yBelowFresh : unionFindRootOf state.links y < state.nextFresh) :
    (unionFindRootOf (stepCupArc state position).links state.nextFresh
        == unionFindRootOf state.links y) = false
      ∧ (unionFindRootOf (stepCupArc state position).links (state.nextFresh + 1)
          == unionFindRootOf state.links y) = false := by
  obtain ⟨rootNf, rootNf1, _⟩ := stepCupArc_freshComponentRoot state position fresh forest
  have yBelowFresh1 : unionFindRootOf state.links y < state.nextFresh + 1 :=
    Nat.lt_succ_of_lt yBelowFresh
  refine ⟨?_, ?_⟩
  · rw [rootNf]; exact beq_false_of_lt yBelowFresh1
  · rw [rootNf1]; exact beq_false_of_lt yBelowFresh1

/-! ## The two trivial count legs -/

/-- ★ **A cup conses exactly one fresh cup-event node.**  `stepCupArc` prepends the event node `nextFresh+2`
to `cupEventNodes`, so the cup-event count rises by exactly one. -/
theorem cupCount_stepCupArc_succ (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).cupEventNodes.length = state.cupEventNodes.length + 1 := rfl

/-- ★ **A cup leaves the cap-event list untouched.**  `stepCupArc` never allocates a cap event, so the
cap-event count is unchanged. -/
theorem capCount_stepCupArc_eq (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).capEventNodes.length = state.capEventNodes.length := rfl

/-! ## THE CORE — a top-of-stack cup shifts the old ports' matching, undisturbed

Private range / list plumbing (per-file copies, following the codebase pattern). -/

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

private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-- Dropping two consecutive FAILING candidates anywhere in the scanned list preserves the scan — the
punctured-scan atom (a per-file copy of the sibling in `ArcCupPuncturedScan`). -/
private theorem findPartnerScan_dropFailingPair (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex legLeft legRight : Nat)
    (leftFails : (legLeft != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes legLeft) == rootHere) = false)
    (rightFails : (legRight != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes legRight) == rootHere) = false) :
    (front tail : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex (front ++ legLeft :: legRight :: tail)
      = findPartnerScan links boundaryNodes rootHere excludeIndex (front ++ tail)
  | [], tail => by
      show findPartnerScan links boundaryNodes rootHere excludeIndex (legLeft :: legRight :: tail)
        = findPartnerScan links boundaryNodes rootHere excludeIndex tail
      rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex legLeft
          (legRight :: tail) leftFails,
        findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex legRight tail rightFails]
  | candidate :: frontRest, tail => by
      show findPartnerScan links boundaryNodes rootHere excludeIndex
          (candidate :: (frontRest ++ legLeft :: legRight :: tail))
        = findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: (frontRest ++ tail))
      rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
          (frontRest ++ legLeft :: legRight :: tail),
        findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate (frontRest ++ tail)]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => rfl
      | false =>
          show findPartnerScan links boundaryNodes rootHere excludeIndex
              (frontRest ++ legLeft :: legRight :: tail)
            = findPartnerScan links boundaryNodes rootHere excludeIndex (frontRest ++ tail)
          exact findPartnerScan_dropFailingPair links boundaryNodes rootHere excludeIndex
            legLeft legRight leftFails rightFails frontRest tail

/-- ★ **THE CORE — a top-of-stack cup shifts each OLD port's partner, undisturbed.**  A cup fired LAST onto an
arbitrary incoming `state` (carrying freshness + the union-find forest invariant) allocates a fresh, ISOLATED
3-node component and splices its two legs into the open-wire list at `windowPosition` — so it leaves every OLD
port's connected component untouched.  In the boundary index space `List.range seedBoundary ++ openWires`, the
two fresh legs land at raw indices `seedBoundary + windowPosition` and `seedBoundary + windowPosition + 1`, and
every old raw index `oldPort < seedBoundary + openWires.length` is pushed up by two exactly when it is at or
beyond the insertion window (`freshShiftAbove (seedBoundary + windowPosition) 2`).

`partnerIndexOf` under the stepped state therefore reads the SHIFTED image of what it read under `state`: the
scan over `List.range steppedTotal` decomposes (`rangeInterleaveAtWindow`) into the below-window prefix, the two
inserted fresh-leg slots, and the past-window tail two higher; the two leg candidates are SKIPPED
(`findPartnerScan_dropFailingPair`), because their boundary node is a fresh leg whose stepped root
(`stepCupArc_freshComponentRoot`, `= nextFresh + 1`) is not the old exclude's root (below `nextFresh`); and every
surviving candidate reads the SAME old boundary node at the shifted position (`natListInsertAt` past-block
reindex) with the SAME component root (`unionFindRootOf_stepCupArc_old`), so the mapped scan is the shift of the
base scan (`findPartnerScan_mapCongr` fed the per-candidate test correspondence). -/
theorem partnerIndexOf_stepCupArc_old (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length)
    (oldPort : Nat) (oldPortInRange : oldPort < seedBoundary + state.openWires.length) :
    partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length)
        (freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      = freshShiftAbove (seedBoundary + windowPosition) 2
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length) oldPort) := by
  -- bridge the stepped fields to their splice / join forms
  have hStepOpen : (stepCupArc state windowPosition).openWires
      = natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1] := rfl
  have hStepLen : (stepCupArc state windowPosition).openWires.length = state.openWires.length + 2 := by
    rw [hStepOpen]
    exact natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  rw [hStepLen, hStepOpen]
  -- window split of the base total
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowFits
  have baseTotalEq : seedBoundary + state.openWires.length
      = (seedBoundary + windowPosition) + tailCount := by
    rw [← tailSpec]; exact (Nat.add_assoc seedBoundary windowPosition tailCount).symm
  have steppedTotalEq : seedBoundary + (state.openWires.length + 2)
      = (seedBoundary + windowPosition) + 2 + tailCount := by
    rw [← Nat.add_assoc seedBoundary state.openWires.length 2, baseTotalEq,
      Nat.add_right_comm (seedBoundary + windowPosition) tailCount 2]
  -- every old boundary read lies below `nextFresh` (old wires are fresh; range ids are below the seed bound)
  have readBelowFresh : ∀ c, c < seedBoundary + state.openWires.length →
      natListGetAt (List.range seedBoundary ++ state.openWires) c < state.nextFresh := by
    intro c cInRange
    cases Nat.lt_or_ge c seedBoundary with
    | inl cBelow =>
        rw [natListGetAt_append_inside (List.range seedBoundary) state.openWires c
            (by rw [rangeLength]; exact cBelow),
          rangeGetAt_below seedBoundary c cBelow]
        exact Nat.lt_of_lt_of_le cBelow seedBelowFresh
    | inr cAtLeast =>
        obtain ⟨k, hk⟩ := Nat.le.dest cAtLeast
        have kInRange : k < state.openWires.length := by
          have hlt : seedBoundary + k < seedBoundary + state.openWires.length := by rw [hk]; exact cInRange
          exact Nat.lt_of_add_lt_add_left hlt
        have readEq : natListGetAt (List.range seedBoundary ++ state.openWires) c
            = natListGetAt state.openWires k := by
          have hIdx : c = k + (List.range seedBoundary).length := by
            rw [rangeLength, ← hk, Nat.add_comm seedBoundary k]
          rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires k]
        rw [readEq]
        exact natListGetAt_lt_ofInRange state.nextFresh state.openWires k kInRange fresh.1
  -- the shifted read into the stepped boundary is the same old node the base boundary read
  have steppedRead : ∀ c, c < seedBoundary + state.openWires.length →
      natListGetAt (List.range seedBoundary
          ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
          (freshShiftAbove (seedBoundary + windowPosition) 2 c)
        = natListGetAt (List.range seedBoundary ++ state.openWires) c := by
    intro c cInRange
    cases Nat.lt_or_ge c (seedBoundary + windowPosition) with
    | inl cBelowThreshold =>
        rw [freshShiftAbove_ofNotLe (seedBoundary + windowPosition) 2 c (Nat.not_le_of_gt cBelowThreshold)]
        cases Nat.lt_or_ge c seedBoundary with
        | inl cBelowSeed =>
            rw [natListGetAt_append_inside (List.range seedBoundary)
                (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) c
                (by rw [rangeLength]; exact cBelowSeed),
              natListGetAt_append_inside (List.range seedBoundary) state.openWires c
                (by rw [rangeLength]; exact cBelowSeed)]
        | inr cAtLeastSeed =>
            obtain ⟨j, hj⟩ := Nat.le.dest cAtLeastSeed
            have jBelowWindow : j < windowPosition := by
              have hlt : seedBoundary + j < seedBoundary + windowPosition := by rw [hj]; exact cBelowThreshold
              exact Nat.lt_of_add_lt_add_left hlt
            have jInOpen : j < state.openWires.length := Nat.lt_of_lt_of_le jBelowWindow windowFits
            have hIdxj : c = j + (List.range seedBoundary).length := by
              rw [rangeLength, ← hj, Nat.add_comm seedBoundary j]
            rw [hIdxj,
              natListGetAt_append_pastBlock (List.range seedBoundary)
                (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) j,
              natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires j,
              natListGetAt_natListInsertAt_below state.openWires windowPosition
                [state.nextFresh, state.nextFresh + 1] j jBelowWindow jInOpen]
    | inr cAtLeastThreshold =>
        rw [freshShiftAbove_ofLe (seedBoundary + windowPosition) 2 c cAtLeastThreshold]
        obtain ⟨t, ht⟩ := Nat.le.dest cAtLeastThreshold
        have baseRead : natListGetAt (List.range seedBoundary ++ state.openWires) c
            = natListGetAt state.openWires (windowPosition + t) := by
          have hIdx : c = (windowPosition + t) + (List.range seedBoundary).length := by
            rw [rangeLength, ← ht, Nat.add_comm (windowPosition + t) seedBoundary,
              Nat.add_assoc seedBoundary windowPosition t]
          rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires (windowPosition + t)]
        have steppedReadValue : natListGetAt (List.range seedBoundary
              ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) (c + 2)
            = natListGetAt state.openWires (windowPosition + t) := by
          have hIdx2 : c + 2 = (windowPosition + t + 2) + (List.range seedBoundary).length := by
            rw [rangeLength, ← ht, Nat.add_comm (windowPosition + t + 2) seedBoundary,
              Nat.add_assoc seedBoundary windowPosition t, Nat.add_assoc seedBoundary (windowPosition + t) 2]
          rw [hIdx2, natListGetAt_append_pastBlock (List.range seedBoundary)
            (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (windowPosition + t + 2)]
          exact natListGetAt_natListInsertAt_pastBlock state.openWires windowPosition
            [state.nextFresh, state.nextFresh + 1] t windowFits
        rw [baseRead, steppedReadValue]
  -- every old port keeps its component root through the top-of-stack cup
  have candidateRootEq : ∀ c, c < seedBoundary + state.openWires.length →
      unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (freshShiftAbove (seedBoundary + windowPosition) 2 c))
        = unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) c) := by
    intro c cInRange
    rw [steppedRead c cInRange]
    exact unionFindRootOf_stepCupArc_old state windowPosition fresh forest
      (natListGetAt (List.range seedBoundary ++ state.openWires) c)
      (unionFindRootOf_lt_of_fresh state.links state.nextFresh (fun edge he => (fresh.2.1 edge he).2)
        (natListGetAt (List.range seedBoundary ++ state.openWires) c) (readBelowFresh c cInRange))
  have oldRootBelow : unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort) < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh (fun edge he => (fresh.2.1 edge he).2)
      (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort) (readBelowFresh oldPort oldPortInRange)
  -- the two inserted leg slots read the two fresh legs
  have legLeftRead : natListGetAt (List.range seedBoundary
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
  have legRightRead : natListGetAt (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
        (seedBoundary + windowPosition + 1) = state.nextFresh + 1 := by
    have hIdx : seedBoundary + windowPosition + 1 = (windowPosition + 1) + (List.range seedBoundary).length := by
      rw [rangeLength, Nat.add_comm (windowPosition + 1) seedBoundary,
        Nat.add_assoc seedBoundary windowPosition 1]
    rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary)
      (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) (windowPosition + 1)]
    exact natListGetAt_natListInsertAt_inside state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) windowFits
  -- the two leg candidates fail the stepped scan test against the old exclude's root
  have legLeftFails : ((seedBoundary + windowPosition
        != freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      && unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (seedBoundary + windowPosition))
        == unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
      = false := by
    rw [legLeftRead, (stepCupArc_freshComponentRoot state windowPosition fresh forest).1,
      beq_false_of_lt (Nat.lt_succ_of_lt oldRootBelow)]
    exact Bool.and_false _
  have legRightFails : ((seedBoundary + windowPosition + 1
        != freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      && unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (seedBoundary + windowPosition + 1))
        == unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
      = false := by
    rw [legRightRead, (stepCupArc_freshComponentRoot state windowPosition fresh forest).2.1,
      beq_false_of_lt (Nat.lt_succ_of_lt oldRootBelow)]
    exact Bool.and_false _
  -- the interleaved range shape and the punctured shift image
  have rangeEq : List.range (seedBoundary + (state.openWires.length + 2))
      = List.range (seedBoundary + windowPosition)
          ++ (seedBoundary + windowPosition) :: (seedBoundary + windowPosition + 1)
              :: (List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset) := by
    rw [steppedTotalEq, rangeInterleaveAtWindow (seedBoundary + windowPosition) tailCount]
    exact appendAssoc (List.range (seedBoundary + windowPosition))
      [seedBoundary + windowPosition, seedBoundary + windowPosition + 1]
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset))
  have imageEq : List.range (seedBoundary + windowPosition)
        ++ (List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)
      = (List.range (seedBoundary + state.openWires.length)).map
          (freshShiftAbove (seedBoundary + windowPosition) 2) := by
    rw [baseTotalEq]
    exact (rangeMapShift_splitsAtWindow (seedBoundary + windowPosition) tailCount).symm
  -- the per-candidate test correspondence
  have testCorr : ∀ candidate, candidate ∈ List.range (seedBoundary + state.openWires.length) →
      (freshShiftAbove (seedBoundary + windowPosition) 2 candidate
          != freshShiftAbove (seedBoundary + windowPosition) 2 oldPort
        && unionFindRootOf (stepCupArc state windowPosition).links
            (natListGetAt (List.range seedBoundary
              ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
              (freshShiftAbove (seedBoundary + windowPosition) 2 candidate))
          == unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
        = (candidate != oldPort
            && unionFindRootOf state.links
                (natListGetAt (List.range seedBoundary ++ state.openWires) candidate)
              == unionFindRootOf state.links
                  (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort)) := by
    intro candidate candidateMem
    have candidateInRange : candidate < seedBoundary + state.openWires.length := mem_range_imp_lt candidateMem
    have bneEq : (freshShiftAbove (seedBoundary + windowPosition) 2 candidate
        != freshShiftAbove (seedBoundary + windowPosition) 2 oldPort) = (candidate != oldPort) := by
      show (!(freshShiftAbove (seedBoundary + windowPosition) 2 candidate
          == freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)) = (!(candidate == oldPort))
      rw [freshShiftAbove_beqCongr (seedBoundary + windowPosition) 2 candidate oldPort]
    rw [candidateRootEq candidate candidateInRange, bneEq]
  -- unfold to the scan form and assemble
  show findPartnerScan (stepCupArc state windowPosition).links
      (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (unionFindRootOf (stepCupArc state windowPosition).links
        (natListGetAt (List.range seedBoundary
          ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
          (freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)))
      (freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      (List.range (seedBoundary + (state.openWires.length + 2)))
    = freshShiftAbove (seedBoundary + windowPosition) 2
        (findPartnerScan state.links (List.range seedBoundary ++ state.openWires)
          (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
          oldPort (List.range (seedBoundary + state.openWires.length)))
  rw [candidateRootEq oldPort oldPortInRange, rangeEq,
    findPartnerScan_dropFailingPair (stepCupArc state windowPosition).links
      (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
      (freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      (seedBoundary + windowPosition) (seedBoundary + windowPosition + 1) legLeftFails legRightFails
      (List.range (seedBoundary + windowPosition))
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)),
    imageEq]
  exact findPartnerScan_mapCongr (stepCupArc state windowPosition).links state.links
    (List.range seedBoundary
      ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
    (List.range seedBoundary ++ state.openWires)
    (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
    (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
    oldPort (freshShiftAbove (seedBoundary + windowPosition) 2)
    (List.range (seedBoundary + state.openWires.length)) testCorr

end FX1Poly.Polygraph
