import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDropCore

/-! # MatchingStepCupOldPartner — a top-of-stack cup shifts the OLD ports' matching, undisturbed
(Track B route 1, brick 3 census core)

The arc-carrier census `partnerIndexOf_stepCupArc_old` reads the old-port partner shift off the ARC step
`stepCupArc`, whose fresh cup component is a THREE-node block (`nextFresh, nextFresh+1, nextFresh+2` with an
internal cup-EVENT node), so its old-root preservation folds through TWO nested `unionFindJoin`s.  The width-`0`
pure-cup determinacy consumer runs the sort on the plain `matchingOfSpineList 0` carrier, whose step `stepCup`
allocates only a TWO-node fresh cup component (`nextFresh, nextFresh+1` — no event node), joining them in a SINGLE
`unionFindJoin`.

This file PORTS the old-port census to the plain `stepCup` carrier positivity-free:

  * ★ `stepCup_freshComponentRoot` — the plain 2-node fresh cup component roots to `nextFresh + 1`: both legs
    `nextFresh`, `nextFresh + 1` share the single component root of `stepCup`'s one `unionFindJoin`.  The plain
    analogue of `stepCupArc_freshComponentRoot`, with the third event leg dropped.
  * ★ `unionFindRootOf_stepCup_old` — an OLD node (base root `< nextFresh`) keeps its component root through the
    single cup join; the plain analogue of `unionFindRootOf_stepCupArc_old`, one join instead of two.
  * ★ `partnerIndexOf_stepCup_old` — THE CORE: `partnerIndexOf` under the stepped state reads the SHIFTED image of
    what it read under `state` for every old port.  The scan over `List.range steppedTotal` decomposes into the
    below-window prefix, the two inserted fresh-leg slots (SKIPPED — their root `nextFresh + 1` is not the old
    exclude's root), and the past-window tail two higher.  The plain analogue of `partnerIndexOf_stepCupArc_old`.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The plain 2-node fresh cup component roots to `nextFresh + 1` -/

/-- ★ **The plain fresh cup component roots to `nextFresh + 1`.**  `stepCup` builds
`links := unionFindJoin state.links nextFresh (nextFresh+1)`.  In a fresh forest both legs are parentless in the
base links, so the single join sends `nextFresh` onto `nextFresh+1`'s root `nextFresh+1`, and `nextFresh+1` stays
its own root — so both fresh legs share the single component root `nextFresh + 1`, at or above `nextFresh` and
hence never the root of an old port. -/
theorem stepCup_freshComponentRoot (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links) :
    unionFindRootOf (stepCup state position).links state.nextFresh = state.nextFresh + 1
      ∧ unionFindRootOf (stepCup state position).links (state.nextFresh + 1) = state.nextFresh + 1 := by
  obtain ⟨_, linkBelow⟩ := fresh
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeMem => (linkBelow edge edgeMem).1
  have rootLegLeft : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_eq_self_ofFresh state.nextFresh state.links childrenBelow state.nextFresh
      (Nat.le_refl state.nextFresh)
  have rootLegRight : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_eq_self_ofFresh state.nextFresh state.links childrenBelow (state.nextFresh + 1)
      (Nat.le_succ state.nextFresh)
  refine ⟨?_, ?_⟩
  · show unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      state.nextFresh = state.nextFresh + 1
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      state.nextFresh forest, rootLegLeft]
    have selfBeq : (state.nextFresh == state.nextFresh) = true := decide_eq_true rfl
    rw [selfBeq]; exact rootLegRight
  · show unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 1) = state.nextFresh + 1
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 1) forest, rootLegLeft, rootLegRight]
    split <;> rfl

/-! ## An old node keeps its component root through the plain cup join -/

/-- ★ **A plain top-of-stack cup leaves every OLD node's root unchanged.**  For a node `y` whose base root lies
below `nextFresh`, the single cup join `unionFindJoin state.links nextFresh (nextFresh+1)` cannot redirect it: the
join only redirects nodes whose root is `nextFresh` (`nextFresh`'s root), and `y`'s root is strictly below
`nextFresh`.  The plain analogue of `unionFindRootOf_stepCupArc_old`, one join instead of two. -/
theorem unionFindRootOf_stepCup_old (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links) (y : Nat)
    (hrooty : unionFindRootOf state.links y < state.nextFresh) :
    unionFindRootOf (stepCup state position).links y = unionFindRootOf state.links y := by
  obtain ⟨_, linkBelow⟩ := fresh
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeMem => (linkBelow edge edgeMem).1
  have rootLegLeft : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_eq_self_ofFresh state.nextFresh state.links childrenBelow state.nextFresh
      (Nat.le_refl state.nextFresh)
  show unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) y
    = unionFindRootOf state.links y
  rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) y forest, rootLegLeft]
  cases hc : state.nextFresh == unionFindRootOf state.links y with
  | true => exact absurd (of_decide_eq_true hc).symm (Nat.ne_of_lt hrooty)
  | false => rfl

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

private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-- Dropping two consecutive FAILING candidates anywhere in the scanned list preserves the scan — the
punctured-scan atom (a per-file copy of the sibling in `ArcCupStepDropCore`). -/
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

/-! ## THE CORE — a plain top-of-stack cup shifts each OLD port's partner, undisturbed -/

/-- ★ **THE CORE (plain carrier) — a top-of-stack cup shifts each OLD port's partner, undisturbed.**  A cup fired
LAST onto an arbitrary incoming `state` (carrying freshness + the union-find forest invariant) allocates a fresh,
ISOLATED 2-node component and splices its two legs into the open-wire list at `windowPosition` — leaving every OLD
port's connected component untouched.  In the boundary index space `List.range seedBoundary ++ openWires`, the two
fresh legs land at raw indices `seedBoundary + windowPosition` and `+ 1`, and every old raw index is pushed up by
two exactly when at or beyond the insertion window (`freshShiftAbove (seedBoundary + windowPosition) 2`).

`partnerIndexOf` under the stepped state reads the SHIFTED image of what it read under `state`: the scan over
`List.range steppedTotal` decomposes (`rangeInterleaveAtWindow`) into the below-window prefix, the two inserted
fresh-leg slots (SKIPPED via `findPartnerScan_dropFailingPair`, because their stepped root `nextFresh + 1`
—`stepCup_freshComponentRoot`— is not the old exclude's root, below `nextFresh`), and the past-window tail two
higher; every surviving candidate reads the SAME old boundary node at the shifted position with the SAME component
root (`unionFindRootOf_stepCup_old`), so the mapped scan is the shift of the base scan (`findPartnerScan_mapCongr`).
The plain analogue of `partnerIndexOf_stepCupArc_old`. -/
theorem partnerIndexOf_stepCup_old (seedBoundary : Nat) (state : WireState) (windowPosition : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length)
    (oldPort : Nat) (oldPortInRange : oldPort < seedBoundary + state.openWires.length) :
    partnerIndexOf (stepCup state windowPosition).links
        (List.range seedBoundary ++ (stepCup state windowPosition).openWires)
        (seedBoundary + (stepCup state windowPosition).openWires.length)
        (freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      = freshShiftAbove (seedBoundary + windowPosition) 2
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length) oldPort) := by
  obtain ⟨openBelow, linkBelow⟩ := fresh
  have freshWS : WireStateFresh state := ⟨openBelow, linkBelow⟩
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeMem => (linkBelow edge edgeMem).2
  -- bridge the stepped fields to their splice / join forms
  have hStepOpen : (stepCup state windowPosition).openWires
      = natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1] := rfl
  have hStepLen : (stepCup state windowPosition).openWires.length = state.openWires.length + 2 := by
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
  -- every old boundary read lies below `nextFresh`
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
        exact natListGetAt_lt_ofInRange state.nextFresh state.openWires k kInRange openBelow
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
      unionFindRootOf (stepCup state windowPosition).links
          (natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (freshShiftAbove (seedBoundary + windowPosition) 2 c))
        = unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) c) := by
    intro c cInRange
    rw [steppedRead c cInRange]
    exact unionFindRootOf_stepCup_old state windowPosition freshWS forest
      (natListGetAt (List.range seedBoundary ++ state.openWires) c)
      (unionFindRootOf_lt state.nextFresh state.links parentsBelow
        (natListGetAt (List.range seedBoundary ++ state.openWires) c) (readBelowFresh c cInRange))
  have oldRootBelow : unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort) < state.nextFresh :=
    unionFindRootOf_lt state.nextFresh state.links parentsBelow
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
      && unionFindRootOf (stepCup state windowPosition).links
          (natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (seedBoundary + windowPosition))
        == unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
      = false := by
    rw [legLeftRead, (stepCup_freshComponentRoot state windowPosition freshWS forest).1,
      beq_false_of_lt (Nat.lt_succ_of_lt oldRootBelow)]
    exact Bool.and_false _
  have legRightFails : ((seedBoundary + windowPosition + 1
        != freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      && unionFindRootOf (stepCup state windowPosition).links
          (natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
            (seedBoundary + windowPosition + 1))
        == unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
      = false := by
    rw [legRightRead, (stepCup_freshComponentRoot state windowPosition freshWS forest).2,
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
        && unionFindRootOf (stepCup state windowPosition).links
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
  show findPartnerScan (stepCup state windowPosition).links
      (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (unionFindRootOf (stepCup state windowPosition).links
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
    findPartnerScan_dropFailingPair (stepCup state windowPosition).links
      (List.range seedBoundary
        ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
      (freshShiftAbove (seedBoundary + windowPosition) 2 oldPort)
      (seedBoundary + windowPosition) (seedBoundary + windowPosition + 1) legLeftFails legRightFails
      (List.range (seedBoundary + windowPosition))
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)),
    imageEq]
  exact findPartnerScan_mapCongr (stepCup state windowPosition).links state.links
    (List.range seedBoundary
      ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
    (List.range seedBoundary ++ state.openWires)
    (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
    (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) oldPort))
    oldPort (freshShiftAbove (seedBoundary + windowPosition) 2)
    (List.range (seedBoundary + state.openWires.length)) testCorr

end FX1Poly.Polygraph
