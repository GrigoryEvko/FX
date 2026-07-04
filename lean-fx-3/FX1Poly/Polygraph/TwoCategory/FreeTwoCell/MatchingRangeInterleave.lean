import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # MatchingRangeInterleave — the cap-window candidate interleave

The candidate-list decomposition feeding the cap-head partner-scan correspondence (peel
campaign H, rung E-3, part 2b).  The composite extract scans `List.range compositeTotal`
while the fresh extract scans `List.range freshTotal` with `compositeTotal = freshTotal + 2`
— the two extra candidates are the consumed window pair sitting at positions
`windowPosition` and `windowPosition + 1`.  Both range lists decompose around the window:
the composite range interleaves the window pair between the below-window candidates and the
shifted tail images, and the two-zone index shift's image of the fresh range is exactly the
same decomposition WITHOUT the pair.  A scan is blind to an all-failing middle segment, so
once the window pair's tests are shown false the two scans meet on the same candidate list.

Everything here is generic: plain ranges, an abstract two-zone index shift, and an abstract
exclude-and-root test — no fold state appears.  Core `List.append_assoc` / `List.append_nil`
/ `List.range_succ` leak `propext`, so the append and range-loop plumbing is hand-rolled.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private append and range-loop plumbing (core lemmas leak propext) -/

/-- Appending the empty list on the right is the identity (hand-rolled; core
`List.append_nil` leaks `propext`). -/
private theorem appendNil : (values : List Nat) → values ++ [] = values
  | [] => rfl
  | headValue :: restValues => congrArg (List.cons headValue) (appendNil restValues)

/-- Appending is associative (hand-rolled; core `List.append_assoc` leaks `propext`). -/
private theorem appendAssoc : (first second third : List Nat) →
    (first ++ second) ++ third = first ++ (second ++ third)
  | [], _, _ => rfl
  | headValue :: restValues, second, third =>
      congrArg (List.cons headValue) (appendAssoc restValues second third)

/-- The range loop's accumulator splits off as a right append (hand-rolled replacement for
core `List.range_loop` reasoning). -/
private theorem rangeLoopAppend : (count : Nat) → (accumulated : List Nat) →
    List.range.loop count accumulated = List.range.loop count [] ++ accumulated
  | 0, _ => rfl
  | count + 1, accumulated => by
      show List.range.loop count (count :: accumulated)
        = List.range.loop (count + 1) [] ++ accumulated
      rw [rangeLoopAppend count (count :: accumulated),
        show List.range.loop (count + 1) [] = List.range.loop count [] ++ [count] from
          rangeLoopAppend count [count]]
      exact (appendAssoc (List.range.loop count []) [count] accumulated).symm

/-- A successor range appends its top element (hand-rolled; core `List.range_succ` leaks
`propext`). -/
private theorem rangeSucc (count : Nat) :
    List.range (count + 1) = List.range count ++ [count] :=
  rangeLoopAppend count [count]

/-! ## The range split -/

/-- **A range splits at any base count**: the candidates past `baseCount` are the
`baseCount`-shifted image of a fresh range. -/
theorem rangeSplit : (baseCount extraCount : Nat) →
    List.range (baseCount + extraCount)
      = List.range baseCount
          ++ (List.range extraCount).map (fun offset => baseCount + offset)
  | baseCount, 0 => (appendNil (List.range baseCount)).symm
  | baseCount, extraCount + 1 => by
      show List.range ((baseCount + extraCount) + 1)
        = List.range baseCount
            ++ (List.range (extraCount + 1)).map (fun offset => baseCount + offset)
      rw [rangeSucc (baseCount + extraCount), rangeSplit baseCount extraCount,
        rangeSucc extraCount,
        mapAppend (fun offset => baseCount + offset) (List.range extraCount) [extraCount]]
      exact appendAssoc (List.range baseCount)
        ((List.range extraCount).map (fun offset => baseCount + offset))
        [baseCount + extraCount]

/-! ## Scans are blind to failing segments -/

/-- **A scan over all-failing candidates returns the exclude sentinel.** -/
theorem findPartnerScan_eqExclude_ofAllFail (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates →
      (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere)
        = false) →
    findPartnerScan links boundaryNodes rootHere excludeIndex candidates = excludeIndex
  | [], _ => rfl
  | candidate :: restCandidates, allFail => by
      rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
        candidate restCandidates (allFail candidate (List.Mem.head restCandidates))]
      exact findPartnerScan_eqExclude_ofAllFail links boundaryNodes rootHere excludeIndex
        restCandidates
        (fun laterCandidate laterMem => allFail laterCandidate
          (List.Mem.tail candidate laterMem))

/-- **An all-failing middle segment drops out of a scan**: the first-hit discipline sails
through candidates whose tests are false, so the scan over `(front ++ middle) ++ back`
equals the scan over `front ++ back`. -/
theorem findPartnerScan_dropMiddle_ofAllFail (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (front middle back : List Nat) →
    (∀ candidate, candidate ∈ middle →
      (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere)
        = false) →
    findPartnerScan links boundaryNodes rootHere excludeIndex ((front ++ middle) ++ back)
      = findPartnerScan links boundaryNodes rootHere excludeIndex (front ++ back)
  | [], middle, back, middleFails => by
      show findPartnerScan links boundaryNodes rootHere excludeIndex (middle ++ back)
        = findPartnerScan links boundaryNodes rootHere excludeIndex back
      exact findPartnerScan_append_ofFrontFails links boundaryNodes rootHere excludeIndex
        middle back
        (findPartnerScan_eqExclude_ofAllFail links boundaryNodes rootHere excludeIndex
          middle middleFails)
  | candidate :: frontRest, middle, back, middleFails => by
      show findPartnerScan links boundaryNodes rootHere excludeIndex
          (candidate :: ((frontRest ++ middle) ++ back))
        = findPartnerScan links boundaryNodes rootHere excludeIndex
            (candidate :: (frontRest ++ back))
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true =>
          have leftFinds : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: ((frontRest ++ middle) ++ back)) = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
              ((frontRest ++ middle) ++ back), headTest]
            exact if_pos rfl
          have rightFinds : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: (frontRest ++ back)) = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
              (frontRest ++ back), headTest]
            exact if_pos rfl
          exact leftFinds.trans rightFinds.symm
      | false =>
          rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
            candidate ((frontRest ++ middle) ++ back) headTest,
            findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
            candidate (frontRest ++ back) headTest]
          exact findPartnerScan_dropMiddle_ofAllFail links boundaryNodes rootHere
            excludeIndex frontRest middle back middleFails

/-! ## The two window decompositions -/

/-- **The composite candidate range interleaves the window pair**: the composite extract's
candidates split into the below-window candidates, the two window candidates themselves,
and the tail images shifted past the consumed pair. -/
theorem rangeInterleaveAtWindow (windowPosition tailCount : Nat) :
    List.range ((windowPosition + 2) + tailCount)
      = (List.range windowPosition ++ [windowPosition, windowPosition + 1])
          ++ (List.range tailCount).map (fun offset => (windowPosition + 2) + offset) := by
  have windowPairSplit : List.range (windowPosition + 2)
      = List.range windowPosition ++ [windowPosition, windowPosition + 1] :=
    rangeLoopAppend windowPosition [windowPosition, windowPosition + 1]
  rw [rangeSplit (windowPosition + 2) tailCount, windowPairSplit]

/-- A tail of window-based offsets lands past the window under the two-zone index shift
(the pointwise leg of `rangeShiftImageAtWindow`). -/
private theorem mapShiftPastWindow (indexShift : Nat → Nat) (windowPosition : Nat)
    (shiftsPastWindow : ∀ index, windowPosition ≤ index → indexShift index = index + 2) :
    (offsets : List Nat) →
    ((offsets.map (fun offset => windowPosition + offset)).map indexShift)
      = offsets.map (fun offset => (windowPosition + 2) + offset)
  | [] => rfl
  | offsetHead :: offsetRest => by
      show indexShift (windowPosition + offsetHead)
          :: ((offsetRest.map (fun offset => windowPosition + offset)).map indexShift)
        = ((windowPosition + 2) + offsetHead)
            :: offsetRest.map (fun offset => (windowPosition + 2) + offset)
      rw [shiftsPastWindow (windowPosition + offsetHead)
          (Nat.le_add_right windowPosition offsetHead),
        Nat.add_right_comm windowPosition offsetHead 2,
        mapShiftPastWindow indexShift windowPosition shiftsPastWindow offsetRest]

/-- **The two-zone index shift's image of the fresh candidate range**: below the window the
shift is the identity, past it every candidate moves up by the consumed pair — the image is
exactly the interleaved composite range WITHOUT the window pair. -/
theorem rangeShiftImageAtWindow (indexShift : Nat → Nat)
    (windowPosition tailCount : Nat)
    (fixesBelowWindow : ∀ index, index < windowPosition → indexShift index = index)
    (shiftsPastWindow : ∀ index, windowPosition ≤ index → indexShift index = index + 2) :
    (List.range (windowPosition + tailCount)).map indexShift
      = List.range windowPosition
          ++ (List.range tailCount).map (fun offset => (windowPosition + 2) + offset) := by
  rw [rangeSplit windowPosition tailCount,
    mapAppend indexShift (List.range windowPosition)
      ((List.range tailCount).map (fun offset => windowPosition + offset)),
    mapFixedOn indexShift (List.range windowPosition)
      (fun index indexMem => fixesBelowWindow index (mem_range_imp_lt indexMem)),
    mapShiftPastWindow indexShift windowPosition shiftsPastWindow (List.range tailCount)]

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-window candidate interleave (peel campaign H, rung E-3,
part 2b).**  The generic range split, the all-failing-segment scan lemmas (a scan returns
the exclude sentinel over all-failing candidates, and an all-failing middle segment drops
out of an appended scan), and the two window decompositions: the composite candidate range
interleaves the window pair between the below-window candidates and the shifted tail
images, and the two-zone index shift's image of the fresh range is the same decomposition
without the pair.  What this marker does NOT claim: the window pair's tests actually FAIL
at the folded composite state (SC-3's off-strand misses instantiated at the scan test), the
per-candidate test correspondence at the folded states, and the assembled
diagram/partner leg.  `= true`. -/
def fxMode_hasCapWindowCandidateInterleave : Bool := true

end FX1Poly.Polygraph
