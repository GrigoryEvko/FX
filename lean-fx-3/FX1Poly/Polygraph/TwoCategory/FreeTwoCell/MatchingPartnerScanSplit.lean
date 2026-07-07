import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan

/-! # MatchingPartnerScanSplit — skipping, splitting, and mapping the partner scan

The partner-scan structure kit (peel campaign H, rung E-3, part 2a).  The extract's partner
scan walks a candidate list in order and returns the FIRST candidate passing the
exclude-and-root test.  Three structural facts drive the cap-head diagram leg: a failing
head candidate is SKIPPED (the scan continues as if it were absent), an appended scan
splits by whether the front finds a partner (first-hit discipline across segment
boundaries), and a scan over a MAPPED candidate list corresponds pointwise to the base scan
whenever every candidate's whole test corresponds — the composite scan then equals the
index-shifted fresh scan once the two extra window candidates are skipped as always-failing
and the remaining segments are shift-images.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private Bool plumbing (per-file copy, following the codebase pattern) -/

/-- A true bang-inequality is a real inequality (hand-rolled; the bne unfolds under `show`). -/
private theorem neOfBneTrue (leftValue rightValue : Nat)
    (bneTrue : (leftValue != rightValue) = true) : leftValue ≠ rightValue := by
  cases beqValue : (leftValue == rightValue) with
  | true =>
      have bneFalse : (leftValue != rightValue) = false := by
        show (!(leftValue == rightValue)) = false
        rw [beqValue]
        rfl
      exact Bool.noConfusion (bneFalse.symm.trans bneTrue)
  | false => exact of_decide_eq_false beqValue

/-! ## Skipping a failing head candidate -/

/-- **A failing head candidate is skipped**: when the head's exclude-and-root test is
false, the scan continues on the tail unchanged. -/
theorem findPartnerScan_cons_ofTestFails (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex candidate : Nat) (rest : List Nat)
    (testFails : (candidate != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere)
      = false) :
    findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: rest)
      = findPartnerScan links boundaryNodes rootHere excludeIndex rest := by
  rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate rest,
    testFails]
  exact if_neg (fun falseEqTrue => Bool.noConfusion falseEqTrue)

/-! ## Splitting an appended scan at the segment boundary -/

/-- **An appended scan whose front fails through continues on the back**: when the front
segment finds no partner (the scan returns the exclude sentinel), the appended scan is the
back segment's scan. -/
theorem findPartnerScan_append_ofFrontFails (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (front back : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex front = excludeIndex →
    findPartnerScan links boundaryNodes rootHere excludeIndex (front ++ back)
      = findPartnerScan links boundaryNodes rootHere excludeIndex back
  | [], _, _ => rfl
  | candidate :: frontRest, back, frontFails => by
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true =>
          have scanFrontEq : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: frontRest) = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
              frontRest, headTest]
            exact if_pos rfl
          have candidateIsExclude : candidate = excludeIndex :=
            scanFrontEq.symm.trans frontFails
          have bneTrue : (candidate != excludeIndex) = true := by
            cases bneValue : (candidate != excludeIndex) with
            | true => rfl
            | false =>
                rw [bneValue] at headTest
                exact Bool.noConfusion headTest
          exact absurd candidateIsExclude (neOfBneTrue candidate excludeIndex bneTrue)
      | false =>
          have skipFront : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: frontRest)
            = findPartnerScan links boundaryNodes rootHere excludeIndex frontRest :=
            findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
              candidate frontRest headTest
          show findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: (frontRest ++ back))
            = findPartnerScan links boundaryNodes rootHere excludeIndex back
          rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
            candidate (frontRest ++ back) headTest]
          exact findPartnerScan_append_ofFrontFails links boundaryNodes rootHere
            excludeIndex frontRest back (skipFront.symm.trans frontFails)

/-- **An appended scan whose front finds a partner IS the front scan**: the first-hit
discipline never reaches the back segment. -/
theorem findPartnerScan_append_ofFoundInFront (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (front back : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex front ≠ excludeIndex →
    findPartnerScan links boundaryNodes rootHere excludeIndex (front ++ back)
      = findPartnerScan links boundaryNodes rootHere excludeIndex front
  | [], _, foundInFront => absurd rfl foundInFront
  | candidate :: frontRest, back, foundInFront => by
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true =>
          have appendScan : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: (frontRest ++ back)) = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
              (frontRest ++ back), headTest]
            exact if_pos rfl
          have frontScan : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: frontRest) = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
              frontRest, headTest]
            exact if_pos rfl
          exact appendScan.trans frontScan.symm
      | false =>
          have skipFront : findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: frontRest)
            = findPartnerScan links boundaryNodes rootHere excludeIndex frontRest :=
            findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
              candidate frontRest headTest
          show findPartnerScan links boundaryNodes rootHere excludeIndex
              (candidate :: (frontRest ++ back))
            = findPartnerScan links boundaryNodes rootHere excludeIndex
                (candidate :: frontRest)
          rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
            candidate (frontRest ++ back) headTest, skipFront]
          exact findPartnerScan_append_ofFoundInFront links boundaryNodes rootHere
            excludeIndex frontRest back
            (fun scanRestIsExclude => foundInFront (skipFront.trans scanRestIsExclude))

/-! ## The mapped-scan congruence -/

/-- ★ **A scan over a mapped candidate list corresponds pointwise to the base scan**: when
every candidate's WHOLE test (exclude bang-inequality and root query, at the shifted index
against the shifted exclude) equals the base test, the mapped scan returns the shifted base
result — first hits correspond position by position. -/
theorem findPartnerScan_mapCongr (compositeLinks freshLinks : List (Nat × Nat))
    (compositeBoundary freshBoundary : List Nat)
    (compositeRoot freshRoot freshExclude : Nat) (indexShift : Nat → Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates →
      (indexShift candidate != indexShift freshExclude
          && unionFindRootOf compositeLinks
              (natListGetAt compositeBoundary (indexShift candidate)) == compositeRoot)
        = (candidate != freshExclude
            && unionFindRootOf freshLinks (natListGetAt freshBoundary candidate)
              == freshRoot)) →
    findPartnerScan compositeLinks compositeBoundary compositeRoot
        (indexShift freshExclude) (candidates.map indexShift)
      = indexShift
        (findPartnerScan freshLinks freshBoundary freshRoot freshExclude candidates)
  | [], _ => rfl
  | candidate :: rest, testCorr => by
      show findPartnerScan compositeLinks compositeBoundary compositeRoot
          (indexShift freshExclude) (indexShift candidate :: rest.map indexShift)
        = indexShift
          (findPartnerScan freshLinks freshBoundary freshRoot freshExclude
            (candidate :: rest))
      rw [findPartnerScan_cons compositeLinks compositeBoundary compositeRoot
          (indexShift freshExclude) (indexShift candidate) (rest.map indexShift),
        findPartnerScan_cons freshLinks freshBoundary freshRoot freshExclude candidate
          rest,
        testCorr candidate (List.Mem.head rest)]
      cases freshTest : (candidate != freshExclude
          && unionFindRootOf freshLinks (natListGetAt freshBoundary candidate)
            == freshRoot) with
      | true => rfl
      | false =>
          exact findPartnerScan_mapCongr compositeLinks freshLinks compositeBoundary
            freshBoundary compositeRoot freshRoot freshExclude indexShift rest
            (fun laterCandidate laterMem =>
              testCorr laterCandidate (List.Mem.tail candidate laterMem))

/-! ## Two-run agreement over a shared candidate list -/

/-- ★ **Two partner scans with pointwise-agreeing whole tests agree.**  Two processing runs (possibly
different links / boundary-node lists / scanned roots, but the SAME exclude sentinel) whose exclude-and-root
whole test agrees at every candidate in the list return the same partner index — first hits coincide position
by position.  This is the scan-level core of the BOTTOM-PREFIX AGREEMENT between a cap block run alone and the
same cap block run as the bottom half of a whole valley: over the shared bottom-port candidates
`List.range bottomCount` the two runs' component tests agree (the cup block preserves bottom-bottom
connectivity), so the two runs' partner scans over the bottom prefix agree. -/
theorem findPartnerScan_congr_ofTestAgree
    (linksFirst linksSecond : List (Nat × Nat)) (boundaryFirst boundarySecond : List Nat)
    (rootFirst rootSecond excludeIndex : Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates →
      (candidate != excludeIndex
          && unionFindRootOf linksFirst (natListGetAt boundaryFirst candidate) == rootFirst)
        = (candidate != excludeIndex
            && unionFindRootOf linksSecond (natListGetAt boundarySecond candidate) == rootSecond)) →
    findPartnerScan linksFirst boundaryFirst rootFirst excludeIndex candidates
      = findPartnerScan linksSecond boundarySecond rootSecond excludeIndex candidates
  | [], _ => rfl
  | candidate :: rest, testAgree => by
      rw [findPartnerScan_cons linksFirst boundaryFirst rootFirst excludeIndex candidate rest,
        findPartnerScan_cons linksSecond boundarySecond rootSecond excludeIndex candidate rest,
        testAgree candidate (List.Mem.head rest)]
      cases secondTest : (candidate != excludeIndex
          && unionFindRootOf linksSecond (natListGetAt boundarySecond candidate) == rootSecond) with
      | true => rfl
      | false =>
          exact findPartnerScan_congr_ofTestAgree linksFirst linksSecond boundaryFirst boundarySecond
            rootFirst rootSecond excludeIndex rest
            (fun laterCandidate laterMem => testAgree laterCandidate (List.Mem.tail candidate laterMem))

/-! ## Honesty marker -/

/-- **Honesty marker — the partner-scan structure kit (peel campaign H, rung E-3,
part 2a).**  Skipping a failing head candidate, splitting an appended scan at the segment
boundary by whether the front finds a partner, the mapped-scan pointwise congruence
(first hits correspond under a whole-test correspondence), and the two-run agreement over a
shared candidate list (pointwise-agreeing tests give agreeing scans — the bottom-prefix
agreement's scan-level core).  What this marker does NOT
claim: the range-segment interleaving decomposition at the cap head (composite candidates
= below-window shift-images, the two always-failing window candidates, then at-or-past
shift-images), the per-candidate test correspondence at the folded states, and the
assembled diagram/partner leg.  `= true`. -/
def fxMode_hasPartnerScanSplitKit : Bool := true

end FX1Poly.Polygraph
