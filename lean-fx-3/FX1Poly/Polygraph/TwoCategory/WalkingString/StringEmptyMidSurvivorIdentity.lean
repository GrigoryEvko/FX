import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # WalkingString/StringEmptyMidSurvivorIdentity — the empty-mid matching survivor-identity base floor
(FC-3 r44, P2c honest partial: the ONE genuinely-new positive-mid LOCATE invariant)

The positive-mid pure-cup LOCATE (the derivation of the brick `StringPositiveMidPureCupDeterminacy`,
`StringPositiveMidCupSortResidual`) is — per the r44 recon adjudication — MECHANICAL modulo exactly ONE
genuinely-new invariant, confined to the LOCATE BASE FLOOR: the empty pure-cup spine over a positive mid-
width bottom boundary has the SURVIVOR-IDENTITY matching.  Every OTHER positive-mid LOCATE ingredient (the
chord-shift descents, the drop-injectivity, the fueled locate/sort assembly) is a pure seed-offset token-
swap riding the SHIPPED seed-general engines (`generalStateCupForwardPartnerMatching midWidth` — landed in
r44 P2b via `stringMatchingLastCup_isShortChord_mid`; `diagramPartner_stepCup midWidth`;
`stringExtractDiagram_stepCup_congr` at a variable seed) plus the r43 P2a snake exclusion.

This file ships that ONE invariant — the honest partial.  `matchingOfSpineList midWidth []` is
`extractDiagram midWidth ⟨List.range midWidth, [], midWidth, 0⟩` (the empty spine leaves the seed
untouched): the fold never runs, links stay empty, and the boundary is `List.range midWidth ++ List.range
midWidth`.  So every TOP survivor port `midWidth + w` (`w < midWidth`) partners the BOTTOM port `w` (its own
copy in the lower range block) — it points strictly BELOW `midWidth`, never forward.  This is the DUAL of
the shipped ARC-carrier `initialPartner_bottomPort_ge` (`StringArcCapInternalCountsPointwise`): the matching-
carrier `extractDiagram` reduces its `.partner` field to the IDENTICAL `partnerIndexOf [] (range ++ range)`
form as `extractArc`'s `.diagram.partner`, so the proof is the byte-for-byte port of the arc's
`initialPartner_topPort_lt` (`WalkingAdjunction/ArcCupInternalCountsPointwise`).

The `emptyMidMatching_noForwardChord` corollary discharges the LOCATE base case: the empty-mid matching has
NO forward chord `(midWidth + w, midWidth + w + 1)` on the survivor region (the survivor points down, below
`midWidth`, never to `midWidth + w + 1`).  So the fueled locate terminates honestly at the empty spine.

Signature-generic (the empty-spine matching reads no 2-cell), fired at the adjoint-triple string signature.

Raw Lean 4 + Init; the private `List.range` / double-range / scan-bound plumbing is a per-file copy (the
codebase pattern).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin, `#print axioms` in the independent witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private `List.range` read-off plumbing (per-file copies, following the codebase pattern) -/

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

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below => natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

/-- Reading `List.range midWidth ++ List.range midWidth` below `midWidth` returns the index. -/
private theorem doubleRangeGet_below {midWidth index : Nat} (indexBelow : index < midWidth) :
    natListGetAt (List.range midWidth ++ List.range midWidth) index = index := by
  have lenEq : (List.range midWidth).length = midWidth := rangeLength midWidth
  rw [natListGetAt_append_inside (List.range midWidth) (List.range midWidth) index
      (by rw [lenEq]; exact indexBelow),
    rangeGetAt_below midWidth index indexBelow]

/-- Reading `List.range midWidth ++ List.range midWidth` at `midWidth + rest` (`rest` below `midWidth`)
returns `rest`. -/
private theorem doubleRangeGet_above {midWidth rest : Nat} (restBelow : rest < midWidth) :
    natListGetAt (List.range midWidth ++ List.range midWidth) (midWidth + rest) = rest := by
  have lenEq : (List.range midWidth).length = midWidth := rangeLength midWidth
  have idxEq : midWidth + rest = rest + (List.range midWidth).length := by
    rw [lenEq, Nat.add_comm rest midWidth]
  rw [idxEq, natListGetAt_append_pastBlock (List.range midWidth) (List.range midWidth) rest,
    rangeGetAt_below midWidth rest restBelow]

/-- A `findPartnerScan` result is below any bound dominating the exclude and every scanned candidate: the
scan returns a scanned candidate or the exclude, and both are below the bound. -/
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

/-! ## The base-floor invariant: the empty-mid matching sends every survivor top port BELOW `midWidth` -/

/-- ★ **The empty pure-cup spine's matching is the survivor identity (top ports point down).**  For
`midWidth ≤ topIndex < midWidth + midWidth`, the empty-mid matching partners `topIndex` with an index
strictly BELOW `midWidth`: the top survivor `topIndex` reads node `topIndex − midWidth` off the second
range block, whose empty-links root is `topIndex − midWidth`, and the scan finds that node's copy in the
FIRST (bottom) range block, which is `< midWidth`.

Matching-carrier port of the ARC-carrier `initialPartner_topPort_lt`
(`WalkingAdjunction/ArcCupInternalCountsPointwise`): `extractDiagram midWidth ⟨List.range midWidth, [],
midWidth, 0⟩` reduces its `.partner` field to the IDENTICAL `partnerIndexOf [] (List.range midWidth ++
List.range midWidth) …`-over-range form as `extractArc`'s `.diagram.partner`, so the scan soundness /
completeness / bound argument is the same.  Signature-generic (the empty spine reads no 2-cell). -/
theorem emptyMidMatching_topPort_lt {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {midWidth topIndex : Nat}
    (topAtLeast : midWidth ≤ topIndex) (topBelow : topIndex < midWidth + midWidth) :
    natListGetAt (matchingOfSpineList midWidth
        ([] : List (SpineAtom signature sourceMode targetMode))).partner topIndex
      < midWidth := by
  have lenEq : (List.range midWidth).length = midWidth := rangeLength midWidth
  obtain ⟨bottomTarget, targetEq⟩ := Nat.le.dest topAtLeast
  have targetLt : bottomTarget < midWidth := by
    have step : midWidth + bottomTarget < midWidth + midWidth := by rw [targetEq]; exact topBelow
    exact Nat.lt_of_add_lt_add_left step
  have topTotal : topIndex < midWidth + (List.range midWidth).length := by rw [lenEq]; exact topBelow
  -- reduce the partner read to a `partnerIndexOf` over the double range (empty links, seed openWires)
  show natListGetAt ((List.range (midWidth + (List.range midWidth).length)).map
      (partnerIndexOf ([] : List (Nat × Nat)) (List.range midWidth ++ List.range midWidth)
        (midWidth + (List.range midWidth).length))) topIndex < midWidth
  rw [natListGetAt_map_below _ (List.range (midWidth + (List.range midWidth).length)) topIndex
      (by rw [rangeLength]; exact topTotal),
    rangeGetAt_below (midWidth + (List.range midWidth).length) topIndex topTotal]
  -- unfold `partnerIndexOf` to the scan; the root at `topIndex` is `bottomTarget`
  show findPartnerScan ([] : List (Nat × Nat)) (List.range midWidth ++ List.range midWidth)
      (unionFindRootOf ([] : List (Nat × Nat))
        (natListGetAt (List.range midWidth ++ List.range midWidth) topIndex)) topIndex
      (List.range (midWidth + (List.range midWidth).length)) < midWidth
  have rootAtTop : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range midWidth ++ List.range midWidth) topIndex) = bottomTarget := by
    rw [← targetEq, doubleRangeGet_above targetLt]; rfl
  rw [rootAtTop]
  -- the scan target `bottomTarget`: a bottom index in the same (empty-links) component, distinct from exclude
  have targetMem : bottomTarget ∈ List.range (midWidth + (List.range midWidth).length) :=
    mem_range_of_lt (Nat.lt_of_lt_of_le targetLt (Nat.le_add_right midWidth (List.range midWidth).length))
  have targetNeTop : bottomTarget ≠ topIndex := by
    intro targetEqTop
    rw [targetEqTop] at targetLt
    exact Nat.lt_irrefl topIndex (Nat.lt_of_lt_of_le targetLt topAtLeast)
  have targetRoot : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range midWidth ++ List.range midWidth) bottomTarget) = bottomTarget := by
    rw [doubleRangeGet_below targetLt]; rfl
  have scanNeTop : findPartnerScan ([] : List (Nat × Nat))
      (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
      (List.range (midWidth + (List.range midWidth).length)) ≠ topIndex :=
    findPartnerScan_neExclude_ofTarget ([] : List (Nat × Nat))
      (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
      (List.range (midWidth + (List.range midWidth).length)) bottomTarget targetMem targetNeTop targetRoot
  have scanRoot : unionFindRootOf ([] : List (Nat × Nat))
      (natListGetAt (List.range midWidth ++ List.range midWidth)
        (findPartnerScan ([] : List (Nat × Nat)) (List.range midWidth ++ List.range midWidth) bottomTarget
          topIndex (List.range (midWidth + (List.range midWidth).length)))) = bottomTarget :=
    findPartnerScan_root_ofFound ([] : List (Nat × Nat))
      (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
      (List.range (midWidth + (List.range midWidth).length)) scanNeTop
  have readAtPartner : natListGetAt (List.range midWidth ++ List.range midWidth)
      (findPartnerScan ([] : List (Nat × Nat)) (List.range midWidth ++ List.range midWidth) bottomTarget
        topIndex (List.range (midWidth + (List.range midWidth).length))) = bottomTarget := scanRoot
  have partnerLt : findPartnerScan ([] : List (Nat × Nat))
      (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
      (List.range (midWidth + (List.range midWidth).length))
      < midWidth + (List.range midWidth).length :=
    findPartnerScan_lt_of_scannedLt ([] : List (Nat × Nat))
      (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
      (midWidth + (List.range midWidth).length) topTotal
      (List.range (midWidth + (List.range midWidth).length))
      (fun candidate candidateMem => mem_range_imp_lt candidateMem)
  -- case on whether the scan result is a bottom or a top index; the top case contradicts `scanNeTop`
  cases Nat.lt_or_ge (findPartnerScan ([] : List (Nat × Nat))
      (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
      (List.range (midWidth + (List.range midWidth).length))) midWidth with
  | inl below => exact below
  | inr above =>
      exfalso
      obtain ⟨resultOffset, resultEq⟩ := Nat.le.dest above
      have resultLt : resultOffset < midWidth := by
        have step : midWidth + resultOffset < midWidth + (List.range midWidth).length := by
          rw [resultEq]; exact partnerLt
        have offLtLen : resultOffset < (List.range midWidth).length := Nat.lt_of_add_lt_add_left step
        rw [lenEq] at offLtLen
        exact offLtLen
      have readAbove : natListGetAt (List.range midWidth ++ List.range midWidth)
          (findPartnerScan ([] : List (Nat × Nat)) (List.range midWidth ++ List.range midWidth) bottomTarget
            topIndex (List.range (midWidth + (List.range midWidth).length))) = resultOffset := by
        rw [← resultEq, doubleRangeGet_above resultLt]
      have offEqTarget : resultOffset = bottomTarget := readAbove.symm.trans readAtPartner
      have partnerEqTop : findPartnerScan ([] : List (Nat × Nat))
          (List.range midWidth ++ List.range midWidth) bottomTarget topIndex
          (List.range (midWidth + (List.range midWidth).length)) = topIndex := by
        rw [← resultEq, offEqTarget, targetEq]
      exact scanNeTop partnerEqTop

/-! ## The corollary the LOCATE base case consumes: no forward chord on the survivor region -/

/-- ★ **The empty-mid matching has NO forward chord on the survivor region.**  For `window < midWidth`, the
survivor top port `midWidth + window` never partners `midWidth + window + 1` — it points strictly below
`midWidth` (`emptyMidMatching_topPort_lt`), whereas `midWidth + window + 1 > midWidth`.  This is what lets
the positive-mid fueled locate terminate honestly at the empty spine: there is no phantom forward chord left
to peel. -/
theorem emptyMidMatching_noForwardChord {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {midWidth window : Nat} (windowBelow : window < midWidth) :
    natListGetAt (matchingOfSpineList midWidth
        ([] : List (SpineAtom signature sourceMode targetMode))).partner (midWidth + window)
      ≠ midWidth + window + 1 := by
  have partnerLt : natListGetAt (matchingOfSpineList midWidth
      ([] : List (SpineAtom signature sourceMode targetMode))).partner (midWidth + window) < midWidth :=
    emptyMidMatching_topPort_lt (Nat.le_add_right midWidth window) (Nat.add_lt_add_left windowBelow midWidth)
  intro partnerEq
  rw [partnerEq] at partnerLt
  have midLe : midWidth ≤ midWidth + window + 1 :=
    Nat.le_trans (Nat.le_add_right midWidth window) (Nat.le_succ (midWidth + window))
  exact Nat.lt_irrefl (midWidth + window + 1) (Nat.lt_of_lt_of_le partnerLt midLe)

/-! ## The named invariant at the adjoint-triple string signature + anti-vacuity fires -/

/-- ★ **The named base-floor invariant `stringEmptyMidMatching_isSurvivorIdentity`** (the recon's rung).  At
the adjoint-triple string signature: the empty pure-cup spine over a positive mid-width bottom boundary is
the survivor identity — every survivor top port `midWidth + window` (`window < midWidth`) points strictly
below `midWidth` (down into the bottom-port block).  The exact base-floor invariant the positive-mid LOCATE
needs, specialized off `emptyMidMatching_topPort_lt`. -/
theorem stringEmptyMidMatching_isSurvivorIdentity {midWidth window : Nat} (windowBelow : window < midWidth) :
    natListGetAt (matchingOfSpineList midWidth
        ([] : List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip))).partner
        (midWidth + window)
      < midWidth :=
  emptyMidMatching_topPort_lt (Nat.le_add_right midWidth window) (Nat.add_lt_add_left windowBelow midWidth)

/-- ★ **The empty-mid matching COMPUTES to the concrete survivor pairing `[2, 3, 0, 1]` at `midWidth = 2`**
(anti-vacuity).  The two survivors `0, 1` pair top-to-bottom (`0 ↔ 2`, `1 ↔ 3`), so both top ports `2, 3`
point below `midWidth = 2` — the genuinely-computed witness of the survivor identity. -/
theorem stringEmptyMidMatching_partnerComputesAtMidTwo :
    (matchingOfSpineList 2
        ([] : List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip))).partner
      = [2, 3, 0, 1] := by decide

/-- ★ **The survivor identity FIRES at mid-`2`, window `0`.**  `stringEmptyMidMatching_isSurvivorIdentity`
at `midWidth = 2` reads survivor top port `2` down to `< 2` — agreeing with the computed `partner[2] = 0`
(`stringEmptyMidMatching_partnerComputesAtMidTwo`). -/
theorem stringEmptyMidMatching_survivorIdentity_firesAtMidTwo :
    natListGetAt (matchingOfSpineList 2
        ([] : List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip))).partner
        (2 + 0)
      < 2 :=
  stringEmptyMidMatching_isSurvivorIdentity (by decide)

/-- ★ **No forward chord FIRES at mid-`2`, window `0`.**  The empty-mid survivor top port `2` never
partners `3` — agreeing with the computed `partner[2] = 0 ≠ 3`.  Cross-checked concretely by
`stringEmptyMidMatching_partnerComputesAtMidTwo` (`partner[2] = 0`). -/
theorem stringEmptyMidMatching_noForwardChord_firesAtMidTwo :
    natListGetAt (matchingOfSpineList 2
        ([] : List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip))).partner
        (2 + 0)
      ≠ 2 + 0 + 1 :=
  emptyMidMatching_noForwardChord (by decide)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the ONE genuinely-new positive-mid LOCATE invariant is built: the empty-mid matching
survivor identity (FC-3 r44, P2c honest partial).**  `emptyMidMatching_topPort_lt` /
`stringEmptyMidMatching_isSurvivorIdentity`: the empty pure-cup spine over a positive mid-width bottom
boundary has the survivor-identity matching — every survivor top port `midWidth + w` (`w < midWidth`) points
strictly below `midWidth`.  Matching-carrier port of the shipped arc-carrier `initialPartner_topPort_lt`
(`extractDiagram` reduces to the identical `partnerIndexOf [] (range ++ range)` form as `extractArc`).  Its
corollary `emptyMidMatching_noForwardChord` discharges the LOCATE base case (no phantom forward chord to
peel).  FIRED at mid-`2` and cross-checked against the genuinely-computed empty-mid partner `[2,3,0,1]`.

  CENSUS (N/K): P2c honest partial delivers the K = 1 genuinely-new base-floor invariant, PROVED (N_proved =
  1) + 1 no-forward-chord corollary + 1 concrete-matching certificate + 3 fires.  0 sub-Props inhabited, 0
  masters flipped.

  What this does NOT close (the residual LOCATE rung, named forward): the brick
  `StringPositiveMidPureCupDeterminacy` (`StringPositiveMidCupSortResidual`) still needs, ON TOP of this base
  floor + the r44 P2b readoff + the r43 P2a snake exclusion, the MECHANICAL seed-offset ports of the r16
  fueled assembly:
    * `stringMatchingChordShift_below_mid` / `stringMatchingChordShift_above_mid` — the trichotomy descents,
      riding `diagramPartner_stepCup midWidth` (mechanical token-swap of the width-`0` chord-shifts);
    * `stringDropLastCup_matching_injective_mid` — the drop-injectivity, riding the already-seed-general
      `stringExtractDiagram_stepCup_congr` (+ the `seedBelowFresh` witness off `processSpine_nextFresh_le`);
    * `stringMatchingLocateAuxMid` / `stringMatchingPureCupSpineSortFueled_mid` — the fueled word-threaded
      locate/sort assembly, then `stringPositiveMidPureCupDeterminacy_proof` inhabiting the LITERAL brick.
  Until that assembly lands, the brick stays OPEN (a specialization = fabrication) and
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip`
  (`StringConvOfMapEqPort`) STAY `false`, honestly.  This round flips ONLY this NEW marker.  `= true`. -/
def fxString_hasEmptyMidSurvivorIdentity : Bool := true

end FX1Poly.Polygraph
