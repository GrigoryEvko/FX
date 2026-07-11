import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcBoundaryCensusPerfectMatchingFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingIndexBridge

/-! # WalkingString/StringMatchingPartnerInvolution — the boundary matching is a fixed-point-free involution on
`matchingOf`, over the walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r31, B3: the involution + no-fixed-point
transport)

The string clone of the walking-adjunction `MatchingPartnerInvolution` (`arcDiagram_partner_isInvolution` /
`matchingOf_partner_isInvolution` / `matchingOf_partner_neSelf`).  The r30 arc-engine fold capstones
(`stringArcBoundaryCensus_ofChainedSpineList` / `stringArcPerfectMatchingTokens_ofChainedSpineList`) deliver the
two-endpoint boundary census and the token-frame perfect matching for a chained string spine; this file TRANSPORTS
the raw involution / no-fixed-point across the shipped diagram = matching bridge (`arcDiagram_eq_matching`), landing
them directly on `matchingOf`'s `partner` field.

The arc engine is signature-BLIND: `partnerIndexOf_isInvolution` / `partnerIndexOf_below` /
`partnerIndexOf_neSelf_ofPerfectMatching` / `arcPerfectMatching_ofTokens` are stated over the bare `ArcWireState`,
and `arcStructureOfSpineList` / `matchingOfSpineList` / `arcDiagram_eq_matching` / `SpineHasCupCapAtoms` /
`natListGetAt_map_inRange` are `{signature}`-generic, so all are REUSED verbatim by import.  The only signature-keyed
consumers — the two r30 fold capstones — are swapped to their shipped string ports.  So every brick below is a
byte-identical token-swap of the walking-adjunction original, rerouting the signature token alone
`adjunctionModeSignature → adjointTripleModeSignature`.  No new mathematics, no unproven residual.

  * `stringArcDiagramPartnerReadAt` — the arc structure's `diagram.partner`, read at an in-range boundary index, IS
    the canonical `partnerIndexOf` on the processed arc state's boundary (a `map`-of-range read-off).
  * `stringPartnerIndexOf_neSelf_ofChainedSpine` — no fixed point at the extracted state of any chained string spine,
    threaded through the shipped string token-frame perfect matching.
  * ★ `stringArcDiagram_partner_isInvolution` — the censused boundary matching is a fixed-point-free involution on the
    arc structure's `.diagram`: a non-fixed partner read maps back to the source.
  * ★ `stringMatchingOf_partner_isInvolution` / `_neSelf` — the same involution + no-fixed-point TRANSPORTED to the
    plain `matchingOf` carrier across the shipped diagram = matching bridge.  For a boundary-disciplined cup/cap
    spine, a non-fixed boundary port's partner-of-partner is the port, and every boundary port is genuinely matched
    to a DISTINCT partner — the `matchingOf` partner-INVOLUTION the cap-restrict subtree consumes.

Two truth-probes fire the transported involution + no-fixed-point end-to-end on the shipped r30 probe valleys: the
genuine NON-DEGENERATE WIDE valley `[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`), where index `0`'s whole-valley
partner is the distinct top `4` (`neSelf` honest) and the involution round-trips `0 ↦ 4 ↦ 0`; and the mid-zero valley
at `bottomCount = 2` as the instantiation smoke test.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; structural recursion on the atom list, no `WellFounded.fix`; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map plumbing (per-file copy with a distinct `SMPI` suffix, keeping the umbrella build's
global table duplicate-free against the walking-adjunction involution and the r30 fold copies) -/

private theorem rangeLoopLengthSMPI : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthSMPI count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthSMPI (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthSMPI count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastSMPI : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastSMPI count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowSMPI : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowSMPI count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastSMPI count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowSMPI (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowSMPI count [] index indexBelow

private theorem natListGetAtMapRangeSMPI (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  rw [natListGetAt_map_inRange mapFunction (List.range total) index
      (by rw [rangeLengthSMPI]; exact inRange),
    rangeGetAtBelowSMPI total index inRange]

/-! ## The diagram-partner read-off (public re-derivation) -/

/-- The arc structure's `diagram.partner`, read at an in-range boundary index, IS the canonical
`partnerIndexOf` on the processed arc state's boundary — `.diagram.partner` is `(List.range total).map
(partnerIndexOf …)` by construction, so the read is a `map`-of-range read-off. -/
private theorem stringArcDiagramPartnerReadAt
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (index : Nat)
    (inRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length) :
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index
      = partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).links
          (List.range bottomCount
            ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires)
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)
          index := by
  have partnerListEq :
      (arcStructureOfSpineList bottomCount spine).diagram.partner
        = (List.range (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)).map
            (partnerIndexOf
              (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).links
              (List.range bottomCount
                ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    spine).openWires)
              (bottomCount
                + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    spine).openWires.length)) := rfl
  rw [partnerListEq]
  exact natListGetAtMapRangeSMPI _ _ index inRange

/-! ## No fixed point at the extracted state of any chained string spine -/

/-- **No fixed point at the extracted state of any chained string spine.**  Folding a boundary-chained
walking-adjoint-triple spine from the canonical seed lands a state whose `partnerIndexOf` matching has NO fixed
point — every boundary index is genuinely matched to a distinct one.  Threaded through the shipped string
token-frame perfect matching `stringArcPerfectMatchingTokens_ofChainedSpineList`; the token → range bridge and the
range-frame no-fixed-point discharge are signature-BLIND (over the bare `ArcWireState`), reused verbatim. -/
private theorem stringPartnerIndexOf_neSelf_ofChainedSpine
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms)
    (index : Nat)
    (indexInRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length) :
    partnerIndexOf
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
        (List.range bottomCount
          ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires)
        (bottomCount
          + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length)
        index
      ≠ index :=
  partnerIndexOf_neSelf_ofPerfectMatching bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
    (arcPerfectMatching_ofTokens bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
      (stringArcPerfectMatchingTokens_ofChainedSpineList bottomCount atoms chained))
    index indexInRange

/-! ## The involution IN the arc structure -/

/-- ★ **The boundary matching is an involution IN the arc structure.**  A non-fixed partner read on the
arc structure's boundary `.diagram` maps back to the source, bridging the raw `partnerIndexOf_isInvolution`
through the diagram read-off at both the source index and its (in-range) partner. -/
theorem stringArcDiagram_partner_isInvolution
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length)
    (notFixed : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index
      ≠ index) :
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index)
      = index := by
  have census := stringArcBoundaryCensus_ofChainedSpineList bottomCount spine chained
  have readIndex := stringArcDiagramPartnerReadAt bottomCount spine index inRange
  have partnerBelow := partnerIndexOf_below
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    bottomCount index inRange
  have notFixed' :
      partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).links
          (List.range bottomCount
            ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires)
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)
          index
        ≠ index := fun partnerEqIndex => notFixed (readIndex.trans partnerEqIndex)
  rw [readIndex, stringArcDiagramPartnerReadAt bottomCount spine _ partnerBelow]
  exact partnerIndexOf_isInvolution bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    census index inRange notFixed'

/-! ## The transported involution on the plain `matchingOf` carrier -/

/-- ★ **The boundary matching is a fixed-point-free involution on `matchingOf`.**  For a
boundary-disciplined cup/cap spine (non-empty bottom boundary), a non-fixed boundary port's
partner-of-partner is the port again.  Landed by transport: the arc structure's `.diagram` IS
`matchingOfSpineList` (the shipped `arcDiagram_eq_matching` bridge), so the arc-carrier involution
rewrites onto the plain carrier verbatim. -/
theorem stringMatchingOf_partner_isInvolution
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (arity : SpineHasCupCapAtoms spine) (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount + (matchingOfSpineList bottomCount spine).topCount)
    (notFixed : natListGetAt (matchingOfSpineList bottomCount spine).partner index ≠ index) :
    natListGetAt (matchingOfSpineList bottomCount spine).partner
        (natListGetAt (matchingOfSpineList bottomCount spine).partner index)
      = index := by
  have bridge : (arcStructureOfSpineList bottomCount spine).diagram
      = matchingOfSpineList bottomCount spine :=
    arcDiagram_eq_matching bottomCount spine arity chained bottomPos
  rw [← bridge] at inRange notFixed ⊢
  exact stringArcDiagram_partner_isInvolution bottomCount spine chained index inRange notFixed

/-! ## The transported no-fixed-point on the plain `matchingOf` carrier -/

/-- ★ **The boundary matching has NO fixed point on `matchingOf`.**  For a boundary-disciplined cup/cap spine
(non-empty bottom boundary), every boundary port is genuinely matched to a DISTINCT partner — the whole valley's
matching is a perfect matching.  Transported from the arc carrier's `stringPartnerIndexOf_neSelf_ofChainedSpine`
through the diagram-partner read-off and the shipped `arcDiagram_eq_matching` bridge.  Together with
`stringMatchingOf_partner_isInvolution` this makes `matchingOf`'s partner map a fixed-point-free involution. -/
theorem stringMatchingOf_partner_neSelf
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (arity : SpineHasCupCapAtoms spine) (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount + (matchingOfSpineList bottomCount spine).topCount) :
    natListGetAt (matchingOfSpineList bottomCount spine).partner index ≠ index := by
  have bridge : (arcStructureOfSpineList bottomCount spine).diagram
      = matchingOfSpineList bottomCount spine :=
    arcDiagram_eq_matching bottomCount spine arity chained bottomPos
  rw [← bridge] at inRange ⊢
  rw [stringArcDiagramPartnerReadAt bottomCount spine index inRange]
  exact stringPartnerIndexOf_neSelf_ofChainedSpine bottomCount spine chained index inRange

/-! ## Concrete truth-probes — the transported involution + no-fixed-point FIRE on the shipped r30 valleys -/

/-- The wide valley `[ε] ++ [η']` at `bottomCount = 4` satisfies the generic cup/cap arity discipline: both
generators are cup/cap by the shipped four-generator classifier. -/
theorem stringWideProbeValley_hasCupCap :
    SpineHasCupCapAtoms ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]) :=
  spineHasCupCapAtoms_cons (adjointTripleSpineAtom_hasCupOrCapArity stringWideProbeCapAtom)
    (spineHasCupCapAtoms_cons (adjointTripleSpineAtom_hasCupOrCapArity stringWideProbeCupAtom)
      (by intro probeAtom probeMem; nomatch probeMem))

/-- ★ **The no-fixed-point FIRES on the genuine non-degenerate wide valley.**  On the concrete valley
`[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`), the bottom port `0` is genuinely matched to a DISTINCT
whole-valley partner (the top `4`) — a real inhabitation over a valley with non-zero mid content, not vacuous.
This is the `notFixed` witness the involution fire consumes. -/
theorem stringMatchingOf_partner_neSelf_firesOnWideValley :
    natListGetAt
        (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])).partner 0
      ≠ 0 :=
  stringMatchingOf_partner_neSelf 4 (by decide)
    ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]) stringWideProbeValley_hasCupCap
    stringWideProbeValley_chained 0 (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 4 _))

/-- ★ **The involution ROUND-TRIPS on the genuine non-degenerate wide valley.**  On the same wide valley the
whole-valley partner of the partner of the bottom port `0` is `0` again (`0 ↦ 4 ↦ 0`), the non-fixed premise
discharged by `stringMatchingOf_partner_neSelf_firesOnWideValley` — the transported involution established on a
non-zero-mid-width valley. -/
theorem stringMatchingOf_partner_isInvolution_firesOnWideValley :
    natListGetAt (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])).partner
        (natListGetAt
          (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])).partner 0)
      = 0 :=
  stringMatchingOf_partner_isInvolution 4 (by decide)
    ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]) stringWideProbeValley_hasCupCap
    stringWideProbeValley_chained 0 (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 4 _))
    stringMatchingOf_partner_neSelf_firesOnWideValley

/-- The mid-zero valley `[ε] ++ [η']` at `bottomCount = 2` satisfies the generic cup/cap arity discipline. -/
theorem stringMidZeroProbeValley_hasCupCap :
    SpineHasCupCapAtoms
      ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom]) :=
  spineHasCupCapAtoms_cons
    (adjointTripleSpineAtom_hasCupOrCapArity stringWidthTelescopeProbeCapAtom)
    (spineHasCupCapAtoms_cons
      (adjointTripleSpineAtom_hasCupOrCapArity stringWidthTelescopeProbeCupAtom)
      (by intro probeAtom probeMem; nomatch probeMem))

/-- ★ **The no-fixed-point smoke-fires on the mid-zero valley.**  The empty-context valley `[ε] ++ [η']` at
`bottomCount = 2` instantiates the transported no-fixed-point end-to-end — the cheap "does it instantiate" check. -/
theorem stringMatchingOf_partner_neSelf_firesOnMidZeroValley :
    natListGetAt
        (matchingOfSpineList 2
          ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])).partner 0
      ≠ 0 :=
  stringMatchingOf_partner_neSelf 2 (by decide)
    ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])
    stringMidZeroProbeValley_hasCupCap stringMidZeroProbeValley_chained 0
    (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 2 _))

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string `matchingOf` partner-INVOLUTION + no-fixed-point is SHIPPED, zero-axiom
(FC-3 r31, B3).**  Landed here over the walking ADJOINT-TRIPLE signature, by transport from the r30 arc-engine
fold capstones:

  * `stringArcDiagram_partner_isInvolution` — the censused boundary matching is a fixed-point-free involution on
    the arc structure's `.diagram` (consuming the r30 `stringArcBoundaryCensus_ofChainedSpineList`).
  * `stringMatchingOf_partner_isInvolution` / `_neSelf` — the same involution + no-fixed-point TRANSPORTED to the
    plain `matchingOf` carrier across the shipped diagram = matching bridge (`arcDiagram_eq_matching`), threading
    the r30 `stringArcPerfectMatchingTokens_ofChainedSpineList`.  For a boundary-disciplined cup/cap spine, a
    non-fixed boundary port's partner-of-partner is the port, and every boundary port is matched to a DISTINCT
    partner — exactly the `matchingOf` partner-involution the cap-restrict subtree names as the hardest new lemma.

  The arc engine is signature-BLIND: `partnerIndexOf_{isInvolution,below,neSelf_ofPerfectMatching}` /
  `arcPerfectMatching_ofTokens` are stated over the bare `ArcWireState`, and `arcStructureOfSpineList` /
  `matchingOfSpineList` / `arcDiagram_eq_matching` / `SpineHasCupCapAtoms` / `natListGetAt_map_inRange` are
  `{signature}`-generic, so all are REUSED verbatim by import.  The only signature-keyed consumers — the two r30
  fold capstones — are swapped to their shipped string ports.  Every brick is a byte-identical token-swap of the
  walking-adjunction `MatchingPartnerInvolution` / `ArcPerfectMatchingIndexBridge` original — no new mathematics,
  no unproven residual.

  Two truth-probes fire the transported facts end-to-end: the genuine NON-DEGENERATE WIDE valley `[ε] ++ [η']` at
  `bottomCount = 4` (mid-width `2`), where index `0`'s whole-valley partner is the distinct top `4`
  (`stringMatchingOf_partner_neSelf_firesOnWideValley`) and the involution round-trips `0 ↦ 4 ↦ 0`
  (`stringMatchingOf_partner_isInvolution_firesOnWideValley`); and the mid-zero valley at `bottomCount = 2` as the
  instantiation smoke test.

  What this marker does NOT claim (honestly), and what the M2c cap subtree still needs above it:
    * the cap-CONSUMED / survivor-bottom / cap-TOP partner legs (B4) that CONSUME this involution;
    * the `stringCapRestrict_reconstructs` / `stringSameWholeMatching_capBlockMatchingEq` splitter (B5).

  So `stringSameWholeMatching_capBlockMatchingEq` (M2c cap) stays un-landed, and
  `fxString_hasAdjointTripleCompleteness` / `fxString_hasConvOfMapEqPortFlip` stay `false`.  This round flips ONLY
  this NEW marker: B3 is shipped as the involution floor above the r30 fold.  `= true`. -/
def fxString_hasMatchingPartnerInvolution : Bool := true

end FX1Poly.Polygraph
