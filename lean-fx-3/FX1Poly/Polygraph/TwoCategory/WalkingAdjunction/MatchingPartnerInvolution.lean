import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold

/-! # MatchingPartnerInvolution — the boundary matching is a fixed-point-free involution on `matchingOf`

The censused partner matching is a fixed-point-free involution on the ARC carrier
(`partnerIndexOf_isInvolution`, over `ArcWireState`).  The valley-append split reads the PLAIN
`matchingOf` carrier (`matchingOfSpineList`, over `WireState`, no event nodes).  This file TRANSPORTS
the involution across the shipped diagram = matching bridge (`arcDiagram_eq_matching`), landing the
involution directly on `matchingOf`'s `partner` field:

  * ★ `arcDiagram_partner_isInvolution` — the involution on the ARC structure's boundary `.diagram`: a
    non-fixed partner read maps back to the source, chaining the raw `partnerIndexOf_isInvolution`
    through the diagram-partner read-off at both the source index and its (in-range) partner.  A public
    re-derivation of the private `diagramPartnerInvolutionAt` (same body).

  * ★ `matchingOf_partner_isInvolution` — the involution on the PLAIN `matchingOf` carrier: for a
    boundary-disciplined cup/cap spine (non-empty bottom), a non-fixed boundary port's partner-of-partner
    is the port again.  The arc structure's `.diagram` IS `matchingOfSpineList` (the shipped bridge), so
    the arc-carrier involution rewrites onto the plain carrier verbatim.

This is the `matchingOf` partner-INVOLUTION the `ValleyCapRestrict` marker named as "the hardest remaining
new lemma, which does not exist in the corpus" — landed by transport, orthogonal to the surjectivity
value-half.  It supplies the cap-TOP port leg of the full `capRestrict` field agreement (a survivor-top's
whole-valley partner is its survivor bottom).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map plumbing (per-file copy, following the codebase pattern) -/

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

private theorem rangeLoopGetAtPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelow : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelow count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPast count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelow (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelow count [] index indexBelow

private theorem natListGetAtMapRange (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  rw [natListGetAt_map_inRange mapFunction (List.range total) index
      (by rw [rangeLength]; exact inRange),
    rangeGetAtBelow total index inRange]

/-! ## The diagram-partner read-off (public re-derivation) -/

/-- The arc structure's `diagram.partner`, read at an in-range boundary index, IS the canonical
`partnerIndexOf` on the processed arc state's boundary — `.diagram.partner` is `(List.range total).map
(partnerIndexOf …)` by construction, so the read is a `map`-of-range read-off. -/
private theorem arcDiagramPartnerReadAt
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  exact natListGetAtMapRange _ _ index inRange

/-- ★ **The boundary matching is an involution IN the arc structure.**  A non-fixed partner read on the
arc structure's boundary `.diagram` maps back to the source, bridging the raw `partnerIndexOf_isInvolution`
through the diagram read-off at both the source index and its (in-range) partner. -/
theorem arcDiagram_partner_isInvolution
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  have census := arcBoundaryCensus_ofChainedSpineList bottomCount spine chained
  have readIndex := arcDiagramPartnerReadAt bottomCount spine index inRange
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
  rw [readIndex, arcDiagramPartnerReadAt bottomCount spine _ partnerBelow]
  exact partnerIndexOf_isInvolution bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    census index inRange notFixed'

/-! ## The transported involution on the plain `matchingOf` carrier -/

/-- ★ **The boundary matching is a fixed-point-free involution on `matchingOf`.**  For a
boundary-disciplined cup/cap spine (non-empty bottom boundary), a non-fixed boundary port's
partner-of-partner is the port again — the involution the `ValleyCapRestrict` marker named as the
hardest remaining new lemma.  Landed by transport: the arc structure's `.diagram` IS
`matchingOfSpineList` (the shipped `arcDiagram_eq_matching` bridge), so the arc-carrier involution
rewrites onto the plain carrier verbatim. -/
theorem matchingOf_partner_isInvolution
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  exact arcDiagram_partner_isInvolution bottomCount spine chained index inRange notFixed

/-! ## Honesty marker -/

/-- **Honesty marker — the `matchingOf` partner-INVOLUTION is SHIPPED (transported from the arc carrier).**
Landed here, zero-axiom:

  * `arcDiagram_partner_isInvolution` — the censused boundary matching is a fixed-point-free involution on
    the arc structure's `.diagram` (public re-derivation of the private diagram involution).

  * `matchingOf_partner_isInvolution` — the same involution TRANSPORTED to the plain `matchingOf` carrier
    across the shipped diagram = matching bridge (`arcDiagram_eq_matching`).  For a boundary-disciplined
    cup/cap spine, a non-fixed boundary port's partner-of-partner is the port — exactly the `matchingOf`
    partner-involution the `ValleyCapRestrict` marker named as "the hardest remaining new lemma, which does
    not exist in the corpus".  It is orthogonal to the surjectivity value-half; it supplies the cap-TOP
    port leg of the full `capRestrict` field agreement.

What this marker does NOT claim: the full `DiagramType.ext` for `capRestrict`, `valleyAppend_split`, or the
whole-valley Piece II.  No gate flag is flipped.  `= true`. -/
def fxMode_hasMatchingPartnerInvolution : Bool := true

end FX1Poly.Polygraph
