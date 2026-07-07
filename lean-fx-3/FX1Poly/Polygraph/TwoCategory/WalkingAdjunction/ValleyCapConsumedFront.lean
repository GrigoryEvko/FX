import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapRestrict
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanLocalize
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # ValleyCapConsumedFront — the cap-consumed partner leg (Piece II tail, cap partner-list case 2)

The full `DiagramType.ext` for `capRestrict` has three partner-field cases.  This file lands the CAP-CONSUMED
case: for a bottom port `k < bc` whose whole-valley partner is ANOTHER bottom (`V.partner[k] < bc`, `≠ k` — a
bottom-bottom cap arc, consumed by the cap block itself), the cap block's OWN partner of `k` equals the whole
valley's partner of `k`: cups are transparent to bottom-bottom connectivity.

The scan-level content is a FRONT-confinement (the dual of the shipped `partnerIndexOf_survivor_dropsToTop`
top-confinement): once the whole-range partner is known to be a bottom, the partner scan is confined to the
bottom prefix `List.range bc`, where the whole run and the cap-alone run agree candidate by candidate (the
shipped bottom-bottom connectivity frame `processSpine_isSameComponent_bottom_ofAllCupArity`).

  * ★ `partnerIndexOf_eq_frontScan_ofFrontNe` — the front-confinement: if the bottom-prefix scan does NOT return
    the exclude sentinel, the whole-range `partnerIndexOf` equals it (`findPartnerScan_append_ofFoundInFront`
    after `rangeSplit`).

  * ★ `frontScan_ne_ofPartnerBelow` — the trigger: if the whole-range partner is a bottom (`< bc`) and not the
    port itself, the bottom-prefix scan does not return the sentinel (otherwise the partner would drop to the
    top segment, `≥ bc`, or be the port).

  * ★ `capConsumed_partner_agree` — the CAP-CONSUMED agreement: cap-alone partner = whole-valley partner for a
    bottom-bottom port, by confining both scans to the bottom prefix and closing with the bottom-bottom
    connectivity frame via `findPartnerScan_congr_ofTestAgree`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Membership in the shifted top segment sits at or above the floor -/

/-- Every member of the shifted top segment `offsets.map (bottomCount + ·)` is `≥ bottomCount`. -/
private theorem mappedShiftMem_ge (bottomCount : Nat) :
    (offsets : List Nat) → (value : Nat) →
    value ∈ offsets.map (fun offset => bottomCount + offset) → bottomCount ≤ value
  | [], value, mem => by
      have mem' : value ∈ ([] : List Nat) := mem
      nomatch mem'
  | offset :: rest, value, mem => by
      have mem' : value ∈ (bottomCount + offset) :: rest.map (fun off => bottomCount + off) := mem
      cases mem' with
      | head => exact Nat.le_add_right bottomCount offset
      | tail _ memRest => exact mappedShiftMem_ge bottomCount rest value memRest

/-! ## The front-confinement (dual of `partnerIndexOf_survivor_dropsToTop`) -/

/-- ★ **The front-confinement.**  If the bottom-prefix scan does NOT return the exclude sentinel `k`, the
whole-range `partnerIndexOf` at `k` equals it: split the range at `bottomCount` (`rangeSplit`), and since the
front finds a partner, the first-hit discipline never reaches the top segment
(`findPartnerScan_append_ofFoundInFront`). -/
theorem partnerIndexOf_eq_frontScan_ofFrontNe (links : List (Nat × Nat)) (bottomCount top : Nat)
    (state : WireState) {portIndex : Nat}
    (frontNe : findPartnerScan links (matchingBoundaryNodes bottomCount state)
        (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
        portIndex (List.range bottomCount) ≠ portIndex) :
    partnerIndexOf links (matchingBoundaryNodes bottomCount state) (bottomCount + top) portIndex
      = findPartnerScan links (matchingBoundaryNodes bottomCount state)
          (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
          portIndex (List.range bottomCount) := by
  unfold partnerIndexOf
  rw [rangeSplit bottomCount top]
  exact findPartnerScan_append_ofFoundInFront links (matchingBoundaryNodes bottomCount state)
    (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
    portIndex (List.range bottomCount) ((List.range top).map (fun offset => bottomCount + offset)) frontNe

/-- ★ **The front-confinement trigger.**  If the whole-range partner of a bottom port `portIndex` is another
bottom (`< bottomCount`) and not the port itself, then the bottom-prefix scan does NOT return the sentinel.
Otherwise the whole scan would drop to the top segment (`findPartnerScan_append_ofFrontFails`), whose result is
a member (`≥ bottomCount`, `mappedShiftMem_ge`) or the sentinel `portIndex` — contradicting the partner being a
bottom other than `portIndex`. -/
theorem frontScan_ne_ofPartnerBelow (links : List (Nat × Nat)) (bottomCount top : Nat)
    (state : WireState) {portIndex : Nat}
    (partnerBelow :
      partnerIndexOf links (matchingBoundaryNodes bottomCount state) (bottomCount + top) portIndex
        < bottomCount)
    (partnerNe :
      partnerIndexOf links (matchingBoundaryNodes bottomCount state) (bottomCount + top) portIndex
        ≠ portIndex) :
    findPartnerScan links (matchingBoundaryNodes bottomCount state)
        (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
        portIndex (List.range bottomCount) ≠ portIndex := by
  intro frontEqPort
  have partnerEqTop :
      partnerIndexOf links (matchingBoundaryNodes bottomCount state) (bottomCount + top) portIndex
        = findPartnerScan links (matchingBoundaryNodes bottomCount state)
            (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
            portIndex ((List.range top).map (fun offset => bottomCount + offset)) := by
    unfold partnerIndexOf
    rw [rangeSplit bottomCount top]
    exact findPartnerScan_append_ofFrontFails links (matchingBoundaryNodes bottomCount state)
      (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
      portIndex (List.range bottomCount) ((List.range top).map (fun offset => bottomCount + offset))
      frontEqPort
  rcases findPartnerScan_result_mem_or_eq_exclude links (matchingBoundaryNodes bottomCount state)
      (unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) portIndex))
      portIndex ((List.range top).map (fun offset => bottomCount + offset)) with topMem | topExcl
  · have topGe : bottomCount ≤ partnerIndexOf links (matchingBoundaryNodes bottomCount state)
        (bottomCount + top) portIndex := partnerEqTop ▸ mappedShiftMem_ge bottomCount (List.range top) _ topMem
    exact absurd partnerBelow (Nat.not_lt.mpr topGe)
  · exact partnerNe (partnerEqTop.trans topExcl)

/-! ## The cap-consumed partner agreement -/

/-- ★ **The cap-consumed partner agreement.**  For a valley `capBlock ++ cupBlock` (pure cup block) and a bottom
port `k < bc` whose whole-valley partner is another bottom (`V.partner[k] < bc`, `≠ k` — a bottom-bottom cap
arc), the cap block's OWN partner of `k` equals the whole valley's partner of `k`.  Both partner reads confine to
the bottom prefix (`partnerIndexOf_eq_frontScan_ofFrontNe` via `frontScan_ne_ofPartnerBelow`), where the whole
run and the cap-alone run agree candidate by candidate — the bottom-bottom connectivity frame
`processSpine_isSameComponent_bottom_ofAllCupArity` fed through `findPartnerScan_congr_ofTestAgree`. -/
theorem capConsumed_partner_agree
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock)
    {consumedPort : Nat} (portBelow : consumedPort < bottomCount)
    (wholePartnerBelow :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort < bottomCount)
    (wholePartnerNe :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort
        ≠ consumedPort) :
    natListGetAt (matchingOfSpineList bottomCount capBlock).partner consumedPort
      = natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have capConditions : MatchingSwapStateConditions bottomCount capState :=
    matchingSwapStateConditions_processSpine bottomCount capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (matchingSwapStateConditions_initial bottomCount bottomPositive)
  -- reduce both sides to `partnerIndexOf` at the bottom port
  have capRead : natListGetAt (matchingOfSpineList bottomCount capBlock).partner consumedPort
      = partnerIndexOf capState.links (matchingBoundaryNodes bottomCount capState)
          (bottomCount + capState.openWires.length) consumedPort :=
    extractDiagram_partner_getAt bottomCount capState consumedPort
      (Nat.lt_of_lt_of_le portBelow (Nat.le_add_right bottomCount capState.openWires.length))
  have wholeRead : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort
      = partnerIndexOf wholeState.links (matchingBoundaryNodes bottomCount wholeState)
          (bottomCount + wholeState.openWires.length) consumedPort := by
    rw [wholeSplit]
    exact extractDiagram_partner_getAt bottomCount wholeState consumedPort
      (Nat.lt_of_lt_of_le portBelow (Nat.le_add_right bottomCount wholeState.openWires.length))
  rw [capRead, wholeRead]
  rw [wholeRead] at wholePartnerBelow wholePartnerNe
  -- the whole scan confines to the front, and so does the cap scan
  have frontWholeNe := frontScan_ne_ofPartnerBelow wholeState.links bottomCount
    wholeState.openWires.length wholeState wholePartnerBelow wholePartnerNe
  have wholeEqFront := partnerIndexOf_eq_frontScan_ofFrontNe wholeState.links bottomCount
    wholeState.openWires.length wholeState frontWholeNe
  -- the two front scans agree over the bottom prefix (bottom-bottom connectivity is cup-invariant)
  have frontsAgree :
      findPartnerScan wholeState.links (matchingBoundaryNodes bottomCount wholeState)
          (unionFindRootOf wholeState.links
            (natListGetAt (matchingBoundaryNodes bottomCount wholeState) consumedPort))
          consumedPort (List.range bottomCount)
        = findPartnerScan capState.links (matchingBoundaryNodes bottomCount capState)
          (unionFindRootOf capState.links
            (natListGetAt (matchingBoundaryNodes bottomCount capState) consumedPort))
          consumedPort (List.range bottomCount) :=
    findPartnerScan_congr_ofTestAgree wholeState.links capState.links
      (matchingBoundaryNodes bottomCount wholeState) (matchingBoundaryNodes bottomCount capState)
      (unionFindRootOf wholeState.links
        (natListGetAt (matchingBoundaryNodes bottomCount wholeState) consumedPort))
      (unionFindRootOf capState.links
        (natListGetAt (matchingBoundaryNodes bottomCount capState) consumedPort))
      consumedPort (List.range bottomCount)
      (fun candidate candidateMem => by
        have candidateBelow : candidate < bottomCount := mem_range_imp_lt candidateMem
        rw [matchingBoundaryNodes_getAt_bottom bottomCount wholeState candidate candidateBelow,
          matchingBoundaryNodes_getAt_bottom bottomCount capState candidate candidateBelow,
          matchingBoundaryNodes_getAt_bottom bottomCount wholeState consumedPort portBelow,
          matchingBoundaryNodes_getAt_bottom bottomCount capState consumedPort portBelow]
        exact congrArg (fun rootMatch => candidate != consumedPort && rootMatch)
          (processSpine_isSameComponent_bottom_ofAllCupArity bottomCount cupBlock cupPure capState
            capConditions candidate consumedPort candidateBelow portBelow))
  -- the cap scan does not return the sentinel either (it equals the whole partner, which is not the port)
  have frontCapNe : findPartnerScan capState.links (matchingBoundaryNodes bottomCount capState)
      (unionFindRootOf capState.links
        (natListGetAt (matchingBoundaryNodes bottomCount capState) consumedPort))
      consumedPort (List.range bottomCount) ≠ consumedPort := by
    rw [← frontsAgree, ← wholeEqFront]
    exact wholePartnerNe
  have capEqFront := partnerIndexOf_eq_frontScan_ofFrontNe capState.links bottomCount
    capState.openWires.length capState frontCapNe
  rw [capEqFront, ← frontsAgree, ← wholeEqFront]

/-! ## Honesty marker -/

/-- **Honesty marker — the CAP-CONSUMED partner leg is SHIPPED.**  Landed here, zero-axiom:

  * `partnerIndexOf_eq_frontScan_ofFrontNe` / `frontScan_ne_ofPartnerBelow` — the front-confinement dual of the
    shipped top-confinement `partnerIndexOf_survivor_dropsToTop`: a bottom-partnered port's scan is confined to
    the bottom prefix.

  * `capConsumed_partner_agree` — cups are transparent to a bottom-bottom cap arc: for `k < bc` with
    `V.partner[k] < bc` and `≠ k`, the cap-alone partner of `k` equals the whole-valley partner, by confining
    both scans to the bottom prefix and closing with the shipped bottom-bottom connectivity frame via
    `findPartnerScan_congr_ofTestAgree`.

This closes the cap-CONSUMED partner case of the full `capRestrict` `DiagramType.ext`.  What this marker does NOT
claim: the cap-TOP partner case (the `matchingOf` involution + `nthSurvivorTop` correctness) or the assembled
`DiagramType.ext` / `valleyAppend_split`.  No gate flag is flipped.  `= true`. -/
def fxMode_hasValleyCapConsumedFront : Bool := true

end FX1Poly.Polygraph
