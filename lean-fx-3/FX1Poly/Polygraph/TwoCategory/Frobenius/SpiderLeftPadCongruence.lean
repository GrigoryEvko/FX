import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderConv
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadCongruence

/-! # WP-FROB r6 (FROB-6) — the spider PARTITION pad congruence at a NONZERO left offset (boundary-changing)

`SpiderPadCongruence.lean` (FROB-3) lifted the RIGHT pad (offset `0`, extra strands to the right of a wider seed):
a spider relation sound at its own boundary `threshold` is `SpiderConv`-convertible in the wider boundary
`threshold + delta`, with the SAME words fired at the SAME positions.  This file installs the mirror LEFT pad:
`delta` extra strands to the LEFT, so every firing position shifts by `delta` (`shiftBrauerWord delta`) and the
boundary widens to `delta + threshold`.  This is the genuinely NONZERO-OFFSET, boundary-CHANGING leg the FROB-5
ledger named (`fxFrob_hasSpiderBoundaryChangingPrefix`).

## The reuse (engine-generic) and the one new payoff

`processBrauer_leftPadSim` (`Brauer/WiringDescPadCongruence.lean`) produces a `MatchingLeftPadSim` for ANY
`List BrauerAtom` word run against its `shiftBrauerWord`-shifted twin — the spider generators `μ` / `δ` / `η` / `ε`
are in scope with zero change.  The shipped payoff `matchingSameComponent_ofLeftPadSimPair`
(`FreeTwoCell/MatchingLeftPadCongruence.lean`) consumes a full `MatchingConnectivityViewSim` base, which BUNDLES a
loop equality; the spider special row `μδ = 1` carries UNEQUAL loop counts (`1` vs `0`) on its two sides, so no such
base sim exists.  So this file installs the leaner `matchingSameComponent_ofSpiderLeftPadSimPair`: the padded
boundary same-component views agree from the BASE view agreement ALONE (open-wire length equality + boundary
`matchingSameComponent` agreement), no loop hypothesis — the loops-free clone of
`matchingSameComponent_ofLeftPadSimPair`, mirroring the FROB-3 right-pad clone
`matchingSameComponent_ofSpiderRightPadSimPair`.

The padded view + padded length then discharge the `SpiderConv.whisker` (empty prefix) at the shifted words —
`spiderConv_relation_inWiderBoundary_leftOffset`.

## Literature anchor

The two-sided pad closure is the Frobenius-structure context closure of Bonchi-Gadducci-Kissinger-Sobocinski-Zanasi
(*String Diagram Rewrite Theory II*, arXiv:2104.14686): with a Frobenius algebra structure the correspondence
between rewriting and DPO is two-sided (cups/caps on BOTH boundaries), so a rule fires soundly padded on either side.
The right pad (FROB-3) is one boundary; this left pad is the other.  The shift discipline (`shiftBrauerWord`) is the
convex/zone bookkeeping the plain-SMC (non-Frobenius) case would otherwise force.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The left-padded connectivity views agree — the leaner (loops-free) payoff -/

/-- ★ **The left-padded same-component relations of two left-pad-simulated runs agree** given ONLY the base
same-component view agreement (no loop hypothesis).  Shifted pairs defer through `componentComm` to the base view,
mixed pad/shifted pairs are `false` on both sides, and pad pairs are the SHARED identifier equality.  The loops-free
clone of `matchingSameComponent_ofLeftPadSimPair` — it takes the base length equality and the base same-component
agreement as separate arguments instead of a full `MatchingConnectivityViewSim` (which bundles a loop equality the
spider special row `μδ = 1` fails).  Mirrors the FROB-3 right-pad clone
`matchingSameComponent_ofSpiderRightPadSimPair` with the pad zone moved to the FRONT of the boundary. -/
theorem matchingSameComponent_ofSpiderLeftPadSimPair (delta bottomCount : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSOne stateTOne)
    (simTwo : MatchingLeftPadSim delta (padIdentifiers 0 delta) stateSTwo stateTTwo)
    (baseLengthsEq : stateSOne.openWires.length = stateSTwo.openWires.length)
    (baseViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + stateSOne.openWires.length →
        secondIndex < bottomCount + stateSOne.openWires.length →
        matchingSameComponent bottomCount stateSOne firstIndex secondIndex
          = matchingSameComponent bottomCount stateSTwo firstIndex secondIndex)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < (delta + bottomCount) + stateTOne.openWires.length)
    (secondInRange : secondIndex < (delta + bottomCount) + stateTOne.openWires.length) :
    matchingSameComponent (delta + bottomCount) stateTOne firstIndex secondIndex
      = matchingSameComponent (delta + bottomCount) stateTTwo firstIndex secondIndex := by
  cases leftPadSim_pairedReadTaxonomy delta bottomCount stateSOne stateTOne stateSTwo
      stateTTwo simOne simTwo baseLengthsEq firstIndex firstInRange with
  | ofBase firstBase firstBaseInRange firstReadOne firstReadTwo =>
      cases leftPadSim_pairedReadTaxonomy delta bottomCount stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseLengthsEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            simOne.componentComm
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) firstBase)
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) secondBase),
            simTwo.componentComm
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) firstBase)
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) secondBase)]
          exact baseViewAgrees firstBase secondBase firstBaseInRange secondBaseInRange
      | ofPad secondPad secondPadBelow secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            leftPadSim_shiftedVsPad_isFalse delta (padIdentifiers 0 delta) stateSOne
              stateTOne simOne
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) firstBase)
              secondPad secondPadBelow,
            leftPadSim_shiftedVsPad_isFalse delta (padIdentifiers 0 delta) stateSTwo
              stateTTwo simTwo
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) firstBase)
              secondPad secondPadBelow]
  | ofPad firstPad firstPadBelow firstReadOne firstReadTwo =>
      cases leftPadSim_pairedReadTaxonomy delta bottomCount stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseLengthsEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            leftPadSim_padVsShifted_isFalse delta (padIdentifiers 0 delta) stateSOne
              stateTOne simOne firstPad
              (natListGetAt (matchingBoundaryNodes bottomCount stateSOne) secondBase)
              firstPadBelow,
            leftPadSim_padVsShifted_isFalse delta (padIdentifiers 0 delta) stateSTwo
              stateTTwo simTwo firstPad
              (natListGetAt (matchingBoundaryNodes bottomCount stateSTwo) secondBase)
              firstPadBelow]
      | ofPad secondPad secondPadBelow secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTOne)
                  secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (delta + bottomCount) stateTTwo)
                  secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            leftPadSim_padVsPad delta (padIdentifiers 0 delta) stateSOne stateTOne simOne
              firstPad secondPad firstPadBelow secondPadBelow,
            leftPadSim_padVsPad delta (padIdentifiers 0 delta) stateSTwo stateTTwo simTwo
              firstPad secondPad firstPadBelow secondPadBelow]

/-! ## The relation at a nonzero left offset is a `SpiderConv` -/

/-- ★ **A spider relation preserving the boundary PARTITION view at its own boundary is convertible at ANY nonzero
LEFT offset.**  Given a relation whose two sides, fired from the seed at boundary `threshold`, have equal open-wire
count and the SAME boundary same-component view on the in-range indices (the partition-preservation the whisker
consumes), the two sides fired from the wider seed `delta + threshold` with every firing position shifted by `delta`
(`shiftBrauerWord delta`, the extra `delta` strands to the LEFT) are `SpiderConv`-convertible.  The whole-word
left-pad simulation (`processBrauer_leftPadSim`, engine-generic) supplies the padded view
(`matchingSameComponent_ofSpiderLeftPadSimPair`) and the padded length (`leftPadSim_wireCount`), which discharge the
`SpiderConv.whisker` at the empty prefix. -/
theorem spiderConv_relation_inWiderBoundary_leftOffset (threshold delta : Nat) (lhs rhs : List BrauerAtom)
    (inRangeLhs : BrauerWordInRange threshold lhs) (inRangeRhs : BrauerWordInRange threshold rhs)
    (baseLengthsEq : (processBrauer (brauerSeed threshold) lhs).openWires.length
        = (processBrauer (brauerSeed threshold) rhs).openWires.length)
    (baseViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < threshold + (processBrauer (brauerSeed threshold) lhs).openWires.length →
        secondIndex < threshold + (processBrauer (brauerSeed threshold) lhs).openWires.length →
        matchingSameComponent threshold (processBrauer (brauerSeed threshold) lhs) firstIndex secondIndex
          = matchingSameComponent threshold (processBrauer (brauerSeed threshold) rhs) firstIndex secondIndex) :
    SpiderConv (delta + threshold) (shiftBrauerWord delta lhs) (shiftBrauerWord delta rhs) := by
  have simLhs := processBrauer_leftPadSim delta threshold lhs inRangeLhs
  have simRhs := processBrauer_leftPadSim delta threshold rhs inRangeRhs
  have paddedLen :
      (processBrauer (brauerSeed (delta + threshold)) (shiftBrauerWord delta lhs)).openWires.length
        = (processBrauer (brauerSeed (delta + threshold)) (shiftBrauerWord delta rhs)).openWires.length := by
    rw [leftPadSim_wireCount delta (padIdentifiers 0 delta) (processBrauer (brauerSeed threshold) lhs)
        (processBrauer (brauerSeed (delta + threshold)) (shiftBrauerWord delta lhs)) simLhs,
      leftPadSim_wireCount delta (padIdentifiers 0 delta) (processBrauer (brauerSeed threshold) rhs)
        (processBrauer (brauerSeed (delta + threshold)) (shiftBrauerWord delta rhs)) simRhs,
      baseLengthsEq]
  exact SpiderConv.whisker (delta + threshold) [] (shiftBrauerWord delta lhs) (shiftBrauerWord delta rhs)
    paddedLen
    (fun firstIndex secondIndex firstBound secondBound =>
      matchingSameComponent_ofSpiderLeftPadSimPair delta threshold
        (processBrauer (brauerSeed threshold) lhs)
        (processBrauer (brauerSeed (delta + threshold)) (shiftBrauerWord delta lhs))
        (processBrauer (brauerSeed threshold) rhs)
        (processBrauer (brauerSeed (delta + threshold)) (shiftBrauerWord delta rhs))
        simLhs simRhs baseLengthsEq baseViewAgrees firstIndex secondIndex firstBound secondBound)

/-! ## Non-vacuity — the relations at a nonzero left offset (boundary-changing, position-shifted)

Each row, fired at a nonzero LEFT offset (extra strands to the left, every position shifted), is
`SpiderConv`-convertible by the left-pad congruence — the base partition-preservation is discharged concretely by
`decide` on the seed states.  These are genuinely BOUNDARY-CHANGING and genuinely NONZERO-OFFSET (the right pad
could only reach offset `0`). -/

/-- The special law's base partition-view agreement at boundary `1`, in the `Nat.decidableBallLT`-friendly order. -/
private theorem specialLeftBaseView_ordered : ∀ firstIndex,
    firstIndex < 1 + (processBrauer (brauerSeed 1) frobSpecial.lhs).openWires.length → ∀ secondIndex,
    secondIndex < 1 + (processBrauer (brauerSeed 1) frobSpecial.lhs).openWires.length →
    matchingSameComponent 1 (processBrauer (brauerSeed 1) frobSpecial.lhs) firstIndex secondIndex
      = matchingSameComponent 1 (processBrauer (brauerSeed 1) frobSpecial.rhs) firstIndex secondIndex := by
  decide

/-- ★ **The special law `μδ = 1` fired at a nonzero LEFT offset is convertible** — the sentinel through the left-pad
congruence.  Its two sides carry UNEQUAL loop counts at the seed (`1` vs `0`), so the shipped loops-based left-pad
payoff `matchingSameComponent_ofLeftPadSimPair` would be inapplicable; the leaner partition payoff carries it because
the partitions AGREE.  Genuinely boundary-changing AND nonzero-offset: boundary `1 → 2`, every position shifted by
`1` (`shiftBrauerWord 1 [comultAt 0, multAt 0] = [comultAt 1, multAt 1]`). -/
theorem spiderConv_special_atLeftOffset :
    SpiderConv 2 (shiftBrauerWord 1 frobSpecial.lhs) (shiftBrauerWord 1 frobSpecial.rhs) :=
  spiderConv_relation_inWiderBoundary_leftOffset 1 1 frobSpecial.lhs frobSpecial.rhs
    (BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1)))
    (BrauerWordInRange.nil 1) rfl
    (fun firstIndex secondIndex hfirst hsecond => specialLeftBaseView_ordered firstIndex hfirst secondIndex hsecond)

/-- The frobenius-law's base partition-view agreement at boundary `2`, in the `Nat.decidableBallLT`-friendly order. -/
private theorem frobLeftLeftBaseView_ordered : ∀ firstIndex,
    firstIndex < 2 + (processBrauer (brauerSeed 2) frobLeft.lhs).openWires.length → ∀ secondIndex,
    secondIndex < 2 + (processBrauer (brauerSeed 2) frobLeft.lhs).openWires.length →
    matchingSameComponent 2 (processBrauer (brauerSeed 2) frobLeft.lhs) firstIndex secondIndex
      = matchingSameComponent 2 (processBrauer (brauerSeed 2) frobLeft.rhs) firstIndex secondIndex := by
  decide

/-- ★ **The Frobenius law `(μ⊗1)(1⊗δ) = δμ` fired at a nonzero LEFT offset is convertible** — via the left-pad
congruence.  Genuinely boundary-changing AND nonzero-offset: boundary `2 → 3`, every position shifted by `1`. -/
theorem spiderConv_frobLeft_atLeftOffset :
    SpiderConv 3 (shiftBrauerWord 1 frobLeft.lhs) (shiftBrauerWord 1 frobLeft.rhs) :=
  spiderConv_relation_inWiderBoundary_leftOffset 2 1 frobLeft.lhs frobLeft.rhs
    (BrauerWordInRange.cons (comultAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (multAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 2)))
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))
    rfl
    (fun firstIndex secondIndex hfirst hsecond => frobLeftLeftBaseView_ordered firstIndex hfirst secondIndex hsecond)

/-- ★ **The nonzero-left-offset identification is non-vacuous.**  The special law fired at left offset `1` relates
GENUINELY DISTINCT words — the shifted μ-after-δ bubble `[comultAt 1, multAt 1]` and the shifted empty diagram `[]` —
as the SAME boundary partition.  So the left-pad congruence makes real boundary-changing, position-shifted
identifications, not only reflexive ones. -/
theorem spiderConv_special_atLeftOffset_identifies_distinct :
    shiftBrauerWord 1 frobSpecial.lhs ≠ shiftBrauerWord 1 frobSpecial.rhs
      ∧ SpiderConv 2 (shiftBrauerWord 1 frobSpecial.lhs) (shiftBrauerWord 1 frobSpecial.rhs) :=
  ⟨by decide, spiderConv_special_atLeftOffset⟩

/-- ★ **The nonzero-left-offset identification is partition-real** — the two distinct shifted words induce the SAME
boundary partition, via `spiderConv_partitionSound` (the FUNCTORIAL soundness, not a per-instance `decide`). -/
theorem spiderConv_special_atLeftOffset_partitionAgrees :
    extraSpiderDiagramOf 2 (shiftBrauerWord 1 frobSpecial.lhs)
      = extraSpiderDiagramOf 2 (shiftBrauerWord 1 frobSpecial.rhs) :=
  spiderConv_partitionSound spiderConv_special_atLeftOffset

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the BOUNDARY-CHANGING (nonzero left-offset) pad congruence is SHIPPED (flag flipped
`false → true`).**  The FROB-3 right pad reached only offset `0` (extra strands to the RIGHT, same positions); this
file installs the mirror LEFT pad: `delta` extra strands to the LEFT, every firing position shifted by `delta`
(`shiftBrauerWord delta`), boundary widened to `delta + threshold`.  The whole-word left-pad simulation
`processBrauer_leftPadSim` is reused VERBATIM over the spider alphabet (engine-generic over `List BrauerAtom`); the
leaner payoff `matchingSameComponent_ofSpiderLeftPadSimPair` transports the boundary partition view across the front
pad WITHOUT a loop hypothesis (so the special row `μδ = 1`, unequal loops but equal partition, is carried);
`spiderConv_relation_inWiderBoundary_leftOffset` packages a relation fired at ANY nonzero left offset as a
`SpiderConv` via the empty-prefix whisker.  NON-VACUOUS + genuinely boundary-CHANGING + genuinely NONZERO-OFFSET:
the special law (`spiderConv_special_atLeftOffset`, boundary `1 → 2`, positions shifted by `1`) and the Frobenius
law (`spiderConv_frobLeft_atLeftOffset`, boundary `2 → 3`) are convertible at the shifted positions, distinct words
(`spiderConv_special_atLeftOffset_identifies_distinct`), partition-real
(`spiderConv_special_atLeftOffset_partitionAgrees`).  Together with the FROB-3 right pad this closes BOTH horizontal
pad directions (BGKSZ II two-sided Frobenius context closure).  `= true`. -/
def fxFrob_hasSpiderBoundaryChangingPadLeft : Bool := true

end FX1Poly.Polygraph
