import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderConv
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence

/-! # WP-FROB r3 (FROB-3) — the spider PARTITION pad congruence (relation in a wider boundary)

The `SpiderConv.whisker` move gates on the boundary PARTITION view (open-wire count + boundary same-component
relation).  To make the contextual instances THEOREMS — a relation fired in a boundary strictly wider than its own
is convertible — this file re-runs the shipped Brauer horizontal-pad simulation over the spider alphabet.

## The reuse (engine-generic) and the one new payoff

`processBrauer_rightPadSim` (`Brauer/WiringDescPadCongruence.lean`) produces a `MatchingRightPadSim` for ANY
`List BrauerAtom` word — the spider generators `μ` / `δ` / `η` / `ε` are in scope with zero change.  The Brauer
payoff `extractDiagram_ofRightPadSimPair` reads the FULL Brauer diagram (partner matching + loops), which cannot be
reused for the spider special row `μδ = 1` (its two sides carry UNEQUAL loop counts, `1` vs `0`, while their spider
partitions AGREE — the loops field is exactly what the spider drops).  So this file installs the leaner
`matchingSameComponent_ofSpiderRightPadSimPair`: the padded boundary same-component views agree from the BASE view
agreement ALONE (no loop hypothesis), mirroring the Brauer payoff's connectivity half but dropping the loop leg.

The padded view then discharges the `SpiderConv.whisker` (empty prefix) directly — a relation sound at its own
boundary `threshold`, fired at offset `0` in the wider boundary `threshold + delta`, is `SpiderConv`-convertible.

## The honest scope

This closes the WIDER-BOUNDARY (right-pad, offset `0`) leg of the contextual closure.  The nonzero-offset leg
(left pad / `shiftBrauerWord`) and the AFTER-ARBITRARY-PREFIX leg (the Brauer two-word functoriality bridge,
`processBrauer_extract_eq_ofCanonicalExtractEq`) are the remaining supply: the Brauer functoriality bridge is
LOOPS-based (it consumes a Brauer canonical extract equality) and so is BLOCKED by the special row exactly as the
right-pad payoff would have been — its loops-free re-homing is the standing residual (ledgered).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The padded connectivity views agree — the leaner (loops-free) payoff -/

/-- ★ **The padded same-component relations of two right-pad-simulated runs agree** given ONLY the base same-component
view agreement (no loop hypothesis).  Shifted pairs defer through `componentComm` to the base view, mixed pad/shifted
pairs are `false` on both sides, and pad pairs are the SHARED identifier equality.  The loops-free clone of
`matchingSameComponent_ofRightPadSimPair` — it takes the base length equality and the base same-component agreement as
separate arguments instead of a full `MatchingConnectivityViewSim` (which bundles a loop equality the spider special
row `μδ = 1` fails). -/
theorem matchingSameComponent_ofSpiderRightPadSimPair (threshold delta : Nat)
    (stateSOne stateTOne stateSTwo stateTTwo : WireState)
    (simOne : MatchingRightPadSim threshold delta (padIdentifiers threshold delta) stateSOne stateTOne)
    (simTwo : MatchingRightPadSim threshold delta (padIdentifiers threshold delta) stateSTwo stateTTwo)
    (baseLengthsEq : stateSOne.openWires.length = stateSTwo.openWires.length)
    (baseViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < threshold + stateSOne.openWires.length →
        secondIndex < threshold + stateSOne.openWires.length →
        matchingSameComponent threshold stateSOne firstIndex secondIndex
          = matchingSameComponent threshold stateSTwo firstIndex secondIndex)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < (threshold + delta) + stateTOne.openWires.length)
    (secondInRange : secondIndex < (threshold + delta) + stateTOne.openWires.length) :
    matchingSameComponent (threshold + delta) stateTOne firstIndex secondIndex
      = matchingSameComponent (threshold + delta) stateTTwo firstIndex secondIndex := by
  cases rightPadSim_pairedReadTaxonomy threshold delta stateSOne stateTOne stateSTwo stateTTwo
      simOne simTwo baseLengthsEq firstIndex firstInRange with
  | ofBase firstBase firstBaseInRange firstReadOne firstReadTwo =>
      cases rightPadSim_pairedReadTaxonomy threshold delta stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseLengthsEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            simOne.componentComm
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) firstBase)
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) secondBase),
            simTwo.componentComm
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) firstBase)
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) secondBase)]
          exact baseViewAgrees firstBase secondBase firstBaseInRange secondBaseInRange
      | ofPad secondPad secondPadLower secondPadUpper secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            rightPadSim_shiftedVsPad_isFalse threshold delta (padIdentifiers threshold delta)
              stateSOne stateTOne simOne
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) firstBase)
              secondPad secondPadLower secondPadUpper,
            rightPadSim_shiftedVsPad_isFalse threshold delta (padIdentifiers threshold delta)
              stateSTwo stateTTwo simTwo
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) firstBase)
              secondPad secondPadLower secondPadUpper]
  | ofPad firstPad firstPadLower firstPadUpper firstReadOne firstReadTwo =>
      cases rightPadSim_pairedReadTaxonomy threshold delta stateSOne stateTOne stateSTwo
          stateTTwo simOne simTwo baseLengthsEq secondIndex secondInRange with
      | ofBase secondBase secondBaseInRange secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            rightPadSim_padVsShifted_isFalse threshold delta (padIdentifiers threshold delta)
              stateSOne stateTOne simOne firstPad
              (natListGetAt (matchingBoundaryNodes threshold stateSOne) secondBase)
              firstPadLower firstPadUpper,
            rightPadSim_padVsShifted_isFalse threshold delta (padIdentifiers threshold delta)
              stateSTwo stateTTwo simTwo firstPad
              (natListGetAt (matchingBoundaryNodes threshold stateSTwo) secondBase)
              firstPadLower firstPadUpper]
      | ofPad secondPad secondPadLower secondPadUpper secondReadOne secondReadTwo =>
          show (unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) firstIndex)
              == unionFindRootOf stateTOne.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTOne) secondIndex))
            = (unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) firstIndex)
              == unionFindRootOf stateTTwo.links
                (natListGetAt (matchingBoundaryNodes (threshold + delta) stateTTwo) secondIndex))
          rw [firstReadOne, secondReadOne, firstReadTwo, secondReadTwo,
            rightPadSim_padVsPad threshold delta (padIdentifiers threshold delta) stateSOne
              stateTOne simOne firstPad secondPad firstPadLower firstPadUpper secondPadLower
              secondPadUpper,
            rightPadSim_padVsPad threshold delta (padIdentifiers threshold delta) stateSTwo
              stateTTwo simTwo firstPad secondPad firstPadLower firstPadUpper secondPadLower
              secondPadUpper]

/-! ## The relation in a wider boundary is a `SpiderConv` -/

/-- ★ **A spider relation preserving the boundary PARTITION view at its own boundary is convertible in ANY wider
boundary.**  Given a relation whose two sides, fired from the seed at boundary `threshold`, have equal open-wire count
and the SAME boundary same-component view on the in-range indices (the partition-preservation the whisker consumes),
the two sides fired from the wider seed `threshold + delta` (offset `0`, the extra `delta` strands to the right) are
`SpiderConv`-convertible.  The whole-word right-pad simulation (`processBrauer_rightPadSim`, engine-generic) supplies
the padded view (`matchingSameComponent_ofSpiderRightPadSimPair`) and the padded length (`rightPadSim_wireCount`),
which discharge the `SpiderConv.whisker` at the empty prefix. -/
theorem spiderConv_relation_inWiderBoundary (threshold delta : Nat) (lhs rhs : List BrauerAtom)
    (inRangeLhs : BrauerWordInRange threshold lhs) (inRangeRhs : BrauerWordInRange threshold rhs)
    (baseLengthsEq : (processBrauer (brauerSeed threshold) lhs).openWires.length
        = (processBrauer (brauerSeed threshold) rhs).openWires.length)
    (baseViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < threshold + (processBrauer (brauerSeed threshold) lhs).openWires.length →
        secondIndex < threshold + (processBrauer (brauerSeed threshold) lhs).openWires.length →
        matchingSameComponent threshold (processBrauer (brauerSeed threshold) lhs) firstIndex secondIndex
          = matchingSameComponent threshold (processBrauer (brauerSeed threshold) rhs) firstIndex secondIndex) :
    SpiderConv (threshold + delta) lhs rhs := by
  have simLhs := processBrauer_rightPadSim threshold delta lhs inRangeLhs
  have simRhs := processBrauer_rightPadSim threshold delta rhs inRangeRhs
  have paddedLen : (processBrauer (brauerSeed (threshold + delta)) lhs).openWires.length
      = (processBrauer (brauerSeed (threshold + delta)) rhs).openWires.length := by
    rw [rightPadSim_wireCount threshold delta (processBrauer (brauerSeed threshold) lhs)
        (processBrauer (brauerSeed (threshold + delta)) lhs) simLhs,
      rightPadSim_wireCount threshold delta (processBrauer (brauerSeed threshold) rhs)
        (processBrauer (brauerSeed (threshold + delta)) rhs) simRhs,
      baseLengthsEq]
  exact SpiderConv.whisker (threshold + delta) [] lhs rhs paddedLen
    (fun firstIndex secondIndex firstBound secondBound =>
      matchingSameComponent_ofSpiderRightPadSimPair threshold delta
        (processBrauer (brauerSeed threshold) lhs) (processBrauer (brauerSeed (threshold + delta)) lhs)
        (processBrauer (brauerSeed threshold) rhs) (processBrauer (brauerSeed (threshold + delta)) rhs)
        simLhs simRhs baseLengthsEq baseViewAgrees firstIndex secondIndex firstBound secondBound)

/-! ## The relations in a wider boundary (non-vacuity for the pad-congruence supply)

Each row, fired in a boundary strictly wider than its own (extra strands to the right), is `SpiderConv`-convertible by
the pad congruence — the base partition-preservation is discharged concretely by `decide` on the seed states.  These
are genuinely BOUNDARY-CHANGING (the pad simulation carries the work), not just the seed relations. -/

/-- The special law's base partition-view agreement at boundary `1`, in the `Nat.decidableBallLT`-friendly order. -/
private theorem specialBaseView_ordered : ∀ firstIndex,
    firstIndex < 1 + (processBrauer (brauerSeed 1) frobSpecial.lhs).openWires.length → ∀ secondIndex,
    secondIndex < 1 + (processBrauer (brauerSeed 1) frobSpecial.lhs).openWires.length →
    matchingSameComponent 1 (processBrauer (brauerSeed 1) frobSpecial.lhs) firstIndex secondIndex
      = matchingSameComponent 1 (processBrauer (brauerSeed 1) frobSpecial.rhs) firstIndex secondIndex := by
  decide

/-- ★ **The special law `μδ = 1` fired in a boundary two wider is convertible** — the sentinel through the pad
congruence.  Its two sides carry UNEQUAL loop counts at the seed (`1` vs `0`), so the Brauer loops-based pad payoff
would be inapplicable; the leaner partition payoff carries it because the partitions AGREE.  Genuinely
boundary-changing: boundary `1 → 3`. -/
theorem spiderConv_special_inWiderBoundary : SpiderConv 3 frobSpecial.lhs frobSpecial.rhs :=
  spiderConv_relation_inWiderBoundary 1 2 frobSpecial.lhs frobSpecial.rhs
    (BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1)))
    (BrauerWordInRange.nil 1) rfl
    (fun firstIndex secondIndex hfirst hsecond => specialBaseView_ordered firstIndex hfirst secondIndex hsecond)

/-- The frobenius-law's base partition-view agreement at boundary `2`, in the `Nat.decidableBallLT`-friendly order. -/
private theorem frobLeftBaseView_ordered : ∀ firstIndex,
    firstIndex < 2 + (processBrauer (brauerSeed 2) frobLeft.lhs).openWires.length → ∀ secondIndex,
    secondIndex < 2 + (processBrauer (brauerSeed 2) frobLeft.lhs).openWires.length →
    matchingSameComponent 2 (processBrauer (brauerSeed 2) frobLeft.lhs) firstIndex secondIndex
      = matchingSameComponent 2 (processBrauer (brauerSeed 2) frobLeft.rhs) firstIndex secondIndex := by
  decide

/-- ★ **The Frobenius law `(μ⊗1)(1⊗δ) = δμ` fired in a boundary one wider is convertible** — via the pad congruence.
Genuinely boundary-changing: boundary `2 → 3`. -/
theorem spiderConv_frobLeft_inWiderBoundary : SpiderConv 3 frobLeft.lhs frobLeft.rhs :=
  spiderConv_relation_inWiderBoundary 2 1 frobLeft.lhs frobLeft.rhs
    (BrauerWordInRange.cons (comultAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (multAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 2)))
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))
    rfl
    (fun firstIndex secondIndex hfirst hsecond => frobLeftBaseView_ordered firstIndex hfirst secondIndex hsecond)

/-- ★ **The in-context identification is non-vacuous.**  The special law fired in the wider boundary `3` relates
GENUINELY DISTINCT words — the μ-after-δ bubble `[comultAt 0, multAt 0]` and the empty diagram `[]` — as the SAME
boundary partition.  So the pad congruence makes real boundary-changing identifications, not only reflexive ones. -/
theorem spiderConv_special_inWiderBoundary_identifies_distinct :
    frobSpecial.lhs ≠ frobSpecial.rhs ∧ SpiderConv 3 frobSpecial.lhs frobSpecial.rhs :=
  ⟨by decide, spiderConv_special_inWiderBoundary⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the spider PARTITION pad congruence is SHIPPED.**  The whole-word right-pad simulation
`processBrauer_rightPadSim` is reused VERBATIM over the spider alphabet (it is engine-generic over `List BrauerAtom`);
the leaner payoff `matchingSameComponent_ofSpiderRightPadSimPair` transports the boundary partition view across the pad
WITHOUT a loop hypothesis (so the special row `μδ = 1`, whose two sides carry unequal loops but equal partition, is
carried); `spiderConv_relation_inWiderBoundary` packages a relation fired in ANY wider boundary (offset `0`) as a
`SpiderConv` via the empty-prefix whisker.  NON-VACUOUS: the special law (`spiderConv_special_inWiderBoundary`, boundary
`1 → 3`) and the Frobenius law (`spiderConv_frobLeft_inWiderBoundary`, boundary `2 → 3`) are convertible in strictly
wider boundaries.  `= true`. -/
def fxFrob_hasSpiderPadCongruence : Bool := true

/-- ★ **Honesty marker — the after-arbitrary-prefix leg is SHIPPED (loops-free re-homing, FROB-4).**  The
after-arbitrary-prefix leg — a relation whiskered after ANY prefix — is now closed in
`Frobenius/SpiderAfterPrefix.lean`: `spiderConv_relation_afterPrefix` feeds the two boundary-partition `whisker` legs
from the loops-free functoriality port `processBrauer_forgetView_eq_ofCanonicalViewParts` (the loops-free re-homing of
the Brauer two-word functoriality, legs length + view kept, leg loops dropped through the cloned view-parts transfer
bricks).  So the special row `μδ = 1` (unequal canonical loops) is no longer an obstruction.  The residual now
narrows to the NONZERO-OFFSET (`shiftBrauerWord` left pad) supply of the canonical view parts at a boundary-CHANGING
post-prefix width; a boundary-PRESERVING prefix reuses the relation's own seed facts prefix-independently.  `= true`. -/
def fxFrob_hasSpiderAfterPrefixContext : Bool := true

end FX1Poly.Polygraph
