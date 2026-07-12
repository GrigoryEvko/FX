import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidCupSortResidual

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPositiveMidCupSortResidual — zero-axiom gate
(FC-3 r40)

Per-declaration zero-axiom gate for the doubly-positive wall's decomposition to ONE named cup-sort brick, the
colour-blind block reassembly gated on it, and the genuine distinct-double-cup fire.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based;
the independent `#print axioms` lines below are the trusted cross-check (they catch a `decide` silently degraded to
`sorryAx` and any `Lean.ofReduceBool` from `native_decide`). -/

namespace FX1PolyAudit

-- ★ W2: the single named sub-Prop the doubly-positive wall factors through
#assert_no_axioms FX1Poly.Polygraph.StringPositiveMidPureCupDeterminacy

-- ★★ W3: the colour-blind block reassembly gated on the ONE brick (the conjunction lemma)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidSameMatchingValleys_spineTraceEquiv

-- the distinct-double-cup fixtures (a genuine equal-matching distinct pair at positive mid-width 2)
#assert_no_axioms FX1Poly.Polygraph.stringGHGH
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidCupAtZeroOverGH
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidCupAtFourOverGHGH
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidCupAtTwoOverGH
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidCupAtZeroOverGHGH
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidDistinctDoubleCupLeftFirst
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidDistinctDoubleCupRightFirst

-- the two `decide` anchors (equal matching + distinct leftContext projections)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidDistinctDoubleCup_matchingsAgree
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidDistinctDoubleCup_leftContextLengthsDiffer

-- ★★ the genuine distinct-block fire (reassembly relates two DISTINCT spines, gated on the brick)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidReassembly_firesOnDistinctDoubleCup

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidCupSortResidual

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringPositiveMidSameMatchingValleys_spineTraceEquiv
#print axioms FX1Poly.Polygraph.stringPositiveMidDistinctDoubleCup_matchingsAgree
#print axioms FX1Poly.Polygraph.stringPositiveMidDistinctDoubleCup_leftContextLengthsDiffer
#print axioms FX1Poly.Polygraph.stringPositiveMidReassembly_firesOnDistinctDoubleCup
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidCupSortResidual

end FX1PolyAudit
