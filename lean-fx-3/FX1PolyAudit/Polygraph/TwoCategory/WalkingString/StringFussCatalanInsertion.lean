import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanInsertion

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanInsertion — zero-axiom gate (FC-2 A)

Per-declaration zero-axiom gate for the generic index-shift lemma kit (L1–L6 + append helpers), the `natList*` /
`wireLabelListGetAt` bridges, the `advanceLabels` companion fold, the `sameLengths` cup/cap preservation, and the
non-crossing planarity predicate + base.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listGetAtD
#assert_no_axioms FX1Poly.Polygraph.listInsertAt
#assert_no_axioms FX1Poly.Polygraph.listRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.listInsertAt_zero
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_append_left
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_append_right
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_insertAt_below
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_insertAt_block
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_insertAt_above
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_removeTwoAt_below
#assert_no_axioms FX1Poly.Polygraph.listGetAtD_removeTwoAt_above
#assert_no_axioms FX1Poly.Polygraph.listInsertAt_length
#assert_no_axioms FX1Poly.Polygraph.listRemoveTwoAt_length
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_eq_listGetAtD
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_eq_listInsertAt
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_eq_listRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.wireLabelListGetAt_eq_listGetAtD
#assert_no_axioms FX1Poly.Polygraph.wireLabelListInsertAt
#assert_no_axioms FX1Poly.Polygraph.wireLabelListRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.advanceLabels
#assert_no_axioms FX1Poly.Polygraph.pathLabels_length_two
#assert_no_axioms FX1Poly.Polygraph.wireLabelListInsertAt_length
#assert_no_axioms FX1Poly.Polygraph.wireLabelListRemoveTwoAt_length
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_openWires_length
#assert_no_axioms FX1Poly.Polygraph.stringStepCap_openWires_length
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_sameLengths_cup
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_sameLengths_cap
#assert_no_axioms FX1Poly.Polygraph.StringNonCrossing
#assert_no_axioms FX1Poly.Polygraph.stringInitialNonCrossing
#assert_no_axioms FX1Poly.Polygraph.fxString_hasIndexShiftKit
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdvanceLabelsAndPlanarityKit
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientPreservationResidual

end FX1PolyAudit
