import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingModel

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingModel — zero-axiom gate

Per-declaration zero-axiom gate for the two-level (two-colour) matching model: the wire labels, the coloured
diagram type and its reader, the four base + four two-level triangle collapses, the saturated-but-not-free
non-vacuity, the cross-level cell and its reads, the congruence bundle, the full soundness reduction (base and
coloured), and the three markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.WireLabel
#assert_no_axioms FX1Poly.Polygraph.wireLabelOfModality
#assert_no_axioms FX1Poly.Polygraph.pathLabels
#assert_no_axioms FX1Poly.Polygraph.ColouredDiagramType
#assert_no_axioms FX1Poly.Polygraph.colouredMatchingOf
#assert_no_axioms FX1Poly.Polygraph.matchingOf_stringTriangleF
#assert_no_axioms FX1Poly.Polygraph.matchingOf_stringTriangleGlo
#assert_no_axioms FX1Poly.Polygraph.matchingOf_stringTriangleGhi
#assert_no_axioms FX1Poly.Polygraph.matchingOf_stringTriangleH
#assert_no_axioms FX1Poly.Polygraph.colouredMatchingOf_stringTriangleF
#assert_no_axioms FX1Poly.Polygraph.colouredMatchingOf_stringTriangleGlo
#assert_no_axioms FX1Poly.Polygraph.colouredMatchingOf_stringTriangleGhi
#assert_no_axioms FX1Poly.Polygraph.colouredMatchingOf_stringTriangleH
#assert_no_axioms FX1Poly.Polygraph.stringSnakeF_generatorCount_ne_identity
#assert_no_axioms FX1Poly.Polygraph.stringSnakeF_saturatedButNotFree
#assert_no_axioms FX1Poly.Polygraph.stringCrossLevelCell
#assert_no_axioms FX1Poly.Polygraph.stringCrossLevel_generatorCount
#assert_no_axioms FX1Poly.Polygraph.stringGF_stringGH_labels
#assert_no_axioms FX1Poly.Polygraph.stringCrossLevel_colouredMatchingOf
#assert_no_axioms FX1Poly.Polygraph.StringMatchingSaturatedCongruence
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_matchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_colouredMatchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.fxString_hasTwoLevelMatchingModel
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPerLevelTriangleMatchingSoundness
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleSoundness

end FX1PolyAudit
