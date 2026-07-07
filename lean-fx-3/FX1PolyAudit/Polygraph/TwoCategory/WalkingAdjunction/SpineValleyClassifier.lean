import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyClassifier

/-! # FX1PolyAudit/…/SpineValleyClassifier — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I commute/straighten classifier totality: the generator-source
mode read-offs, the `natWindowDistance = 0 → eq` arithmetic, the `orientationExcludedBothLegs` impossibility, and
the classifier case-totality must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupAtom_leftMidMode_isBase
#assert_no_axioms FX1Poly.Polygraph.capAtom_leftMidMode_isTip
#assert_no_axioms FX1Poly.Polygraph.natWindowDistance_eq_zero_imp_eq
#assert_no_axioms FX1Poly.Polygraph.orientationExcludedBothLegs_impossible
#assert_no_axioms FX1Poly.Polygraph.classifyAdjacentAtoms_ne_orientationExcluded
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyClassifierTotality

end FX1PolyAudit
