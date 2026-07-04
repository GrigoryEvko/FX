import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.WhiskerReframing

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/WhiskerReframing — zero-axiom gate

Per-declaration zero-axiom gate for the whisker re-framing kit: the atom context extenders,
the boundary-cast algebra, and the atom re-framing pair.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAtom.extendLeft
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.extendRight
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.castBoundary_castBoundary
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.whiskerLeft_castBoundary
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.whiskerRight_castBoundary
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.ofCastLeft
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.whiskerLeft_atomFrame_convFull
#assert_no_axioms FX1Poly.Polygraph.whiskerRight_atomFrame_convFull
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasWhiskerReframingKit

end FX1PolyAudit
