import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.IntervalNotConvRigidHeads

/-! # FX1PolyAudit/IntervalNotConvRigidHeads — interval-non-fibrancy discharge zero-axiom gate

Per-declaration zero-axiom gate for `FX1Poly/Typed/Metatheory/Validity/IntervalNotConvRigidHeads.lean`: every
rigid type-former head is NOT convertible to the interval (the `¬ UnionClassifierIsDimension` discharges the
fibrancy-requiring sites consume).  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.boolTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.natTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.unitTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.emptyTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.stepStar_intervalTypeCell_eq
#assert_no_axioms FX1Poly.Typed.productTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.sumTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.eitherTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.listTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.optionTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.idTypeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_not_conv_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.bridgeTypeCell_not_conv_intervalTypeCell

end FX1PolyAudit
