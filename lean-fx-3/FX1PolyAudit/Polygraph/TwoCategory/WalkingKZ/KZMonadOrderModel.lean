import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZMonadOrderModel

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingKZ.KZMonadOrderModel — zero-axiom gate (the KZ hom-order model)

Per-declaration zero-axiom gate for the walking-KZ hom-order model: the pointwise order `mapLE`, its decidability,
the poset laws, the non-triviality smokes, and the three order-monotonicity closures.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mapLE
#assert_no_axioms FX1Poly.Polygraph.decMapLE
#assert_no_axioms FX1Poly.Polygraph.mapLE_refl
#assert_no_axioms FX1Poly.Polygraph.mapLE_of_eq
#assert_no_axioms FX1Poly.Polygraph.mapLE_trans
#assert_no_axioms FX1Poly.Polygraph.mapLE_antisymm
#assert_no_axioms FX1Poly.Polygraph.mapLE01
#assert_no_axioms FX1Poly.Polygraph.not_mapLE10
#assert_no_axioms FX1Poly.Polygraph.composeMap_mapLE_left
#assert_no_axioms FX1Poly.Polygraph.composeMap_mapLE_right
#assert_no_axioms FX1Poly.Polygraph.embedLocalMap_mapLE
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasHomOrderModel

end FX1PolyAudit
