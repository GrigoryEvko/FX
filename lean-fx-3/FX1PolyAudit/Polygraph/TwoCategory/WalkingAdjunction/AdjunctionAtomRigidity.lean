import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionAtomRigidity

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/AdjunctionAtomRigidity — zero-axiom gate

Per-declaration zero-axiom gate for seed atom rigidity: generator uniqueness and the
read-off determination of chained spine atoms.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionTwoCell_unique
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtom_eq_of_readOffs

end FX1PolyAudit
