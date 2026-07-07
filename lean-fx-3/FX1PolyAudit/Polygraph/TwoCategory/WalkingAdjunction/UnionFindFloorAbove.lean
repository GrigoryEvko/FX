import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.UnionFindFloorAbove

/-! # FX1PolyAudit/…/UnionFindFloorAbove — zero-axiom gate

Per-declaration zero-axiom gate for the at-or-above-floor union-find root locality (the dual of the shipped
below-floor locality): under floor-homogeneity of the edges, an at-or-above-floor node keeps its root at or
above the floor — the cup-leg root-separation kernel of the valley classification's cup direction.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindParent_ge
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot_ge_of_edgesPreserveFloor
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_ge_of_edgesPreserveFloor
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasUnionFindFloorAbove

end FX1PolyAudit
