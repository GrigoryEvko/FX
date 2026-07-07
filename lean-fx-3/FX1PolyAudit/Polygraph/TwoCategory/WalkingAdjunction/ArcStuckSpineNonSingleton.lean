import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineNonSingleton

/-! # FX1PolyAudit/…/ArcStuckSpineNonSingleton — zero-axiom gate

Per-declaration zero-axiom gate for the STUCK-case non-singleton witness: two DISTINCT four-atom spines over
the boundary `left`, both STUCK (one bottom port, one top port — no seed cap, no boundary cup — cup-headed,
cap-tailed), share the WHOLE `FullArcStructure`.  So `arcStructureOf` is not injective on stuck spines and
the dichotomy's STUCK residual is genuine, not a `refl`.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.doubleSnake_atomReadoff
#assert_no_axioms FX1Poly.Polygraph.nestedSnake_atomReadoff
#assert_no_axioms FX1Poly.Polygraph.doubleSnake_isStuckByPorts
#assert_no_axioms FX1Poly.Polygraph.nestedSnake_isStuckByPorts
#assert_no_axioms FX1Poly.Polygraph.stuckSpines_distinct
#assert_no_axioms FX1Poly.Polygraph.stuckSpines_arcStructure_eq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStuckSpineNonSingleton

end FX1PolyAudit
