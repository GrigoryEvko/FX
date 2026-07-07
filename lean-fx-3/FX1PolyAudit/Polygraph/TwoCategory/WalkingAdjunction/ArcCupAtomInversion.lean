import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupAtomInversion

/-! # FX1PolyAudit/…/ArcCupAtomInversion — zero-axiom gate

Per-declaration zero-axiom gate for the boundary → cup-atom occurrence inversion: from a cup-arity
head arc-equal to the second spine, the second spine splits at a genuine cup occurrence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupAtomInversion
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupAtomInversion

end FX1PolyAudit
