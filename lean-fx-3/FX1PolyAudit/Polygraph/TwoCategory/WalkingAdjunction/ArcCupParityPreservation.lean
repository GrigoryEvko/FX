import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupParityPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupParityPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cup step's preservation of the opposite-class
strand-endpoint invariant: the class-stable splice backmap and the old/leg dispatch.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcEndTokenClass_cupBackmap
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenParity_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupParityPreservation

end FX1PolyAudit
