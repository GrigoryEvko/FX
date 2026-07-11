import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcStrandClosureFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcStrandClosureFold — zero-axiom gate
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE/count substrate)

Per-declaration zero-axiom gate for the closed-strand fold ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringIsSameComponent_stepArcAtom_queriesStable
#assert_no_axioms FX1Poly.Polygraph.stringArcStrandClosure_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.stringArcStrandClosure_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.stringIsSameComponent_processArcSpine_queriesStable
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcStrandClosureFold

end FX1PolyAudit
