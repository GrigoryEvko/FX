import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesion.CohesionDecision — zero-axiom gate (decision modulo thinness)

Per-declaration zero-axiom gate for the walking-cohesion decision: the thinness Prop, the local-posetality package,
the decision assembly and interface, the non-vacuity witnesses, and the honesty markers (the walled quadruple flag
included).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.CohesionThinness
#assert_no_axioms FX1Poly.Polygraph.CohesionLocalPosetality
#assert_no_axioms FX1Poly.Polygraph.decideCohesionConvViaThinness
#assert_no_axioms FX1Poly.Polygraph.cohesionSaturatedWordProblemModuloPosetality
#assert_no_axioms FX1Poly.Polygraph.cohesionDecision_genuineIdentification
#assert_no_axioms FX1Poly.Polygraph.cohesionDecision_genuineSeparation
#assert_no_axioms FX1Poly.Polygraph.decideCohesion_isTrue_ofPosetality
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasDecisionAssemblyModuloThinness
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasCohesionQuadrupleDecision

end FX1PolyAudit
