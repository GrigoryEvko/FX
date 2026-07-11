import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryWordLoops

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBoundaryWordLoops — zero-axiom gate (BRAUER r31)

Per-declaration zero-axiom gate for the boundary-word loops field: the B1 phase-zero eval probes
(`boundaryPhaseLoops_probe_monster` / `_adversarialB` / `_circleLift`) and the B1 marker.

Independent `#print axioms` (scratch) reported every decl as "does not depend on any axioms".  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- B1: the three phase-zeros, truth-probed by evaluation
#assert_no_axioms FX1Poly.Polygraph.boundaryPhaseLoops_probe_monster
#assert_no_axioms FX1Poly.Polygraph.boundaryPhaseLoops_probe_adversarialB
#assert_no_axioms FX1Poly.Polygraph.boundaryPhaseLoops_probe_circleLift

-- B1: the honesty marker for the re-export + probes
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundaryPhaseLoopsProbe

end FX1PolyAudit
