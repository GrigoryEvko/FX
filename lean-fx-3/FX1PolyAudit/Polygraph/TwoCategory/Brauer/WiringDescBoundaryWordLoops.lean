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

-- B2: the position-general cup loops-zero step
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cup_loops_atPos

-- B2: the three phase loops-zero folds (D2 crossing, D3 cup, D4 cap) + the distinctness carrier
#assert_no_axioms FX1Poly.Polygraph.crossingWord_loops_zero
#assert_no_axioms FX1Poly.Polygraph.cupWord_loops_zero
#assert_no_axioms FX1Poly.Polygraph.capWord_loops_zero_ofDistinct
#assert_no_axioms FX1Poly.Polygraph.crossingWord_preserves_distinct

-- B2: THE WELD -- the boundary word closes zero loops, and the full loops field
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_ofForm
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_general
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_general_wildThrough
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_general_wildCupLoop

-- B2: the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundaryWordLoopsField

end FX1PolyAudit
