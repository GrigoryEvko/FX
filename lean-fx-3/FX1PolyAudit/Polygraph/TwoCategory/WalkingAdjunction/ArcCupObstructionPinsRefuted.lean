import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupObstructionPinsRefuted

/-! # FX1PolyAudit/…/ArcCupObstructionPinsRefuted — zero-axiom gate

Per-declaration zero-axiom gate for the refutation that the ∀-pins cup reduction is dead on the
obstruction: `arcCupOrbitPins_isFalse_onObstruction` (the front split forces the refuted
`arc leftTail @ 4 = arc rightTail @ 4`, so `arcCupOrbitWitness_ofWindowPinAndTailsCancel`'s premise
is unsatisfiable) must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitPins_isFalse_onObstruction
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupObstructionPinsRefuted

end FX1PolyAudit
