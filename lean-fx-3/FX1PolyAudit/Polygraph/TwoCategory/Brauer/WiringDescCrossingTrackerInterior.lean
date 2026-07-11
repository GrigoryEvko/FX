import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTrackerInterior

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCrossingTrackerInterior — zero-axiom gate (BRAUER r23, the
interior-phase crossing tracker, fired on the real six-phase fold)

Per-declaration zero-axiom gate: the interior-phase tracker
(`crossingWordFold_openWire_sameComponent_afterPrefix`), the adversarial-B corrected-reconstruction pin
(`reconstructAdversarialB_correctedFields`), the real top-phase firing
(`crossingTracker_topPhase_adversarialB`, `…_decided`), and the honesty marker
(`fxBrauer_hasInteriorCrossingTracker`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWire_sameComponent_afterPrefix
#assert_no_axioms FX1Poly.Polygraph.reconstructAdversarialB_correctedFields
#assert_no_axioms FX1Poly.Polygraph.crossingTracker_topPhase_adversarialB
#assert_no_axioms FX1Poly.Polygraph.crossingTracker_topPhase_adversarialB_decided
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInteriorCrossingTracker

end FX1PolyAudit
