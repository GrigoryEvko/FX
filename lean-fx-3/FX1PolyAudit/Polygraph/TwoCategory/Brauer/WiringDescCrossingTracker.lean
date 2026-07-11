import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingTracker

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCrossingTracker — zero-axiom gate (BRAUER r23, the
GENERAL non-seed crossing open-wire tracker — the r19 fresh-id bridge)

Per-declaration zero-axiom gate: the public adjacent-swap / crossing open-wire get re-proofs
(`natListGetAt_applyAdjacentSwap`, `natListGetAt_crossingReplaceBlock`, `stepWiringCrossing_openWire_get`), the
single-crossing correspondence (`stepWiringCrossing_openWire_pointwiseSwap`), the swap-fold pointwise-preservation
kit (`natListPointwiseSameComponent_applyAdjacentSwap`, `natListPointwiseSameComponent_foldl`), the GENERAL tracker
(`crossingWordFold_openWire_sameComponent_incomingPort`), its seed corollary
(`crossingWordFold_openWire_sameComponent_incomingPort_seed`), the non-seed post-cap firing
(`crossingWordFold_openWire_sameComponent_incomingPort_postCap`, `…_postCap_decided`), and the honesty marker
(`fxBrauer_hasGeneralCrossingTracker`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_applyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_crossingReplaceBlock
#assert_no_axioms FX1Poly.Polygraph.stepWiringCrossing_openWire_get
#assert_no_axioms FX1Poly.Polygraph.stepWiringCrossing_openWire_pointwiseSwap
#assert_no_axioms FX1Poly.Polygraph.natListPointwiseSameComponent_applyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.natListPointwiseSameComponent_foldl
#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWire_sameComponent_incomingPort
#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWire_sameComponent_incomingPort_seed
#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWire_sameComponent_incomingPort_postCap
#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWire_sameComponent_incomingPort_postCap_decided
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasGeneralCrossingTracker

end FX1PolyAudit
