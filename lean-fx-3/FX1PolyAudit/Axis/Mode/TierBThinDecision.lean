import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.TierBThinDecision

/-! # FX1PolyAudit/Axis/Mode/TierBThinDecision — zero-axiom gate (Tier-B thin decision)

Per-declaration zero-axiom gate for the Tier-B thin mode-theory decision: the `ThinModeTheory` interface,
the generic `decideThinTwoCellConv`, the walking-involution instance, the classifier non-vacuity smokes, and
the Tier-B flag + its involution-marker pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ThinModeTheory
#assert_no_axioms FX1Poly.Polygraph.decideThinTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.fxInvolutionThinModeTheory
#assert_no_axioms FX1Poly.Polygraph.fxInvolutionThin_classify_double_eq_nil
#assert_no_axioms FX1Poly.Polygraph.fxInvolutionThin_classify_single_ne_nil
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasTierBThinDecision
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasTierBThinDecision_matchesInvolutionMarker

end FX1PolyAudit
