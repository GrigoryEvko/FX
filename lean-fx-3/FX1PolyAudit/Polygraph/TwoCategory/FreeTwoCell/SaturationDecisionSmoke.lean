import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SaturationDecisionSmoke

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SaturationDecisionSmoke — zero-axiom gate

Per-declaration zero-axiom gate for the computed saturation-decision smoke on the
Eckmann–Hilton bubble signature.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bubbleTwoCellDecEq
#assert_no_axioms FX1Poly.Polygraph.bubbleSaturationExhausts
#assert_no_axioms FX1Poly.Polygraph.bubbleTraceDecision_acceptsSwappedTraces
#assert_no_axioms FX1Poly.Polygraph.bubbleTraceDecision_rejectsShorterTrace

end FX1PolyAudit
