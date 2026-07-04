import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceNormalForm

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TraceNormalForm — zero-axiom gate

Per-declaration zero-axiom gate for the minimal-extraction trace normal form and its
soundness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isMeasureLexSmaller
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction
#assert_no_axioms FX1Poly.Polygraph.normalizeSpineWithFuel
#assert_no_axioms FX1Poly.Polygraph.normalizeSpine
#assert_no_axioms FX1Poly.Polygraph.normalizeSpineWithFuel_isTraceEquivalent
#assert_no_axioms FX1Poly.Polygraph.normalizeSpine_isTraceEquivalent

end FX1PolyAudit
