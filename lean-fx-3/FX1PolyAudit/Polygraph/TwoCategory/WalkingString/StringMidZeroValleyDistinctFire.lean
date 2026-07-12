import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyDistinctFire

/-! # FX1PolyAudit/…/WalkingString/StringMidZeroValleyDistinctFire — zero-axiom gate
(FC-3 r39, the genuine non-diagonal distinct-pair fire of the mid-width-`0` valley reducer)

Per-declaration zero-axiom gate for the distinct double-cap fire: the two firing orders
(`stringDistinctDoubleCapLeftFirst` / `stringDistinctDoubleCapRightFirst`), the genuine non-diagonal fire
`stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap`, the distinctness anchor
`stringDistinctDoubleCap_leftContextLengthsDiffer`, and the honesty marker.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` lines below are the trusted cross-check. -/

set_option maxHeartbeats 4000000

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringDistinctDoubleCapLeftFirst
#assert_no_axioms FX1Poly.Polygraph.stringDistinctDoubleCapRightFirst
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap
#assert_no_axioms FX1Poly.Polygraph.stringDistinctDoubleCap_leftContextLengthsDiffer
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyDistinctFire

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringDistinctDoubleCapLeftFirst
#print axioms FX1Poly.Polygraph.stringDistinctDoubleCapRightFirst
#print axioms FX1Poly.Polygraph.stringMidZeroValleyTraceEquiv_firesOnDistinctDoubleCap
#print axioms FX1Poly.Polygraph.stringDistinctDoubleCap_leftContextLengthsDiffer
#print axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyDistinctFire

end FX1PolyAudit
