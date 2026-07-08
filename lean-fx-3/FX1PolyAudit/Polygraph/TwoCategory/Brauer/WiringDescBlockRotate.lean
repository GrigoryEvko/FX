import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBlockRotate

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBlockRotate — zero-axiom gate (KEYSTONE4 leg 1)

Per-declaration zero-axiom gate for the combinatorial legs of the cross-order trace correspondence: the
`sigma`-equivariance of the decoded arc trace (`wiringArcEvents_map`, brick B1) and the two fresh output-block
images under `blockRotate` (`rangeMapAdd_map_blockRotate_first` / `_second`, brick B2), plus the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- brick B1: the arc-trace decode is sigma-equivariant
#assert_no_axioms FX1Poly.Polygraph.wiringArcEvents_map

-- brick B2: the two fresh output-block images under blockRotate
#assert_no_axioms FX1Poly.Polygraph.rangeMapAdd_map_blockRotate_first
#assert_no_axioms FX1Poly.Polygraph.rangeMapAdd_map_blockRotate_second

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringArcEventsBlockRotateLegs

end FX1PolyAudit
