import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescConnectivityMono — zero-axiom gate (KEYSTONE8 ingredient)

Per-declaration zero-axiom gate for the connectivity-monotone half of the same-component window-locality subsystem:
the generic arc fold (`stepWiringArcs_isSameComponent_ofBase`), the single-step
(`stepWiring_isSameComponent_ofBase`), the whole-fold (`processBrauer_isSameComponent_ofBase`), and the honesty
marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_isSameComponent_ofBase
#assert_no_axioms FX1Poly.Polygraph.stepWiring_isSameComponent_ofBase
#assert_no_axioms FX1Poly.Polygraph.processBrauer_isSameComponent_ofBase

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasConnectivityMonotonicity

end FX1PolyAudit
