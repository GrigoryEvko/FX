import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCoreSwapBundle

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCoreSwapBundle — zero-axiom gate (KEYSTONE4 leg 4)

Per-declaration zero-axiom gate for the block-swap `MatchingComponentSim` bundle and the boundary-diagram
commutation, both discharged modulo the single `openMap` hypothesis.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_componentSim_ofOpenMap
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_extract_ofOpenMap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescCoreSwapBundleModuloOpenMap

end FX1PolyAudit
