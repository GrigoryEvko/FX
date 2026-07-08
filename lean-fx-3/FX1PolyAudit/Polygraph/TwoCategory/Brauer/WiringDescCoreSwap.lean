import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCoreSwap

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCoreSwap — zero-axiom gate (KEYSTONE4 leg 3)

Per-declaration zero-axiom gate for the cross-order trace correspondences and the two ORDER-SWAP
`MatchingComponentSim` fields (the union-find join-order independence over the generic `stepWiring` engine):
`wiringDescCoreSwap_alphaTrace` / `wiringDescCoreSwap_betaTrace`, `wiringDescCoreSwap_componentComm`,
`wiringDescCoreSwap_loopsEq`, plus the helpers and honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- helpers
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_all_lt

-- the two per-block trace correspondences
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_alphaTrace
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_betaTrace

-- the two order-swap MatchingComponentSim fields
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_componentComm
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_loopsEq

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescCoreSwapTraces
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescCoreSwapOrderSwap

end FX1PolyAudit
