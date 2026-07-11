import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCellRoundTripLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCellRoundTripLedger — zero-axiom gate for the r13 LEDGER
(the backward round-trip + payload-zip ship / master re-audit / #2043 state markers, WP-AMALG-2 r13)

Per-declaration zero-axiom gate for the three r13 ledger markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r13BackwardRoundTripAndZipShip
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r13MasterReauditHolds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r13StateLedger

end FX1PolyAudit
