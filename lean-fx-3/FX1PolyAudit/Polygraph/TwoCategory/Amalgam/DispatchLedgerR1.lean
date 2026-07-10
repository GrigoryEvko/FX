import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchLedgerR1

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DispatchLedgerR1 — zero-axiom gate for the WP-AMALG-2 r1 ledger
(B4)

Per-declaration zero-axiom gate: the four ledger markers (r1 bricks shipped, the SN-non-modularity caveat, the
surviving jams recorded, and the ledger itself).  Each is a hypothesis-free `Bool` def.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r1BricksShipped
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_snNonModularCaveat
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r1JamsRecorded
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasDispatchLedgerR1

end FX1PolyAudit
