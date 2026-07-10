import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizationInductionLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizationInductionLedger — zero-axiom gate for the r7
ledger markers (WP-AMALG-2 r7, B4/B5)

Per-declaration zero-axiom gate for the three r7 ledger honesty markers (the no-flip verdict, the narrowed
residual, the stale-ledger correction flag).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r7ShipsCruxNoFlip
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r7NamedResidualTopInduction
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_dispatchLedgerLeftCoprojectionStaleFlag

end FX1PolyAudit
