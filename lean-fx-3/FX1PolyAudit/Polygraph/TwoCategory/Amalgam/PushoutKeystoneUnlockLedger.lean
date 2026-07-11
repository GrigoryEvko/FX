import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutKeystoneUnlockLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutKeystoneUnlockLedger — zero-axiom gate for the r11 ledger
markers (WP-AMALG-2 r11, B5)

Per-declaration zero-axiom gate for the three r11 ledger honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r11KeystoneUnlocksTwoNearestNodes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r11NodeAccounting
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r11MastersHold

end FX1PolyAudit
