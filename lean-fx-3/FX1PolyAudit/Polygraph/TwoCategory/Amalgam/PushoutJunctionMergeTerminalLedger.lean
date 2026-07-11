import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutJunctionMergeTerminalLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutJunctionMergeTerminalLedger — zero-axiom gate for the r22
TERMINAL junction-merge ledger (WP-AMALG-2 r22, arm b′ / B3)

Per-declaration zero-axiom gate for the terminal reader-arm scoreboard (3 DONE / 0 MECHANICAL / 2 JAM-A), the both-arms
completion, the witness-agreement probe, the masters-stay-walled + close-criterion-false theorem, and the r22 WP-AMALG-3
inheritance ledger.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutReaderArmStatusR22
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutReaderArmStatusR22_scoreboard
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerJunctionMergeBothArmsShip
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerJunctionMuWitnessesAgree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.junctionMergeTerminalMastersStayWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_wpAmalg3InheritanceLedgerR22
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wpAmalg3InheritsR22
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushout2043StateAfterArmBPrime

end FX1PolyAudit
