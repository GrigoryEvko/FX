import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutJunctionMergeCeilingLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutJunctionMergeCeilingLedger — zero-axiom gate for the r21 B3+B4
junction-merge ceiling ledger + WP-AMALG-3 inheritance ledger (WP-AMALG-2 r21, B3 + B4)

Per-declaration zero-axiom gate for the r21 reader-arm scoreboard, its 2/1/2 verdict, the junction-merge wall-hold, the
masters-stay-walled ledger, the #2043 state marker, and the WP-AMALG-3 inheritance ledger + its byte-intact witness.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutReaderArmStatusR21
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutReaderArmStatusR21_scoreboard
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftJunctionShipsArmBResidual
#assert_no_axioms FX1Poly.Polygraph.Amalgam.junctionMergeCeilingMastersStayWalled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushout2043StateAfterArmB
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_wpAmalg3InheritanceLedger
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wpAmalg3Inherits

end FX1PolyAudit
