import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerLedger — zero-axiom gate (WP-BRAUER terminal T2/T3)

Per-declaration zero-axiom gate for the terminal round's T2 readback target + T3 ledger: the general readback
`Prop` (`BrauerCrossingOnlyReadback`), its fresh four-strand non-vacuity instance, the readback residual marker,
the MACHINE-CHECKED completeness decomposition (`fxBrauer_terminalDecomposition`), and the terminal-ledger marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- T2: the general readback target Prop + fresh non-vacuity instance + residual marker
#assert_no_axioms FX1Poly.Polygraph.BrauerCrossingOnlyReadback
#assert_no_axioms FX1Poly.Polygraph.brauerCrossingOnlyReadback_instance_fourStrand
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingOnlyReadback

-- T3: the machine-checked terminal decomposition + the ledger marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_terminalDecomposition
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTerminalLedger

end FX1PolyAudit
