import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCellConverseLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCellConverseLedger — zero-axiom gate for the r12 cell-converse
LEDGER honesty markers (WP-AMALG-2 r12)

Per-declaration zero-axiom gate for the three r12 ledger markers (the cell converse ships forward + gen backward
section, the node accounting, the masters hold).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r12CellConverseShips
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r12NodeAccounting
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r12MastersHold

end FX1PolyAudit
