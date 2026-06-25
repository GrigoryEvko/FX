import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.NativityLedger

/-! # FX1PolyAudit/AuditNativityLedger — NATIVE-61 nativity-ledger audit shard

Per-declaration zero-axiom gate for the nativity coverage ledger: every live generator is tabled
(typing-table row or reduction-table redex row), the split, and the ledger object.  Free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.liveGeneratorIsTabled
#assert_no_axioms FX1Poly.Typed.tabledSplitsIntoTypingOrRedexRow
#assert_no_axioms FX1Poly.Typed.NativityLedger
#assert_no_axioms FX1Poly.Typed.nativityLedgerHolds

end FX1PolyAudit
