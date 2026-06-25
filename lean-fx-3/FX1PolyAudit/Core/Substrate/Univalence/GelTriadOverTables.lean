import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.GelTriadOverTables

/-! # FX1PolyAudit/AuditGelTriadOverTables — zero-axiom gate for the gel triad over tables

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/GelTriadOverTables.lean`: the two
computational faces of transpension's `Gel A B R ≃ R` judgmental equivalence, both shipped over tables as
data — the iota/β computing half (`gelBetaTableConv_decidable`, decidable Conv by computation, already audited
separately) tied to the eta/retract half (`gelEtaRow ∈ etaRuleTable`, typed-directed, raw-inert, covered by
the generic eta-table SN).

The membership (`gelEtaRow_memTable`), the generic eta-table SN over the singleton
(`gelEtaTable_isStronglyNormalizing`), the scope-safety (`gelEtaTable_isScopeSafe`), the raw-inertness pin
(`gelEtaTable_rawInert`), and the four honesty markers must all be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.gelEtaRow_memTable
#assert_no_axioms FX1Poly.Core.gelEtaTable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.gelEtaTable_isScopeSafe
#assert_no_axioms FX1Poly.Core.gelEtaTable_rawInert
#assert_no_axioms FX1Poly.Core.fxTranspensionGelIota_decidableConvByComputation
#assert_no_axioms FX1Poly.Core.fxTranspensionGelEta_isTypedDirectedTableRow
#assert_no_axioms FX1Poly.Core.fxTranspensionGelEta_rawConvByComputation
#assert_no_axioms FX1Poly.Core.fxTranspensionGelTriad_shippedOverTablesAsData

end FX1PolyAudit
