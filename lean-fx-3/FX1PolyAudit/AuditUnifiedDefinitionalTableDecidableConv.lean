import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.UnifiedDefinitionalTableDecidableConv

/-! # FX1PolyAudit/AuditUnifiedDefinitionalTableDecidableConv — zero-axiom gate, the union table capstone

Per-declaration zero-axiom gate for
`FX1Poly/Core/Substrate/Univalence/UnifiedDefinitionalTableDecidableConv.lean`: the FULL
definitional-univalence rewrite system — the size-shrinking univalence row AND the size-growing transport
row — shipped over ONE two-row table with decidable conversion off the generic `StepOverTable` engine, the
table-native replacement for the bespoke `UnifiedDefinitionalRowConfluence` capstone.

The compatibility firing fact (`univalenceShapedDemoRule_firingPreservesProductFormerCount`), the
certificates (`unifiedDefinitionalTable_isWf`, `unifiedDefinitionalTable_isScopeUniform`), the generic
orthogonal confluence (`unifiedDefinitionalTable_isConfluent`), the per-step lexicographic decrease over the
two-row table relation (`stepOverUnifiedTable_decreasesLex`), the generic lex-SN combinator
(`unifiedDefinitionalTable_isStronglyNormalizing`), and the generic decidable conversion
(`unifiedDefinitionalTableConv_decidable`) must all be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega` — including the `Nat.zero_add` step in the product-former preservation. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_firingPreservesProductFormerCount
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalTable_isWf
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalTable_isConfluent
#assert_no_axioms FX1Poly.Core.stepOverUnifiedTable_decreasesLex
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalTable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.unifiedDefinitionalTableConv_decidable
#assert_no_axioms FX1Poly.Core.fxUnifiedDefinitionalConv_shippedOverOneTableAsData

end FX1PolyAudit
