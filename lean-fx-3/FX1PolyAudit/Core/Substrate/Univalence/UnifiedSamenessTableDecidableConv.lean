import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.UnifiedSamenessTableDecidableConv

/-! # FX1PolyAudit/AuditUnifiedSamenessTableDecidableConv
    — zero-axiom gate for the FULL definitional-sameness table

Per-declaration zero-axiom gate for
`FX1Poly/Core/Substrate/Univalence/UnifiedSamenessTableDecidableConv.lean`: the three orthogonal
definitional-sameness rules — univalence (size-shrinking), transport (size-growing), and transpension gel-β
(subterm projection) — unified as ONE three-row table `[univalenceShapedDemoRule, sizeGrowingTransportDemoRule,
gelBetaIotaRow]`, with decidable conversion read off the generic `StepOverTable` engine.  This is the concrete
object behind OP3-SAMENESS: univalence and parametricity decided by ONE computation.

The new gel-β product-former monotonicity lemma (`gelBetaIotaRow_firingProductFormerLe`), the certificates
(`unifiedSamenessTable_isWf`, `unifiedSamenessTable_isScopeUniform`), the generic confluence
(`unifiedSamenessTable_isConfluent`), the joint lexicographic decrease over the table relation
(`stepOverSamenessTable_decreasesLex`), the generic SN combinator (`unifiedSamenessTable_isStronglyNormalizing`),
and the generic decidable conversion (`unifiedSamenessTableConv_decidable`) must all be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — the `firesOn?` head inversions, the
`RawSize` / `productFormerCount` arithmetic, and the `Nat.lt_of_le_of_ne` lex combination stay axiom-clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.gelBetaIotaRow_firingProductFormerLe
#assert_no_axioms FX1Poly.Core.unifiedSamenessTable_isWf
#assert_no_axioms FX1Poly.Core.unifiedSamenessTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.unifiedSamenessTable_isConfluent
#assert_no_axioms FX1Poly.Core.stepOverSamenessTable_decreasesLex
#assert_no_axioms FX1Poly.Core.unifiedSamenessTable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.unifiedSamenessTableConv_decidable
#assert_no_axioms FX1Poly.Core.fxUnifiedSamenessConv_shippedOverOneTableAsData

end FX1PolyAudit
