import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.UnivalenceTableDecidableConv

/-! # FX1PolyAudit/AuditUnivalenceTableDecidableConv — zero-axiom gate for table-native univalence Conv

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/UnivalenceTableDecidableConv.lean`:
definitional-univalence decidable conversion shipped OVER THE TABLE AS DATA, at the singleton table
`[univalenceShapedDemoRule]`.  This is the table-native replacement for the bespoke
`UnivalenceRowDecidableConv` — the rule is the shipped `IotaRuleDesc` row and every stage but SN is the
GENERIC `StepOverTable` engine.

The certificates (`univalenceTable_isWf`, `univalenceTable_isScopeUniform`), the generic confluence
(`univalenceTable_isConfluent`), the one bespoke-as-data size lemma over the table relation
(`univalenceShapedDemoRule_firingSizeDrop`, `stepOverUnivalenceTable_sizeStrictlyDecreases`), the generic
SN combinator (`univalenceTable_isStronglyNormalizing`), and the generic decidable conversion
(`univalenceTableConv_decidable`) must all be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — the `firesOn?` head inversion + `StepOverTable.rec` size analysis stay
axiom-clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.univalenceTable_isWf
#assert_no_axioms FX1Poly.Core.univalenceTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.univalenceTable_isConfluent
#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_firingSizeDrop
#assert_no_axioms FX1Poly.Core.stepOverUnivalenceTable_sizeStrictlyDecreases
#assert_no_axioms FX1Poly.Core.univalenceTable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.univalenceTableConv_decidable
#assert_no_axioms FX1Poly.Core.fxUnivalenceConv_shippedOverTableAsData

end FX1PolyAudit
