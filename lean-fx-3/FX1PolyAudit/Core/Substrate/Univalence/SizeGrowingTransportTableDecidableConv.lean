import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.SizeGrowingTransportTableDecidableConv

/-! # FX1PolyAudit/AuditSizeGrowingTransportTableDecidableConv — zero-axiom gate, size-growing rule as data

Per-declaration zero-axiom gate for
`FX1Poly/Core/Substrate/Univalence/SizeGrowingTransportTableDecidableConv.lean`: the SIZE-GROWING
definitional rule `glueElim(productCode A B) ↝ pair(glueElim A, glueElim B)` shipped over the table as the
row `sizeGrowingTransportDemoRule`, with decidable conversion read off the generic `StepOverTable` engine.

The row's adequacy (`sizeGrowingTransportDemoRule_firesOnProductCode`), the certificates
(`transportTable_isWf`, `sizeGrowingTransportDemoRule_isScopeUniform`, `transportTable_isScopeUniform`),
the generic confluence (`transportTable_isConfluent`), the bespoke-as-data product-former measure decrease
over the table relation (`sizeGrowingTransportDemoRule_firingProductFormerDrop`,
`stepOverTransportTable_productFormerStrictlyDecreases`), the generic measure-SN combinator
(`transportTable_isStronglyNormalizing`), and the generic decidable conversion
(`transportTableConv_decidable`) must all be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemoRule_firesOnProductCode
#assert_no_axioms FX1Poly.Core.transportTable_isWf
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemoRule_isScopeUniform
#assert_no_axioms FX1Poly.Core.transportTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.transportTable_isConfluent
#assert_no_axioms FX1Poly.Core.sizeGrowingTransportDemoRule_firingProductFormerDrop
#assert_no_axioms FX1Poly.Core.stepOverTransportTable_productFormerStrictlyDecreases
#assert_no_axioms FX1Poly.Core.transportTable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.transportTableConv_decidable
#assert_no_axioms FX1Poly.Core.fxSizeGrowingTransportConv_shippedOverTableAsData

end FX1PolyAudit
