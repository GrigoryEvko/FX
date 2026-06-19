import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.GelBetaTableDecidableConv

/-! # FX1PolyAudit/AuditGelBetaTableDecidableConv — zero-axiom gate for table-native transpension gel-β Conv

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/GelBetaTableDecidableConv.lean`: the
transpension β-rule (gel-β, transpension-at-affine = the relational universe) `ungel(gel a b r) ↝ r`
shipped over the table as the row `gelBetaIotaRow`, with decidable conversion off the generic `StepOverTable`
engine.

The certificates (`gelBetaTable_isWf`, `gelBetaTable_isScopeUniform`), the generic confluence
(`gelBetaTable_isConfluent`), the one bespoke-as-data size lemma over the table relation
(`gelBetaIotaRow_firingSizeDrop`, `stepOverGelBetaTable_sizeStrictlyDecreases`), the generic SN combinator
(`gelBetaTable_isStronglyNormalizing`), and the generic decidable conversion (`gelBetaTableConv_decidable`)
must all be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — the
`firesOn?` head inversion + the `RawSize` transitivity chain stay axiom-clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.gelBetaTable_isWf
#assert_no_axioms FX1Poly.Core.gelBetaTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.gelBetaTable_isConfluent
#assert_no_axioms FX1Poly.Core.gelBetaIotaRow_firingSizeDrop
#assert_no_axioms FX1Poly.Core.stepOverGelBetaTable_sizeStrictlyDecreases
#assert_no_axioms FX1Poly.Core.gelBetaTable_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.gelBetaTableConv_decidable
#assert_no_axioms FX1Poly.Core.fxTranspensionGelBetaConv_shippedOverTableAsData

end FX1PolyAudit
