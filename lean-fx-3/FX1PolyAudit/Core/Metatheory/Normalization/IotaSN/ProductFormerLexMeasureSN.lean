import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.IotaSN.ProductFormerLexMeasureSN

/-! # FX1PolyAudit/AuditProductFormerLexMeasureSN — zero-axiom gate for the relocated generic measures

Per-declaration zero-axiom gate for
`FX1Poly/Core/Metatheory/Normalization/IotaSN/ProductFormerLexMeasureSN.lean`: the type-complexity measure
`RawTerm.productFormerCount` (a count of `gen_productCode` nodes) with its node-weight `rfl` lemmas, and the
generic `lex(primaryMeasure, RawTerm.size)` strong-normalization combinator
`wellFounded_of_lexMeasureStrictlyDecreasing`.  These were relocated here as the generic ingredients that the
now-retired bespoke `SizeGrowingTransportRowSN` / `LexJointRowSN` scaffolding was built on; they are reused
by the table-native definitional-univalence files.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.productFormerCount
#assert_no_axioms FX1Poly.Core.RawTermChildren.productFormerCount
#assert_no_axioms FX1Poly.Core.productFormerCount_glueElim
#assert_no_axioms FX1Poly.Core.productFormerCount_pair
#assert_no_axioms FX1Poly.Core.productFormerCount_productCode
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasureStrictlyDecreasing

end FX1PolyAudit
