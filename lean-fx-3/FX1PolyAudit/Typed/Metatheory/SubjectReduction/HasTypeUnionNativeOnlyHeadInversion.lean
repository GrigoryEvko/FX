import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionNativeOnlyHeadInversion

/-! # FX1PolyAudit/AuditHasTypeUnionNativeOnlyHeadInversion — native-only head-inversion audit shard

Per-declaration zero-axiom gate for the `ofGrown`-free value-head inversion twins (TYTAB-DEPREC-1 /
TYTAB-2-RETIRE, #1706 / #1698): the native-only versions of the pair / option-Some / either-Inl / either-Inr
/ list-cons head inversions, each reflected through the redundancy equivalence (`toUnion` / `toNativeOnly`)
with NO `ofGrown` constructor and NO grown master.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.invertAtPairHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.invertAtOptionSomeHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.invertAtEitherInlHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.invertAtEitherInrHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnionNativeOnly.invertAtListConsHead

end FX1PolyAudit
