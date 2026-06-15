import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.SliceCategory

/-! # FX1PolyAudit/AuditTier0ContextSliceCategory — zero-axiom gate for context-2's slice-category residue

Per-declaration zero-axiom gate for `context-2`'s strictly context-side substrate
(`FX1Poly/Tier0/Context/SliceCategory.lean`): the slice category `C/U` as a genuine
`RawCategory` (slice-morphism extensionality, identity, composition, and the assembled
category with all three laws PROVED) plus the generic display — the universal natural
transformation from the projection family to the constant-universe family whose
naturality square IS the slice triangle's commute condition — and the wiring over the
FX context axis's substitution category.

The Uemura BIJECTION proper (type-formers ↔ representable natural transformations) is the
cross-axis `×type` deliverable and is deferred to `fib-1`; only the context-category
substrate it lives in is gated here.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The slice category C/U is a genuine RawCategory
#assert_no_axioms FX1Poly.Tier0.SliceMorphism.ext
#assert_no_axioms FX1Poly.Tier0.SliceObject.identityMorphism
#assert_no_axioms FX1Poly.Tier0.SliceMorphism.compose
#assert_no_axioms FX1Poly.Tier0.sliceCategory

-- The generic display (the universal family + its naturality square)
#assert_no_axioms FX1Poly.Tier0.sliceProjectionFamily
#assert_no_axioms FX1Poly.Tier0.universeConstantFamily
#assert_no_axioms FX1Poly.Tier0.genericDisplayNatTrans

-- Wired over the FX context axis's substitution category
#assert_no_axioms FX1Poly.Tier0.fxSubstSliceCategory
#assert_no_axioms FX1Poly.Tier0.fxSubstGenericDisplay
#assert_no_axioms FX1Poly.Tier0.fxSubstSliceCategory_object

end FX1PolyAudit
