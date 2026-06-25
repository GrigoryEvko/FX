import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.SliceCategory

/-! # FX1PolyAudit/AuditTier0ContextSliceCategory — zero-axiom gate for context-2's slice-category residue

Per-declaration zero-axiom gate for `context-2`'s strictly context-side substrate
(`FX1Poly/Tier0/Context/SliceCategory.lean`): the slice category `C/U` as a genuine
`RawCategory` (slice-morphism extensionality, identity, composition, all three laws PROVED);
the generic display nat-trans; both families PROVED functorial (`*_isFunctorial`); the
Grothendieck bijection `SliceObject ≃ UniverseElement` (`sliceToElement`/`elementToSlice` +
round-trips); the generic display's PROVED universal property (classifies every universe
element bijectively, stable under reindexing) plus the honest degeneracy
(`genericDisplay_component_surjective`); the vertical 2-cell structure on slice nat-transes
(`idTrans`/`vcomp` + componentwise unit laws); and the wiring over the FX context axis.

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

-- The two families are genuine functors (paying for "functorial")
#assert_no_axioms FX1Poly.Tier0.sliceProjectionFamily_isFunctorial
#assert_no_axioms FX1Poly.Tier0.universeConstantFamily_isFunctorial

-- The slice category is the category of elements of U (Grothendieck bijection)
#assert_no_axioms FX1Poly.Tier0.UniverseElement
#assert_no_axioms FX1Poly.Tier0.sliceToElement
#assert_no_axioms FX1Poly.Tier0.elementToSlice
#assert_no_axioms FX1Poly.Tier0.elementToSlice_sliceToElement
#assert_no_axioms FX1Poly.Tier0.sliceToElement_elementToSlice

-- The generic display's proved universal property (+ the honest degeneracy)
#assert_no_axioms FX1Poly.Tier0.genericDisplay_component_elementToSlice
#assert_no_axioms FX1Poly.Tier0.genericDisplay_component_eq_classifier
#assert_no_axioms FX1Poly.Tier0.genericDisplay_classifier_reconstructs
#assert_no_axioms FX1Poly.Tier0.genericDisplay_component_surjective
#assert_no_axioms FX1Poly.Tier0.SliceObject.reindex
#assert_no_axioms FX1Poly.Tier0.genericDisplay_component_reindex

-- The vertical 2-cell structure on slice natural transformations
#assert_no_axioms FX1Poly.Tier0.SliceNatTrans.idTrans
#assert_no_axioms FX1Poly.Tier0.SliceNatTrans.vcomp
#assert_no_axioms FX1Poly.Tier0.SliceNatTrans.idTrans_component
#assert_no_axioms FX1Poly.Tier0.SliceNatTrans.vcomp_component
#assert_no_axioms FX1Poly.Tier0.SliceNatTrans.idTrans_vcomp_component
#assert_no_axioms FX1Poly.Tier0.SliceNatTrans.vcomp_idTrans_component

end FX1PolyAudit
