import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionModalityFragment

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesion.CohesionModalityFragment — zero-axiom gate (thin fragment)

Per-declaration zero-axiom gate for the walking-cohesion thin per-modality fragment: the shape / flat / sharp
endo-hom collapses (idempotence doing real work) and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cohesionShapeLeftUnitConvId
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeRightUnitConvId
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeUnitComposites_viaIdempotence
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeHom_thinOnRepresentatives
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatLeftCounitConvId
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatRightCounitConvId
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatCounitComposites_viaIdempotence
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatHom_thinOnRepresentatives
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpLeftUnitConvId
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpRightUnitConvId
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpUnitComposites_viaIdempotence
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpHom_thinOnRepresentatives
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasModalityFragmentThinness

end FX1PolyAudit
