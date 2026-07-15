import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.CohesionGlobalSectionsEdge

/-! # FX1PolyAudit/Axis/Mode/CohesionGlobalSectionsEdge — zero-axiom gate for the cohesion edge

Per-declaration zero-axiom gate for the cohesion EDGE (`FX1Poly/Axis/Mode/CohesionGlobalSectionsEdge.lean`):
the explicit-functor hom-adjunction + its derived bijectivity + bridges, the global-sections geometric morphism,
the cohesion adjoint quadruple + the edge + the locally-connected / local witnesses + the modalities, the trivial
witness + smokes, the bridge to `mode-13`'s `CohesiveQuadruple`, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The explicit-functor hom-adjunction + derived bijectivity + bridges
#assert_no_axioms FX1Poly.Axis.HomAdjunctionBetween
#assert_no_axioms FX1Poly.Axis.HomAdjunctionBetween.transpose_injective
#assert_no_axioms FX1Poly.Axis.HomAdjunctionBetween.transpose_surjective
#assert_no_axioms FX1Poly.Axis.identityHomAdjunctionBetween
#assert_no_axioms FX1Poly.Axis.HomAdjunctionBetween.toHomAdjunction
#assert_no_axioms FX1Poly.Axis.HomAdjunction.toBetween
#assert_no_axioms FX1Poly.Axis.HomAdjunctionBetween.toHomAdjunction_functors

-- The geometric morphism — the vertical edge
#assert_no_axioms FX1Poly.Axis.GeometricMorphism
#assert_no_axioms FX1Poly.Axis.identityGeometricMorphism
#assert_no_axioms FX1Poly.Axis.GeometricMorphism.transpose_injective

-- The cohesion adjoint quadruple + edge + shared functors + locally-connected / local + modalities
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.globalSectionsEdge
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.globalSectionsEdge_inverseImage
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.globalSectionsEdge_directImage
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.discrete_shared
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.globalSections_shared
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.isLocallyConnectedWitness
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.isLocalWitness
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.shapeModality
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.flatModality
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.sharpModality

-- The trivial witness + smokes
#assert_no_axioms FX1Poly.Axis.trivialCohesionQuadruple
#assert_no_axioms FX1Poly.Axis.trivialCohesionQuadruple_edge
#assert_no_axioms FX1Poly.Axis.trivialCohesionQuadruple_shapeModality
#assert_no_axioms FX1Poly.Axis.trivialCohesionQuadruple_flatModality
#assert_no_axioms FX1Poly.Axis.trivialCohesionQuadruple_sharpModality

-- The bridge to mode-13's CohesiveQuadruple
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.toCohesiveQuadruple
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.toCohesiveQuadruple_shapeModality
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.toCohesiveQuadruple_flatModality
#assert_no_axioms FX1Poly.Axis.CohesionAdjointQuadruple.toCohesiveQuadruple_sharpModality

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasCohesionAdjointQuadruple
#assert_no_axioms FX1Poly.Axis.fxMode_hasGlobalSectionsEdge
#assert_no_axioms FX1Poly.Axis.fxMode_hasCohesiveToposModelEdge
#assert_no_axioms FX1Poly.Axis.fxMode_hasGeometricMorphismLeftExact

end FX1PolyAudit
