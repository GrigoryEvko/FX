import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CohesionGlobalSectionsEdge

/-! # FX1PolyAudit/Tier0/Mode/CohesionGlobalSectionsEdge — zero-axiom gate for the cohesion edge

Per-declaration zero-axiom gate for the cohesion EDGE (`FX1Poly/Tier0/Mode/CohesionGlobalSectionsEdge.lean`):
the explicit-functor hom-adjunction + its derived bijectivity + bridges, the global-sections geometric morphism,
the cohesion adjoint quadruple + the edge + the locally-connected / local witnesses + the modalities, the trivial
witness + smokes, the bridge to `mode-13`'s `CohesiveQuadruple`, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The explicit-functor hom-adjunction + derived bijectivity + bridges
#assert_no_axioms FX1Poly.Tier0.HomAdjunctionBetween
#assert_no_axioms FX1Poly.Tier0.HomAdjunctionBetween.transpose_injective
#assert_no_axioms FX1Poly.Tier0.HomAdjunctionBetween.transpose_surjective
#assert_no_axioms FX1Poly.Tier0.identityHomAdjunctionBetween
#assert_no_axioms FX1Poly.Tier0.HomAdjunctionBetween.toHomAdjunction
#assert_no_axioms FX1Poly.Tier0.HomAdjunction.toBetween
#assert_no_axioms FX1Poly.Tier0.HomAdjunctionBetween.toHomAdjunction_functors

-- The geometric morphism — the vertical edge
#assert_no_axioms FX1Poly.Tier0.GeometricMorphism
#assert_no_axioms FX1Poly.Tier0.identityGeometricMorphism
#assert_no_axioms FX1Poly.Tier0.GeometricMorphism.transpose_injective

-- The cohesion adjoint quadruple + edge + shared functors + locally-connected / local + modalities
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.globalSectionsEdge
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.globalSectionsEdge_inverseImage
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.globalSectionsEdge_directImage
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.discrete_shared
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.globalSections_shared
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.isLocallyConnectedWitness
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.isLocalWitness
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeModality
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatModality
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.sharpModality

-- The trivial witness + smokes
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_edge
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_shapeModality
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_flatModality
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_sharpModality

-- The bridge to mode-13's CohesiveQuadruple
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.toCohesiveQuadruple
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.toCohesiveQuadruple_shapeModality
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.toCohesiveQuadruple_flatModality
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.toCohesiveQuadruple_sharpModality

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionAdjointQuadruple
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGlobalSectionsEdge
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesiveToposModelEdge
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGeometricMorphismLeftExact

end FX1PolyAudit
