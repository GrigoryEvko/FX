import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Cohesion

/-! # FX1PolyAudit/AuditTier0ModeCohesion — zero-axiom gate for mode-13

Per-declaration zero-axiom gate for `mode-13` (`FX1Poly/Tier0/Mode/Cohesion.lean`): the hom-adjunction + its
derived bijectivity, the cohesive adjoint quadruple + the four functors + the three modalities, the trivial
witness + the modality smokes, the differential cohesion extension, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The hom-adjunction + derived bijectivity
#assert_no_axioms FX1Poly.Tier0.HomAdjunction
#assert_no_axioms FX1Poly.Tier0.identityHomAdjunction
#assert_no_axioms FX1Poly.Tier0.HomAdjunction.transpose_injective
#assert_no_axioms FX1Poly.Tier0.HomAdjunction.transpose_surjective

-- The cohesive adjoint quadruple + functors + modalities
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.shapeFunctor
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.discFunctor
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.pointsFunctor
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.codiscFunctor
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.shapeModality
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.flatModality
#assert_no_axioms FX1Poly.Tier0.CohesiveQuadruple.sharpModality

-- The trivial witness + modality smokes
#assert_no_axioms FX1Poly.Tier0.trivialCohesion
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_shapeModality
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_flatModality
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_sharpModality

-- Differential cohesion
#assert_no_axioms FX1Poly.Tier0.DifferentialCohesion
#assert_no_axioms FX1Poly.Tier0.DifferentialCohesion.reductionModality
#assert_no_axioms FX1Poly.Tier0.DifferentialCohesion.infinitesimalShapeModality
#assert_no_axioms FX1Poly.Tier0.trivialDifferentialCohesion
#assert_no_axioms FX1Poly.Tier0.trivialDifferentialCohesion_reductionModality

-- The ʃ ⊣ ♭ ⊣ ♯ adjoint string (for the trivial cohesion)
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_shapeFlatAdjunction
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_flatSharpAdjunction
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_shapeFlatAdjunction_functors
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_flatSharpAdjunction_functors
#assert_no_axioms FX1Poly.Tier0.trivialCohesion_adjointString

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesiveModalityAdjointString
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModalFracture
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesiveToposModel
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelCohesionConnection

end FX1PolyAudit
