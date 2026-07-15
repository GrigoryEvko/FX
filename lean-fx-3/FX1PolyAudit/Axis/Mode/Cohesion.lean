import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Cohesion

/-! # FX1PolyAudit/AuditAxisModeCohesion — zero-axiom gate for mode-13

Per-declaration zero-axiom gate for `mode-13` (`FX1Poly/Axis/Mode/Cohesion.lean`): the hom-adjunction + its
derived bijectivity, the cohesive adjoint quadruple + the four functors + the three modalities, the trivial
witness + the modality smokes, the differential cohesion extension, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The hom-adjunction + derived bijectivity
#assert_no_axioms FX1Poly.Axis.HomAdjunction
#assert_no_axioms FX1Poly.Axis.identityHomAdjunction
#assert_no_axioms FX1Poly.Axis.HomAdjunction.transpose_injective
#assert_no_axioms FX1Poly.Axis.HomAdjunction.transpose_surjective

-- The cohesive adjoint quadruple + functors + modalities
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.shapeFunctor
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.discFunctor
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.pointsFunctor
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.codiscFunctor
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.shapeModality
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.flatModality
#assert_no_axioms FX1Poly.Axis.CohesiveQuadruple.sharpModality

-- The trivial witness + modality smokes
#assert_no_axioms FX1Poly.Axis.trivialCohesion
#assert_no_axioms FX1Poly.Axis.trivialCohesion_shapeModality
#assert_no_axioms FX1Poly.Axis.trivialCohesion_flatModality
#assert_no_axioms FX1Poly.Axis.trivialCohesion_sharpModality

-- Differential cohesion
#assert_no_axioms FX1Poly.Axis.DifferentialCohesion
#assert_no_axioms FX1Poly.Axis.DifferentialCohesion.reductionModality
#assert_no_axioms FX1Poly.Axis.DifferentialCohesion.infinitesimalShapeModality
#assert_no_axioms FX1Poly.Axis.trivialDifferentialCohesion
#assert_no_axioms FX1Poly.Axis.trivialDifferentialCohesion_reductionModality

-- The ʃ ⊣ ♭ ⊣ ♯ adjoint string (for the trivial cohesion)
#assert_no_axioms FX1Poly.Axis.trivialCohesion_shapeFlatAdjunction
#assert_no_axioms FX1Poly.Axis.trivialCohesion_flatSharpAdjunction
#assert_no_axioms FX1Poly.Axis.trivialCohesion_shapeFlatAdjunction_functors
#assert_no_axioms FX1Poly.Axis.trivialCohesion_flatSharpAdjunction_functors
#assert_no_axioms FX1Poly.Axis.trivialCohesion_adjointString

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasCohesiveModalityAdjointString
#assert_no_axioms FX1Poly.Axis.fxMode_hasModalFracture
#assert_no_axioms FX1Poly.Axis.fxMode_hasCohesiveToposModel
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelCohesionConnection

end FX1PolyAudit
