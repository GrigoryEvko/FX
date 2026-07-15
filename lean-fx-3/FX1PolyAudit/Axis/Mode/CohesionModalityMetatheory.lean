import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.CohesionModalityMetatheory

/-! # FX1PolyAudit/Axis/Mode/CohesionModalityMetatheory — zero-axiom gate for the cohesion-family structural metatheory

Per-declaration zero-axiom gate for the cohesion-family structural metatheory
(`FX1Poly/Axis/Mode/CohesionModalityMetatheory.lean`): the recovery-classification (kind + position +
non-degeneracy), the family bundle of concrete (co)reflective witnesses + the (co)unit ties, the structure-class
facts (flat central, triangle β/η, pieces-have-points), and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The recovery-classification
#assert_no_axioms FX1Poly.Axis.cohesionModalityKind
#assert_no_axioms FX1Poly.Axis.cohesionModalityPosition
#assert_no_axioms FX1Poly.Axis.cohesionModalityKind_shape_eq_sharp
#assert_no_axioms FX1Poly.Axis.cohesionModalityKind_flat_ne_shape

-- The family bundle of concrete (co)reflective witnesses + the (co)unit ties
#assert_no_axioms FX1Poly.Axis.trivialCohesionModalityFamily
#assert_no_axioms FX1Poly.Axis.trivialCohesionModalityFamily_shapeUnit
#assert_no_axioms FX1Poly.Axis.trivialCohesionModalityFamily_flatCounit
#assert_no_axioms FX1Poly.Axis.trivialCohesionModalityFamily_sharpUnit

-- The structure-class facts
#assert_no_axioms FX1Poly.Axis.cohesionFamily_flatCentral
#assert_no_axioms FX1Poly.Axis.cohesionFamily_triangleBetaEta
#assert_no_axioms FX1Poly.Axis.cohesionFamily_piecesHavePoints

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasCohesionFamilyStructuralMetatheory
#assert_no_axioms FX1Poly.Axis.fxMode_hasCohesionFamilyComputationMetatheory

end FX1PolyAudit
