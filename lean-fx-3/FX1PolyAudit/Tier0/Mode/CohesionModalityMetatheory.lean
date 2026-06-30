import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CohesionModalityMetatheory

/-! # FX1PolyAudit/Tier0/Mode/CohesionModalityMetatheory — zero-axiom gate for the cohesion-family structural metatheory

Per-declaration zero-axiom gate for the cohesion-family structural metatheory
(`FX1Poly/Tier0/Mode/CohesionModalityMetatheory.lean`): the recovery-classification (kind + position +
non-degeneracy), the family bundle of concrete (co)reflective witnesses + the (co)unit ties, the structure-class
facts (flat central, triangle β/η, pieces-have-points), and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The recovery-classification
#assert_no_axioms FX1Poly.Tier0.cohesionModalityKind
#assert_no_axioms FX1Poly.Tier0.cohesionModalityPosition
#assert_no_axioms FX1Poly.Tier0.cohesionModalityKind_shape_eq_sharp
#assert_no_axioms FX1Poly.Tier0.cohesionModalityKind_flat_ne_shape

-- The family bundle of concrete (co)reflective witnesses + the (co)unit ties
#assert_no_axioms FX1Poly.Tier0.trivialCohesionModalityFamily
#assert_no_axioms FX1Poly.Tier0.trivialCohesionModalityFamily_shapeUnit
#assert_no_axioms FX1Poly.Tier0.trivialCohesionModalityFamily_flatCounit
#assert_no_axioms FX1Poly.Tier0.trivialCohesionModalityFamily_sharpUnit

-- The structure-class facts
#assert_no_axioms FX1Poly.Tier0.cohesionFamily_flatCentral
#assert_no_axioms FX1Poly.Tier0.cohesionFamily_triangleBetaEta
#assert_no_axioms FX1Poly.Tier0.cohesionFamily_piecesHavePoints

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionFamilyStructuralMetatheory
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionFamilyComputationMetatheory

end FX1PolyAudit
