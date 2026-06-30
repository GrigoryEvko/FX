import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CohesionAdjointString

/-! # FX1PolyAudit/Tier0/Mode/CohesionAdjointString — zero-axiom gate for the cohesion adjoint string

Per-declaration zero-axiom gate for the cohesion `ʃ ⊣ ♭ ⊣ ♯` adjoint string + axioms
(`FX1Poly/Tier0/Mode/CohesionAdjointString.lean`): the two cast-free modal adjunctions, the adjoint-string
package + the shared-middle fact, the (co)pointed units + the points comparison, the trivial-witness idempotency
+ string + unit smokes, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The two cast-free modal adjunctions
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeFlatAdjunction
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatSharpAdjunction

-- The adjoint string package + shared middle
#assert_no_axioms FX1Poly.Tier0.CohesionModalityAdjointString
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.cohesionAdjointString
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.cohesionAdjointString_middle

-- The (co)pointed units + the points comparison
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeUnit
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCounit
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.sharpUnit
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.piecesHavePoints
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.piecesHavePoints_eq

-- The trivial-witness idempotency smokes
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_shapeModality_idempotent
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_flatModality_idempotent
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_sharpModality_idempotent

-- The trivial-witness string + unit smokes
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_shapeFlat_transpose
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_flatSharp_transpose
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_shapeUnit
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_flatCounit
#assert_no_axioms FX1Poly.Tier0.trivialCohesionQuadruple_piecesHavePoints

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionAdjointString
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionAxioms
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionModalityIdempotent
#assert_no_axioms FX1Poly.Tier0.fxMode_hasPiecesHavePointsEpi
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionModalityComputation

end FX1PolyAudit
