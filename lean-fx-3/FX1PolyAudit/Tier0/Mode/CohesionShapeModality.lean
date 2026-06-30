import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CohesionShapeModality

/-! # FX1PolyAudit/Tier0/Mode/CohesionShapeModality — zero-axiom gate for the cohesion shape modality `ʃ`

Per-declaration zero-axiom gate for the reflective positive modality `ʃ = Disc ∘ Π₀`
(`FX1Poly/Tier0/Mode/CohesionShapeModality.lean`): the unit's definitional restatement + its β/η law, the
reflective mapping-out row `ʃ ⊣ ♭` (shape recursion, `Π₀` as a positive modality) + β/η + faithfulness, the
concrete idempotent reflective-monad witness + its unit tie + idempotency smoke, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The shape monad unit + its β/η
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeUnit_eq
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeUnit_untranspose

-- The reflective row `ʃ ⊣ ♭`: `Π₀` as a positive modality
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeRecursion
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeRecursion_transpose
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.shapeMap_unique

-- The concrete shape monad (trivial witness)
#assert_no_axioms FX1Poly.Tier0.trivialCohesionShapeModality
#assert_no_axioms FX1Poly.Tier0.trivialCohesionShapeModality_unit
#assert_no_axioms FX1Poly.Tier0.trivialCohesionShapeModality_idempotent

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionShapeModality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionShapeMonadGeneral

end FX1PolyAudit
