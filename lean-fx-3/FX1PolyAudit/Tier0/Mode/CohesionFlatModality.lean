import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.CohesionFlatModality

/-! # FX1PolyAudit/Tier0/Mode/CohesionFlatModality — zero-axiom gate for the cohesion flat modality `♭`

Per-declaration zero-axiom gate for the comonadic discrete modality `♭ = Disc ∘ Γ`
(`FX1Poly/Tier0/Mode/CohesionFlatModality.lean`): the counit's definitional restatement + its β/η law, the crisp
/ Fitch-style row `♭ ⊣ ♯` with crisp corecursion + β/η + faithfulness, the concrete idempotent comonad witness +
its counit tie + idempotency smoke, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The flat comonad counit + its β/η
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCounit_eq
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCounit_transpose

-- The crisp / Fitch-style row `♭ ⊣ ♯` + crisp corecursion
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCrispRow
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCrispCorecursion
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCrispCorecursion_transpose
#assert_no_axioms FX1Poly.Tier0.CohesionAdjointQuadruple.flatCrispMap_unique

-- The concrete flat comonad (trivial witness)
#assert_no_axioms FX1Poly.Tier0.trivialCohesionFlatComodality
#assert_no_axioms FX1Poly.Tier0.trivialCohesionFlatComodality_counit
#assert_no_axioms FX1Poly.Tier0.trivialCohesionFlatComodality_idempotent

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionFlatModality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCohesionFlatComonadGeneral

end FX1PolyAudit
