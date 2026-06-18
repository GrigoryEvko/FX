import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeOne

/-! # FX1PolyAudit/AuditTier0TypeOne — zero-axiom gate for type-1 (the LEFT / initial structure)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeOne.lean`: the three backed flips
(dependent Σ formation, the initial-algebra universal property, data-former reducibility) and the three
deferral honesty markers (dependent Σ elimination, object-level inductive initiality, W-types).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasDependentSumFormation
#assert_no_axioms FX1Poly.Tier0.fxType_dependentSumFormation_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasInitialAlgebra
#assert_no_axioms FX1Poly.Tier0.fxType_initialAlgebra_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasDataFormerReducibility
#assert_no_axioms FX1Poly.Tier0.fxType_dataFormerReducibility_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasDependentSumElimination
#assert_no_axioms FX1Poly.Tier0.fxType_hasInductiveTypeObjectInitiality
#assert_no_axioms FX1Poly.Tier0.fxType_hasWTypes

end FX1PolyAudit
