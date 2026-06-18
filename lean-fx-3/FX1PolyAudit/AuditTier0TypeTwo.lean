import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeTwo

/-! # FX1PolyAudit/AuditTier0TypeTwo — zero-axiom gate for type-2 (the MIDDLE rung)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeTwo.lean`: the four backed flips
(dependent Π formation, function dynamics, the universe classifier, the Tarski roundtrip) and the three
deferral honesty markers.  Gating `fxType_tarskiRoundtrip_isBacked` here transitively certifies the cited
Core Tarski theorems (`tarskiDecode` / `tarskiEncode` / `universeMembership_iff`) zero-axiom.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The four backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasDependentFunctionFormation
#assert_no_axioms FX1Poly.Tier0.fxType_dependentFunctionFormation_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasFunctionDynamics
#assert_no_axioms FX1Poly.Tier0.fxType_functionDynamics_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasUniverseClassifier
#assert_no_axioms FX1Poly.Tier0.fxType_universeClassifier_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasTarskiRoundtrip
#assert_no_axioms FX1Poly.Tier0.fxType_tarskiRoundtrip_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasFibredFunctionRightAdjoint
#assert_no_axioms FX1Poly.Tier0.fxType_hasDisplayMapClassifier
#assert_no_axioms FX1Poly.Tier0.fxType_hasTarskiRoundtripInverse

end FX1PolyAudit
