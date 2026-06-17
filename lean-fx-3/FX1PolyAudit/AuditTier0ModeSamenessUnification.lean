import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.SamenessUnification

/-! # FX1PolyAudit/AuditTier0ModeSamenessUnification — zero-axiom gate for mode-19

Per-declaration zero-axiom gate for `mode-19` (`FX1Poly/Tier0/Mode/SamenessUnification.lean`): the arity ↔
multiplier classification + the reflexivity = diagonal identity, the binary sameness machinery + the
univalence = parametricity@Eq unification + the finest-reflexive theorem, the abstraction-theorem category +
SIP transport, the nominal freshness, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The arity ↔ multiplier classification
#assert_no_axioms FX1Poly.Tier0.SamenessArity
#assert_no_axioms FX1Poly.Tier0.SamenessArity.multiplierClass
#assert_no_axioms FX1Poly.Tier0.SamenessArity.hasReflexivity
#assert_no_axioms FX1Poly.Tier0.samenessArity_reflexivity_eq_diagonal

-- The shared binary sameness machinery
#assert_no_axioms FX1Poly.Tier0.Sameness
#assert_no_axioms FX1Poly.Tier0.identitySameness
#assert_no_axioms FX1Poly.Tier0.relationalSameness
#assert_no_axioms FX1Poly.Tier0.identity_is_relational_at_Eq
#assert_no_axioms FX1Poly.Tier0.Sameness.IsReflexive
#assert_no_axioms FX1Poly.Tier0.identitySameness_reflexive
#assert_no_axioms FX1Poly.Tier0.relational_not_reflexive
#assert_no_axioms FX1Poly.Tier0.identity_finest_reflexive

-- The abstraction theorem (parametricity) + SIP transport
#assert_no_axioms FX1Poly.Tier0.Respects
#assert_no_axioms FX1Poly.Tier0.id_respects
#assert_no_axioms FX1Poly.Tier0.comp_respects
#assert_no_axioms FX1Poly.Tier0.identity_respects
#assert_no_axioms FX1Poly.Tier0.const_respects_of_reflexive

-- Nominal freshness (the affine, irreflexive case)
#assert_no_axioms FX1Poly.Tier0.freshness
#assert_no_axioms FX1Poly.Tier0.freshness_irreflexive
#assert_no_axioms FX1Poly.Tier0.nominal_is_affine

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTranspensionArityUnification
#assert_no_axioms FX1Poly.Tier0.fxMode_hasProofRelevantSameness
#assert_no_axioms FX1Poly.Tier0.fxMode_hasNAryArity
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelSamenessConnection

end FX1PolyAudit
