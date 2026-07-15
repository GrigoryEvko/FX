import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.SamenessUnification

/-! # FX1PolyAudit/AuditAxisModeSamenessUnification — zero-axiom gate for mode-19

Per-declaration zero-axiom gate for `mode-19` (`FX1Poly/Axis/Mode/SamenessUnification.lean`): the arity ↔
multiplier classification + the reflexivity = diagonal identity, the binary sameness machinery + the
univalence = parametricity@Eq unification + the finest-reflexive theorem, the abstraction-theorem category +
SIP transport, the nominal freshness, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The arity ↔ multiplier classification
#assert_no_axioms FX1Poly.Axis.SamenessArity
#assert_no_axioms FX1Poly.Axis.SamenessArity.multiplierClass
#assert_no_axioms FX1Poly.Axis.SamenessArity.hasReflexivity
#assert_no_axioms FX1Poly.Axis.samenessArity_reflexivity_eq_diagonal

-- The shared binary sameness machinery
#assert_no_axioms FX1Poly.Axis.Sameness
#assert_no_axioms FX1Poly.Axis.identitySameness
#assert_no_axioms FX1Poly.Axis.relationalSameness
#assert_no_axioms FX1Poly.Axis.identity_is_relational_at_Eq
#assert_no_axioms FX1Poly.Axis.Sameness.IsReflexive
#assert_no_axioms FX1Poly.Axis.identitySameness_reflexive
#assert_no_axioms FX1Poly.Axis.relational_not_reflexive
#assert_no_axioms FX1Poly.Axis.identity_finest_reflexive

-- The abstraction theorem (parametricity) + SIP transport
#assert_no_axioms FX1Poly.Axis.Respects
#assert_no_axioms FX1Poly.Axis.id_respects
#assert_no_axioms FX1Poly.Axis.comp_respects
#assert_no_axioms FX1Poly.Axis.identity_respects
#assert_no_axioms FX1Poly.Axis.const_respects_of_reflexive

-- Nominal freshness (the affine, irreflexive case)
#assert_no_axioms FX1Poly.Axis.freshness
#assert_no_axioms FX1Poly.Axis.freshness_irreflexive
#assert_no_axioms FX1Poly.Axis.nominal_is_affine

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasTranspensionArityUnification
#assert_no_axioms FX1Poly.Axis.fxMode_hasProofRelevantSameness
#assert_no_axioms FX1Poly.Axis.fxMode_hasNAryArity
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelSamenessConnection

end FX1PolyAudit
