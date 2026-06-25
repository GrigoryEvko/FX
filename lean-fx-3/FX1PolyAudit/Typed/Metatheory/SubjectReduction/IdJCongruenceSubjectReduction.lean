import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IdJCongruenceSubjectReduction

/-! # FX1PolyAudit/IdJCongruenceSubjectReduction — idJ base-context congruence SR audit shard

Per-declaration zero-axiom gate for the two base-context idJ eliminator-congruence subject reduction arms
(gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): witness / baseCase congruence. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.idJWitnessCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.idJBaseCaseCongruenceSubjectReduction

end FX1PolyAudit
