import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.NatRecCongruenceSubjectReduction

/-! # FX1PolyAudit/NatRecCongruenceSubjectReduction — natRec base-context congruence SR audit shard

Per-declaration zero-axiom gate for the natRec eliminator-congruence subject reduction arms
(gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): scrutinee / zeroBranch / stepBranch congruence. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natRecScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natRecZeroBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natRecStepBranchCongruenceSubjectReduction

end FX1PolyAudit
