import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.NatElimCongruenceSubjectReduction

/-! # FX1PolyAudit/NatElimCongruenceSubjectReduction — natElim base-context congruence SR audit shard

Per-declaration zero-axiom gate for the natElim eliminator-congruence subject reduction arms
(gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): scrutinee / zeroBranch / stepBranch congruence. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natElimScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natElimZeroBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.natElimStepBranchCongruenceSubjectReduction

end FX1PolyAudit
