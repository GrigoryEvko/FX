import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ListElimCongruenceSubjectReduction

/-! # FX1PolyAudit/ListElimCongruenceSubjectReduction — listElim base-context congruence SR audit shard

Per-declaration zero-axiom gate for the three base-context listElim eliminator-congruence subject reduction
arms (gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): scrutinee / nilBranch / consBranch congruence. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.listElimScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.listElimNilBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.listElimConsBranchCongruenceSubjectReduction

end FX1PolyAudit
