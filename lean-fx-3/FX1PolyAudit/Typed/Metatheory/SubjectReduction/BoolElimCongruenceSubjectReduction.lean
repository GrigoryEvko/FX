import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.BoolElimCongruenceSubjectReduction

/-! # FX1PolyAudit/BoolElimCongruenceSubjectReduction — boolElim recursor congruence SR audit shard

Per-declaration zero-axiom gate for the three base-context boolElim eliminator-congruence subject reduction
arms (gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): scrutinee / thenBranch / elseBranch congruence. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.boolElimScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.boolElimThenBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.boolElimElseBranchCongruenceSubjectReduction

end FX1PolyAudit
