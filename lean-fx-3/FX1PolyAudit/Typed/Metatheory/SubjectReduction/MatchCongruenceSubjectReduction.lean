import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.MatchCongruenceSubjectReduction

/-! # FX1PolyAudit/MatchCongruenceSubjectReduction — option/either base-context congruence SR audit shard

Per-declaration zero-axiom gate for the six base-context optionMatch / eitherMatch eliminator-congruence
subject reduction arms (gate 2 of the consistency leg, TYTAB-2-FT-SR #1697): scrutinee + both branch
positions for each matcher. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.optionMatchScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.optionMatchNoneBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.optionMatchSomeBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.eitherMatchScrutineeCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.eitherMatchLeftBranchCongruenceSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.eitherMatchRightBranchCongruenceSubjectReduction

end FX1PolyAudit
