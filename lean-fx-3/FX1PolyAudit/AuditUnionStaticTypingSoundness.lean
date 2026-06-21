import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.UnionStaticTypingSoundness

/-! # FX1PolyAudit/AuditUnionStaticTypingSoundness — the union reserved-head refutation

Per-declaration zero-axiom gate for the single-judgment HON-5 successor: the union-classifier
false-peel, the union-reserved → honesty-reserved refinement, the headline refutation (a head the
full-union classifier `hasUnionEliminatorTypingRule` reports RESERVED is untyped by
`HasTypeUnion` at every context and classifier — the nineteen-arm induction), the contrapositive
liveness API, and the reserved-exemplar smoke.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.hasUnionEliminatorTypingRule_falsePeel
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_falseOfUnionReserved
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.reservedHeadUntyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.headIsUnionLive
#assert_no_axioms FX1Poly.Typed.hasUnionEliminatorTypingRule_hilbertSpace
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.hilbertSpaceHeadUntyped

/-! ## TYTAB-1 brick 3: the bundle-generic judgment + its kernel pinning are axiom-clean -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnionOver
#assert_no_axioms FX1Poly.Typed.HasTypeUnion
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.intro
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.elim
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.conv
-- ★ TYTAB-2 VAR+UNIV: the two native structural-leaf arms (var + universe formation).
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.var
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.universeFormation

end FX1PolyAudit
