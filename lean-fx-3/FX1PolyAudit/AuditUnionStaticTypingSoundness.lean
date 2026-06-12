import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.UnionStaticTypingSoundness

/-! # FX1PolyAudit/AuditUnionStaticTypingSoundness — the union reserved-head refutation

Per-declaration zero-axiom gate for the single-judgment HON-5 successor: the union-classifier
false-peel, the union-reserved → honesty-reserved refinement, the headline refutation (a head the
full-union classifier `hasUnionEliminatorTypingRule` reports RESERVED is untyped by
`HasTypeNativeUnion` at every context and classifier — the nineteen-arm induction), the contrapositive
liveness API, and the reserved-exemplar smoke.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.hasUnionEliminatorTypingRule_falsePeel
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_falseOfUnionReserved
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.reservedHeadUntyped
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.headIsUnionLive
#assert_no_axioms FX1Poly.Typed.hasUnionEliminatorTypingRule_hilbertSpace
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.hilbertSpaceHeadUntyped

end FX1PolyAudit
