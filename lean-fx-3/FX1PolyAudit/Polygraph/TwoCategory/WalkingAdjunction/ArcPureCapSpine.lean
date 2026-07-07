import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine

/-! # FX1PolyAudit/…/ArcPureCapSpine — zero-axiom gate

Per-declaration zero-axiom gate for the pure-cap regime detector: at the walking adjunction, a
spine with zero total cup tally has every atom carrying cap arity — the regime predicate for the
peel-first cap sort.  The purity kit (converse, length reflection, cons-inversion, head arity) is
gated alongside.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.allCapArity_ofCupAtomCountZero
#assert_no_axioms FX1Poly.Polygraph.cupAtomCount_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.capAtomCount_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.allCapArity_ofCons
#assert_no_axioms FX1Poly.Polygraph.headCapArity
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPureCapSpine

end FX1PolyAudit
