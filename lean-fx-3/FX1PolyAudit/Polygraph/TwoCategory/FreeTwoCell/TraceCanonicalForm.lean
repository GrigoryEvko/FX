import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceCanonicalForm

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TraceCanonicalForm — zero-axiom gate

Per-declaration zero-axiom gate for the least-element canonical form: the
self-contained key order, the lexicographic trace order with its total-order facts,
the minimum selection, and the canonical-form invariance theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.compareNatKeys
#assert_no_axioms FX1Poly.Polygraph.compareNatKeys_selfIsEq
#assert_no_axioms FX1Poly.Polygraph.compareNatKeys_eqImpliesEqual
#assert_no_axioms FX1Poly.Polygraph.compareNatKeys_swapSymm
#assert_no_axioms FX1Poly.Polygraph.compareNatKeys_ltTrans
#assert_no_axioms FX1Poly.Polygraph.AtomKeying
#assert_no_axioms FX1Poly.Polygraph.compareTraces
#assert_no_axioms FX1Poly.Polygraph.compareTraces_selfIsEq
#assert_no_axioms FX1Poly.Polygraph.compareTraces_eqImpliesEqual
#assert_no_axioms FX1Poly.Polygraph.compareTraces_swapSymm
#assert_no_axioms FX1Poly.Polygraph.compareTraces_ltTrans
#assert_no_axioms FX1Poly.Polygraph.IsTraceLeq
#assert_no_axioms FX1Poly.Polygraph.isTraceLeq_ofSelf
#assert_no_axioms FX1Poly.Polygraph.isTraceLeq_trans
#assert_no_axioms FX1Poly.Polygraph.selectSmallerTrace
#assert_no_axioms FX1Poly.Polygraph.selectSmallerTrace_ofGt
#assert_no_axioms FX1Poly.Polygraph.selectSmallerTrace_ofNotGt
#assert_no_axioms FX1Poly.Polygraph.selectSmallerTrace_isEither
#assert_no_axioms FX1Poly.Polygraph.selectSmallerTrace_isLeqFirst
#assert_no_axioms FX1Poly.Polygraph.selectSmallerTrace_isLeqSecond
#assert_no_axioms FX1Poly.Polygraph.selectLeastTraceFrom
#assert_no_axioms FX1Poly.Polygraph.selectLeastTraceFrom_isCurrentOrMember
#assert_no_axioms FX1Poly.Polygraph.selectLeastTraceFrom_isLeqAll
#assert_no_axioms FX1Poly.Polygraph.canonicalTraceRepresentative
#assert_no_axioms FX1Poly.Polygraph.canonicalTraceRepresentative_isInClass
#assert_no_axioms FX1Poly.Polygraph.canonicalTraceRepresentative_isEquivToSeed
#assert_no_axioms FX1Poly.Polygraph.canonicalTraceRepresentative_isEquivInvariant

end FX1PolyAudit
