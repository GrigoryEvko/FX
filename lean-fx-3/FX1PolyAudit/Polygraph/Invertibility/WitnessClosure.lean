import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Invertibility.WitnessClosure

/-! # FX1PolyAudit/Polygraph/Invertibility/WitnessClosure — zero-axiom gate

Per-declaration zero-axiom gate for the generic witness-closure core: the monotone `WitnessOperator`,
the impredicative least fixpoint (`inductiveClosure` + its induction / closure / unfolding lemmas), the
greatest fixpoint (`coinductiveClosure` + post-fixedness / greatest-ness / closure), and the headline
skeleton `inductiveClosure_subset_coinductiveClosure` (least ⊆ greatest).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Invertibility.WitnessOperator
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_least
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_closedUnderApply
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_unfold
#assert_no_axioms FX1Poly.Polygraph.Invertibility.IsPostFixed
#assert_no_axioms FX1Poly.Polygraph.Invertibility.coinductiveClosure
#assert_no_axioms FX1Poly.Polygraph.Invertibility.IsPostFixed.subset_coinductiveClosure
#assert_no_axioms FX1Poly.Polygraph.Invertibility.coinductiveClosure_isPostFixed
#assert_no_axioms FX1Poly.Polygraph.Invertibility.coinductiveClosure_closedUnderApply
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_subset_coinductiveClosure

end FX1PolyAudit
