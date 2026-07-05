import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcPairUntouched — zero-axiom gate

Per-declaration zero-axiom gate for the untouched-pair invariant substrate: the membership
plumbing (splice survival, read-disjoint removal survival, range membership), the
unlinked-node predicate with its join preservation, the invariant's cup / disjoint-cap step
preservation, and the initial-state instance.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mem_natListInsertAt_of_mem
#assert_no_axioms FX1Poly.Polygraph.mem_natListRemoveTwoAt_of_ne_reads
#assert_no_axioms FX1Poly.Polygraph.mem_range_of_lt
#assert_no_axioms FX1Poly.Polygraph.ArcNodeUnlinked
#assert_no_axioms FX1Poly.Polygraph.arcNodeUnlinked_unionFindJoin
#assert_no_axioms FX1Poly.Polygraph.ArcPairUntouched
#assert_no_axioms FX1Poly.Polygraph.arcPairUntouched_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.arcPairUntouched_stepCapArc_ofDisjointReads
#assert_no_axioms FX1Poly.Polygraph.arcPairUntouched_initial
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPairUntouchedInvariant

end FX1PolyAudit
