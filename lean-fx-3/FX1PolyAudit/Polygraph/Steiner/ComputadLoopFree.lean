import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Steiner.ComputadLoopFree

/-! # FX1PolyAudit/Polygraph/Steiner/ComputadLoopFree — zero-axiom gate (the inhabited loop-free
    instance)

Per-declaration zero-axiom gate for the ADC-computed same-dimension Steiner overlap order and the
REAL inhabited loop-free basis: the concrete overlap order, the single-object semiring computad's
augmented directed complex, the structural entry-is-zero fact, the no-overlap-edge lemma, and the
genuine `IsLoopFreeBasis` witness (structural `Acc`, NOT `WellFounded.fix`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Steiner.sameDimensionOverlapOrder
#assert_no_axioms FX1Poly.Polygraph.Steiner.semiringBasisCount
#assert_no_axioms FX1Poly.Polygraph.Steiner.semiringBoundaryMatrix
#assert_no_axioms FX1Poly.Polygraph.Steiner.listGetWithDefaultEmpty
#assert_no_axioms FX1Poly.Polygraph.Steiner.semiringBoundaryEntryIsZero
#assert_no_axioms FX1Poly.Polygraph.Steiner.singleObjectSemiringComplex
#assert_no_axioms FX1Poly.Polygraph.Steiner.singleObjectSemiringComplex_entryIsZero
#assert_no_axioms FX1Poly.Polygraph.Steiner.noSingleObjectSemiringOverlapEdge
#assert_no_axioms FX1Poly.Polygraph.Steiner.singleObjectSemiringComplex_isLoopFreeBasis
#assert_no_axioms FX1Poly.Polygraph.Steiner.polygraph_hasInhabitedLoopFreeBasis

end FX1PolyAudit
