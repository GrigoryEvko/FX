import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.OrientedReducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.OrientedReducer — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the expanding-oriented single-atom Godement swap: the oriented sub-relation
(`AdjunctionOrientedSwap`), its Godement embedding (`adjunctionOrientedSwapIsGodement`), the strong-normalization
measure and proof (`adjunctionLeftContextLengthSum`, `adjunctionOrientedSwap_leftContextSum_lt`,
`adjunctionOrientedSwapTerminating`), the Newman confluence reduction
(`adjunctionOrientedSwapConfluentOfWeaklyConfluent`), the theory cons-congruence
(`adjunctionOrientedTheory_consCongr`), the Eckmann–Hilton + contracting-counit witnesses, and the harness with
`terminating`/`orientedIsGodement`/`confluent` discharged (`adjunctionTraceDecisionViaExpandingReducer`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AdjunctionOrientedSwap
#assert_no_axioms FX1Poly.Polygraph.adjunctionOrientedSwapIsGodement
#assert_no_axioms FX1Poly.Polygraph.adjunctionLeftContextLengthSum
#assert_no_axioms FX1Poly.Polygraph.adjunctionOrientedSwap_leftContextSum_lt
#assert_no_axioms FX1Poly.Polygraph.adjunctionOrientedSwapTerminating
#assert_no_axioms FX1Poly.Polygraph.adjunctionOrientedSwapConfluentOfWeaklyConfluent
#assert_no_axioms FX1Poly.Polygraph.adjunctionOrientedTheory_consCongr
#assert_no_axioms FX1Poly.Polygraph.adjunctionParallelUnits_orientedSwap
#assert_no_axioms FX1Poly.Polygraph.adjunctionParallelUnits_measure_redex
#assert_no_axioms FX1Poly.Polygraph.adjunctionParallelUnits_measure_reduct
#assert_no_axioms FX1Poly.Polygraph.adjunctionCounitGodementStep
#assert_no_axioms FX1Poly.Polygraph.adjunctionCounitGate_isContracting
#assert_no_axioms FX1Poly.Polygraph.adjunctionTraceDecisionViaExpandingReducer
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasOrientedTraceCanonicalForm

end FX1PolyAudit
