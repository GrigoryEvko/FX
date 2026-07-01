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

#assert_no_axioms FX1Poly.Tier0.AdjunctionOrientedSwap
#assert_no_axioms FX1Poly.Tier0.adjunctionOrientedSwapIsGodement
#assert_no_axioms FX1Poly.Tier0.adjunctionLeftContextLengthSum
#assert_no_axioms FX1Poly.Tier0.adjunctionOrientedSwap_leftContextSum_lt
#assert_no_axioms FX1Poly.Tier0.adjunctionOrientedSwapTerminating
#assert_no_axioms FX1Poly.Tier0.adjunctionOrientedSwapConfluentOfWeaklyConfluent
#assert_no_axioms FX1Poly.Tier0.adjunctionOrientedTheory_consCongr
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnits_orientedSwap
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnits_measure_redex
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnits_measure_reduct
#assert_no_axioms FX1Poly.Tier0.adjunctionCounitGodementStep
#assert_no_axioms FX1Poly.Tier0.adjunctionCounitGate_isContracting
#assert_no_axioms FX1Poly.Tier0.adjunctionTraceDecisionViaExpandingReducer
#assert_no_axioms FX1Poly.Tier0.fxMode_hasOrientedTraceCanonicalForm

end FX1PolyAudit
