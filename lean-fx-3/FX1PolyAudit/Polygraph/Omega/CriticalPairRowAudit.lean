import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CriticalPairRow

/-! # FX1PolyAudit.Polygraph.Omega.CriticalPairRowAudit — zero-axiom gate for the dim-3 critical-pair row
family (OMEGA-4 r1, B1).

Per-declaration `#assert_no_axioms` on the globular row's parallelism reader, the critical-pair-to-row
constructor, the singleton relation packaging, the generating 3-cell, and the interchange non-vacuity
(the globular row, its 3-cell, its parallelism, and the structural-distinctness witness). -/

namespace FX1PolyAudit

-- CriticalPairRow.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.criticalPairRow_isParallelPair
#assert_no_axioms FX1Poly.Polygraph.Omega.criticalPairRowOfParallelLegs
#assert_no_axioms FX1Poly.Polygraph.Omega.criticalPairRel
#assert_no_axioms FX1Poly.Polygraph.Omega.criticalPairThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCriticalRow
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCriticalRow_isParallelPair
#assert_no_axioms FX1Poly.Polygraph.Omega.interchangeCriticalRow_legsDistinct

end FX1PolyAudit
