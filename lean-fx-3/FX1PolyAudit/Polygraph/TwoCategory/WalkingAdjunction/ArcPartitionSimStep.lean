import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimStep

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPartitionSimStep — zero-axiom gate

Per-declaration zero-axiom gate for the partition simulation's join substrate: the
`sigma`-twisted join congruence and the partition-keyed count transport through a merge.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_sigmaCorr
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_unionFindJoin_partitionMatch
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_componentsCorr
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_loopsCorr

end FX1PolyAudit
