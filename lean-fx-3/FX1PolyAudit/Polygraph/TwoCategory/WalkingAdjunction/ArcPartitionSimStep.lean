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
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_cupJoins_corr
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_cupJoins_partitionMatch
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_capJoins_corr
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_capJoins_partitionMatch
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_cupCountCorr
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_capCountCorr
#assert_no_axioms FX1Poly.Polygraph.arcPartitionSim_stepArcAtom

end FX1PolyAudit
