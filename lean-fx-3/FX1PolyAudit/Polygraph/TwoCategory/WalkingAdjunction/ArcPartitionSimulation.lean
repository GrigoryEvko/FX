import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimulation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPartitionSimulation — zero-axiom gate

Per-declaration zero-axiom gate for the sigma-twisted partition simulation interface: the bridge
from the renaming simulation, the `SameArcPartition` readout, and the equal-extract corollary.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcPartitionSim_of_arcStepSimCount
#assert_no_axioms FX1Poly.Polygraph.sameArcPartition_of_arcPartitionSim
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_arcPartitionSim

end FX1PolyAudit
