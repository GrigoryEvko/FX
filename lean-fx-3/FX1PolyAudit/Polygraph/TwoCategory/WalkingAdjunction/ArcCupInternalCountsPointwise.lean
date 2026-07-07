import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupInternalCountsPointwise

/-! # FX1PolyAudit/…/ArcCupInternalCountsPointwise — zero-axiom gate

Per-declaration zero-axiom gate for the per-port cup-count characterization (leaf 2a-i): on a
boundary-chained pure-cup spine the internal cup count at each port is a function of the boundary
`diagram` (`cupPortIndicator` of the partner — a top-top short chord reads `1`, all else `0`), and two
pure-cup spines with equal `diagram` have equal `internalCupCounts`.  The private base/step/scan
lemmas are covered transitively: any `propext` / `Quot.sound` leak in them would surface on the public
theorems asserted here.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupPortIndicator
#assert_no_axioms FX1Poly.Polygraph.pureCup_internalCupCounts_pointwise
#assert_no_axioms FX1Poly.Polygraph.pureCupSpines_internalCupCountsAgree_ofDiagram
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupInternalCountsPointwise

end FX1PolyAudit
