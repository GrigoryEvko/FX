import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapInternalCountsPointwise

/-! # FX1PolyAudit/…/ArcCapInternalCountsPointwise — zero-axiom gate

Per-declaration zero-axiom gate for the per-port cap-count characterization (leaf 2a-ii): on a
boundary-chained pure-cap spine the internal cap count at each port is a function of the boundary
`diagram` (`capPortIndicator` of the partner — a bottom-bottom short chord reads `1`, all else `0`), and
two pure-cap spines with equal `diagram` have equal `internalCapCounts`.  The private base/step (peel-
first) lemmas are covered transitively: any `propext` / `Quot.sound` leak in them would surface on the
public theorems asserted here.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capPortIndicator
#assert_no_axioms FX1Poly.Polygraph.pureCap_internalCapCounts_pointwise
#assert_no_axioms FX1Poly.Polygraph.pureCapSpines_internalCapCountsAgree_ofDiagram
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapInternalCountsPointwise

end FX1PolyAudit
