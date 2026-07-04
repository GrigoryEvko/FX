import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapAgreeObstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapCapAgreeObstruction — zero-axiom gate

Per-declaration zero-axiom gate for the second cap-cap obstruction: the disjoint-component
fixture's non-degeneracy certificate and the refutation that the two cap-cap run orders are
plain `ArcStateAgree` (the event-attachment swap).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capCapDisjoint_meetsSwapSideConditions
#assert_no_axioms FX1Poly.Polygraph.not_arcStateAgree_capCapDisjoint

end FX1PolyAudit
