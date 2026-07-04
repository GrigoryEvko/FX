import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEventCountTransport

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcEventCountTransport — zero-axiom gate

Per-declaration zero-axiom gate for the per-strand event-count transport (peel campaign H,
extract-correspondence rung 2): the generic scan kit (append / singleton / map through a
component correspondence) and the four assembled composite-count decompositions at reindexed
probes.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_singleton
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_mapCorr
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_cupEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_capEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_cupEventCountAtImage
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_capEventCountAtImage

end FX1PolyAudit
