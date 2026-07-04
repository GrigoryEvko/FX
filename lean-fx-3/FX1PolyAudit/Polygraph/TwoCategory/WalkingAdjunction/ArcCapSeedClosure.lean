import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSeedClosure

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapSeedClosure — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head seed closure (peel campaign H,
strand-closure rung 3): the right-wire avoidance atom, the closed-strand witness at the
cap-head seed, the composite-end-state FALSE evaluation of the cap head's event indicator,
and the clean composite-equals-fresh cap-event count equality.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_missesRightWire
#assert_no_axioms FX1Poly.Polygraph.arcStrandClosure_capHeadSeed
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowAnchorMissesReindexed
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_capEventCount_ofChained

end FX1PolyAudit
