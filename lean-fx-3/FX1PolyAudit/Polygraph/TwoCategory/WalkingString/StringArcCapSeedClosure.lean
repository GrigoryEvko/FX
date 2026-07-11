import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapSeedClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapSeedClosure — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the cap-head seed closure ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowAnchorMissesReindexed
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_capEventCount_ofChained
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapSeedClosure

end FX1PolyAudit
