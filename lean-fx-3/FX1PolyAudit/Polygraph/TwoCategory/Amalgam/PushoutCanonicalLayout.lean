import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalLayout

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCanonicalLayout — zero-axiom gate for the general
canonical wall/gap layout type (WP-AMALG-2 r7, B2/B3)

Per-declaration zero-axiom gate for the three boundary layouts, the three cell layouts, and the honesty marker.
(The `VcompGapPair` structure carries no proof obligation; its projections are covered by the layout consumers.)

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapMidLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapUpperLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapLowerLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapVcompLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCanonicalGapLayout

end FX1PolyAudit
