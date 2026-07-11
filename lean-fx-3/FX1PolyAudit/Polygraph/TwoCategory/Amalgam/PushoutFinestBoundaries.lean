import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestBoundaries

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFinestBoundaries — zero-axiom gate for the finest layout's
middle + codomain round-trips (Finding-A first-zip, WP-AMALG-2 r12)

Per-declaration zero-axiom gate for the two extra boundary round-trips (middle, codomain) of `finestLayout`, their
word-level helpers, and the witness probe.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLetterPair_gapMidWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_finestLayoutMid
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapMidLayout_finestLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLetterPair_gapCodWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_finestLayoutCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_finestLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLayoutWitnessAllBoundaries
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFinestAllBoundaryRoundTrips

end FX1PolyAudit
