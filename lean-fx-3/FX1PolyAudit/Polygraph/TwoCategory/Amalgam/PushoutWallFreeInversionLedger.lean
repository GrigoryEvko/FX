import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeInversionLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreeInversionLedger — zero-axiom gate for the r10 ledger
(WP-AMALG-2 r10, B4/B5)

Per-declaration zero-axiom gate for the r10 honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r10ShipsWallFreeInversionAndGapMerge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r10NamedOpenNodes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r10NoFlipHeld

end FX1PolyAudit
