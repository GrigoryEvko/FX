import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallBlockRefutationLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallBlockRefutationLedger — zero-axiom gate for the r8
ledger markers (WP-AMALG-2 r8, B3/B4/B5)

Per-declaration zero-axiom gate for the two r8 honesty markers (the wall-block refutation of the alignment, and the
sharpened no-flip residual).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r8WallBlockRefutesAlignment
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r8ResidualSharpenedNoFlip

end FX1PolyAudit
