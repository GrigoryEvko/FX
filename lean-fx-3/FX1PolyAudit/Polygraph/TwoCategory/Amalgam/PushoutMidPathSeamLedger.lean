import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMidPathSeamLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutMidPathSeamLedger — zero-axiom gate for the r9 ledger
markers (WP-AMALG-2 r9, B5)

Per-declaration zero-axiom gate for the two r9 ledger honesty markers (the seam bypasses the r8 jam, and the
sharpened reconstruction-inversion residual).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r9SeamBypassesR8Jam
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_r9ReconstructionInversionResidual

end FX1PolyAudit
