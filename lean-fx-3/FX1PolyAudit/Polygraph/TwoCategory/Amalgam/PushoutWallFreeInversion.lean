import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeInversion

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreeInversion — zero-axiom gate for the letter-level
wall-free inversion (WP-AMALG-2 r10, B1)

Per-declaration zero-axiom gate for the `Nat.blt`-false bridge, the letter converse of `embedRightLetter`, its two
round-trips, letter-level injectivity, and the concrete gap-letter truth-probe.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.geOfBltFalse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.retractRightLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.retractRightLetter_val
#assert_no_axioms FX1Poly.Polygraph.Amalgam.retractRightLetter_embedRightLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedRightLetter_retractRightLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedRightLetter_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tLetter_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sLetter_notWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tLetter_retract
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWallFreeLetterInversion

end FX1PolyAudit
