import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutEndoModeTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutEndoModeTransport — zero-axiom gate for the
endo-`ModalityPath`-at-single-mode transport (WP-AMALG-2 r11, B1)

Per-declaration zero-axiom gate for the singleton fact, the endo-generator consequence, the transport, its two
round-trips (word round-trip + reflection injectivity), the wall-free hypothesis, the concrete truth-probe, and the
negative control.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutModeUnique
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutGenEndpoints
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutEndoPathOfWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_pushoutEndoPathOfWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_injective
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutEndoPathOfWord_pushoutPathWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pathWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.endoTransport_twoLetterProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushTPath_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushSPath_notWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasEndoModeTransport

end FX1PolyAudit
