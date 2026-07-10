import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin — zero-axiom gate (FC-3 r11, B1/B2)

Per-declaration zero-axiom gate for the shared-top last-cup pin: the length-0-path equality
(`modalityPathEqOfLengthZero`, private — checked transitively), the LENGTH→WORD adapter
(`stringLastCupDomWord_eq_of_sharedCod_sameWindow`), the WORD-driven drop-in
(`stringSpineAtom_eq_of_sharedCod_sameWindow`), the concrete-cup non-vacuity
(`stringSharedCodCupPin_firesOnConcreteCup`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringLastCupDomWord_eq_of_sharedCod_sameWindow
#assert_no_axioms FX1Poly.Polygraph.stringSpineAtom_eq_of_sharedCod_sameWindow
#assert_no_axioms FX1Poly.Polygraph.stringSharedCodCupPin_firesOnConcreteCup
#assert_no_axioms FX1Poly.Polygraph.fxString_hasLastCupSharedTopPin

end FX1PolyAudit
