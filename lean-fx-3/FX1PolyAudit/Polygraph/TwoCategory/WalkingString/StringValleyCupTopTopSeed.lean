import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupTopTopSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCupTopTopSeed — zero-axiom gate
(FC-3 r34, Piece-II tail: CLOSING the string top-top cup-arc partner, the case-3 gate of
`stringCupRestrict_reconstructs`, over the walking ADJOINT-TRIPLE signature)

Per-declaration zero-axiom gate for the string top-top cup-arc closer: the load-bearing seed fact
`stringPureCapTopPartnerBelow`, the assembled `stringCupTopTopPartner`, and the seed-leg truth-probe
`stringPureCapTopPartnerBelow_firesOnWideValley`.  The private range / arithmetic plumbing
(`rangeLoopLenSCTTS`, `rangeLenSCTTS`, `addSubCancelSCTTS`, `getAtMemSCTTS`) is covered transitively.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringPureCapTopPartnerBelow
#assert_no_axioms FX1Poly.Polygraph.stringCupTopTopPartner
#assert_no_axioms FX1Poly.Polygraph.stringPureCapTopPartnerBelow_firesOnWideValley
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupTopTopPartnerClosed

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringPureCapTopPartnerBelow
#print axioms FX1Poly.Polygraph.stringCupTopTopPartner
#print axioms FX1Poly.Polygraph.stringPureCapTopPartnerBelow_firesOnWideValley
#print axioms FX1Poly.Polygraph.fxString_hasCupTopTopPartnerClosed

end FX1PolyAudit
