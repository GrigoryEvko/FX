import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringKParameterizationCensus

/-! # FX1PolyAudit.…WalkingString.StringKParameterizationCensus — zero-axiom gate (FC-4 r1 opener, O1 census)

Per-declaration zero-axiom gate for the `k`-parameterization census: the faithful index abstraction
(`wireLabelIndex`, `pathIndexWord`), the orientation predicate (`isAscendingPair`), the `k`-generic carrier
(`adjointStringCupCods`/`adjointStringCapDoms` and their `atTwo`/`atThree` elaboration + orientation pins), the
shipped-world embedding pins, and the four road markers.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.wireLabelIndex
#assert_no_axioms FX1Poly.Polygraph.pathIndexWord
#assert_no_axioms FX1Poly.Polygraph.isAscendingPair
#assert_no_axioms FX1Poly.Polygraph.adjointStringCupCodAt
#assert_no_axioms FX1Poly.Polygraph.adjointStringCapDomAt
#assert_no_axioms FX1Poly.Polygraph.adjointStringCupCods
#assert_no_axioms FX1Poly.Polygraph.adjointStringCapDoms
#assert_no_axioms FX1Poly.Polygraph.adjointStringCupCods_atTwo
#assert_no_axioms FX1Poly.Polygraph.adjointStringCupCods_atThree
#assert_no_axioms FX1Poly.Polygraph.adjointStringCapDoms_atTwo
#assert_no_axioms FX1Poly.Polygraph.adjointStringCapDoms_atThree
#assert_no_axioms FX1Poly.Polygraph.adjointStringCupCods_allAscending_atThree
#assert_no_axioms FX1Poly.Polygraph.adjointStringCapDoms_allDescending_atThree
#assert_no_axioms FX1Poly.Polygraph.pathIndexWord_stringFG
#assert_no_axioms FX1Poly.Polygraph.pathIndexWord_stringGF
#assert_no_axioms FX1Poly.Polygraph.pathIndexWord_stringGH
#assert_no_axioms FX1Poly.Polygraph.pathIndexWord_stringHG
#assert_no_axioms FX1Poly.Polygraph.shippedCupCods_eq_carrierAtTwo
#assert_no_axioms FX1Poly.Polygraph.shippedCapDoms_eq_carrierAtTwo
#assert_no_axioms FX1Poly.Polygraph.fxString_hasKParameterizationCensus
#assert_no_axioms FX1Poly.Polygraph.fxString_hasKGenericConnectivityEngine
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNColourOrientationLabelPinningCrux
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNColourAtomPinReroute

end FX1PolyAudit
