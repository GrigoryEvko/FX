import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleAtomPinReroute

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleAtomPinReroute — zero-axiom gate (FC-4 r2, bricks R2 + R1/R3)

Per-declaration zero-axiom gate for the cup-restricted COD atom-pin reroute + the `k = 3` engine fire: the refutation
pin (`quad_dom_does_not_determine_cod`, dom→cod STILL refuted), the cup COD pin
(`stringQuadTwoCell_domPack_uniqueOfCod_forCups`) and the cap DOM dual
(`stringQuadTwoCell_codPack_uniqueOfDom_forCaps`), the wide truth-probe tables at `k = 3` AND `k = 4`, the `k = 3`
engine fixtures (`quadEngineCupFires` / `quadEngineCupCapClosesLoop`), the LOCATE fire / decline, and the two markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.quad_dom_does_not_determine_cod
#assert_no_axioms FX1Poly.Polygraph.stringQuadTwoCell_domPack_uniqueOfCod_forCups
#assert_no_axioms FX1Poly.Polygraph.stringQuadTwoCell_codPack_uniqueOfDom_forCaps
#assert_no_axioms FX1Poly.Polygraph.natListEqB
#assert_no_axioms FX1Poly.Polygraph.natWordListAllDistinct
#assert_no_axioms FX1Poly.Polygraph.natWordListsCrossDisjoint
#assert_no_axioms FX1Poly.Polygraph.cupCods_allDistinct_atThree
#assert_no_axioms FX1Poly.Polygraph.cupCods_allDistinct_atFour
#assert_no_axioms FX1Poly.Polygraph.capDoms_allDistinct_atThree
#assert_no_axioms FX1Poly.Polygraph.capDoms_allDistinct_atFour
#assert_no_axioms FX1Poly.Polygraph.cupCapCrossDisjoint_atThree
#assert_no_axioms FX1Poly.Polygraph.cupCapCrossDisjoint_atFour
#assert_no_axioms FX1Poly.Polygraph.collapsedCupDoms_notAllDistinct
#assert_no_axioms FX1Poly.Polygraph.quadCupAtomBase
#assert_no_axioms FX1Poly.Polygraph.quadCapAtomBase
#assert_no_axioms FX1Poly.Polygraph.quadCupAtom_isCup
#assert_no_axioms FX1Poly.Polygraph.quadCapAtom_isCap
#assert_no_axioms FX1Poly.Polygraph.quadEngineCupFires
#assert_no_axioms FX1Poly.Polygraph.quadEngineCupCapClosesLoop
#assert_no_axioms FX1Poly.Polygraph.quadLocateFiresOnCupThenCap
#assert_no_axioms FX1Poly.Polygraph.quadLocateDeclinesOnCupThenCup
#assert_no_axioms FX1Poly.Polygraph.fxString_hasQuadrupleAtomPinReroute
#assert_no_axioms FX1Poly.Polygraph.fxString_hasKGenericConnectivityEngineFired

end FX1PolyAudit
