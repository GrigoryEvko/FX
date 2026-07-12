import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidCupReadoff

/-! # FX1PolyAudit.…WalkingString.StringGenericMidCupReadoff — zero-axiom gate (FC-4 r6, the readoff tranche)

Per-declaration zero-axiom gate for the generic mid-width cup readoff bricks: the OFFSET short-chord readoff, the
two chord-shift descents, the cup-end open-wire split, each `k = 2` recovery pair (shipped inhabitant + generic-at-
two), the `k = 3` fires with their quad fixtures and computed-matching certificates, the negative control, and the
marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` (in particular the
`by decide` matching certificates and fires pull no `propext`). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.genericMatchingLastCup_isShortChord_mid
#assert_no_axioms FX1Poly.Polygraph.genericMatchingChordShift_below_mid
#assert_no_axioms FX1Poly.Polygraph.genericMatchingChordShift_above_mid
#assert_no_axioms FX1Poly.Polygraph.genericMatchingOpenWiresCupEndSplit_mid
#assert_no_axioms FX1Poly.Polygraph.stringShortChordMid_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringShortChordMid_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringChordShiftBelowMid_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringChordShiftBelowMid_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringChordShiftAboveMid_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringChordShiftAboveMid_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringCupEndSplitMid_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringCupEndSplitMid_viaGenericSignatureAtTwo
#assert_no_axioms FX1Poly.Polygraph.quadMidOneCupOverL1
#assert_no_axioms FX1Poly.Polygraph.quadMidOneCupOverL1_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.genericShortChordMid_firesAtThree
#assert_no_axioms FX1Poly.Polygraph.quadCupEndFixture
#assert_no_axioms FX1Poly.Polygraph.genericCupEndSplit_firesAtThree
#assert_no_axioms FX1Poly.Polygraph.quadCupWindowTwo
#assert_no_axioms FX1Poly.Polygraph.quadBelowFixture
#assert_no_axioms FX1Poly.Polygraph.quadBelowFixture_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.quadBelowPrefix_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.genericChordShiftBelowMid_firesAtThree
#assert_no_axioms FX1Poly.Polygraph.quadCupWindowZeroRideTwo
#assert_no_axioms FX1Poly.Polygraph.quadAboveFixture
#assert_no_axioms FX1Poly.Polygraph.quadAboveFixture_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.genericChordShiftAboveMid_firesAtThree
#assert_no_axioms FX1Poly.Polygraph.genericShortChordMid_firesAtThree_notFixed
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericMidCupReadoff

end FX1PolyAudit
