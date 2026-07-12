import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidCupReadoff

/-! # FX1PolyAudit.…WalkingString.StringGenericMidCupReadoffAxiomWitness — INDEPENDENT axiom witness (FC-4 r6)

The trusted independent cross-check for the generic mid-width cup readoff bricks: raw `#print axioms` (the built-in,
NOT the custom `#assert_no_axioms` command) on the OFFSET short-chord readoff, the two chord-shift descents, the
cup-end split, each `k = 2` recovery pair, the `k = 3` fires with their quad fixtures and computed-matching
certificates, the negative control, and the marker.  Each must print `does not depend on any axioms` (in particular
the `by decide` certificates and fires pull no `propext`). -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.genericMatchingLastCup_isShortChord_mid
#print axioms FX1Poly.Polygraph.genericMatchingChordShift_below_mid
#print axioms FX1Poly.Polygraph.genericMatchingChordShift_above_mid
#print axioms FX1Poly.Polygraph.genericMatchingOpenWiresCupEndSplit_mid
#print axioms FX1Poly.Polygraph.stringShortChordMid_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringShortChordMid_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringChordShiftBelowMid_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringChordShiftBelowMid_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringChordShiftAboveMid_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringChordShiftAboveMid_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringCupEndSplitMid_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringCupEndSplitMid_viaGenericSignatureAtTwo
#print axioms FX1Poly.Polygraph.quadMidOneCupOverL1
#print axioms FX1Poly.Polygraph.quadMidOneCupOverL1_matchingComputes
#print axioms FX1Poly.Polygraph.genericShortChordMid_firesAtThree
#print axioms FX1Poly.Polygraph.quadCupEndFixture
#print axioms FX1Poly.Polygraph.genericCupEndSplit_firesAtThree
#print axioms FX1Poly.Polygraph.quadCupWindowTwo
#print axioms FX1Poly.Polygraph.quadBelowFixture
#print axioms FX1Poly.Polygraph.quadBelowFixture_matchingComputes
#print axioms FX1Poly.Polygraph.quadBelowPrefix_matchingComputes
#print axioms FX1Poly.Polygraph.genericChordShiftBelowMid_firesAtThree
#print axioms FX1Poly.Polygraph.quadCupWindowZeroRideTwo
#print axioms FX1Poly.Polygraph.quadAboveFixture
#print axioms FX1Poly.Polygraph.quadAboveFixture_matchingComputes
#print axioms FX1Poly.Polygraph.genericChordShiftAboveMid_firesAtThree
#print axioms FX1Poly.Polygraph.genericShortChordMid_firesAtThree_notFixed
#print axioms FX1Poly.Polygraph.fxString_hasGenericMidCupReadoff

end FX1PolyAudit
