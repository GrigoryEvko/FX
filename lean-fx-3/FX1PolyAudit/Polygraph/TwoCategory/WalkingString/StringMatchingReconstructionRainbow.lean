import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionRainbow

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionRainbow — zero-axiom gate

Per-declaration zero-axiom gate for the FC-8 reconstruction-route realization: the endo through-strand and
cross-level reconstructions, the three recon evals (`F`-snake, the FC-7 counterexample collapse, the cross-level
valley), the `F`-snake-stack `convToReconstruct` closure, the matching-underdetermines-colour sharpening, the FC-2
count cross-check, and the two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringReconstructIdentityForm
#assert_no_axioms FX1Poly.Polygraph.stringReconstructCrossLevel
#assert_no_axioms FX1Poly.Polygraph.stringReconstructIdentityForm_left_eq_identityF
#assert_no_axioms FX1Poly.Polygraph.stringReconstruct_snakeF_convToReconstruct
#assert_no_axioms FX1Poly.Polygraph.stringReconstructIdentityForm_right_eq_identityG
#assert_no_axioms FX1Poly.Polygraph.stringReconstruct_collapses_fc7Pair
#assert_no_axioms FX1Poly.Polygraph.stringReconstructCrossLevel_matchingOf
#assert_no_axioms FX1Poly.Polygraph.stringReconstruct_crossLevel_convToReconstruct
#assert_no_axioms FX1Poly.Polygraph.stringReconstruct_snakeStackF_convToReconstruct
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGlo_snakeGhi_matchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGlo_ne_identityG
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGhi_ne_identityG
#assert_no_axioms FX1Poly.Polygraph.stringReconstruct_matchingUnderdeterminesColour
#assert_no_axioms FX1Poly.Polygraph.stringReconstructTargetCount_two
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReconstructionRainbowRealized
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReconstructionRouteFlip

end FX1PolyAudit
