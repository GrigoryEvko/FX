import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenFactor

/-! # FX1PolyAudit/…/SpineValleyStraightenFactor — zero-axiom gate

Per-declaration zero-axiom gate for the STRAIGHTEN 2a local factorization: the `zigZagSharedLeg` → window-distance-1
extraction (`natWindowDistance_eq_one_of_zigZag`), the width dichotomy (`zigZagSharedLeg_widthDichotomy`), and the
two handedness factorizations forced by seed rigidity from the boundary word + width relation
(`sharedLegFactorHandednessA` / `sharedLegFactorHandednessB`).  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natWindowDistance_eq_one_of_zigZag
#assert_no_axioms FX1Poly.Polygraph.zigZagSharedLeg_widthDichotomy
#assert_no_axioms FX1Poly.Polygraph.sharedLegFactorHandednessA
#assert_no_axioms FX1Poly.Polygraph.sharedLegFactorHandednessB
#assert_no_axioms FX1Poly.Polygraph.capAtom_generatorCod_length_zero
#assert_no_axioms FX1Poly.Polygraph.cupCapDeletionReconnects
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenFactor

end FX1PolyAudit
