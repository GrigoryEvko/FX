import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCupWindowProvisos

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCupWindowProvisos — zero-axiom gate

Per-declaration zero-axiom gate for the discharged single-cup partner-scan window provisos: the fresh cup legs
miss a below-fresh survivor's component, and its `windowPairFails` boolean shape.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCup_freshLeg_offSurvivor
#assert_no_axioms FX1Poly.Polygraph.stepCup_windowPairFails_atFreshLegs
#assert_no_axioms FX1Poly.Polygraph.cupBlock_frontFails_ofMidIsolated
#assert_no_axioms FX1Poly.Polygraph.stepCup_unionFindRootOf_oldNode
#assert_no_axioms FX1Poly.Polygraph.testCorr_ofCorrespondences

end FX1PolyAudit
