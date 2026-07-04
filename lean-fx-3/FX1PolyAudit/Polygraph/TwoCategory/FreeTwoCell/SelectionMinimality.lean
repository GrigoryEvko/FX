import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SelectionMinimality

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SelectionMinimality — zero-axiom gate

Per-declaration zero-axiom gate for the measure order kit and the minimal-selection
certificates (membership + measure-minimality + tie component equalities).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natLtOfBltIsTrue
#assert_no_axioms FX1Poly.Polygraph.natBltIsTrueOfLt
#assert_no_axioms FX1Poly.Polygraph.natBltSelfIsFalse
#assert_no_axioms FX1Poly.Polygraph.natBeqSelfIsTrue
#assert_no_axioms FX1Poly.Polygraph.natBeqIsTrueOfEq
#assert_no_axioms FX1Poly.Polygraph.natLtOrEqOrGt
#assert_no_axioms FX1Poly.Polygraph.boolOrLeftIsTrue
#assert_no_axioms FX1Poly.Polygraph.boolOrRightIsTrue
#assert_no_axioms FX1Poly.Polygraph.boolAndIsTrueOfBoth
#assert_no_axioms FX1Poly.Polygraph.MeasureLexBelow
#assert_no_axioms FX1Poly.Polygraph.measureLexBelow_ofSmallerIsTrue
#assert_no_axioms FX1Poly.Polygraph.smallerIsTrue_ofMeasureLexBelow
#assert_no_axioms FX1Poly.Polygraph.measureLexBelow_irrefl
#assert_no_axioms FX1Poly.Polygraph.measureLexBelow_trans
#assert_no_axioms FX1Poly.Polygraph.measureLexBelow_trichotomy
#assert_no_axioms FX1Poly.Polygraph.isMeasureLexSmaller_irrefl
#assert_no_axioms FX1Poly.Polygraph.isMeasureLexSmaller_trans
#assert_no_axioms FX1Poly.Polygraph.smallerIsFalse_ofBeatenBelow
#assert_no_axioms FX1Poly.Polygraph.smallerIsFalse_chain
#assert_no_axioms FX1Poly.Polygraph.measureComponentsEq_ofNeitherSmaller
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction_consWinner
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction_consKeeper
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction_isHeadOrMember
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction_isUnbeaten
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction_isMemberOfCandidates
#assert_no_axioms FX1Poly.Polygraph.selectMinimalExtraction_isUnbeatenByMember

end FX1PolyAudit
