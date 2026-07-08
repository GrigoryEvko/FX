import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyOracleDispatch

/-! # FX1PolyAudit/…/SpineValleyOracleDispatch — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I per-step oracle dispatch: the Type-valued locate
(`locateCupThenCap_of_cup_of_not_allCups`, `locateCupThenCap_of_not_valley`, `locateCupThenCapSpine`), the CLOSED
dispatch (`valleyCellDescentStepOracle`, both COMMUTE and STRAIGHTEN halves discharged), and the sharpened
reduction of `MatchingReductsShareSpineTrace` to `CellValleyTraceEquiv` ALONE
(`matchingReductsShareSpineTrace_of_valleyTraceEquiv`).  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.locateCupThenCap_of_cup_of_not_allCups
#assert_no_axioms FX1Poly.Polygraph.locateCupThenCap_of_not_valley
#assert_no_axioms FX1Poly.Polygraph.locateCupThenCapSpine
#assert_no_axioms FX1Poly.Polygraph.valleyCellDescentStepOracle
#assert_no_axioms FX1Poly.Polygraph.matchingReductsShareSpineTrace_of_valleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyOracleDispatch

end FX1PolyAudit
