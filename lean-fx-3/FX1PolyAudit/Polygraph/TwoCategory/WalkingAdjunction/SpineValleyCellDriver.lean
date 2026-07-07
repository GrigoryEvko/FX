import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellDriver

/-! # FX1PolyAudit/…/SpineValleyCellDriver — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I mixed cell driver: the fuel-structural
`SaturatedTwoCellConv`-valued descent (accumulation + termination) and the honest reduction of
`MatchingReductsShareSpineTrace` to (per-step oracle) ∧ (cell-level Piece II) must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.valleyDescentDriverCell
#assert_no_axioms FX1Poly.Polygraph.valleyNFCell
#assert_no_axioms FX1Poly.Polygraph.cellDescentConv
#assert_no_axioms FX1Poly.Polygraph.valleyNFCell_isValley
#assert_no_axioms FX1Poly.Polygraph.matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCellDriver

end FX1PolyAudit
