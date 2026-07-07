import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteLift

/-! # FX1PolyAudit/…/SpineValleyCommuteLift — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I COMMUTE producer brick: the atom-prefix trace-equivalence
congruence (`spineTraceEquiv_prependAtoms`, folding `SpineTraceEquiv.consCongr`), the prefixed swap → cell
conversion (`commutePrefixSwapCellLift`, `toGodementStep` → `ofStep` → prepend → `ofSpineTraceEquiv`), and the
COMMUTE `CellDescentResult` builder from the flat located swap (`cellDescentResult_ofCommutePrefixSwap`, chaining
into `cellDescentResult_ofCommuteStep`).  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_prependAtoms
#assert_no_axioms FX1Poly.Polygraph.commutePrefixSwapCellLift
#assert_no_axioms FX1Poly.Polygraph.cellDescentResult_ofCommutePrefixSwap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCommuteLift

end FX1PolyAudit
