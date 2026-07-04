import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineTraceReconstruction — zero-axiom gate

Per-declaration zero-axiom gate for the count rearrangement, the chainability transports, the
readback conversion along the trace equivalence, the reconstruction headline, the
characterization, and the flipped marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natAdd_middleFourExchange
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.chainNonempty_ofSpineDiffCountEq
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.chainNonempty_iff
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.readback_convFull
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.twoCellConvFull_iff_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineTraceReconstruction

end FX1PolyAudit
