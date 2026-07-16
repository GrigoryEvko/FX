import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingTraced.TracedDiagramBoxCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingTraced.TracedDiagramBoxCount — zero-axiom gate (the genuine-generator count invariant + SOUNDNESS)

Per-declaration zero-axiom gate for the walking traced PROP genuine-generator invariant: the `boxCount` fold and
its defining / sample-diagram smokes, the SOUNDNESS theorem `boxCount_congr_of_conv`, the non-vacuity witnesses (an
axiom fires positively; non-convertible pairs separate by `boxCount`), the witnessed-incompleteness collision, and
the markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.boxCount
#assert_no_axioms FX1Poly.Polygraph.boxCount_empty
#assert_no_axioms FX1Poly.Polygraph.boxCount_idWire
#assert_no_axioms FX1Poly.Polygraph.boxCount_box
#assert_no_axioms FX1Poly.Polygraph.boxCount_swap
#assert_no_axioms FX1Poly.Polygraph.boxCount_seq
#assert_no_axioms FX1Poly.Polygraph.boxCount_tensor
#assert_no_axioms FX1Poly.Polygraph.boxCount_traceN
#assert_no_axioms FX1Poly.Polygraph.boxCount_yankingLeft
#assert_no_axioms FX1Poly.Polygraph.boxCount_vanishingBoxLeft
#assert_no_axioms FX1Poly.Polygraph.boxCount_tighteningLeft
#assert_no_axioms FX1Poly.Polygraph.boxCount_tighteningRight
#assert_no_axioms FX1Poly.Polygraph.boxCount_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.tracedConv_yanking_idWire
#assert_no_axioms FX1Poly.Polygraph.boxCount_vanishingBoxLeft_eq_box_via_soundness
#assert_no_axioms FX1Poly.Polygraph.boxCount_tightening_eq_via_soundness
#assert_no_axioms FX1Poly.Polygraph.tracedNotConv_box_idWire
#assert_no_axioms FX1Poly.Polygraph.tracedNotConv_tensorBoxBox_box
#assert_no_axioms FX1Poly.Polygraph.boxCount_swap_eq_tensorIdWireIdWire
#assert_no_axioms FX1Poly.Polygraph.fxTraced_hasSignatureAndTraceInvariant
#assert_no_axioms FX1Poly.Polygraph.fxTraced_hasSignatureAndBoxCountSoundness
#assert_no_axioms FX1Poly.Polygraph.fxTraced_hasWordProblemDecided

end FX1PolyAudit
