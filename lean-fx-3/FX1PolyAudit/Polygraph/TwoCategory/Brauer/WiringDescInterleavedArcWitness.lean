import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescInterleavedArcWitness

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescInterleavedArcWitness — zero-axiom gate (BRAUER r32)

Per-declaration zero-axiom gate for the interleaved-arc witness: the diagram identity, the load-bearing straddle
step, the three-move corrected-form reach, the fourth (straddle) sink rung and its clean instance, the boundary
decomposition of the global straddle monovariant and its clean corollary, the honesty markers, and the machine-checked
terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.interleavedArc_diagramEq_singleCrossing
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_interleavedArc_straddleStep
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_interleavedArc_reachesCorrectedForm
#assert_no_axioms FX1Poly.Polygraph.arcSink_straddle
#assert_no_axioms FX1Poly.Polygraph.arcSink_straddle_clean
#assert_no_axioms FX1Poly.Polygraph.straddleWindowBit
#assert_no_axioms FX1Poly.Polygraph.straddleBoundaryCount
#assert_no_axioms FX1Poly.Polygraph.straddleCount_append_decomposes
#assert_no_axioms FX1Poly.Polygraph.straddleCount_isAdditive_ofCleanBoundary
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInterleavedArcWitness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleSinkRung
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleBoundaryDecomposition
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInterleavedArcGlobalFold
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_interleavedArcTerminalState

end FX1PolyAudit
