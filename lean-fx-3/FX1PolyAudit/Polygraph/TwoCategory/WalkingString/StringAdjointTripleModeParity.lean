import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointTripleModeParity

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringAdjointTripleModeParity — zero-axiom gate
(FC-3 r22, B2 P1)

Per-declaration zero-axiom gate for the adjoint-triple parity substrate: the opposite-mode involution, the
targets-opposite-mode fact, the distance recursion and its from-opposite / add laws, the absolute mode formula,
the two-shift stability, the atom window-position-mode pin, and the marker.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjointTripleOppositeMode
#assert_no_axioms FX1Poly.Polygraph.adjointTripleOppositeMode_isInvolutive
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModality_targetsOppositeMode
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModeAtDistance
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModeAtDistance_fromOppositeStart
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModeAtDistance_add
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModalityPath_targetMode_eq_modeAtDistance
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModeAtDistance_stableUnderTwoShift
#assert_no_axioms FX1Poly.Polygraph.adjointTripleAtom_windowPositionMode
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleModeParity

end FX1PolyAudit
