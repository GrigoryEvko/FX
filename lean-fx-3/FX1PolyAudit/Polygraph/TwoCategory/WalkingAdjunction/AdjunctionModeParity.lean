import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionModeParity

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/AdjunctionModeParity — zero-axiom gate

Per-declaration zero-axiom gate for the parity substrate: the opposite-mode involution, the
modality target pin, the distance formula with its two composition laws, and the absolute
path-target formula.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionOppositeMode_isInvolutive
#assert_no_axioms FX1Poly.Polygraph.adjunctionModality_targetsOppositeMode
#assert_no_axioms FX1Poly.Polygraph.adjunctionModeAtDistance_fromOppositeStart
#assert_no_axioms FX1Poly.Polygraph.adjunctionModeAtDistance_add
#assert_no_axioms FX1Poly.Polygraph.adjunctionPath_targetMode_eq_modeAtDistance

end FX1PolyAudit
