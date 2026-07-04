import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapSuccessorEnumeration

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SwapSuccessorEnumeration — zero-axiom gate

Per-declaration zero-axiom gate for the saturation search's move layer: the one-swap
successor enumeration with its soundness and completeness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listMemMapOfMem
#assert_no_axioms FX1Poly.Polygraph.listMemMapInverted
#assert_no_axioms FX1Poly.Polygraph.swapSuccessors
#assert_no_axioms FX1Poly.Polygraph.swapSuccessors_isSound
#assert_no_axioms FX1Poly.Polygraph.swapSuccessors_isComplete

end FX1PolyAudit
