import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapBoundary

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/AtomicSwapBoundary — zero-axiom gate

Per-declaration zero-axiom gate for the boundary-chain transfer along atomic swaps and the
full atomic trace equivalence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.composePath_length_double
#assert_no_axioms FX1Poly.Polygraph.natSumFive_ofNestedTail
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_target_of_spineAtomSwap
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_source_of_spineAtomSwap
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_iff_of_atomicTraceEquiv

end FX1PolyAudit
