import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapChain

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SwapChain — zero-axiom gate

Per-declaration zero-axiom gate for the single-swap chain normalization of the atomic
trace closure.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.OneAdjacentSwap.symm
#assert_no_axioms FX1Poly.Polygraph.OneAdjacentSwap.toAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.OneAdjacentSwapChain.trans
#assert_no_axioms FX1Poly.Polygraph.OneAdjacentSwapChain.symm
#assert_no_axioms FX1Poly.Polygraph.OneAdjacentSwapChain.consCongr
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.toOneAdjacentSwapChain
#assert_no_axioms FX1Poly.Polygraph.oneAdjacentSwapChain_iff_atomicTraceEquiv

end FX1PolyAudit
