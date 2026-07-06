import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomCountTraceInvariance

/-! # FX1PolyAudit/…/AtomCountTraceInvariance — zero-axiom gate

Per-declaration zero-axiom gate for the cup/cap atom-count trace invariance: two spine lists related
by `AtomicTraceEquiv` carry equal cup and cap atom counts (the swap keeps each atom's generator).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupAtomCount_eq_of_atomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.capAtomCount_eq_of_atomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasAtomCountTraceInvariance

end FX1PolyAudit
