import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/AtomicSwap — zero-axiom gate

Per-declaration zero-axiom gate for the atomic swap data layer, the Godement embedding, the
atomic closure with its inclusion, the list transport, and the prefix congruence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.toGodementStep
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.toSpineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.castList
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.prependSpineDiff
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasAtomicSwapGeneration

end FX1PolyAudit
