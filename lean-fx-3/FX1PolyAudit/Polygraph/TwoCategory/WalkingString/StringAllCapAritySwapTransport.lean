import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAllCapAritySwapTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringAllCapAritySwapTransport — zero-axiom gate
(FC-3 r22, B2 P4)

Per-declaration zero-axiom gate for the pure-cap arity transport along the atomic swap: the two one-swap
transports, the head-cons congruence, the biconditional closure, the forward extraction, and the marker.  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.allCapArity_ofAtomicSwap
#assert_no_axioms FX1Poly.Polygraph.allCapArity_ofAtomicSwap_rev
#assert_no_axioms FX1Poly.Polygraph.allCapArity_atomicConsCongr
#assert_no_axioms FX1Poly.Polygraph.allCapArity_iff_ofAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.allCapArity_preservedOfAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasAllCapAritySwapTransport

end FX1PolyAudit
