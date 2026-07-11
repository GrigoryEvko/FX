import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AllCupAritySwapTransport

/-! # FX1PolyAudit/…/AllCupAritySwapTransport — zero-axiom gate

Per-declaration zero-axiom gate for the DIRECT (classifier-free, signature-generic) transport of
the pure-cup regime along the atomic swap: the swap keeps each atom's generator, so the cup
arities transport by matching the swap constructor and inverting the two head arities.  The
biconditional closure `allCupArity_iff_ofAtomicTraceEquiv` is the Route-B keystone that lets the
pure-cup peel drop the walking-adjunction classifier `adjunctionSpineAtom_isCupOrCap`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.allCupArity_ofAtomicSwap
#assert_no_axioms FX1Poly.Polygraph.allCupArity_ofAtomicSwap_rev
#assert_no_axioms FX1Poly.Polygraph.allCupArity_atomicConsCongr
#assert_no_axioms FX1Poly.Polygraph.allCupArity_iff_ofAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasAllCupAritySwapTransport

end FX1PolyAudit
