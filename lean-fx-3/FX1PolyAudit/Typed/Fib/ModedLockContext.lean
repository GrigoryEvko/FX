import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.ModedLockContext

/-! # FX1PolyAudit.Typed.Fib.ModedLockContext — zero-axiom gate (fib-3 #3)

Per-declaration zero-axiom gate for the mode-indexed lock telescope whose `locks(Δ)` composes real
`ModalityPath`s: the `ModedContext` inductive, its `atMode` / `baseModeOf` accessors, the `locksOf` suffix-lock
composition and its unfolders (empty / CX/EXTEND transparency / CX/LOCK composition), the associative
two-lock composite, and the two affine seals that specialize back to the shipped `obligationModalityToPath`
values.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.ModedContext
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.atMode
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.baseModeOf
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.locksOf
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.locksOf_empty
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.locksOf_cons
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.locksOf_lockCons
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.locksOf_lockCons_lockCons
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineSingleLockContext
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineSingleLockContext_locks
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineExtendContext
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineExtendContext_locks

end FX1PolyAudit
