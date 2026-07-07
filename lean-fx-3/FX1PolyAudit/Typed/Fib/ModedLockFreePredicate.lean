import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.ModedLockFreePredicate

/-! # FX1PolyAudit.Typed.Fib.ModedLockFreePredicate — zero-axiom gate (#7B)

Per-declaration zero-axiom gate for the decidable lock-free predicate over the mode-indexed lock telescope and
the REAL discharge of the retirement Tier E `ofGrownReflected` side condition: `ModedContext.isLockFree` with
its unfolders and decidability, the general `locks` length-zero bridge, the affine-seal `locks`-identity
bridge, the kernel `toModedShape` reflection, the mode-theoretic meaning of lock-freeness, and the decided
`ofGrownReflected` capstone.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.ModedContext.isLockFree
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.isLockFree_empty
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.isLockFree_cons
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.isLockFree_lockCons
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.decidableIsLockFree
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.lockFreeImpliesLocksLengthZero
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineLockFreeImpliesLocksIdentityOverMode
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineLockFreeImpliesLocksIdentity
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineSingleLockContextNotLockFree
#assert_no_axioms FX1Poly.Core.Fib.ModedContext.affineExtendContextIsLockFree
#assert_no_axioms FX1Poly.Typed.TypingContext.toModedShape
#assert_no_axioms FX1Poly.Typed.isLockFreeContext_eq_toModedShape_isLockFree
#assert_no_axioms FX1Poly.Typed.TypingContext.lockFreeImpliesShapeLocksIdentity
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.ofGrownReflectedDecidably

end FX1PolyAudit
