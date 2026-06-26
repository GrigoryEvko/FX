import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.ModeLockMultiplier

/-! # FX1PolyAudit.Core.Fib.ModeLockMultiplier — zero-axiom gate (fib-3a / A1-FIB3-SEED)

Per-declaration zero-axiom gate for the Core→Tier0/Mode rewire: the affine dimension lock's mode-12 void
multiplier, its unpointedness, and the wiring tying the kernel's structural fibrant-inaccessibility to the
mode-axis unpointedness. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.affineDimensionLockMultiplier
#assert_no_axioms FX1Poly.Core.Fib.affineDimensionLockMultiplier_isUnpointable
#assert_no_axioms FX1Poly.Core.Fib.lockFibrantInaccessibility_witnessedByUnpointedMultiplier

end FX1PolyAudit
