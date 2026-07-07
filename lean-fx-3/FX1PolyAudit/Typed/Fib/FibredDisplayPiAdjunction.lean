import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.FibredDisplayPiAdjunction

/-! # FX1PolyAudit.Typed.Fib.FibredDisplayPiAdjunction — zero-axiom gate (honest weak `weaken ⊣ Π` bundle)

Per-declaration zero-axiom gate for the WEAK fibred-Π adjunction bundle — the honest bounded stand-in for the
impossible `ContextLock` promotion of `fxWeakeningLock`: the `FibredDisplayPiAdjunction` `Prop`-bundle of the
four shipped ContextDisplayPi theorems and its witness.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.FibredDisplayPiAdjunction
#assert_no_axioms FX1Poly.Core.Fib.fibredDisplayPiAdjunctionWitness

end FX1PolyAudit
