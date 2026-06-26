import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.UniverseElDecode

/-! # FX1PolyAudit.Core.Fib.UniverseElDecode — zero-axiom gate (fib-2b)

Per-declaration zero-axiom gate for the bridge's typing tie-in (the bridged code typed at the bridged successor
via universeFormation) and the El decode (the bridged universe's Tarski membership semantics). Must be free of
propext, Quot.sound, Classical, sorry, native_decide, omega. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_typedAtSuccessor
#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_tarskiDecode
#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_universeMembership_iff
#assert_no_axioms FX1Poly.Core.Fib.typeTermUniverseReflection

end FX1PolyAudit
