import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.UniverseCodeBridge

/-! # FX1PolyAudit.Typed.Fib.UniverseCodeBridge — zero-axiom gate (fib-2a)

Per-declaration zero-axiom gate for the type ↔ term universe-code bridge: the forward bridge, the on-the-nose
payload coincidence, the data-level round-trip, and the successor↔level-bump coherence. All rfl-level; must be
free of propext, Quot.sound, Classical, sorry, native_decide, omega. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell
#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_unfold
#assert_no_axioms FX1Poly.Core.Fib.payloadToAxisCode
#assert_no_axioms FX1Poly.Core.Fib.payloadToAxisCode_roundTrip
#assert_no_axioms FX1Poly.Core.Fib.axisSuccessor_eq_levelBump
#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_preserves_level

end FX1PolyAudit
