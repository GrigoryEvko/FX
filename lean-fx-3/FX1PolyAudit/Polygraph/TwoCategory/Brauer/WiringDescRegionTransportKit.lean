import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescRegionTransportKit

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescRegionTransportKit — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r41 J-transport reshape kit: the `Eq.rec`-with-explicit-motive transport
combinator (`RegionCupOutcome.transportByRegionEq`) and its fate-preservation (`transportByRegionEq_fate`), the
hand-rolled `&&`-split (`andEqTrue_left` / `andEqTrue_right`), the crossing reconstruction chain
(`arcsAreCrossing_reconstruct` / `crossingWiring_reconstruct` / `crossingAtom_reconstruct`), the per-arm reshape
(`transportCrossingHead`), the honesty marker, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the `Eq.rec` transport with an
explicit motive, the hand-rolled `&&`-split (`Bool.and_eq_true` leaks `propext`), `Nat.eq_of_beq_eq_true`, the
list-of-pairs inversion, and structure eta are all axiom-free (`Bool.and_eq_true`, `Nat.sub_*`, `List.append_assoc` are
deliberately avoided).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RegionCupOutcome.transportByRegionEq
#assert_no_axioms FX1Poly.Polygraph.andEqTrue_left
#assert_no_axioms FX1Poly.Polygraph.andEqTrue_right
#assert_no_axioms FX1Poly.Polygraph.arcsAreCrossing_reconstruct
#assert_no_axioms FX1Poly.Polygraph.crossingWiring_reconstruct
#assert_no_axioms FX1Poly.Polygraph.crossingAtom_reconstruct
#assert_no_axioms FX1Poly.Polygraph.transportCrossingHead
#assert_no_axioms FX1Poly.Polygraph.transportByRegionEq_fate
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRegionOutcomeTransportKit
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_regionTransportKitTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.RegionCupOutcome.transportByRegionEq
#print axioms FX1Poly.Polygraph.crossingAtom_reconstruct
#print axioms FX1Poly.Polygraph.transportCrossingHead
#print axioms FX1Poly.Polygraph.transportByRegionEq_fate
#print axioms FX1Poly.Polygraph.fxBrauer_regionTransportKitTerminalState

end FX1PolyAudit
