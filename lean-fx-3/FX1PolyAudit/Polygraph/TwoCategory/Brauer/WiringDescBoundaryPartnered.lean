import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartnered

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartnered — zero-axiom gate (BRAUER-MIDDLE r11 B1)

Per-declaration zero-axiom gate for the partner-totality existence leg: the invariant (`boundaryPartnered`), the
seed base case (`boundaryPartnered_seed`), the non-vacuity witnesses (`boundaryPartnered_seed_two`,
`boundaryPartnered_seedPair_firing`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the partner-totality invariant + the seed base case
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_seed

-- non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_seed_two
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_seedPair_firing

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundaryPartneredSeed
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundaryPartneredFold

end FX1PolyAudit
