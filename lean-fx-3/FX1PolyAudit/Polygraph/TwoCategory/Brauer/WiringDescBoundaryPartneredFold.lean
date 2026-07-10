import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartneredFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartneredFold — zero-axiom gate (BRAUER-MIDDLE r12)

Per-declaration zero-axiom gate for the partner-TOTALITY fold: the three per-atom preservations
(`boundaryPartnered_stepCup` / `_stepCrossing` / `_stepCap`), the per-atom dispatch and whole-fold lift
(`boundaryPartnered_stepBrauerAtom` / `_processBrauer`), the seed payoff (`boundaryPartnered_reachable`), the
universal read-off corollary (`partnerIndexOf_readsPartner_reachable`), the non-vacuity witnesses, and the
honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the three per-atom partner-totality preservations
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_stepCup
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_stepCrossing
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_stepCap

-- the per-atom dispatch + the whole-fold lift + the seed payoff
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_stepBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_processBrauer
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_reachable

-- the universal read-off corollary
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsPartner_reachable

-- non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_reachable_capThenCup
#assert_no_axioms FX1Poly.Polygraph.boundaryPartnered_capThenCup_firing

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBoundaryPartneredFoldLift
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTagCorrMastersFromTotality

end FX1PolyAudit
