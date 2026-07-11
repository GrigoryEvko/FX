import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingDistinct

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCrossingDistinct — zero-axiom gate (BRAUER r30 B2 X)

Per-declaration zero-axiom gate for the crossing preservation of the zero-loops invariant: the heaviest per-step
lemma `brauerOpenEndsDistinct_stepWiringCrossing` (an in-range crossing preserves `BrauerOpenEndsDistinct`, the
pullback of the base invariant along the window transposition) and the honesty marker
`fxBrauer_hasOpenEndsDistinctCrossing`.

Independent `#print axioms` (scratch) reported every decl as "does not depend on any axioms".  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- (X) the crossing preserves distinctness
#assert_no_axioms FX1Poly.Polygraph.brauerOpenEndsDistinct_stepWiringCrossing

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasOpenEndsDistinctCrossing

end FX1PolyAudit
