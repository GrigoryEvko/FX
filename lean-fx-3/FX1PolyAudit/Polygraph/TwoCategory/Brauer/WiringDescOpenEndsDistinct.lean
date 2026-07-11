import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescOpenEndsDistinct

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescOpenEndsDistinct — zero-axiom gate (BRAUER r30 B2 cap side)

Per-declaration zero-axiom gate for the zero-loops invariant and its cap side: the fresh-seed distinctness
(`brauerOpenEndsDistinct_seed`, S), the cap's unconditional-join link update (`stepWiring_cap_links`), the cap
zero-loop on a distinct pair (`stepWiring_cap_loops_ofDistinct`, C1), the cap distinctness preservation
(`brauerOpenEndsDistinct_stepWiringCap`, C2), and the honesty marker `fxBrauer_hasOpenEndsDistinctCapSide`.

Independent `#print axioms` (scratch) reported every decl as "does not depend on any axioms".  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- Section 1: the fresh seed satisfies the invariant
#assert_no_axioms FX1Poly.Polygraph.brauerOpenEndsDistinct_seed

-- Section 2: the cap's link update is an unconditional join
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cap_links

-- Section 3: (C1) a cap on a distinct pair closes no loop
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cap_loops_ofDistinct

-- Section 4: (C2) a cap preserves distinctness
#assert_no_axioms FX1Poly.Polygraph.brauerOpenEndsDistinct_stepWiringCap

-- Section 5: the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasOpenEndsDistinctCapSide

end FX1PolyAudit
