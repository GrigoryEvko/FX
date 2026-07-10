import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.LedgerR1

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.LedgerR1 — zero-axiom gate for the POLY-TAB r1 aggregate verdict +
grown deletion list + POLY-TAB-2 plan (POLY-TAB r1, P4 + P5).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_polyTabR1Complete
#assert_no_axioms FX1Poly.Polygraph.Table.polyTabR1Complete_holds
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_polyTabR1LedgerComplete
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_hasMonadNativeRefounding
#assert_no_axioms FX1Poly.Polygraph.Table.hasMonadNativeRefounding_holds

end FX1PolyAudit
