import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.Ledger — zero-axiom gate for the POLY-TAB r0 aggregate verdict
(POLY-TAB r0, T5).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_polyTabR0Complete
#assert_no_axioms FX1Poly.Polygraph.Table.polyTabR0Complete_holds
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_falsifiabilityCheckPassed

end FX1PolyAudit
