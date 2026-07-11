import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR30Ledger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerR30Ledger — zero-axiom gate (BRAUER r30 B5)

Per-declaration zero-axiom gate for the r30 grand ledger: the machine-checked `rfl`-conjunction
`fxBrauer_r30GrandLedger` (leg 1 circle accounting + leg 2 invariant/preservation `true`; loops-field assembly and all
masters `false`) and the honesty marker `fxBrauer_hasBrauerR30Complete`.

Independent `#print axioms` (scratch) reported every decl as "does not depend on any axioms".  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r30GrandLedger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerR30Complete

end FX1PolyAudit
