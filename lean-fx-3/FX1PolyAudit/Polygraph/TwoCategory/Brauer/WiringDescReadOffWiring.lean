import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReadOffWiring

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescReadOffWiring — zero-axiom gate (BRAUER-MIDDLE r11 B3+B5)

Per-declaration zero-axiom gate for the wired read-off firings and the machine-checked r11 ledger: the explicit
crossing well-formedness witness (`wellFormedBrauerFold_crossingSeed`), the wired firings
(`readOffWired_capThenCup`, `readOffWired_crossing`), the honesty marker (`fxBrauer_hasReadOffWiredFiring`), the
grand ledger (`fxBrauer_r11Ledger`), and the terminal marker (`fxBrauer_hasBrauerMiddleR11Complete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the explicit crossing well-formedness witness
#assert_no_axioms FX1Poly.Polygraph.wellFormedBrauerFold_crossingSeed

-- the wired read-off firings
#assert_no_axioms FX1Poly.Polygraph.readOffWired_capThenCup
#assert_no_axioms FX1Poly.Polygraph.readOffWired_crossing

-- the honesty marker + the machine-checked grand ledger + the terminal marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffWiredFiring
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r11Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR11Complete

end FX1PolyAudit
