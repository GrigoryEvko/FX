import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TypingTableBundle

/-! # AuditTypingTableBundle — zero-axiom gate for TYTAB-1 brick 1

The static-side typing-table bundle (the mirror of the RW-5 `RuleTableBundle`): the
`fxTypingBundle` value gathering all nineteen shipped typing dispatchers, and the faithfulness
certificate that every field is definitionally the existing table.  Each pin must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.fxTypingBundle
#assert_no_axioms FX1Poly.Typed.fxTypingBundle_faithful

end FX1PolyAudit
