import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Ledger.TypeAxis.TypeThree

/-! # FX1PolyAudit/AuditTier0TypeThree — zero-axiom gate for type-3 (the RIGHT / M-types rung)

Per-declaration zero-axiom gate for `FX1Poly/Typed/Ledger/TypeAxis/TypeThree.lean`: the three backed flips
(terminal coalgebra / finality, coinduction, the greatest fixpoint) and the three deferral honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The three backed flips
#assert_no_axioms FX1Poly.Tier0.fxType_hasTerminalCoalgebra
#assert_no_axioms FX1Poly.Tier0.fxType_terminalCoalgebra_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasCoinduction
#assert_no_axioms FX1Poly.Tier0.fxType_coinduction_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasGreatestFixpoint
#assert_no_axioms FX1Poly.Tier0.fxType_greatestFixpoint_isBacked

-- The deferral honesty markers
#assert_no_axioms FX1Poly.Tier0.fxType_hasCoinductiveTypeFormer
#assert_no_axioms FX1Poly.Tier0.fxType_hasContainerMType
#assert_no_axioms FX1Poly.Tier0.fxType_hasCoinductiveReducibility

end FX1PolyAudit
