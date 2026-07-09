import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedComponentDecider

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.SaturatedComponentDecider — zero-axiom gate for the REAL-relation
saturated component decider (WP-AMALG r3, piece 2a)

Per-declaration zero-axiom gate for: the four walking-idempotent-monad laws as a `CellRel` (`IdempotentLawRel`),
the two-way iso (`monadSaturated_to_genericIdempotent` / `idempotentSaturated_to_generic` / `idempotentIsCongruence`
/ `generic_to_idempotentSaturated` / `idempotentSaturated_iff_generic`), the UNCONDITIONAL real-relation decider
(`decideSaturatedConvOverIdempotent`), and non-vacuity (`idempotenceRowConv` /
`idempotentGenericDecidesTrue_smoke` / `idempotentGenericDecidesTrue_smoke_holds`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.IdempotentLawRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturated_to_genericIdempotent
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentSaturated_to_generic
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentIsCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.generic_to_idempotentSaturated
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentSaturated_iff_generic
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decideSaturatedConvOverIdempotent
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotenceRowConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentGenericDecidesTrue_smoke
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentGenericDecidesTrue_smoke_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasSaturatedComponentDecider

end FX1PolyAudit
