import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.NatNumeralUnionCanonicity

/-! # FX1PolyAudit/AuditNatNumeralUnionCanonicity — DEEP Nat canonicity over the union

Per-declaration zero-axiom gate for the deep-numeral extraction: the fuel-indexed worker (structural
fuel induction, never `WellFounded.fix`), the headline (a closed normal union-typed term at
`natTypeCell` with no bridge-fragment occurrence is a DEEP `IsNatNumeral` — the Milestone-A
Nat-canonicity pillar over the ONE judgment), and the numeral-2 non-vacuity smoke.  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNormalNatNumeralBounded
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNormalNatNumeral
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNormalNatNumeral.numeralTwo

end FX1PolyAudit
