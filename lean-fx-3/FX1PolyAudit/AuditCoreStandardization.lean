import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Standardization

/-! # FX1PolyAudit/AuditCoreStandardization — zero-axiom gate for term-12 (standardization + finite developments)

Per-declaration zero-axiom gate for `FX1Poly/Core/Rewriting/Standardization.lean`: the finite-developments
finiteness theorem (`accessibleBelowMeasure` / `developmentsAreFinite` — a strictly-decreasing `Nat` measure
is strongly normalizing), and the head/internal factorization core of standardization
(`pushOneInternalPastHeads` / `factorizationOfStrongPostponement` — strong postponement gives
`head* ∘ internal*`), plus the witnesses.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Finite developments: the development measure terminates
#assert_no_axioms FX1Poly.Core.accessibleBelowMeasure
#assert_no_axioms FX1Poly.Core.developmentsAreFinite

-- Standardization: head/internal factorization via strong postponement
#assert_no_axioms FX1Poly.Core.pushOneInternalPastHeads
#assert_no_axioms FX1Poly.Core.factorizationOfStrongPostponement

-- The concrete witnesses
#assert_no_axioms FX1Poly.Core.exampleFiniteDevelopment
#assert_no_axioms FX1Poly.Core.exampleFactorization

end FX1PolyAudit
