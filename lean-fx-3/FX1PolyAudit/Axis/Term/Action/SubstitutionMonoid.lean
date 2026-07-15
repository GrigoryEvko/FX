import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Action.SubstitutionMonoid

/-! # FX1PolyAudit/AuditAxisTermSubstitutionMonoid — zero-axiom gate for term-10 (FPT substitution monoid)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Action/SubstitutionMonoid.lean`: the Fiore-Plotkin-
Turi substitution monoid (`SubstitutionMonoid` + the three monoid laws), the substitution-category
consequence (`kleisliComp` + `kleisli_leftId` / `kleisli_rightId` / `kleisli_assoc`, pointwise), and the
variables-only witness (`variableSubstitutionMonoid`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The substitution monoid (carrier + var + subst + the three monoid laws)
#assert_no_axioms FX1Poly.Core.SubstitutionMonoid

-- The substitution (Kleisli) category: composition + the three category laws from the monoid laws
#assert_no_axioms FX1Poly.Core.SubstitutionMonoid.kleisliComp
#assert_no_axioms FX1Poly.Core.SubstitutionMonoid.kleisli_leftId
#assert_no_axioms FX1Poly.Core.SubstitutionMonoid.kleisli_rightId
#assert_no_axioms FX1Poly.Core.SubstitutionMonoid.kleisli_assoc

-- The variables-only witness (the initial / empty-signature substitution monoid)
#assert_no_axioms FX1Poly.Core.variableSubstitutionMonoid

-- ★ The FX kernel syntax instance: RawTerm + parallel substitution IS a substitution monoid
#assert_no_axioms FX1Poly.Core.rawTermSubstitutionMonoid

end FX1PolyAudit
