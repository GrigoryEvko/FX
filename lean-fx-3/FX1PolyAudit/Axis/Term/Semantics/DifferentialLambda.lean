import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Semantics.DifferentialLambda

/-! # FX1PolyAudit/AuditAxisTermDifferentialLambda — zero-axiom gate for term-25 (differential λ-calculus)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Semantics/DifferentialLambda.lean`: the abstract
derivation (`DifferentialAlgebra` / `DifferentialAlgebra.deriv_square` / `onePointDifferentialAlgebra`), the
concrete differential/linear substitution (`ResourceTerm` / `occurrences` / `linearSubst` /
`linearSubst_app`), the hand-proved `List` helpers (`listLengthMap` / `listLengthAppendReversed`), linearity
and the constant rule (`linearSubst_length_eq_occurrences` / `linearSubst_eq_nil_of_absent`), and the `x²`
witness (`exampleSquare` / `exampleSquare_occurrences` / `exampleSquare_derivative` /
`exampleSquare_derivative_length`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The abstract derivation: linearity + the Leibniz product rule + concrete models (terminal + products)
#assert_no_axioms FX1Poly.Core.DifferentialAlgebra
#assert_no_axioms FX1Poly.Core.DifferentialAlgebra.deriv_square
#assert_no_axioms FX1Poly.Core.onePointDifferentialAlgebra
#assert_no_axioms FX1Poly.Core.productDifferentialAlgebra

-- The concrete differential / linear substitution + the Leibniz product rule
#assert_no_axioms FX1Poly.Core.ResourceTerm
#assert_no_axioms FX1Poly.Core.occurrences
#assert_no_axioms FX1Poly.Core.linearSubst
#assert_no_axioms FX1Poly.Core.linearSubst_app

-- Hand-proved zero-axiom List helpers
#assert_no_axioms FX1Poly.Core.listLengthMap
#assert_no_axioms FX1Poly.Core.listLengthAppendReversed

-- Linearity (degree = occurrence count) + the constant rule + its converse (present ⟹ nonzero derivative)
#assert_no_axioms FX1Poly.Core.linearSubst_length_eq_occurrences
#assert_no_axioms FX1Poly.Core.linearSubst_eq_nil_of_absent
#assert_no_axioms FX1Poly.Core.linearSubst_ne_nil_of_present

-- The x² witness (derivative of a square is the two-summand sum 2x)
#assert_no_axioms FX1Poly.Core.exampleSquare
#assert_no_axioms FX1Poly.Core.exampleSquare_occurrences
#assert_no_axioms FX1Poly.Core.exampleSquare_derivative
#assert_no_axioms FX1Poly.Core.exampleSquare_derivative_length

end FX1PolyAudit
