import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismMinimalPolynomialTwoByTwo

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/EndomorphismMinimalPolynomialTwoByTwo — zero-axiom gate

Per-declaration zero-axiom gate for the WP-ENDO r2 minimal-polynomial (annihilation) separator: the
decidable scalarness predicate, the minimal-polynomial degree, the degree-dissimilarity predicate, the
scalar/Jordan degree groundings, the share-char-poly and share-rank blindness witnesses, the
scalar-versus-Jordan separation certificate, and the marker.

The separator computes the minimal-polynomial degree over `ℤ` (scalarness of the `2×2` block) — no
`ℚ[x]` machinery — and reaches the one equal-char-poly-equal-rank case the power-based separators leave
uncovered.  The scalarness predicate is reducible so the `if` and `decide` see its decidable `And` of
`Int` equalities; the file stays free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The decidable scalarness predicate + the minimal-polynomial degree.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismIsScalarTwoByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMinimalPolynomialDegreeTwoByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.EndomorphismDissimilarByMinimalPolynomialDegree

-- The degree groundings + the blindness witnesses (shared char poly, shared rank).
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMinimalPolynomialDegreeScalarExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismMinimalPolynomialDegreeJordanExample
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismJordanVersusScalarShareCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismJordanVersusScalarShareRank

-- The scalar-versus-Jordan separation certificate + the marker.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSeparatesScalarFromJordanSameCharPolySameRank
#assert_no_axioms FX1Poly.ComputerAlgebra.fxEndo_hasMinimalPolynomialDegreeSeparator

end FX1PolyAudit
