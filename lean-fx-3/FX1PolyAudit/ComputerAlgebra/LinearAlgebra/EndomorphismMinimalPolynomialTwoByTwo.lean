import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismMinimalPolynomialTwoByTwo

/-! # EndomorphismMinimalPolynomialTwoByTwo — zero-axiom gate

Per-declaration zero-axiom gate for the minimal-polynomial (degree) separator: the decidable scalarness
predicate, the minimal-polynomial degree, the degree-dissimilarity predicate, the scalar/Jordan degree
groundings, the share-char-poly and share-rank blindness witnesses, and the scalar-versus-Jordan
separator.  The scalarness predicate is reducible so `if` and `decide` see its decidable `And` of `Int`
equalities; the file stays free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
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

-- The scalar-versus-Jordan separation certificate.
#assert_no_axioms FX1Poly.ComputerAlgebra.endomorphismSeparatesScalarFromJordanSameCharPolySameRank

end FX1PolyAudit
