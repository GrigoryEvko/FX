import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CertificateFunctor

/-! # FX1PolyAudit.Polygraph.Omega.CertificateFunctorAudit — zero-axiom gate for the abstract
certificate -> dim-3 cell functor (OMEGA-4 r2, B1).

Per-declaration `#assert_no_axioms` on the object map (`stepComputad`), the state / step / path maps,
the boundary computations, the composition law (leg 4), the functor (`encodeHomotopy`, leg 2), the
least-congruence factorization, the confluence-square row + 3-cell (leg 3), the regression tie against
r1's `diamondThreeCell`, and the second-certificate non-vacuity. -/

namespace FX1PolyAudit

-- CertificateFunctor.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.stepGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.stepComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeState
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeStep
#assert_no_axioms FX1Poly.Polygraph.Omega.encodePath
#assert_no_axioms FX1Poly.Polygraph.Omega.encodePath_nil
#assert_no_axioms FX1Poly.Polygraph.Omega.encodePath_cons
#assert_no_axioms FX1Poly.Polygraph.Omega.encodePath_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.encodePath_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.AbsorbsStrictAxioms
#assert_no_axioms FX1Poly.Polygraph.Omega.encodePath_comp_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.EncodedDiamondRel
#assert_no_axioms FX1Poly.Polygraph.Omega.encodedDiamondBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.functorBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.AbsorbsDiamonds
#assert_no_axioms FX1Poly.Polygraph.Omega.absorbsStrictAxioms_functorBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.absorbsDiamonds_functorBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeHomotopy
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeHomotopyModel
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeHomotopy_viaLeastCongruence
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeConfluenceRow
#assert_no_axioms FX1Poly.Polygraph.Omega.encodeConfluenceThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.completeUnitStep
#assert_no_axioms FX1Poly.Polygraph.Omega.completeDiamondCell
#assert_no_axioms FX1Poly.Polygraph.Omega.functorialCompleteDiamondCell
#assert_no_axioms FX1Poly.Polygraph.Omega.functorialCompleteDiamondLegsCoincide
#assert_no_axioms FX1Poly.Polygraph.Omega.boolTrivialStep
#assert_no_axioms FX1Poly.Polygraph.Omega.boolDiamond
#assert_no_axioms FX1Poly.Polygraph.Omega.boolLeftStep
#assert_no_axioms FX1Poly.Polygraph.Omega.boolRightStep
#assert_no_axioms FX1Poly.Polygraph.Omega.boolDiamondCell
#assert_no_axioms FX1Poly.Polygraph.Omega.secondCertificateThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.secondModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.secondLabelCode
#assert_no_axioms FX1Poly.Polygraph.Omega.secondGenBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.secondCertificateLegsDistinct
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_certificateFunctorShippedR2

end FX1PolyAudit
