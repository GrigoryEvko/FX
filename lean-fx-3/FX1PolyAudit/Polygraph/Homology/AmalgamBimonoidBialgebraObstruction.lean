import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AmalgamBimonoidBialgebraObstruction

/-! # FX1PolyAudit/Polygraph/Homology/AmalgamBimonoidBialgebraObstruction — zero-axiom gate (the
    bimonoid amalgamation obstruction in the PROP grading: the without-law complex, the with-law
    complex + two-complex comparison, and the probe-decided degree-1 class)

Per-declaration zero-axiom gate for TOWER-MV r3 (the bimonoid round): the arity boundary and its
re-grading pin; the without-law relation boundary and its chain-complex proof; the with-law relation
boundary + bialgebra column + comparison; the Smith normal forms, ranks, degree-1 homology free ranks,
and no-torsion facts; the degree-1 class, the relative cocycle, the escape-without / boundary-with
theorems, the part-alone `H1 = 0` facts, the killer theorem, and the two round-3 markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidArityBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidArityBoundaryIsR1Regrade
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidRelationBoundaryWithoutLaw
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawIsChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidBialgebraLawColumn
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidRelationBoundaryWithLaw
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidBialgebraColumnIsLastWithLawColumn
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawIsChainComplex
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidArityBoundarySmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidAritySmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidArityCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidArityBoundaryReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawCertificateProducesSmithNormalForm
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawReducesToSmith
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidArityRank
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawRank
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawRank
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawDegreeOneHomologyFreeRankIsOne
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawDegreeOneHomologyFreeRank
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawDegreeOneHomologyFreeRankIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidWithLawHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.BimonoidTwoComplexComparisonStatement
#assert_no_axioms FX1Poly.Polygraph.Homology.bimonoidTwoComplexComparison

end FX1PolyAudit
