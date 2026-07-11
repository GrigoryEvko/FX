import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.FreshGeneratorTietzeExpansionInvariance

/-! # FX1PolyAudit/Polygraph/Homology/FreshGeneratorTietzeExpansionInvariance — zero-axiom gate (the
    generic fresh-generator Tietze-expansion theorem: the block constructor, the no-new-critical-pair
    fact, the generic degree-1/degree-2 homology-preservation theorems, and the three instances fed
    through them)

Per-declaration zero-axiom gate for H2-SQUIER-NOGO r3 bricks B1..B5.  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B1: the generic block constructor + the no-new-critical-pair fact + the hand probe
#assert_no_axioms FX1Poly.Polygraph.Homology.expandWalkerPresentationWithFreshGenerator
#assert_no_axioms FX1Poly.Polygraph.Homology.freshGeneratorExpansionAddsNoCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Homology.freshGeneratorExpansionKeepsDegreeThreeChain
#assert_no_axioms FX1Poly.Polygraph.Homology.freshGeneratorExpansionBumpsGeneratorCount
#assert_no_axioms FX1Poly.Polygraph.Homology.listAppendSingletonLength
#assert_no_axioms FX1Poly.Polygraph.Homology.freshGeneratorExpansionBumpsRuleCount
#assert_no_axioms FX1Poly.Polygraph.Homology.handProbeExpandedTietzePresentation
#assert_no_axioms FX1Poly.Polygraph.Homology.handProbeComputesExpandedBoundaryDimOne
#assert_no_axioms FX1Poly.Polygraph.Homology.handProbeExpandedTietzeBoundaryOfDimOneSmithCertificate
#assert_no_axioms FX1Poly.Polygraph.Homology.handProbeExpandedBoundaryReducesToSmithNormalForm

-- B3: the reader-level diagonal inductions + the generic degree-1/degree-2 preservation theorems
#assert_no_axioms FX1Poly.Polygraph.Homology.natSuccSubSuccEqSub
#assert_no_axioms FX1Poly.Polygraph.Homology.homologyInvariantEq
#assert_no_axioms FX1Poly.Polygraph.Homology.smithRankWithinTopNonzeroIsSuccessor
#assert_no_axioms FX1Poly.Polygraph.Homology.nonUnitInvariantFactorsUnitConsIsStable
#assert_no_axioms FX1Poly.Polygraph.Homology.tietzeExpansionPreservesDegreeOneInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.tietzeExpansionPreservesDegreeTwoInvariant

end FX1PolyAudit
