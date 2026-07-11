import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AnickTelescopeAugmentationAndMonomialFiniteness

/-! # FX1PolyAudit/Polygraph/Homology/AnickTelescopeAugmentationAndMonomialFiniteness — zero-axiom gate
    (the COMPUTED cyclic-3 telescope augmentation, the certificate-layer EXACTNESS predicate with
    both-sides instances, and the acyclic-graph TRUNCATION criterion + the `{xy}` finite witness)

Per-declaration zero-axiom gate for TOWER-ANICK r5 (#2144): the group-ring augmentation and the telescope
ties (`cyclicThreeGroupRingAugmentation`, `cyclicThreeNormAugmentationIsThree`, the tower-entry tie, the reproduction
of the r4 bare constant, the sharpened dichotomy), the exactness predicate and its both-sides instances
(`isExactAtDegree`, `cyclicThreeTensoredExactAtEvenPositive`, `cyclicThreeTensoredNotExactAtOdd`,
`fibMonomialNeverExact`), the truncation crown (`linearObstructionSystem`, `linearSystemChainCensusTruncates`,
`linearObstructionForcesSecondLetterIsOne`, `noLinearChainOfLengthThreeOrMore`, `selfLoopSystemDoesNotTruncate`,
`threeQualitativeChainRegimesAtDegreeFive`), and the ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B1: the computed cyclic-3 telescope augmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeGroupRingAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNorm
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryElement
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormAugmentationIsThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeBoundaryAugmentationIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTelescopeAugmentsToTowerEntries
#assert_no_axioms FX1Poly.Polygraph.Homology.computedNormAugmentationReproducesShippedConstant
#assert_no_axioms FX1Poly.Polygraph.Homology.computedNormAugmentationIsShippedTorsionFactor
#assert_no_axioms FX1Poly.Polygraph.Homology.sharpenedAugmentationDichotomy

-- B2: the exactness predicate and both-sides instances
#assert_no_axioms FX1Poly.Polygraph.Homology.isExactAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTensoredExactAtEvenPositive
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeTensoredNotExactAtOdd
#assert_no_axioms FX1Poly.Polygraph.Homology.fibMonomialNeverExact
#assert_no_axioms FX1Poly.Polygraph.Homology.certificateLayerSeesTensoredExactnessNotResolutionExactness
#assert_no_axioms FX1Poly.Polygraph.Homology.contractingHomotopyIngredientsPresentAssemblyNamedNode

-- B3: the truncation crown
#assert_no_axioms FX1Poly.Polygraph.Homology.linearObstructionSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.linearSystemChainCensusTruncates
#assert_no_axioms FX1Poly.Polygraph.Homology.linearObstructionForcesSecondLetterIsOne
#assert_no_axioms FX1Poly.Polygraph.Homology.noLinearChainOfLengthThreeOrMore
#assert_no_axioms FX1Poly.Polygraph.Homology.selfLoopSystemDoesNotTruncate
#assert_no_axioms FX1Poly.Polygraph.Homology.threeQualitativeChainRegimesAtDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicObstructionGraphTruncatesChains
#assert_no_axioms FX1Poly.Polygraph.Homology.truncationEqualsFiniteGlobalDimension
#assert_no_axioms FX1Poly.Polygraph.Homology.allDegreesTruncationClosedFormIsNamedNode

-- B4: the ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.towerAnickRoundFiveLedgerIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.cyclicThreeNormAugmentationIsThree
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeTelescopeAugmentsToTowerEntries
#print axioms FX1Poly.Polygraph.Homology.sharpenedAugmentationDichotomy
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeTensoredExactAtEvenPositive
#print axioms FX1Poly.Polygraph.Homology.cyclicThreeTensoredNotExactAtOdd
#print axioms FX1Poly.Polygraph.Homology.fibMonomialNeverExact
#print axioms FX1Poly.Polygraph.Homology.linearObstructionForcesSecondLetterIsOne
#print axioms FX1Poly.Polygraph.Homology.noLinearChainOfLengthThreeOrMore
#print axioms FX1Poly.Polygraph.Homology.linearSystemChainCensusTruncates
#print axioms FX1Poly.Polygraph.Homology.threeQualitativeChainRegimesAtDegreeFive

end FX1PolyAudit
