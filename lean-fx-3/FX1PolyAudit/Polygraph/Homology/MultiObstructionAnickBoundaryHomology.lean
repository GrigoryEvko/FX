import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.MultiObstructionAnickBoundaryHomology

/-! # FX1PolyAudit/Polygraph/Homology/MultiObstructionAnickBoundaryHomology — zero-axiom gate (the ANICK
    BOUNDARY MAP and HOMOLOGY of the branching monomial carrier: the word-level differential
    `d([w]) = head ⊗ tail`, the minimality down-payment (the augmented coefficient vanishes, `d ∘ d = 0`
    via first-two-letters-are-a-relation), the zero-differential Smith read-off `H_d = <c(d), []>`, the
    unbounded-Betti / infinite-homological-dimension upgrade, and the cyclic-3 telescope cross-check)

Per-declaration zero-axiom gate for TOWER-ANICK r4 (#2144): the word-level Anick differential and the
minimality lemmas (`fibAnickDifferentialTailIsChain`, `fibAnickAugmentedDifferentialIsZero` = the
zero-matrix theorem, `fibAnickDifferentialSquareCoefficientIsRelation` = `d ∘ d = 0`), the concrete `d_2`
3 x 5 truth probes, the zero-differential homology read-off (`H_d = <c(d), []>`, `H_2 = Z^5`, `H_3 = Z^8`,
`H_d != 0` for all `d`, the unbounded-Betti upgrade), the cyclic-3 cross-check (the 2-periodic `Z/3`
telescope reproduced, the augmentation dichotomy, the opposite-sides contrast), and the bridge ledger
markers (the monomial gift, the general telescope bill, the `S_1` wall unmoved, the named feeds).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- L2: the word-level Anick differential and the minimality down-payment
#assert_no_axioms FX1Poly.Polygraph.Homology.wordAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickDifferentialHead
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickDifferentialTail
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickDifferentialTailIsChain
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickDifferentialHeadAugmentsToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickAugmentedDifferentialIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickDifferentialSquareCoefficientIsRelation
#assert_no_axioms FX1Poly.Polygraph.Homology.fibDegreeTwoDifferentialHeadsAndTails
#assert_no_axioms FX1Poly.Polygraph.Homology.fibDegreeTwoDifferentialTailsAreChains
#assert_no_axioms FX1Poly.Polygraph.Homology.fibDegreeTwoDifferentialAugmentsToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.fibDegreeTwoDifferentialSquareCoefficientsAreRelations

-- L1: the zero-differential Smith read-off and the H_d computations
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickZeroDifferential
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyDataAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyInvariantAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyInvariantIsFreeOnChains
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyFreeRankEqualsChainCount
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyHasNoTorsion
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyAtDegreeTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyAtDegreeThree
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyIsNonzeroAtEveryDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.fibAnickHomologyFreeRankIsUnbounded

-- the cyclic-3 telescope cross-check
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeNormAugmentationIsOddTorsionFactor
#assert_no_axioms FX1Poly.Polygraph.Homology.augmentationDichotomyFibonacciVersusCyclicThree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeCrossCheckReproducesTwoPeriodic
#assert_no_axioms FX1Poly.Polygraph.Homology.fibonacciVersusCyclicThreeAtDegreeTwoDiffer

-- the bridge ledger markers (the monomial gift, the general telescope bill, the S_1 wall unmoved, the feeds)
#assert_no_axioms FX1Poly.Polygraph.Homology.monomialDegeneracyGivesFreeHomology
#assert_no_axioms FX1Poly.Polygraph.Homology.generalTelescopeHomologyIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.anickResolutionExactnessIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.aModuleAnickDifferentialIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.normDifferentialFromRelationIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.arrowToXMonoidHomologyIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionSingleDegreeInfinityStaysWalledInHomology
#assert_no_axioms FX1Poly.Polygraph.Homology.towerAnickRoundFourLedgerIsComplete

end FX1PolyAudit
