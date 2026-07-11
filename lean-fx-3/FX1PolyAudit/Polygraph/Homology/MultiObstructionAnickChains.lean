import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.MultiObstructionAnickChains

/-! # FX1PolyAudit/Polygraph/Homology/MultiObstructionAnickChains — zero-axiom gate (the MULTI-OBSTRUCTION
    Anick carrier: the branching two-generator monomial system whose minimal-overlap chains grow as
    `F(d+3)`, the word-carrying marked chain + decidable multi-obstruction guard, the fueled binary-word
    enumerator, the Fibonacci growth census + SHIPPED asymptotic unboundedness, and the crown ledger
    re-firing the rank oracle at the branching carrier — the `S_1` single-degree-∞ wall UNMOVED)

Per-declaration zero-axiom gate for TOWER-ANICK r3 (#2144): the obstruction systems as data, the
multi-obstruction guard (`isObstructionPair` / `allAdjacentPairsAreObstructions` reusing `natEqBool`)
and the `MarkedMultiChain` carrier, the B1 truth probes (the five degree-2 chains recognised, the
`yy`-factor overlaps rejected), the fueled `allWordsOfLength` enumerator + rank oracle, the growing
census `2, 3, 5, 8, 13, 21, 34`, the degeneracy to r1's constant `1`, the two-state transfer recursion
with the Fibonacci law + strict growth + the SHIPPED asymptotic unboundedness, and the crown markers
(the r3 realization, the `S_1` wall unmoved, the named residual nodes).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- A: the obstruction systems as data
#assert_no_axioms FX1Poly.Polygraph.Homology.fibObstructionSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.singleObstructionUnarySystem

-- B: the multi-obstruction guard, the carrier, and the truth probes
#assert_no_axioms FX1Poly.Polygraph.Homology.isObstructionPair
#assert_no_axioms FX1Poly.Polygraph.Homology.allAdjacentPairsAreObstructions
#assert_no_axioms FX1Poly.Polygraph.Homology.MarkedMultiChain.isMinimal
#assert_no_axioms FX1Poly.Polygraph.Homology.xyIsObstructionYyIsNot
#assert_no_axioms FX1Poly.Polygraph.Homology.degreeTwoChainCensusRecognized
#assert_no_axioms FX1Poly.Polygraph.Homology.yyFactorChainIsRejected
#assert_no_axioms FX1Poly.Polygraph.Homology.markedXyxChain
#assert_no_axioms FX1Poly.Polygraph.Homology.markedChainXyxIsMinimal

-- C: the enumerator, the growing census, and the degeneracy to r1
#assert_no_axioms FX1Poly.Polygraph.Homology.allWordsOfLength
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionChainsAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionChainRankOracle
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionCensusThroughDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionChainCountAtDegreeSix
#assert_no_axioms FX1Poly.Polygraph.Homology.singleObstructionMultiChainCountIsConstantOne
#assert_no_axioms FX1Poly.Polygraph.Homology.singleObstructionDegeneratesToAnickConstant

-- D: the transfer recursion, the Fibonacci law, growth, and the SHIPPED asymptotic unboundedness
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountPair
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountEndingInX
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountEndingInY
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountTotal
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountSatisfiesFibonacciRecursion
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountCensusThroughDegreeSix
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountAgreesWithEnumeratorThroughDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionChainCountStrictlyGrows
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountExceedsBoth
#assert_no_axioms FX1Poly.Polygraph.Homology.fibChainCountTotalExceedsDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionRankIsUnbounded
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionGeneralEnumeratorCollapseIsNamedNode

-- E: the crown ledger markers (the r3 realization, the S_1 wall unmoved, the named residual nodes)
#assert_no_axioms FX1Poly.Polygraph.Homology.fibObstructionSystemHasConvergentWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.fibCarrierDegreeThreeRankIsFinite
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionRankExceedsSingleLetterConstant
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionAnickCarrierIsRealized
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionSingleDegreeInfinityStaysWalled
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionAnickBoundaryAndHomologyIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.variableLengthMultiObstructionGuardIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.towerAnickRoundThreeLedgerIsComplete

end FX1PolyAudit
