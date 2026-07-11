import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.NaryAlphabetObstructionChainEnumerator

/-! # FX1PolyAudit/Polygraph/Homology/NaryAlphabetObstructionChainEnumerator — zero-axiom gate (the
    n-ary alphabet obstruction-chain enumerator, r11 named residual (0))

Per-declaration zero-axiom gate for TOWER-ANICK r12 (#2144): the n-ary enumerator + census pipeline
(`allWordsOverAlphabet`, `multiObstructionChainsAtDegreeOver`, `multiObstructionChainRankOracleOver`),
the four n-ary length-bridge lemmas (`memAppendCases`, `memMapConsHasLength`,
`memFlatMapWordsOverAlphabetHasLength`, `memWordsOverAlphabetHasLength`), the subsumption headline
(`binaryEnumeratorAgrees`, `binaryChainsAgree`, `binaryOracleAgrees`), the n-ary censuses
(`naryCompleteGraphCensus`, `naryDisjointUnionCensus`, `naryDisjointUnionListSplitAndAdditivity`,
`naryDisjointUnionDegreeZeroExcluded`, `binaryRegressionCensus`), the reconnection corollaries
(`dagChainNaryCensus`, `dagChainNaryCensusZeroAtDegreeFour`, `diamondNaryCensus`,
`threeCycleNaryCensusIsConstant`), the census -> exactness bridge (`censusZeroImpliesExactOver` +
witnesses), and the ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the four
load-bearing decls are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The n-ary enumerator + census pipeline
#assert_no_axioms FX1Poly.Polygraph.Homology.allWordsOverAlphabet
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionChainsAtDegreeOver
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionChainRankOracleOver

-- The n-ary length bridge (the genuinely-new proof burden)
#assert_no_axioms FX1Poly.Polygraph.Homology.memAppendCases
#assert_no_axioms FX1Poly.Polygraph.Homology.memMapConsHasLength
#assert_no_axioms FX1Poly.Polygraph.Homology.memFlatMapWordsOverAlphabetHasLength
#assert_no_axioms FX1Poly.Polygraph.Homology.memWordsOverAlphabetHasLength

-- The subsumption headline
#assert_no_axioms FX1Poly.Polygraph.Homology.binaryEnumeratorAgrees
#assert_no_axioms FX1Poly.Polygraph.Homology.binaryChainsAgree
#assert_no_axioms FX1Poly.Polygraph.Homology.binaryOracleAgrees

-- The n-ary censuses (truth-probed before proving)
#assert_no_axioms FX1Poly.Polygraph.Homology.completeGraphObstructions
#assert_no_axioms FX1Poly.Polygraph.Homology.completeGraphAlphabet
#assert_no_axioms FX1Poly.Polygraph.Homology.naryCompleteGraphCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointUnionAlphabet
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointBlockXx
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointBlockYy
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointBlockZz
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointUnionSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.naryDisjointUnionCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.naryDisjointUnionListSplitAndAdditivity
#assert_no_axioms FX1Poly.Polygraph.Homology.naryDisjointUnionDegreeZeroExcluded
#assert_no_axioms FX1Poly.Polygraph.Homology.binaryRegressionCensus

-- The reconnection corollaries (the r11 hostile graphs healed)
#assert_no_axioms FX1Poly.Polygraph.Homology.graphReconnectAlphabet
#assert_no_axioms FX1Poly.Polygraph.Homology.dagChainSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.diamondSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.threeCycleAlphabet
#assert_no_axioms FX1Poly.Polygraph.Homology.threeCycleSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.dagChainNaryCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.dagChainNaryCensusZeroAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.diamondNaryCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.threeCycleNaryCensusIsConstant

-- The n-ary census -> exactness bridge
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionHomologyDataAtDegreeOver
#assert_no_axioms FX1Poly.Polygraph.Homology.multiObstructionHomologyInvariantIsFreeOnCensusOver
#assert_no_axioms FX1Poly.Polygraph.Homology.censusZeroImpliesExactOver
#assert_no_axioms FX1Poly.Polygraph.Homology.dagChainExactAtDegreeFour
#assert_no_axioms FX1Poly.Polygraph.Homology.diamondExactAtDegreeThree

-- The ledger markers
#assert_no_axioms FX1Poly.Polygraph.Homology.naryDisjointAdditivityGeneralIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.naryAlphabetObstructionChainEnumeratorIsComplete

/-! ### Independent `#print axioms` cross-check for the four load-bearing decls (not trusting the
    fuel-based macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.allWordsOverAlphabet
#print axioms FX1Poly.Polygraph.Homology.memWordsOverAlphabetHasLength
#print axioms FX1Poly.Polygraph.Homology.memAppendCases
#print axioms FX1Poly.Polygraph.Homology.binaryEnumeratorAgrees

end FX1PolyAudit
