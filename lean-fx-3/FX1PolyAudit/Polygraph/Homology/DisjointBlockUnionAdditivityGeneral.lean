import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.DisjointBlockUnionAdditivityGeneral

/-! # FX1PolyAudit/Polygraph/Homology/DisjointBlockUnionAdditivityGeneral — zero-axiom gate
    (the GENERAL k-block disjoint-union census additivity, TOWER-ANICK r16, #2145 TOWER-TRUNC)

Per-declaration zero-axiom gate for the r16 general additivity: the separator-driven forward
monochromaticity (`guardEdgesXOfUnionLeadTrue` / `guardEdgesYOfUnionLeadFalse` /
`guardUnionForwardToBlockGeneral`), the pointwise block-`or` identity + pair-exclusion + block
disjointness (`guardUnionEqualsBlockOrGeneral` / `edgesXPairExcludesEdgesYPair` /
`guardBlocksDisjointGeneral`), the general two-block additivity `twoBlockAdditivityOverSeparator` with its
r15 recovery corollary `twoBlockDisjointAdditivityViaSeparator`, the k-block scaffolding (`sumOverBlocks` /
`alphabetDisjoint` / `pairwiseDisjointAlphabets`), the base case `emptyEdgesCensusZeroAtPositiveDegree`, the
new rest-pair leg `restPairSeparatorFalse`, the headline `kBlockAdditivity`, and the k=3 end-to-end witness
`threeSelfLoopBlockAdditivity`.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing decls are ALSO checked with the core `#print axioms` command (which does not truncate) — each
must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the separator-driven forward monochromaticity
#assert_no_axioms FX1Poly.Polygraph.Homology.guardEdgesXOfUnionLeadTrue
#assert_no_axioms FX1Poly.Polygraph.Homology.guardEdgesYOfUnionLeadFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.guardUnionForwardToBlockGeneral

-- the pointwise identity, pair-exclusion, block disjointness
#assert_no_axioms FX1Poly.Polygraph.Homology.guardUnionEqualsBlockOrGeneral
#assert_no_axioms FX1Poly.Polygraph.Homology.edgesXPairExcludesEdgesYPair
#assert_no_axioms FX1Poly.Polygraph.Homology.guardBlocksDisjointGeneral

-- the general two-block additivity + the r15 recovery corollary
#assert_no_axioms FX1Poly.Polygraph.Homology.twoBlockAdditivityOverSeparator
#assert_no_axioms FX1Poly.Polygraph.Homology.selfLoopPairForcesEq
#assert_no_axioms FX1Poly.Polygraph.Homology.twoBlockDisjointAdditivityViaSeparator

-- the k-block scaffolding
#assert_no_axioms FX1Poly.Polygraph.Homology.sumOverBlocks
#assert_no_axioms FX1Poly.Polygraph.Homology.alphabetDisjoint
#assert_no_axioms FX1Poly.Polygraph.Homology.pairwiseDisjointAlphabets

-- the base case, the new rest-pair leg, and the k-block headline
#assert_no_axioms FX1Poly.Polygraph.Homology.emptyEdgesGuardFalseOnLongWord
#assert_no_axioms FX1Poly.Polygraph.Homology.emptyEdgesCensusZeroAtPositiveDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.restPairSeparatorFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.kBlockAdditivity

-- the k=3 end-to-end non-vacuity witness
#assert_no_axioms FX1Poly.Polygraph.Homology.selfLoopBlock
#assert_no_axioms FX1Poly.Polygraph.Homology.selfLoopBlockLocality
#assert_no_axioms FX1Poly.Polygraph.Homology.singletonAlphabetDisjoint
#assert_no_axioms FX1Poly.Polygraph.Homology.threeSelfLoopBlockAdditivity

-- the r16 ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointBlockUnionAdditivityGeneralIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.twoBlockAdditivityOverSeparator
#print axioms FX1Poly.Polygraph.Homology.kBlockAdditivity
#print axioms FX1Poly.Polygraph.Homology.guardUnionForwardToBlockGeneral
#print axioms FX1Poly.Polygraph.Homology.restPairSeparatorFalse
#print axioms FX1Poly.Polygraph.Homology.emptyEdgesCensusZeroAtPositiveDegree
#print axioms FX1Poly.Polygraph.Homology.threeSelfLoopBlockAdditivity

end FX1PolyAudit
