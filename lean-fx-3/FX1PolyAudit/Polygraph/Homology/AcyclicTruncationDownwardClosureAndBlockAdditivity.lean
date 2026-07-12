import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AcyclicTruncationDownwardClosureAndBlockAdditivity

/-! # FX1PolyAudit/Polygraph/Homology/AcyclicTruncationDownwardClosureAndBlockAdditivity — zero-axiom gate
    (the TIGHT self-propagating truncation / downward-closure of the census support, TOWER-ANICK r15, #2145)

Per-declaration zero-axiom gate for the r15 downward-closure certificate: the n-ary enumerator
cons-decomposition (`memFlatMapWordsConsSplit`, `memWordsOverAlphabetConsSplit`), the two filter-positivity
bridges (`filterPositiveHasWitness`, `memberPassingImpliesFilterPositive`), the downward-closure step
`censusPositiveDownwardClosed`, the self-propagating truncation `censusZeroPropagatesUpward`, and the r14
closed-form corollary `acyclicCensusZeroPropagatesFromAlphabetLength`.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing decls are ALSO checked with the core `#print axioms` command (which does not truncate) — each
must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the n-ary enumerator cons-decomposition
#assert_no_axioms FX1Poly.Polygraph.Homology.memFlatMapWordsConsSplit
#assert_no_axioms FX1Poly.Polygraph.Homology.memWordsOverAlphabetConsSplit

-- the two filter-positivity bridges
#assert_no_axioms FX1Poly.Polygraph.Homology.filterPositiveHasWitness
#assert_no_axioms FX1Poly.Polygraph.Homology.memberPassingImpliesFilterPositive

-- the tight self-propagating truncation + the r14 corollary
#assert_no_axioms FX1Poly.Polygraph.Homology.censusPositiveDownwardClosed
#assert_no_axioms FX1Poly.Polygraph.Homology.censusZeroPropagatesUpward
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicCensusZeroPropagatesFromAlphabetLength

-- T2: the filter-length toolkit
#assert_no_axioms FX1Poly.Polygraph.Homology.filterConsFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.filterConsTrue
#assert_no_axioms FX1Poly.Polygraph.Homology.filterCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.natAddOnePullLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.filterOrLengthSplit

-- T2: the pair-level append split + the reverse (block -> union) containment
#assert_no_axioms FX1Poly.Polygraph.Homology.isObstructionPairAppendSplit
#assert_no_axioms FX1Poly.Polygraph.Homology.guardAppendOfLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.guardAppendOfRight

-- T2: the forward (hard) monochromaticity
#assert_no_axioms FX1Poly.Polygraph.Homology.unionPairLeadZeroForcesZero
#assert_no_axioms FX1Poly.Polygraph.Homology.unionPairLeadOneForcesOne
#assert_no_axioms FX1Poly.Polygraph.Homology.unionPairFirstLetterCases
#assert_no_axioms FX1Poly.Polygraph.Homology.guardXxOfUnionLeadZero
#assert_no_axioms FX1Poly.Polygraph.Homology.guardYyOfUnionLeadOne
#assert_no_axioms FX1Poly.Polygraph.Homology.guardUnionForwardToBlock

-- T2: the pointwise identity, disjointness, and the additivity headline
#assert_no_axioms FX1Poly.Polygraph.Homology.guardUnionEqualsBlockOr
#assert_no_axioms FX1Poly.Polygraph.Homology.xxTrueImpliesYyFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.guardBlocksDisjoint
#assert_no_axioms FX1Poly.Polygraph.Homology.twoBlockDisjointAdditivity

-- the r15 ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicTruncationDownwardClosureAndBlockAdditivityIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.censusZeroPropagatesUpward
#print axioms FX1Poly.Polygraph.Homology.censusPositiveDownwardClosed
#print axioms FX1Poly.Polygraph.Homology.memWordsOverAlphabetConsSplit
#print axioms FX1Poly.Polygraph.Homology.twoBlockDisjointAdditivity
#print axioms FX1Poly.Polygraph.Homology.guardUnionEqualsBlockOr
#print axioms FX1Poly.Polygraph.Homology.filterOrLengthSplit

end FX1PolyAudit
