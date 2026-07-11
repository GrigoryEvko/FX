import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.AcyclicTruncationClosedFormAndDisjointUnionAdditivity

/-! # FX1PolyAudit/Polygraph/Homology/AcyclicTruncationClosedFormAndDisjointUnionAdditivity — zero-axiom
    gate (the `{xy}` fuel-soundness closed form crossing the `flatMap`-membership wall + the
    disjoint-union Mayer-Vietoris seed)

Per-declaration zero-axiom gate for TOWER-ANICK r10 NODE-3 (#2144 / #2145): the crossed
`flatMap`-membership length bridge (`memFlatMapWordsHasLength`, `memWordsHasLength`), the filter-empties
step (`filterAllFalseIsNil`, `linearGuardFalseOnLengthGeThree`), the `{xy}` closed form
(`linearCensusZeroAboveDegreeOne`, `linearSystemExactAboveDegreeOne`, `linearAcyclicImpliesTruncation`),
the disjoint-union Mayer-Vietoris seed (`xxSystem`, `yySystem`, `unionSystem`, `mvCensuses`,
`mvListSplitAndAdditivity`), and the named-node / ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- A: the crossed flatMap-membership length bridge
#assert_no_axioms FX1Poly.Polygraph.Homology.memFlatMapWordsHasLength
#assert_no_axioms FX1Poly.Polygraph.Homology.memWordsHasLength

-- B: the filter-empties step and the length-≥ 3 guard failure
#assert_no_axioms FX1Poly.Polygraph.Homology.filterAllFalseIsNil
#assert_no_axioms FX1Poly.Polygraph.Homology.linearGuardFalseOnLengthGeThree

-- C: the {xy} fuel-soundness closed form
#assert_no_axioms FX1Poly.Polygraph.Homology.linearCensusZeroAboveDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.linearSystemExactAboveDegreeOne
#assert_no_axioms FX1Poly.Polygraph.Homology.linearAcyclicImpliesTruncation

-- D: the disjoint-union Mayer-Vietoris seed
#assert_no_axioms FX1Poly.Polygraph.Homology.xxSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.yySystem
#assert_no_axioms FX1Poly.Polygraph.Homology.unionSystem
#assert_no_axioms FX1Poly.Polygraph.Homology.mvCensuses
#assert_no_axioms FX1Poly.Polygraph.Homology.mvListSplitAndAdditivity

-- E: the named nodes and the ledger marker
#assert_no_axioms FX1Poly.Polygraph.Homology.generalGraphLongestPathBoundIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.disjointUnionAdditivityIsNamedNode
#assert_no_axioms FX1Poly.Polygraph.Homology.acyclicTruncationClosedFormAndDisjointUnionAdditivityIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.memWordsHasLength
#print axioms FX1Poly.Polygraph.Homology.filterAllFalseIsNil
#print axioms FX1Poly.Polygraph.Homology.linearCensusZeroAboveDegreeOne
#print axioms FX1Poly.Polygraph.Homology.linearSystemExactAboveDegreeOne
#print axioms FX1Poly.Polygraph.Homology.mvListSplitAndAdditivity

end FX1PolyAudit
