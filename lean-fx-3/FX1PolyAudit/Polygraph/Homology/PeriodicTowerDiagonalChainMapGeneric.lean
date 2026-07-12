import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.PeriodicTowerDiagonalChainMapGeneric

/-! # FX1PolyAudit/Polygraph/Homology/PeriodicTowerDiagonalChainMapGeneric — zero-axiom gate (the GENERIC
    all-`n` group-ring convolution kit + the Roberts Lemma 4.3.4 annihilation `N (t - 1) = 0`)

Per-declaration zero-axiom gate for TOWER-RING (#2147, r3): the clean Int helpers + the range-to-
`descendingSum` bridge (`listSumRange`, around the `List.range` propext wall); the cyclic indicator + the
discrete-Stokes telescope (`descendingSumTelescopes`); the group-ring coefficient reader (`ringCoeffAt`)
+ its append / flatMap / map linearity + `ringConvolve`; the per-entry telescope reduction; ★ the
generic annihilation `N (t - 1) = 0` (`normAnnihilatesTMinusOne` / `normTimesTMinusOneVanishesForAllModuli`)
with its `n = 3, 5, 0` instantiations; and the r3 named-residual + ledger nodes.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.intSubSelf
#assert_no_axioms FX1Poly.Polygraph.Homology.intSubCancelChain
#assert_no_axioms FX1Poly.Polygraph.Homology.listSum
#assert_no_axioms FX1Poly.Polygraph.Homology.descendingSum
#assert_no_axioms FX1Poly.Polygraph.Homology.listSumAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.listSumRangeLoop
#assert_no_axioms FX1Poly.Polygraph.Homology.listSumRange
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicIndicator
#assert_no_axioms FX1Poly.Polygraph.Homology.descendingSumTelescopes
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicIndicatorAtModulusEqAtZero
#assert_no_axioms FX1Poly.Polygraph.Homology.ringCoeffAt
#assert_no_axioms FX1Poly.Polygraph.Homology.ringCoeffAtAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.sumEntries
#assert_no_axioms FX1Poly.Polygraph.Homology.ringCoeffAtFlatMap
#assert_no_axioms FX1Poly.Polygraph.Homology.sumEntriesOfMap
#assert_no_axioms FX1Poly.Polygraph.Homology.ringConvolve
#assert_no_axioms FX1Poly.Polygraph.Homology.bifNegOne
#assert_no_axioms FX1Poly.Polygraph.Homology.convolutionEntryTelescopes
#assert_no_axioms FX1Poly.Polygraph.Homology.normAnnihilatesTMinusOne
#assert_no_axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesForAllModuli
#assert_no_axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesAtModulusThree
#assert_no_axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesAtModulusFive
#assert_no_axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesAtModulusZero
#assert_no_axioms FX1Poly.Polygraph.Homology.genericChainMapCoefficientAssemblyIsNamedResidual
#assert_no_axioms FX1Poly.Polygraph.Homology.periodicTowerDiagonalChainMapGenericLedgerIsComplete

end FX1PolyAudit
