import FX1Poly.Polygraph.Homology.PeriodicTowerDiagonalChainMapGeneric

/-! # FX1PolyAudit.Polygraph.Homology.PeriodicTowerDiagonalChainMapGenericAxiomWitness — independent
    #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of TOWER-RING (#2147) r3:
the range-to-`descendingSum` bridge `listSumRange`, the discrete-Stokes telescope
`descendingSumTelescopes`, the group-ring flatMap linearity `ringCoeffAtFlatMap`, and ★ the generic
all-`n` annihilation `N (t - 1) = 0` (`normAnnihilatesTMinusOne` / `normTimesTMinusOneVanishesForAllModuli`)
with its instantiations, plus the r3 named-residual + ledger nodes.  Each must print "does not depend on
any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.listSumRange
#print axioms FX1Poly.Polygraph.Homology.descendingSumTelescopes
#print axioms FX1Poly.Polygraph.Homology.cyclicIndicatorAtModulusEqAtZero
#print axioms FX1Poly.Polygraph.Homology.ringCoeffAtFlatMap
#print axioms FX1Poly.Polygraph.Homology.sumEntriesOfMap
#print axioms FX1Poly.Polygraph.Homology.convolutionEntryTelescopes
#print axioms FX1Poly.Polygraph.Homology.normAnnihilatesTMinusOne
#print axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesForAllModuli
#print axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesAtModulusThree
#print axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesAtModulusFive
#print axioms FX1Poly.Polygraph.Homology.normTimesTMinusOneVanishesAtModulusZero
#print axioms FX1Poly.Polygraph.Homology.genericChainMapCoefficientAssemblyIsNamedResidual
#print axioms FX1Poly.Polygraph.Homology.periodicTowerDiagonalChainMapGenericLedgerIsComplete

end FX1PolyAudit
