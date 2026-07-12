import FX1Poly.Polygraph.Homology.PeriodicTowerDiagonalChainMap

/-! # FX1PolyAudit.Polygraph.Homology.PeriodicTowerDiagonalChainMapAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of TOWER-RING (#2147) r2 —
the explicit Cartan-Eilenberg / Roberts diagonal `Delta : W -> W (X) W` on the `ZZ/n` periodic
resolution: the diagonal itself, the four-parity-component chain-map pins `n in {2,3,5}` x degree
`{1..5}`, the even-even <-> r1-shuffle bridge, the GENERIC selection lemma, the GENERIC derived-cup
agreement `cupFromDiagonal = cupEvenPair`, and the diagonal-induced cup's graded-commutativity /
associativity re-founded from r1.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.diagonalEven
#print axioms FX1Poly.Polygraph.Homology.diagonalOdd
#print axioms FX1Poly.Polygraph.Homology.diagonalEvenEvenSummandIsShuffleLift
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeOne
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeTwo
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusTwoAtDegreeFive
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeOne
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeTwo
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeThree
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusThreeAtDegreeFive
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeOne
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeTwo
#print axioms FX1Poly.Polygraph.Homology.diagonalIsChainMapModulusFiveAtDegreeFive
#print axioms FX1Poly.Polygraph.Homology.cupFromDiagonalSquareIsDegreeTwoGenerator
#print axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAgreesWithR1Square
#print axioms FX1Poly.Polygraph.Homology.evenEvenSelectIsOne
#print axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAgreesWithCupEvenPair
#print axioms FX1Poly.Polygraph.Homology.cupFromDiagonalGradedCommutes
#print axioms FX1Poly.Polygraph.Homology.cupFromDiagonalAssociates
#print axioms FX1Poly.Polygraph.Homology.diagonalGenericChainMapIsNamedNode
#print axioms FX1Poly.Polygraph.Homology.periodicTowerDiagonalChainMapLedgerIsComplete

end FX1PolyAudit
