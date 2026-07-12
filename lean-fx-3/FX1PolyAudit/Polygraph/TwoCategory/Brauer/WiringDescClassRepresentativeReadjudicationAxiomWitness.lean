import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeReadjudication

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeReadjudicationAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r51 class-representative
re-adjudication: the census enumerators, the (i,j)-representative family and its diagram-only well-definedness, the
r50-jam-residue-is-the-representative pins, the coverage machinery and arrival probes, the honesty markers, and the
machine-checked terminal state.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.isCupBrauerAtom
#print axioms FX1Poly.Polygraph.isCapBrauerAtom
#print axioms FX1Poly.Polygraph.cupCountOfWord
#print axioms FX1Poly.Polygraph.hasExactlyOneCup
#print axioms FX1Poly.Polygraph.isCapFreeWord
#print axioms FX1Poly.Polygraph.censusAlphabet
#print axioms FX1Poly.Polygraph.censusWordsOfLength
#print axioms FX1Poly.Polygraph.singleCupWords
#print axioms FX1Poly.Polygraph.capFreeSingleCupWords
#print axioms FX1Poly.Polygraph.regionKindIndex
#print axioms FX1Poly.Polygraph.regionKindsAgree
#print axioms FX1Poly.Polygraph.countWordsOfKind
#print axioms FX1Poly.Polygraph.classRepresentativeOf
#print axioms FX1Poly.Polygraph.classRepresentativeOf_dependsOnDiagram
#print axioms FX1Poly.Polygraph.straddleRepresentativeIsJamResidue
#print axioms FX1Poly.Polygraph.straddleReachesItsRepresentative
#print axioms FX1Poly.Polygraph.natListBeq
#print axioms FX1Poly.Polygraph.diagramBeq
#print axioms FX1Poly.Polygraph.representativeRealizesOwnDiagram
#print axioms FX1Poly.Polygraph.countRepresentativesRealizing
#print axioms FX1Poly.Polygraph.straddleRepresentativeRealizes
#print axioms FX1Poly.Polygraph.straddleRepresentativeIsFixedPoint
#print axioms FX1Poly.Polygraph.fxBrauer_hasClassRepresentativeReadjudication
#print axioms FX1Poly.Polygraph.fxBrauer_hasClassRepresentativeDischarged
#print axioms FX1Poly.Polygraph.fxBrauer_classRepresentativeReadjudicationTerminalState

end FX1PolyAudit
