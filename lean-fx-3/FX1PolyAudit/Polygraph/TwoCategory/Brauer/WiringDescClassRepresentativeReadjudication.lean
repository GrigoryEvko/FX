import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeReadjudication

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeReadjudication — zero-axiom gate (r51)

Per-declaration zero-axiom gate for the BRAUER r51 class-representative re-adjudication: the committed reproducible
census enumerators (`isCupBrauerAtom`, `isCapBrauerAtom`, `cupCountOfWord`, `hasExactlyOneCup`, `isCapFreeWord`,
`censusAlphabet`, `censusWordsOfLength`, `singleCupWords`, `capFreeSingleCupWords`, `regionKindIndex`,
`regionKindsAgree`, `countWordsOfKind`), the (i,j)-representative family (`classRepresentativeOf`) with its diagram-only
well-definedness (`classRepresentativeOf_dependsOnDiagram`), the r50-jam-residue-is-the-representative pins
(`straddleRepresentativeIsJamResidue`, `straddleReachesItsRepresentative`), the coverage machinery (`natListBeq`,
`diagramBeq`, `representativeRealizesOwnDiagram`, `countRepresentativesRealizing`) with the arrival probes
(`straddleRepresentativeRealizes`, `straddleRepresentativeIsFixedPoint`), the honesty markers, and the machine-checked
terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix` — the
enumerators are structural over `List.range`/`List.flatMap`/`List.map`/`List.filter`, the representative composition is
the shipped structural extractor, and the pins are `decide`s over `Nat.beq` / the derived `DecidableEq` on
`List BrauerAtom` and `DiagramType`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isCupBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.isCapBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.cupCountOfWord
#assert_no_axioms FX1Poly.Polygraph.hasExactlyOneCup
#assert_no_axioms FX1Poly.Polygraph.isCapFreeWord
#assert_no_axioms FX1Poly.Polygraph.censusAlphabet
#assert_no_axioms FX1Poly.Polygraph.censusWordsOfLength
#assert_no_axioms FX1Poly.Polygraph.singleCupWords
#assert_no_axioms FX1Poly.Polygraph.capFreeSingleCupWords
#assert_no_axioms FX1Poly.Polygraph.regionKindIndex
#assert_no_axioms FX1Poly.Polygraph.regionKindsAgree
#assert_no_axioms FX1Poly.Polygraph.countWordsOfKind
#assert_no_axioms FX1Poly.Polygraph.classRepresentativeOf
#assert_no_axioms FX1Poly.Polygraph.classRepresentativeOf_dependsOnDiagram
#assert_no_axioms FX1Poly.Polygraph.straddleRepresentativeIsJamResidue
#assert_no_axioms FX1Poly.Polygraph.straddleReachesItsRepresentative
#assert_no_axioms FX1Poly.Polygraph.natListBeq
#assert_no_axioms FX1Poly.Polygraph.diagramBeq
#assert_no_axioms FX1Poly.Polygraph.representativeRealizesOwnDiagram
#assert_no_axioms FX1Poly.Polygraph.countRepresentativesRealizing
#assert_no_axioms FX1Poly.Polygraph.straddleRepresentativeRealizes
#assert_no_axioms FX1Poly.Polygraph.straddleRepresentativeIsFixedPoint
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasClassRepresentativeReadjudication
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasClassRepresentativeDischarged
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_classRepresentativeReadjudicationTerminalState

end FX1PolyAudit
