import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.MonadCoherentPresentation

/-! # FX1PolyAudit.Polygraph.Omega.MonadCoherentPresentationAudit — zero-axiom gate for the walking-monad
five-critical-pair Squier demonstrator (OMEGA-4 continued, WP-SQUIER capstone opening).

Per-declaration `#assert_no_axioms` on the re-encoded 2-polygraph generators, the five critical-pair leg
pairs, the base relation, the five generating 3-cells, the five peak / valley joins, the assembled
resolutions and the bundled coherent presentation, the two literally-globular `CriticalPairRow`
instances, the least-congruence universal property, the native five-count / cofork column, the
structural-distinctness and modulo-strict witnesses, and the honesty markers. -/

namespace FX1PolyAudit

-- MonadCoherentPresentation.lean — the 2-polygraph generators
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaGenBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPoint
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaTGen
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaTtWord
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaIdOne
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaEtaGen
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaMuGen

-- the five critical-pair leg pairs
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocRightLeg

-- the base relation
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaBaseRel

-- the five generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocThreeCell

-- the five peak joins
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocPeakJoin

-- the five valley joins
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocValleyJoin

-- the assembled resolutions and the coherent presentation
#assert_no_axioms FX1Poly.Polygraph.Omega.MonadCriticalPairResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.MonadWalkerCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.monadWalkerCoherentPresentation

-- the two literally-globular CriticalPairRow instances
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonRow
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocRow
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonRow_isParallelPair
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocRow_isParallelPair

-- the least-congruence universal property
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaCriticalPairsIdentifiedInEveryModel

-- the native five-count and cofork column
#assert_no_axioms FX1Poly.Polygraph.Omega.allMonadOmegaCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaCriticalPairCountIsFive
#assert_no_axioms FX1Poly.Polygraph.Omega.allMonadOmegaCriticalPairsExhaustive
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaCriticalPairCoforkColumn

-- the structural-distinctness and modulo-strict witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRightUnitAssocLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaRootUnitAssocLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaUnitUnitLegs_notLiterallyParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaLeftUnitAssocLegs_notLiterallyParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.monadOmegaPentagonLegs_literallyParallel

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingMonadFiveCriticalPairsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingMonadSquierPresentationOpensCapstone
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingMonadFullHomotopyBasisReached

end FX1PolyAudit
