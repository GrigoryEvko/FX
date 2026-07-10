import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.CyclicThreeDemonstrator

/-! # FX1PolyAudit.Polygraph.Omega.CyclicThreeDemonstratorAudit — zero-axiom gate for the
walking-cyclic-3 two-critical-pair Squier demonstrator (OMEGA-4 continued, WP-SQUIER r2).

Per-declaration `#assert_no_axioms` on the re-encoded 2-polygraph generators, the four critical-pair legs
and their boundaries, the base relation, the two generating 3-cells, the two peak joins (the associativity
chains — the genuinely new proof content) and the two valley joins (units), the assembled resolutions and
coherent presentation, the least-congruence universal property, the native two-count / rule-count / cofork
column, the structural-distinctness and modulo-strict witnesses, and the honesty markers. -/

namespace FX1PolyAudit

-- CyclicThreeDemonstrator.lean — the 2-polygraph generators
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaGenBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaPoint
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSGen
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsWord
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssWord
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaIdOne
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaRhoGen

-- the four critical-pair legs and their boundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssLeftLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssLeftLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssRightLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssRightLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssLeftLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssLeftLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssRightLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssRightLeg_boundaryTarget

-- the base relation and the two generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssThreeCell

-- the two peak joins (the associativity chains) and the two valley joins
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssValleyJoin

-- the assembled resolutions and the coherent presentation
#assert_no_axioms FX1Poly.Polygraph.Omega.CyclicThreeOmegaCriticalPairResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.CyclicThreeWalkerCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeWalkerCoherentPresentation

-- the least-congruence universal property
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaCriticalPairsIdentifiedInEveryModel

-- the native two-count, rule-count, and cofork column
#assert_no_axioms FX1Poly.Polygraph.Omega.allCyclicThreeOmegaCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaCriticalPairCountIsTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.allCyclicThreeOmegaCriticalPairsExhaustive
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaGeneratingRuleCount
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaCriticalPairCoforkColumn

-- the structural-distinctness and modulo-strict witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSsssLegs_notLiterallyParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaSssssLegs_notLiterallyParallel

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_cyclicThreeTwoCriticalPairsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_cyclicThreeOneRuleTwoCriticalPairsNewShape
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_cyclicThreeFullHomotopyBasisReached

end FX1PolyAudit
