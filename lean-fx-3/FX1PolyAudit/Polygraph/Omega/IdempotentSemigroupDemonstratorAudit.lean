import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.IdempotentSemigroupDemonstrator

/-! # FX1PolyAudit.Polygraph.Omega.IdempotentSemigroupDemonstratorAudit — zero-axiom gate for the
walking-idempotent-semigroup one-critical-pair Squier demonstrator (OMEGA-4 continued, WP-SQUIER r2).

Per-declaration `#assert_no_axioms` on the re-encoded 2-polygraph generators, the two critical-pair legs
and their boundaries, the base relation, the generating 3-cell, the peak / valley joins (associativity /
half-globular refl), the assembled resolution and coherent presentation, the least-congruence universal
property, the native one-count / cofork column, the structural-distinctness / modulo-strict / literal
half-globular witnesses, and the honesty markers. -/

namespace FX1PolyAudit

-- IdempotentSemigroupDemonstrator.lean — the 2-polygraph generators
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaGenBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaPoint
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEGen
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeWord
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMuGen

-- the two critical-pair legs and their boundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeLeftLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeRightLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeLeftLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeRightLeg_boundaryTarget

-- the base relation and the generating 3-cell
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeThreeCell

-- the peak / valley joins
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeePeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeValleyJoin

-- the assembled resolution and the coherent presentation
#assert_no_axioms FX1Poly.Polygraph.Omega.IdempotentSemigroupCriticalPairResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.IdempotentSemigroupWalkerCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupWalkerCoherentPresentation

-- the least-congruence universal property
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaCriticalPairsIdentifiedInEveryModel

-- the native one-count and cofork column
#assert_no_axioms FX1Poly.Polygraph.Omega.allIdempotentSemigroupOmegaCriticalPairs
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaCriticalPairCountIsOne
#assert_no_axioms FX1Poly.Polygraph.Omega.allIdempotentSemigroupOmegaCriticalPairsExhaustive
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaCriticalPairCoforkColumn

-- the structural-distinctness / modulo-strict / literal half-globular witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeLegs_notLiterallyParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeValley_literallyEqual

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_idempotentSemigroupCriticalPairShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_idempotentSemigroupHalfGlobularValleyOnTheNose
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_idempotentSemigroupFullHomotopyBasisReached

end FX1PolyAudit
