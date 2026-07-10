import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.PresentationOpDualityWithId

/-! # FX1PolyAudit.Polygraph.Omega.PresentationOpDualityWithIdAudit — zero-axiom gate for the op-dual
transport of the Omega-lane Squier presentations (WP-SQUIER r3, the #2082 op-dual round).

Per-declaration `#assert_no_axioms` on the cell involution and its involutivity, the boundary-commutation
lemma and its two extractions, the strict-law op-stability (interchange on the nose), the op'd relation and
the generic convertibility transport, the op'd-strict-coincides corollary, the generic critical-pair
resolution and its peak<->valley op-swap, the two genuine op-dual walkers (walking comonad five pairs,
idempotent comonad one pair) with their statements / presentations / UPs and the truth-probe, and the honesty
markers. -/

namespace FX1PolyAudit

-- PresentationOpDualityWithId.lean — the cell involution
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellExpr
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellExpr_involutive

-- the boundary-commutation lemma and its extractions
#assert_no_axioms FX1Poly.Polygraph.Omega.OpBoundaryCommutes
#assert_no_axioms FX1Poly.Polygraph.Omega.opBoundaryCommutes_all
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellExpr_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellExpr_boundaryTarget

-- the strict-law op-stability
#assert_no_axioms FX1Poly.Polygraph.Omega.opStrictAxiomStable

-- the op'd relation and the generic convertibility transport
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellRelOver
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellRelOver_involutive
#assert_no_axioms FX1Poly.Polygraph.Omega.opDualityForwardCongruenceWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.opConvWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.opCellRelOverStrictAxiom_derivable

-- the generic critical-pair resolution and its peak<->valley op-swap
#assert_no_axioms FX1Poly.Polygraph.Omega.CriticalPairResolvedOver
#assert_no_axioms FX1Poly.Polygraph.Omega.opCriticalPairResolved

-- the walking comonad = op(monad), five op-dual critical pairs
#assert_no_axioms FX1Poly.Polygraph.Omega.monadResolvedToOver
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaUnitUnitResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaLeftUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaRightUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaPentagonResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaRootUnitAssocResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.ComonadWalkerCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadWalkerCoherentPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadCriticalPairsIdentifiedInEveryModel

-- the idempotent comonad = op(idempotent semigroup), one op-dual critical pair
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentResolvedToOver
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentComonadPeakJoinTransported
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentComonadOmegaEeeResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.IdempotentComonadWalkerCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentComonadWalkerCoherentPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentComonadCriticalPairsIdentifiedInEveryModel

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_omegaLaneHasOpInvolutionAndTransportR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierFamilyTwoGenuineOpDualsShippedR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierOpDualPresentationNotConvergenceR3

end FX1PolyAudit
