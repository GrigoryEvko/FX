import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingEquivalencePresentation

/-! # FX1PolyAudit.Polygraph.Omega.WalkingEquivalencePresentationAudit — zero-axiom gate for the
walking-equivalence two-object invertible-unit/counit presentation (WP-EQUIV r1, B1).

Per-declaration `#assert_no_axioms` on the two-object signature and comparators, the objects / 1-cells /
2-cell generators, the four cancellation cells and their literal boundaries, the four cancellation rows and
the base relation, the four generating 3-cells, the per-pair resolutions (peak refl / valley refl — literally
globular on both boundaries), the coherent presentation, the least-congruence universal property, the
four-row census, the structural-distinctness / literal-globularity witnesses, and the honesty markers. -/

namespace FX1PolyAudit

-- WalkingEquivalencePresentation.lean — the two-object signature and comparators
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivGenLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLabelTag
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLabelBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivModeBeq
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivGenBeq

-- the objects and the 1-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivObjectA
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivObjectB
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFGen
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivGGen
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitA
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitB
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdA
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdB

-- the four invertible unit/counit 2-generators
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaGen
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaInvGen
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEpsGen
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEpsInvGen

-- the four cancellation cells and their literal boundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaEtaInv
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdIdA
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaInvEta
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdUnitA
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEpsEpsInv
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdUnitB
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEpsInvEps
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdIdB
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaEtaInv_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaEtaInv_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaInvEta_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaInvEta_boundaryTarget

-- the four cancellation rows and the base relation
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivCancellationRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivBaseRel

-- the four generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelForwardThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelBackwardThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCounitCancelForwardThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCounitCancelBackwardThreeCell

-- the per-pair resolutions and the coherent presentation
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivCancellationResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelForwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelBackwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCounitCancelForwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCounitCancelBackwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivalenceCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivalenceCoherentPresentation

-- the least-congruence universal property
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCancellationsIdentifiedInEveryModel

-- the four-row census
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivCancellationLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.allWalkingEquivCancellations
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCancellationCountIsFour
#assert_no_axioms FX1Poly.Polygraph.Omega.allWalkingEquivCancellationsExhaustive

-- the structural-distinctness / literal-globularity witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivObjects_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivFG_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelForwardLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelBackwardLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCounitCancelForwardLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivCounitCancelBackwardLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelForwardLegs_literallyParallelSource
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelForwardLegs_literallyParallelTarget

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_walkingEquivalencePresentationShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_cancellationRowsLiterallyGlobularBothBoundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_firstTwoObjectOmegaWalker

-- B2 — the adjoint equivalence: the two triangle legs and their identity 2-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdF
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdG
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleLeg_boundaryTarget

-- B2 — the two triangle rows and the adjoint base relation
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivTriangleRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivPresentationRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivBaseRel

-- B2 — the two triangle generating 3-cells
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleThreeCell

-- B2 — the six per-pair resolutions over the adjoint base relation
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivUnitCancelForwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivUnitCancelBackwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivCounitCancelForwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivCounitCancelBackwardResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleResolved
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleResolved

-- B2 — the adjoint coherent presentation and the least-congruence UP
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingAdjointEquivalenceCoherentPresentationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjointEquivalenceCoherentPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivRowsIdentifiedInEveryModel

-- B2 — the triangle census
#assert_no_axioms FX1Poly.Polygraph.Omega.WalkingEquivTriangleLabel
#assert_no_axioms FX1Poly.Polygraph.Omega.allWalkingEquivTriangles
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivTriangleCountIsTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingAdjEquivRowCountIsSix

-- B2 — the op-duality transport truth-probes
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleResolvedOpTransported
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitCancelForwardResolvedOpTransported

-- B2 — the triangle non-vacuity / modulo-strict witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLegs_notLiterallyParallelSource
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLegs_notLiterallyParallelTarget

-- B2 — the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_walkingAdjointEquivalenceTrianglesShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_equivalenceSelfOpDualFreeRider

-- B3 — the promotion: the abstract engine, the right defect inverse, the mechanized invertibility
#assert_no_axioms FX1Poly.Polygraph.Omega.convEndoInvertibleIdempotent_isIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefectInverse
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefect_leftInverse

-- B3 — the conditional promotion (right triangle from idempotency) and the non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_ofIdempotency
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefectInverse_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightDefectRoundTrip_notLiterallyId

-- B3 — the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionRightDefectInvertibilityMechanized
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionReducedToIdempotency
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionIdempotencyFromLeftTriangleWalled

end FX1PolyAudit
