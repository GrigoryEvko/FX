import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.InvolutionDemonstrator

/-! # FX1PolyAudit.Polygraph.Omega.InvolutionDemonstratorAudit — zero-axiom gate for the walking-involution
dim-3 Squier demonstrator (OMEGA-4 r1, B2).

Per-declaration `#assert_no_axioms` on the re-encoded 2-polygraph generators, the two critical-pair legs and
their boundaries, the generating 3-cell, the joinability witnesses (peak associativity + valley units), the
structural-distinctness and out-of-scope (non-literal-parallelism) witnesses, and the honesty marker. -/

namespace FX1PolyAudit

-- InvolutionDemonstrator.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionSGen
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionRhoGen
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionLeftLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionLeftLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionRightLeg_boundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionRightLeg_boundaryTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionBaseRel
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionSssThreeCell
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionLegs_distinct
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionLeftUnitJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionRightUnitJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionPeakJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionValleyJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionLegs_notLiterallyParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_involutionSssCriticalPairShipped

end FX1PolyAudit
