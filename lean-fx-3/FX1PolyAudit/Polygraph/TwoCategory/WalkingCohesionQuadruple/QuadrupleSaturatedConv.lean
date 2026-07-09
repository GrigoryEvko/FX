import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleSaturatedConv

/-! # FX1PolyAudit.…WalkingCohesionQuadruple.QuadrupleSaturatedConv — zero-axiom gate (the saturated conv)

Per-declaration zero-axiom gate for the walking-cohesion-quadruple saturated 2-cell convertibility: the nine
generator cells, the identity cells, the six triangle snakes, the six ff-iso round-trip composites, the relation
itself, the embeddings, the three ff-invertibility witnesses, and the two shared-leg snake coherences.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.quadUnitLowerCell
#assert_no_axioms FX1Poly.Polygraph.quadCounitLowerCell
#assert_no_axioms FX1Poly.Polygraph.quadUnitMiddleCell
#assert_no_axioms FX1Poly.Polygraph.quadCounitMiddleCell
#assert_no_axioms FX1Poly.Polygraph.quadUnitUpperCell
#assert_no_axioms FX1Poly.Polygraph.quadCounitUpperCell
#assert_no_axioms FX1Poly.Polygraph.quadInvCounitLowerCell
#assert_no_axioms FX1Poly.Polygraph.quadInvUnitMiddleCell
#assert_no_axioms FX1Poly.Polygraph.quadInvCounitUpperCell
#assert_no_axioms FX1Poly.Polygraph.quadPi0IdCell
#assert_no_axioms FX1Poly.Polygraph.quadDiscIdCell
#assert_no_axioms FX1Poly.Polygraph.quadGammaIdCell
#assert_no_axioms FX1Poly.Polygraph.quadCodiscIdCell
#assert_no_axioms FX1Poly.Polygraph.quadDiscPi0IdCell
#assert_no_axioms FX1Poly.Polygraph.quadDiscGammaIdCell
#assert_no_axioms FX1Poly.Polygraph.quadCodiscGammaIdCell
#assert_no_axioms FX1Poly.Polygraph.quadNilPointSetIdCell
#assert_no_axioms FX1Poly.Polygraph.quadTriPi0SnakeCell
#assert_no_axioms FX1Poly.Polygraph.quadTriDiscLoSnakeCell
#assert_no_axioms FX1Poly.Polygraph.quadTriDiscHiSnakeCell
#assert_no_axioms FX1Poly.Polygraph.quadTriGammaLoSnakeCell
#assert_no_axioms FX1Poly.Polygraph.quadTriGammaHiSnakeCell
#assert_no_axioms FX1Poly.Polygraph.quadTriCodiscSnakeCell
#assert_no_axioms FX1Poly.Polygraph.quadLowerCounitRoundRightCell
#assert_no_axioms FX1Poly.Polygraph.quadLowerCounitRoundLeftCell
#assert_no_axioms FX1Poly.Polygraph.quadMiddleUnitRoundRightCell
#assert_no_axioms FX1Poly.Polygraph.quadMiddleUnitRoundLeftCell
#assert_no_axioms FX1Poly.Polygraph.quadUpperCounitRoundRightCell
#assert_no_axioms FX1Poly.Polygraph.quadUpperCounitRoundLeftCell
#assert_no_axioms FX1Poly.Polygraph.QuadCohesionSaturatedTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.QuadCohesionSaturatedTwoCellConv.ofConv
#assert_no_axioms FX1Poly.Polygraph.quadCohesionConvOfStep
#assert_no_axioms FX1Poly.Polygraph.quadLowerCounitIsInvertible
#assert_no_axioms FX1Poly.Polygraph.quadMiddleUnitIsInvertible
#assert_no_axioms FX1Poly.Polygraph.quadUpperCounitIsInvertible
#assert_no_axioms FX1Poly.Polygraph.quadDiscSnakesCohere
#assert_no_axioms FX1Poly.Polygraph.quadGammaSnakesCohere
#assert_no_axioms FX1Poly.Polygraph.fxQuadCohesion_hasSaturatedConvWithFullyFaithful

end FX1PolyAudit
