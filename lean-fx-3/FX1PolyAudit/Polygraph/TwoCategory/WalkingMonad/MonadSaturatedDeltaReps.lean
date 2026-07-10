import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps — zero-axiom gate (the deep bridge)

Per-declaration zero-axiom gate for the bespoke-free DEEP saturated-Δ representatives bridge: the unit /
multiplication free 2-cells and the three law composites, relocated VERBATIM from the pure-bespoke Δ chain so the
survivor lane can consume the walking-monad skeleton conv-decoupled.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadUnitTwoCell
#assert_no_axioms FX1Poly.Polygraph.monadMulTwoCell
#assert_no_axioms FX1Poly.Polygraph.monadLeftUnitCell
#assert_no_axioms FX1Poly.Polygraph.monadRightUnitCell
#assert_no_axioms FX1Poly.Polygraph.monadAssocLeftCell
#assert_no_axioms FX1Poly.Polygraph.monadAssocRightCell
#assert_no_axioms FX1Poly.Polygraph.monadIdTCell

end FX1PolyAudit
