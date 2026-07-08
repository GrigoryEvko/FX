import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedConv

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedConv — zero-axiom gate (the saturated walking-monad convertibility)

Per-declaration zero-axiom gate for the SATURATED walking-monad 2-cell convertibility: the unit / multiplication
cells, the three law composites, the saturated relation, its `ofConv` embedding, the three monad-law witnesses,
the whiskered / coherence smokes, and the established marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadUnitTwoCell
#assert_no_axioms FX1Poly.Polygraph.monadMulTwoCell
#assert_no_axioms FX1Poly.Polygraph.monadLeftUnitCell
#assert_no_axioms FX1Poly.Polygraph.monadRightUnitCell
#assert_no_axioms FX1Poly.Polygraph.monadAssocLeftCell
#assert_no_axioms FX1Poly.Polygraph.monadAssocRightCell
#assert_no_axioms FX1Poly.Polygraph.monadIdTCell
#assert_no_axioms FX1Poly.Polygraph.MonadSaturatedTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.MonadSaturatedTwoCellConv.ofConv
#assert_no_axioms FX1Poly.Polygraph.monadLeftUnitHolds
#assert_no_axioms FX1Poly.Polygraph.monadRightUnitHolds
#assert_no_axioms FX1Poly.Polygraph.monadAssocHolds
#assert_no_axioms FX1Poly.Polygraph.monadLeftUnitWhiskeredHolds
#assert_no_axioms FX1Poly.Polygraph.monadUnitCoherence
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasSaturatedTwoCellConvRelation

end FX1PolyAudit
