import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupImageCover

/-! # FX1PolyAudit/…/ValleyCupImageCover — zero-axiom gate

Per-declaration zero-axiom gate for the cup fold's value-surjectivity (image-complement half of the
surjectivity residual #2185): a pure-cup block's order embedding covers every below-floor final open-wire
position (`processSpine_wireOrderImageCover_ofAllCupArity`), built from the single-splice surjectivity
`shiftPastPosition_surjOffBlock`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.shiftPastPosition_surjOffBlock
#assert_no_axioms FX1Poly.Polygraph.processSpine_wireOrderImageCover_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyCupImageCover

end FX1PolyAudit
