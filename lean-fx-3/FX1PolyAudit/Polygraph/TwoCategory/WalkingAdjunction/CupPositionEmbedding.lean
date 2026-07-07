import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.CupPositionEmbedding

/-! # FX1PolyAudit/…/CupPositionEmbedding — zero-axiom gate

Per-declaration zero-axiom gate for the concrete, seed-agnostic cup position embedding (Piece II tail keystone):
the concrete embedding function and the two concrete order-embedding facts (order embedding + image cover) that pin
both cup-run twin-instantiations to ONE literal `phi = cupPositionEmbedding cupBlock`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupPositionEmbedding
#assert_no_axioms FX1Poly.Polygraph.cupPositionEmbedding_isWireOrderEmbedding
#assert_no_axioms FX1Poly.Polygraph.cupPositionEmbedding_imageCover
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasConcreteCupPositionEmbedding

end FX1PolyAudit
