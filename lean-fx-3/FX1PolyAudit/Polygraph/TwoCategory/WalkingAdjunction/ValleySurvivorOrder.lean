import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleySurvivorOrder

/-! # FX1PolyAudit/…/ValleySurvivorOrder — zero-axiom gate

Per-declaration zero-axiom gate for the survivor-order-preservation leg of the valley-append split (Piece II tail
of the fib-3 gate): a pure-cup block order-embeds any boundary-tracking mid-state's open wires into the final open
wires (`processSpine_wireOrderEmbedding_ofAllCupArity`), built from the single-splice position embedding and its
value / order / bound lemmas.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_shiftPastPosition
#assert_no_axioms FX1Poly.Polygraph.shiftPastPosition_strictMono
#assert_no_axioms FX1Poly.Polygraph.shiftPastPosition_lt
#assert_no_axioms FX1Poly.Polygraph.wireOrderEmbedding_id
#assert_no_axioms FX1Poly.Polygraph.wireOrderEmbedding_comp
#assert_no_axioms FX1Poly.Polygraph.stepCup_wireOrderEmbedding
#assert_no_axioms FX1Poly.Polygraph.processSpine_wireOrderEmbedding_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleySurvivorOrderPreservation

end FX1PolyAudit
