import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedFragmentNonConfluence

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedFragmentNonConfluence — zero-axiom gate

Per-declaration zero-axiom gate for the whiskered-snake falsification: the peak, its two
normal forms, the two reduction chains, the two reducer-halt irreducibility certificates,
distinctness, and the two negative punchlines.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakePeak
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakeDistributedNormal
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakeIdentityNormal
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakePeak_reducesTo_distributed
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakePeak_reducesTo_identity
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakeDistributedNormal_irreducible
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnakeIdentityNormal_irreducible
#assert_no_axioms FX1Poly.Polygraph.whiskeredSnake_normalForms_distinct
#assert_no_axioms FX1Poly.Polygraph.saturatedFragment_notConfluent
#assert_no_axioms FX1Poly.Polygraph.saturatedFragment_notLocallyConfluent

end FX1PolyAudit
