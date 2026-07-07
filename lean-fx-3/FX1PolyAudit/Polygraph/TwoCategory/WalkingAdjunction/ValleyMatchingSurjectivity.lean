import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSurjectivity

/-! # FX1PolyAudit/…/ValleyMatchingSurjectivity — zero-axiom gate

Per-declaration zero-axiom gate for the SURJECTIVITY of the cup embedding onto the survivor positions (Piece
II tail): a whole-valley top port is a survivor-top iff it is a cup-embedding image position — the pure
combination of the shipped classification and value cover.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.survivorTop_iff_cupImage
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSurvivorTopCupImageBridge

end FX1PolyAudit
