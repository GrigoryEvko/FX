import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellLift

/-! # FX1PolyAudit/…/SpineValleyCellLift — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I cell-lifts (i)+(ii) per-step moves: the STRAIGHTEN lifts
(`snakePrefixStraightens` / `snakeStraightensInContext`, a collapsing frame-pair removed via
`zigzagStraightensPrefix` + `vcompAssoc`), the COMMUTE lifts (`godementExchangePrefix` /
`godementExchangeInContext`, two disjoint atoms transposed via `saturatedGodementExchange` bracketed by
`vcompAssoc`s), and the typed spine swap → cell conversion (`commuteAtomSwapCellLift`: `SpineAtomSwap` →
Godement step → trace equivalence → `SaturatedTwoCellConv`).  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.snakePrefixStraightens
#assert_no_axioms FX1Poly.Polygraph.snakeStraightensInContext
#assert_no_axioms FX1Poly.Polygraph.godementExchangePrefix
#assert_no_axioms FX1Poly.Polygraph.godementExchangeInContext
#assert_no_axioms FX1Poly.Polygraph.commuteAtomSwapCellLift
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCellLiftMoves

end FX1PolyAudit
