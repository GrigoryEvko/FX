import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryWordChain

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineBoundaryWordChain — zero-axiom gate

Per-declaration zero-axiom gate for the spine boundary-WORD-chain substrate (STRING-JOINT r2 WALL 2 brick A):
the word-chain predicate's cons inversion, the production lemma for spine difference-lists, the initial-state
seed, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_tail
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_spineDiff
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineBoundaryWordChained_spine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineBoundaryWordChainSubstrate

end FX1PolyAudit
