import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyBlockSplit

/-! # FX1PolyAudit/…/SpineValleyBlockSplit — zero-axiom gate

Per-declaration zero-axiom gate for the Piece-I block extractor: converting the cell driver's `Bool`-tag valley
predicate into the typed `capBlock ++ cupBlock` form (`AllCapArity` / `AllCupArity`) that the Piece-II tail
consumes.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupArity_of_isCupAtom_true
#assert_no_axioms FX1Poly.Polygraph.capArity_of_isCupAtom_false
#assert_no_axioms FX1Poly.Polygraph.allCupArity_of_allCups
#assert_no_axioms FX1Poly.Polygraph.spineValley_blockSplit
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyBlockSplit

end FX1PolyAudit
