import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSpineTopWord — zero-axiom gate (FC-3 r12)

Per-declaration zero-axiom gate for the spine top-word extractor: the extractor (`spineListTopWord`), its empty-spine
base case (`spineListTopWord_nil`), the production law (`spineListTopWord_spineDiff`), the initial-state seed
(`RawTwoCellExpr.spineListTopWord_spine`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineListTopWord
#assert_no_axioms FX1Poly.Polygraph.spineListTopWord_nil
#assert_no_axioms FX1Poly.Polygraph.spineListTopWord_spineDiff
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineListTopWord_spine
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineTopWordExtractor

end FX1PolyAudit
