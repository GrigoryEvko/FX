import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineAtomWordPin

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSpineAtomWordPin — zero-axiom gate (FC-3 r10, B1 keystone)

Per-declaration zero-axiom gate for the word-level spine-atom pin: the parallel-generator subsingleton
(`stringTwoCell_unique_of_wordBoundaries`), the dom-determined cod pack (`stringTwoCell_codPack_uniqueOfDom`), the
keystone atom pin (`stringSpineAtom_eq_of_wordReadOffs`), and the two markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringTwoCell_unique_of_wordBoundaries
#assert_no_axioms FX1Poly.Polygraph.stringTwoCell_codPack_uniqueOfDom
#assert_no_axioms FX1Poly.Polygraph.stringSpineAtom_eq_of_wordReadOffs
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineAtomWordPin
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineAtomWordPinCompletenessFlip

end FX1PolyAudit
