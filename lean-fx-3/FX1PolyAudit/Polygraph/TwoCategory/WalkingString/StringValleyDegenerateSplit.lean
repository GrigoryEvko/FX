import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit — zero-axiom gate

Per-declaration zero-axiom gate for the Piece-II three-way split: the colour-blind block extractor (the block
split + its three arity read-offs), the empty-source cap collapse, the case-(a) reducer proved from the width-0
sub-producer, the three named colour-keyed sub-producer Props, the FULL three-way split reducing
`StringCellValleyTraceEquiv` to those three, and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCupArity_of_isCupAtom_true
#assert_no_axioms FX1Poly.Polygraph.stringCapArity_of_isCupAtom_false
#assert_no_axioms FX1Poly.Polygraph.stringAllCupArity_of_allCups
#assert_no_axioms FX1Poly.Polygraph.stringSpineValley_blockSplit
#assert_no_axioms FX1Poly.Polygraph.stringCapBlockEmpty_ofSourceZero
#assert_no_axioms FX1Poly.Polygraph.StringWidthZeroPureCupDeterminacy
#assert_no_axioms FX1Poly.Polygraph.StringWidthZeroPureCupDeterminacyShared
#assert_no_axioms FX1Poly.Polygraph.stringDegenerateEmptySource_of_widthZero
#assert_no_axioms FX1Poly.Polygraph.StringMidZeroValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.StringCellValleyTraceEquivPositive
#assert_no_axioms FX1Poly.Polygraph.stringCellValleyTraceEquiv_of_widthZero_of_midZero
#assert_no_axioms FX1Poly.Polygraph.fxString_hasValleyDegenerateSplit

end FX1PolyAudit
