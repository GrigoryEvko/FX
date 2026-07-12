import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringIdentificationCapstone

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringIdentificationCapstone — zero-axiom gate
(FC-3 r46, the post-flip harvest + the #2209 identification)

Per-declaration zero-axiom gate for the identification capstone: the two-level (coloured) completeness, the full
Piece-II valley trace-equivalence, the second valley-assembly derivation of the #2020 decision, the identification
biconditional `stringSaturatedConv_iff_matchingOf_eq`, and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringConvOfColouredMapEq_holds
#assert_no_axioms FX1Poly.Polygraph.stringCellValleyTraceEquiv_holds
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_viaThreeSubProducers
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_iff_matchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.fxString_hasIdentificationCapstone

end FX1PolyAudit
