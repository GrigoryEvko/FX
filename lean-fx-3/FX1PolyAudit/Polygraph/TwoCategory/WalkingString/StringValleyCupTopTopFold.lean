import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCupTopTopFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCupTopTopFold — zero-axiom gate
(FC-3 r34, Piece-II tail: the two-floor peel induction of the top-top offset agreement, over the walking
ADJOINT-TRIPLE signature)

Per-declaration zero-axiom gate for the string two-floor peel induction `stringTopRegionOffsetAgrees_fold`.  The
private range/length plumbing (`rangeLoopLenSCTTF`, `rangeLenSCTTF`, `stepCupArcOpenWiresLenSCTTF`,
`extractArcPartnerLenSCTTF`) is covered transitively.  Every declaration must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringTopRegionOffsetAgrees_fold
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupTopTopFold

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringTopRegionOffsetAgrees_fold
#print axioms FX1Poly.Polygraph.fxString_hasCupTopTopFold

end FX1PolyAudit
