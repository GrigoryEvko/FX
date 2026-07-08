import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthZeroCupWitness

/-! # FX1PolyAudit/…/SpineValleyWidthZeroCupWitness — zero-axiom gate

Per-declaration zero-axiom gate for the route-2 interchange mechanism proven on the refuting pair
(Track B): the two interchange-reordered disjoint tail cups over the shared width-`0` head cup are
`SpineTraceEquiv`, by a single Godement step transposing the head cup with the tail cup.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.widthZeroPeelReorderings_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyWidthZeroCupWitness

end FX1PolyAudit
