import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyMidZeroReassembly

/-! # FX1PolyAudit/…/SpineValleyMidZeroReassembly — zero-axiom gate

Per-declaration zero-axiom gate for the mid-width-`0` valley block reassembly (Track B, MidZero cap dual): the
mid-`0` block reassembly (cap sort + width-`0` cup determinacy + append glue), the isolated mid-`0` cup-block
reconstruction residual interface, and the gated mid-`0` whole-valley `SpineTraceEquiv`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.midZeroSameMatchingValleys_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.MidZeroCupBlockReconstruct
#assert_no_axioms FX1Poly.Polygraph.midZeroValleysWithEqualMatching_spineTraceEquiv

end FX1PolyAudit
