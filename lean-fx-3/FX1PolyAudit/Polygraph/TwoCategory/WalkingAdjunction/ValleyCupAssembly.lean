import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupAssembly

/-! # FX1PolyAudit/…/ValleyCupAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the cup half of the valley-append split + the clean whole-valley theorem
(Piece II tail final assembly, gated on `cupRestrict_reconstructs`): the cup-block matching equality
(`sameWholeMatching_cupBlockMatchingEq`), the full split (`valleyAppend_split`), and the whole-valley
`SpineTraceEquiv` (`valleysWithEqualMatching_spineTraceEquiv`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.sameWholeMatching_cupBlockMatchingEq
#assert_no_axioms FX1Poly.Polygraph.valleyAppend_split
#assert_no_axioms FX1Poly.Polygraph.valleysWithEqualMatching_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyCupAssemblyGatedOnReconstruction

end FX1PolyAudit
