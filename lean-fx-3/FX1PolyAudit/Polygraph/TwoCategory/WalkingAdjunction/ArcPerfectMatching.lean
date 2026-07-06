import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatching

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPerfectMatching — zero-axiom gate

Per-declaration zero-axiom gate for the perfect-matching (no-fixed-point) foundation: the
perfect-matching invariant forbids `partnerIndexOf` fixed points, and the seed state is perfectly
matched (every bottom port and open slot has a genuine partner).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_neSelf_ofPerfectMatching
#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatching_initial

end FX1PolyAudit
