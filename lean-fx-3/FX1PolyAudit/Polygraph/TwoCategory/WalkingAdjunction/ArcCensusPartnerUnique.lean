import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCensusPartnerUnique — zero-axiom gate

Per-declaration zero-axiom gate for the census partner uniqueness (peel campaign H, cup rung
2d-v): any exhibited same-component candidate pins the canonical partner scan's answer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_uniqueSameComponent

end FX1PolyAudit
