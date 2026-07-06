import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadRealizeCupToucher

/-! # FX1PolyAudit/…/ArcCupHeadRealizeCupToucher — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head discharge with the arity/boundary pins discharged:
the arity-generic assembly's six cup pins cut to the two genuine orbit residuals (window pin + tails
cancel) plus the located toucher being a cup.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupHeadExtractionConclusion_ofLocatedCupBubble
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadRealizeCupToucher

end FX1PolyAudit
