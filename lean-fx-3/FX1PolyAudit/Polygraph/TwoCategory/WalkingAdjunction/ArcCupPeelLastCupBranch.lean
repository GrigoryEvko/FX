import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPeelLastCupBranch

/-! # FX1PolyAudit/…/ArcCupPeelLastCupBranch — zero-axiom gate

Per-declaration zero-axiom gate for the CUP branch of the peel-last obligation `SpineArcLastExtractionChained`:
the realized back-bubble trace equivalence, the matched-remainder boundary chain, and their assembly into the
obligation's threefold existential (modulo the located split + back-bubble existence + moved-image pin + mixed
arc-cancellation, all named residuals).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `ofReduceBool`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcLastCupCase_backBubbleTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.arcLastCupCase_matchedInitChained
#assert_no_axioms FX1Poly.Polygraph.arcLastCupCase_extractionConclusion_ofLocatedBackBubbleAndCancel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPeelLastCupBranch

end FX1PolyAudit
