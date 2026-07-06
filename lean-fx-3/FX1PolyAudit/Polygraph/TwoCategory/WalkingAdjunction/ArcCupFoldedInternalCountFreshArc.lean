import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedInternalCountFreshArc

/-! # FX1PolyAudit/…/ArcCupFoldedInternalCountFreshArc — zero-axiom gate

Per-declaration zero-axiom gate for the cup tails-cancel's two INTERNAL count legs derived from fresh-seed
arc equality: the folded cup- and cap-count list agreements
`arcCupFoldedInternalCupCountList_agrees_ofFreshArcEqual` / `…Cap…` (the fold's per-index readoff is the
arc-structure `internalCupCounts` / `internalCapCounts` field entry, so equal fresh arc structures give
equal folded lists — no `sameClassification`) must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedInternalCupCountList_agrees_ofFreshArcEqual
#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedInternalCapCountList_agrees_ofFreshArcEqual
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupFoldedInternalCountFreshArc

end FX1PolyAudit
