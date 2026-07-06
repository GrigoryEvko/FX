import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedDiagramFreshArc

/-! # FX1PolyAudit/…/ArcCupFoldedDiagramFreshArc — zero-axiom gate

Per-declaration zero-axiom gate for the cup tails-cancel's DIAGRAM leg derived from fresh-seed arc
equality: the folded partner list agreement `arcCupFoldedDiagramPartnerList_agrees_ofFreshArcEqual` (the
fold's per-index `partnerIndexOf` readoff is the arc-structure `.diagram.partner` field entry, so equal
fresh arc structures give equal folded partner lists — no `sameClassification`) must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedDiagramPartnerList_agrees_ofFreshArcEqual
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupFoldedDiagramFreshArc

end FX1PolyAudit
