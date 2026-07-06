import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexInjective

/-! # FX1PolyAudit/…/ArcCupReindexInjective — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head reindexing's injectivity atom:
`arcCupHeadReindexRecover` (the piecewise value-recovery inverse),
`arcCupHeadReindex_recoverLeftInverse` (left inverse by the four-zone probe trichotomy), and
`arcCupHeadReindex_injective` (injectivity from the left inverse) must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_recoverLeftInverse
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_injective
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupReindexInjective

end FX1PolyAudit
