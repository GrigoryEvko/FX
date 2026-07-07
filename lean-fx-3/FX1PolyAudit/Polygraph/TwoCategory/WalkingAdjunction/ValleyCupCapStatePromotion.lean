import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupCapStatePromotion

/-! # FX1PolyAudit/…/ValleyCupCapStatePromotion — zero-axiom gate

Per-declaration zero-axiom gate for sub-node (ii) of the top-top two-run offset fold: the general in-valley cap
seed `processArcSpine (arcInit bottomCount) capBlock` carries every `diagramPartner_stepCupArc` precondition
(`ArcStateFresh` / `isUnionFindForest` / `seedBelowFresh` / `ArcBoundaryCensus`) at floor `bottomCount`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapState_arcStateFresh
#assert_no_axioms FX1Poly.Polygraph.arcCapState_isUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.arcCapState_seedBelowFresh
#assert_no_axioms FX1Poly.Polygraph.arcCapState_arcBoundaryCensus
#assert_no_axioms FX1Poly.Polygraph.arcCapState_stepCupArc_preconditions
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupCapStatePromotion

end FX1PolyAudit
