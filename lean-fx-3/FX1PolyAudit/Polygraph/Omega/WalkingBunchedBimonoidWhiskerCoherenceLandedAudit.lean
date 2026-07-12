import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWhiskerCoherenceLanded

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidWhiskerCoherenceLandedAudit — zero-axiom gate for the
WP-PROP r19 substrate harvest: the whisker-1-cell associator (+dual) + whisker-commute LANDED into `StrictAxiomRel`,
and the identity-whisker unitor machine-refuted / walled.

Per-declaration `#assert_no_axioms` on the landed-row convertibilities, their `linearizeFull` soundness folds, the
concrete bunched instances, the ★★ unitor STOP (chain tables differ + non-convertibility), and both markers, PLUS
independent (non-fuel) `#print axioms` on a landed-row soundness fold, the unitor STOP, and the two markers. -/

namespace FX1PolyAudit

-- L1 — the landed rows fire as `StrictAxiomRel` convertibilities (generic + bunched instances).
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerAssociatorLeftConv
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerAssociatorRightConv
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerCommuteConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerAssocLeftLanded
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerCommuteLanded

-- L2 — the landed rows fold through the extended `linearizeFullSoundness` to equal chain tables.
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerAssociatorLeft_linearizeFull
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerAssociatorRight_linearizeFull
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerCommute_linearizeFull

-- L3 — the ★★ identity-whisker unitor STOP.
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerIdentityUnitorTablesDiffer
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerIdentityUnitor_not_conv
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskerIdentityUnitorTop_equal

-- L4 — the honest r19 markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerAssociatorAndCommuteLanded
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerIdentityUnitorChainRefutedStaysWalled

-- Independent (non-fuel) axiom prints on a landed-row soundness fold, the unitor STOP, and the two markers.
#print axioms FX1Poly.Polygraph.Omega.whiskerAssociatorLeft_linearizeFull
#print axioms FX1Poly.Polygraph.Omega.whiskerIdentityUnitor_not_conv
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerAssociatorAndCommuteLanded
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerIdentityUnitorChainRefutedStaysWalled

end FX1PolyAudit
