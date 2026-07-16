import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingEquivalencePromotionUnitorScope

/-! # FX1PolyAudit.Polygraph.Omega.WalkingEquivalencePromotionUnitorScopeAudit — zero-axiom gate for the
WP-EQUIV #2068 r4 promotion delivery over the whisker-unitor-augmented scope.

Per-declaration `#assert_no_axioms` on the relation-monotonicity fold, the two scope relations, the
scope-generic helpers, the two slide laws, the triangle-consequence chain, the middle collapse, the
idempotency and right-triangle promotions (generic + both instantiations), the flag-free eta-parity guard,
and the honesty markers — plus independent `#print axioms` on the headlines. -/

namespace FX1PolyAudit

-- the relation-monotonicity fold
#assert_no_axioms FX1Poly.Polygraph.Omega.saturatedConvOverWithIdMonoAbsorber
#assert_no_axioms FX1Poly.Polygraph.Omega.saturatedConvOverWithIdMono

-- the unitor-augmented scope relations
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitorScopeRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivUnitorLeftTriangleRel

-- the scope-generic helpers
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeAbsorbTrailingId
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeCancelRightFactor

-- the two slide laws
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeEtaInvSlidesAcrossUnitA
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeEpsSlidesAcrossUnitB

-- the left triangle spent
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeTriangleWhiskeredNormalized
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeSlidEpsIsSlidEtaInv
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeUnitBSlidEps

-- the middle collapse and the promotion (generic)
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeMiddleCollapses
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeIdempotencyFromLeftTriangle
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivScopeRightTriangleFromLeftTriangle

-- the conditional instantiations over the unitor scope
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotencyFromLeftTriangleOverUnitorScope
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleFromLeftTriangleOverUnitorScope

-- the non-vacuous instantiations over the triangle-adjoined bench
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangle_derivableOverUnitorTriangleRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotency_derivableOverUnitorTriangleRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_derivableOverUnitorTriangleRel

-- the flag-free eta-parity guard
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaFamilyFlagFreeContribution
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaFamilyFlagFree_pairsEta
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaFamilyFlagFree_pairsEps
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaFamilyParity_flagIndependent
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivEtaFamilyParity_ofUnitorScopeRow
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangle_notDerivableOverUnitorScopeRel
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_notDerivableOverUnitorScopeRel

-- the kernel-computed pins
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangleLeg_etaFamilyParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdF_etaFamilyParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangleLeg_etaFamilyParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivIdG_etaFamilyParityPin
#assert_no_axioms FX1Poly.Polygraph.Omega.walkingEquivDoubledRightTriangleLeg_distinctFromSingle

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionOverWhiskerUnitorScopeMechanized
#assert_no_axioms FX1Poly.Polygraph.Omega.fxEquiv_promotionUnitorWallLocalizedBothSides

-- independent axiom prints on the headlines (must print "does not depend on any axioms")
#print axioms FX1Poly.Polygraph.Omega.walkingEquivScopeIdempotencyFromLeftTriangle
#print axioms FX1Poly.Polygraph.Omega.walkingEquivScopeRightTriangleFromLeftTriangle
#print axioms FX1Poly.Polygraph.Omega.walkingEquivIdempotency_derivableOverUnitorTriangleRel
#print axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_derivableOverUnitorTriangleRel
#print axioms FX1Poly.Polygraph.Omega.walkingEquivLeftTriangle_notDerivableOverUnitorScopeRel
#print axioms FX1Poly.Polygraph.Omega.walkingEquivRightTriangle_notDerivableOverUnitorScopeRel

end FX1PolyAudit
