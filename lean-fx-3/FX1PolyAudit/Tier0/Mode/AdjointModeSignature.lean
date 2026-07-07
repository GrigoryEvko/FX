import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.AdjointModeSignature

/-! # FX1PolyAudit/Tier0/Mode/AdjointModeSignature — zero-axiom gate for the signature-parametric adjoint mode theory

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Mode/AdjointModeSignature.lean` — the MATT Definition 2.1
adjoint mode theory lifted to an arbitrary `ModeSignature`: the `AdjointClass` 4-tag decoration with its
membership predicates and containment laws, the generic `AdjointModeSignature` structure with the partial right
adjoint and class-implication laws, the derived edge predicates, the recovering 2LTT fibrancy instance (with the
`FibrancyMorphismShape` recovery bridge), the walking-adjunction seed instance, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The MATT class tag
#assert_no_axioms FX1Poly.Tier0.AdjointClass
#assert_no_axioms FX1Poly.Tier0.AdjointClass.isTangible
#assert_no_axioms FX1Poly.Tier0.AdjointClass.isSharp
#assert_no_axioms FX1Poly.Tier0.AdjointClass.isTransparent
#assert_no_axioms FX1Poly.Tier0.AdjointClass.isSinister
#assert_no_axioms FX1Poly.Tier0.AdjointClass.isSharp_implies_isTangible
#assert_no_axioms FX1Poly.Tier0.AdjointClass.isTransparent_implies_isTangible

-- ★ The signature-parametric adjoint mode theory
#assert_no_axioms FX1Poly.Tier0.AdjointModeSignature

-- Generic edge predicates
#assert_no_axioms FX1Poly.Tier0.AdjointModeSignature.isTangibleEdge
#assert_no_axioms FX1Poly.Tier0.AdjointModeSignature.isSharpEdge
#assert_no_axioms FX1Poly.Tier0.AdjointModeSignature.isTransparentEdge
#assert_no_axioms FX1Poly.Tier0.AdjointModeSignature.isSinisterEdge
#assert_no_axioms FX1Poly.Tier0.AdjointModeSignature.isSinisterEdge_hasRightAdjoint

-- Instance 1 — the recovering 2LTT fibrancy instance (adjoint-completed quiver)
#assert_no_axioms FX1Poly.Tier0.FibrancyModalityAdj
#assert_no_axioms FX1Poly.Tier0.fibrancyAdjGraph
#assert_no_axioms FX1Poly.Tier0.fibrancyAdjModeSignature
#assert_no_axioms FX1Poly.Tier0.fibrancyAdjointModeSignature
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_rightAdjoint_inclusion
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_rightAdjoint_inclusionAdj
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusion_isSinister_matches
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusion_isSharp_matches
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusion_isTransparent_matches
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusion_isTangible_matches
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusionAdj_isSinister_matches
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusion_isSinister
#assert_no_axioms FX1Poly.Tier0.fibrancyAdj_inclusion_hasRightAdjoint

-- Instance 2 — the walking-adjunction seed
#assert_no_axioms FX1Poly.Tier0.adjunctionAdjointModeSignature
#assert_no_axioms FX1Poly.Tier0.adjunction_left_isSinister
#assert_no_axioms FX1Poly.Tier0.adjunction_left_rightAdjoint
#assert_no_axioms FX1Poly.Tier0.adjunction_left_hasRightAdjoint
#assert_no_axioms FX1Poly.Tier0.adjunction_right_not_isSinister
#assert_no_axioms FX1Poly.Tier0.adjunction_right_rightAdjoint_none

-- Honesty marker
#assert_no_axioms FX1Poly.Tier0.fxMode_hasAdjointModeSignature

end FX1PolyAudit
