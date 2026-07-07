import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Grade.GradedSpectrum

/-! # FX1PolyAudit/Tier0/Mode/GradedSpectrum — zero-axiom gate

Per-declaration zero-axiom gate for the smooth-gradient `GradedSpectrum`: the new coordinate orders
(Epistemic, AdjointClass fan), the product partial order, the pole embeddings, the monotone rung diagonal
with its decategorification classifier, the two witnessed interior positions, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.EpistemicStrength.rank_injective
#assert_no_axioms FX1Poly.Tier0.EpistemicStrength.le_refl
#assert_no_axioms FX1Poly.Tier0.EpistemicStrength.le_trans
#assert_no_axioms FX1Poly.Tier0.EpistemicStrength.le_antisymm
#assert_no_axioms FX1Poly.Tier0.AdjointClass.le_refl
#assert_no_axioms FX1Poly.Tier0.AdjointClass.le_trans
#assert_no_axioms FX1Poly.Tier0.AdjointClass.le_antisymm
#assert_no_axioms FX1Poly.Tier0.AdjointClass.tangible_le
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.le_refl
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.le_trans
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.le_antisymm
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.bottom_le
#assert_no_axioms FX1Poly.Tier0.geometricOfModal_sinister
#assert_no_axioms FX1Poly.Tier0.geometricOfModal_tangible
#assert_no_axioms FX1Poly.Tier0.geometricOfModal_sharp
#assert_no_axioms FX1Poly.Tier0.geometricOfModal_transparent
#assert_no_axioms FX1Poly.Tier0.fibrantKind_geometric
#assert_no_axioms FX1Poly.Tier0.exotypeKind_geometric
#assert_no_axioms FX1Poly.Tier0.monotone_rungs
#assert_no_axioms FX1Poly.Tier0.rungOfSpectrum_rungPos
#assert_no_axioms FX1Poly.Tier0.strictPole_lt_interiorBlend
#assert_no_axioms FX1Poly.Tier0.interiorBlend_lt_rungR4
#assert_no_axioms FX1Poly.Tier0.interiorBlend_ne_poles
#assert_no_axioms FX1Poly.Tier0.directedPole_lt_interiorFibrancy_lt_omega
#assert_no_axioms FX1Poly.Tier0.interiorFibrancy_ne_geometricOfModal
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGradedSpectrum

end FX1PolyAudit
