import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Grade.GradedSpectrum

/-! # FX1PolyAudit/Axis/Mode/GradedSpectrum — zero-axiom gate

Per-declaration zero-axiom gate for the smooth-gradient `GradedSpectrum`: the new coordinate orders
(Epistemic, AdjointClass fan), the product partial order, the pole embeddings, the monotone rung diagonal
with its decategorification classifier, the two witnessed interior positions, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.EpistemicStrength.rank_injective
#assert_no_axioms FX1Poly.Axis.EpistemicStrength.le_refl
#assert_no_axioms FX1Poly.Axis.EpistemicStrength.le_trans
#assert_no_axioms FX1Poly.Axis.EpistemicStrength.le_antisymm
#assert_no_axioms FX1Poly.Axis.AdjointClass.le_refl
#assert_no_axioms FX1Poly.Axis.AdjointClass.le_trans
#assert_no_axioms FX1Poly.Axis.AdjointClass.le_antisymm
#assert_no_axioms FX1Poly.Axis.AdjointClass.tangible_le
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.le_refl
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.le_trans
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.le_antisymm
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.bottom_le
#assert_no_axioms FX1Poly.Axis.geometricOfModal_sinister
#assert_no_axioms FX1Poly.Axis.geometricOfModal_tangible
#assert_no_axioms FX1Poly.Axis.geometricOfModal_sharp
#assert_no_axioms FX1Poly.Axis.geometricOfModal_transparent
#assert_no_axioms FX1Poly.Axis.fibrantKind_geometric
#assert_no_axioms FX1Poly.Axis.exotypeKind_geometric
#assert_no_axioms FX1Poly.Axis.monotone_rungs
#assert_no_axioms FX1Poly.Axis.rungOfSpectrum_rungPos
#assert_no_axioms FX1Poly.Axis.strictPole_lt_interiorBlend
#assert_no_axioms FX1Poly.Axis.interiorBlend_lt_rungR4
#assert_no_axioms FX1Poly.Axis.interiorBlend_ne_poles
#assert_no_axioms FX1Poly.Axis.directedPole_lt_interiorFibrancy_lt_omega
#assert_no_axioms FX1Poly.Axis.interiorFibrancy_ne_geometricOfModal
#assert_no_axioms FX1Poly.Axis.fxMode_hasGradedSpectrum

end FX1PolyAudit
