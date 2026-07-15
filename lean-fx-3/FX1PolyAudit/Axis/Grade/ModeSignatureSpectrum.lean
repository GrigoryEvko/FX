import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Grade.ModeSignatureSpectrum

/-! # FX1PolyAudit/Axis/Mode/ModeSignatureSpectrum — zero-axiom gate

Per-declaration zero-axiom gate for the Polygraph → grade↔mode spectrum wiring leaf: the rung strict
order, the maps FROM the mode carrier (`spectrumOfAdjointEdge` / `spectrumOfFibrancyKind` /
`richnessRungOfModeSignature`), the pole-landing theorems, the CENTERPIECE R2 < R5 crossover, and the
additive v1 sharpenings (richness gradient, order embedding, R3→R4 crossover, lossy decategorification,
`bottom` uniqueness).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Part A: the rung strict order + wiring maps
#assert_no_axioms FX1Poly.Axis.SpectrumRung.rank
#assert_no_axioms FX1Poly.Axis.SpectrumRung.lt
#assert_no_axioms FX1Poly.Axis.spectrumOfAdjointEdge
#assert_no_axioms FX1Poly.Axis.spectrumOfFibrancyKind
#assert_no_axioms FX1Poly.Axis.ModeSignatureRichness
#assert_no_axioms FX1Poly.Axis.richnessRungOfModeSignature
#assert_no_axioms FX1Poly.Axis.adjunctionSeedRichness
#assert_no_axioms FX1Poly.Axis.SemiringMode
#assert_no_axioms FX1Poly.Axis.SemiringModality
#assert_no_axioms FX1Poly.Axis.semiringModeGraph
#assert_no_axioms FX1Poly.Axis.singleObjectSemiringSignature
#assert_no_axioms FX1Poly.Axis.singleObjectSemiringRichness
#assert_no_axioms FX1Poly.Axis.spectrumOfAdjunctionSeed

-- Part A: pole-landing theorems
#assert_no_axioms FX1Poly.Axis.spectrumOfAdjointEdge_adjunctionLeft
#assert_no_axioms FX1Poly.Axis.spectrumOfAdjointEdge_adjunctionRight
#assert_no_axioms FX1Poly.Axis.spectrumOfAdjointEdge_fibrancyInclusion
#assert_no_axioms FX1Poly.Axis.spectrumOfAdjointEdge_fibrancyInclusionAdj
#assert_no_axioms FX1Poly.Axis.spectrumOfFibrancyKind_fibrant
#assert_no_axioms FX1Poly.Axis.spectrumOfFibrancyKind_exotype
#assert_no_axioms FX1Poly.Axis.rungOfSpectrum_adjunctionSeed
#assert_no_axioms FX1Poly.Axis.adjunctionSeed_richnessRung_r5
#assert_no_axioms FX1Poly.Axis.singleObjectSemiring_richnessRung_r2

-- ★★★ The centerpiece
#assert_no_axioms FX1Poly.Axis.crossover_semiring_strictly_below_adjunctionSeed

-- Part B: the additive v1 sharpenings
#assert_no_axioms FX1Poly.Modal.UsageGrade.rank
#assert_no_axioms FX1Poly.Modal.UsageGrade.rank_le_of_le
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.characterCount
#assert_no_axioms FX1Poly.Axis.AdjointClass.fanRank
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.richnessOf
#assert_no_axioms FX1Poly.Axis.FibrancyFeatures.characterCount_le_of_le
#assert_no_axioms FX1Poly.Axis.AdjointClass.fanRank_le_of_le
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.richnessOf_monotone
#assert_no_axioms FX1Poly.Axis.richnessOf_rungPos_strictMono
#assert_no_axioms FX1Poly.Axis.featuresOfAdjointClass_le_iff
#assert_no_axioms FX1Poly.Axis.geometricOfModal_le_iff
#assert_no_axioms FX1Poly.Axis.crossover_r3_r4
#assert_no_axioms FX1Poly.Axis.rungOfSpectrum_interiorBlend
#assert_no_axioms FX1Poly.Axis.rungOfSpectrum_not_injective
#assert_no_axioms FX1Poly.Axis.GradedSpectrum.bottom_unique
#assert_no_axioms FX1Poly.Axis.fxMode_hasSpectrumPolygraphWiring

end FX1PolyAudit
