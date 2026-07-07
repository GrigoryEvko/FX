import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Grade.ModeSignatureSpectrum

/-! # FX1PolyAudit/Tier0/Mode/ModeSignatureSpectrum — zero-axiom gate

Per-declaration zero-axiom gate for the Polygraph → grade↔mode spectrum wiring leaf: the rung strict
order, the maps FROM the mode carrier (`spectrumOfAdjointEdge` / `spectrumOfFibrancyKind` /
`richnessRungOfModeSignature`), the pole-landing theorems, the CENTERPIECE R2 < R5 crossover, and the
additive v1 sharpenings (richness gradient, order embedding, R3→R4 crossover, lossy decategorification,
`bottom` uniqueness).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Part A: the rung strict order + wiring maps
#assert_no_axioms FX1Poly.Tier0.SpectrumRung.rank
#assert_no_axioms FX1Poly.Tier0.SpectrumRung.lt
#assert_no_axioms FX1Poly.Tier0.spectrumOfAdjointEdge
#assert_no_axioms FX1Poly.Tier0.spectrumOfFibrancyKind
#assert_no_axioms FX1Poly.Tier0.ModeSignatureRichness
#assert_no_axioms FX1Poly.Tier0.richnessRungOfModeSignature
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRichness
#assert_no_axioms FX1Poly.Tier0.SemiringMode
#assert_no_axioms FX1Poly.Tier0.SemiringModality
#assert_no_axioms FX1Poly.Tier0.semiringModeGraph
#assert_no_axioms FX1Poly.Tier0.singleObjectSemiringSignature
#assert_no_axioms FX1Poly.Tier0.singleObjectSemiringRichness
#assert_no_axioms FX1Poly.Tier0.spectrumOfAdjunctionSeed

-- Part A: pole-landing theorems
#assert_no_axioms FX1Poly.Tier0.spectrumOfAdjointEdge_adjunctionLeft
#assert_no_axioms FX1Poly.Tier0.spectrumOfAdjointEdge_adjunctionRight
#assert_no_axioms FX1Poly.Tier0.spectrumOfAdjointEdge_fibrancyInclusion
#assert_no_axioms FX1Poly.Tier0.spectrumOfAdjointEdge_fibrancyInclusionAdj
#assert_no_axioms FX1Poly.Tier0.spectrumOfFibrancyKind_fibrant
#assert_no_axioms FX1Poly.Tier0.spectrumOfFibrancyKind_exotype
#assert_no_axioms FX1Poly.Tier0.rungOfSpectrum_adjunctionSeed
#assert_no_axioms FX1Poly.Tier0.adjunctionSeed_richnessRung_r5
#assert_no_axioms FX1Poly.Tier0.singleObjectSemiring_richnessRung_r2

-- ★★★ The centerpiece
#assert_no_axioms FX1Poly.Tier0.crossover_semiring_strictly_below_adjunctionSeed

-- Part B: the additive v1 sharpenings
#assert_no_axioms FX1Poly.Modal.UsageGrade.rank
#assert_no_axioms FX1Poly.Modal.UsageGrade.rank_le_of_le
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.characterCount
#assert_no_axioms FX1Poly.Tier0.AdjointClass.fanRank
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.richnessOf
#assert_no_axioms FX1Poly.Tier0.FibrancyFeatures.characterCount_le_of_le
#assert_no_axioms FX1Poly.Tier0.AdjointClass.fanRank_le_of_le
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.richnessOf_monotone
#assert_no_axioms FX1Poly.Tier0.richnessOf_rungPos_strictMono
#assert_no_axioms FX1Poly.Tier0.featuresOfAdjointClass_le_iff
#assert_no_axioms FX1Poly.Tier0.geometricOfModal_le_iff
#assert_no_axioms FX1Poly.Tier0.crossover_r3_r4
#assert_no_axioms FX1Poly.Tier0.rungOfSpectrum_interiorBlend
#assert_no_axioms FX1Poly.Tier0.rungOfSpectrum_not_injective
#assert_no_axioms FX1Poly.Tier0.GradedSpectrum.bottom_unique
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSpectrumPolygraphWiring

end FX1PolyAudit
