import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FibrancyMode

/-! # FX1PolyAudit/Tier0/Mode/FibrancyMode — zero-axiom gate for the fibrancy mode axis

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Mode/FibrancyMode.lean` — the 2LTT fibrant / exotype mode
structure (Shulman MATT Examples 2.5 / 3.6): the `f` / `e` mode classifier with the decidable subuniverse order
`fibrant ≤ exotype`, the consumption interface (`isFibrantMode` / `fibrancyOf`), the fibrancy mode 2-category
polygraph, the four MATT predicate classes (with `ι` sinister and NOT sharp proven cast-free), the negative
coercion `ι ◇→` with its terms-bijection, the fibrant reflective subuniverse (`mode-20`), the abstract SR-facing
bridge, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The two fibrancy modes + the subuniverse order
#assert_no_axioms FX1Poly.Tier0.FibrancyKind
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.fibrancyRank
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.fibrancyRank_injective
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.le
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.le_refl
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.le_trans
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.le_antisymm
#assert_no_axioms FX1Poly.Tier0.decidableFibrancyLe
#assert_no_axioms FX1Poly.Tier0.fibrant_le_exotype
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.fibrant_le
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.le_exotype

-- The fibrancy propagation join
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.joinFibrancy
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.joinFibrancy_fibrant_left
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.joinFibrancy_exotype_left
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.joinFibrancy_exotype_right

-- ★ The consumption interface (kernel-facing)
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.isFibrant
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.IsFibrantMode
#assert_no_axioms FX1Poly.Tier0.FibrancyKind.isFibrant_eq_true_iff
#assert_no_axioms FX1Poly.Tier0.fibrancyOf
#assert_no_axioms FX1Poly.Tier0.isFibrantMode
#assert_no_axioms FX1Poly.Tier0.isFibrantMode_fibrant
#assert_no_axioms FX1Poly.Tier0.isFibrantMode_exotype
#assert_no_axioms FX1Poly.Tier0.isFibrantMode_eq_true_iff_fibrant
#assert_no_axioms FX1Poly.Tier0.isFibrantMode_le_exotype
#assert_no_axioms FX1Poly.Tier0.isFibrant_joinFibrancy

-- The fibrancy mode 2-category as a mode-0 polygraph
#assert_no_axioms FX1Poly.Tier0.FibrancyModality
#assert_no_axioms FX1Poly.Tier0.fibrancyModeGraph
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusionPath
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusionPath_length
#assert_no_axioms FX1Poly.Tier0.fibrancyModeSignature
#assert_no_axioms FX1Poly.Tier0.fibrancyModesDistinct
#assert_no_axioms FX1Poly.Tier0.fibrancyHasDirectedInclusion

-- The four MATT predicate classes (ι sinister, NOT sharp)
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.sourceMode
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.targetMode
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.isIdentity
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.isTangible
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.isSharp
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.isTransparent
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.isSinister
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusion_isSinister
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusion_not_isSharp
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusion_not_isTransparent
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusion_sinister_and_not_sharp
#assert_no_axioms FX1Poly.Tier0.identityFibrant_isSharp
#assert_no_axioms FX1Poly.Tier0.identityExotype_isSharp
#assert_no_axioms FX1Poly.Tier0.identityFibrant_isTransparent
#assert_no_axioms FX1Poly.Tier0.identityExotype_isTransparent
#assert_no_axioms FX1Poly.Tier0.isSharp_implies_isTangible
#assert_no_axioms FX1Poly.Tier0.isTransparent_implies_isTangible
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.rightAdjoint
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusion_rightAdjoint
#assert_no_axioms FX1Poly.Tier0.rightAdjoint_sourceMode_eq_targetMode
#assert_no_axioms FX1Poly.Tier0.rightAdjoint_targetMode_eq_sourceMode

-- ★ Composition in the fibrancy mode 2-category — ι is an isomorphism (MATT Example 2.5)
#assert_no_axioms FX1Poly.Tier0.FibrancyMorphismShape.compose
#assert_no_axioms FX1Poly.Tier0.compose_identityExotype_fibrancyInclusion
#assert_no_axioms FX1Poly.Tier0.compose_fibrancyInclusion_identityFibrant
#assert_no_axioms FX1Poly.Tier0.compose_fibrancyInclusion_rightAdjoint
#assert_no_axioms FX1Poly.Tier0.compose_rightAdjoint_fibrancyInclusion
#assert_no_axioms FX1Poly.Tier0.fibrancyInclusion_isInvertible
#assert_no_axioms FX1Poly.Tier0.rightAdjoint_involutive
#assert_no_axioms FX1Poly.Tier0.compose_sharp_transparent_isTangible

-- The negative coercion ι ◇→ : 𝒰_f ↪ 𝒰_e + its terms-bijection
#assert_no_axioms FX1Poly.Tier0.FibrantType
#assert_no_axioms FX1Poly.Tier0.coerceFibrantToExotype
#assert_no_axioms FX1Poly.Tier0.coerceFibrantToExotype_onTerms
#assert_no_axioms FX1Poly.Tier0.coerceFibrantToExotype_termsBijection

-- The fibrant reflective subuniverse (mode-20 Modality)
#assert_no_axioms FX1Poly.Tier0.fibrantReflectiveSubuniverse
#assert_no_axioms FX1Poly.Tier0.exotypeComplementComodality
#assert_no_axioms FX1Poly.Tier0.fibrantReflectiveSubuniverse_localize_isModal
#assert_no_axioms FX1Poly.Tier0.fibrantReflectionAsFibrantType
#assert_no_axioms FX1Poly.Tier0.fibrantReflectiveSubuniverse_idempotent

-- ★ The SR-facing bridge (abstract — instantiated by the Typed layer)
#assert_no_axioms FX1Poly.Tier0.FibrancyModeAssignment
#assert_no_axioms FX1Poly.Tier0.FibrancyModeBridge
#assert_no_axioms FX1Poly.Tier0.FibrancyModeBridge.isAtFibrantMode
#assert_no_axioms FX1Poly.Tier0.FibrancyModeBridge.isAtFibrantMode_not_conv_interval
#assert_no_axioms FX1Poly.Tier0.FibrancyModeBridge.isAtFibrantMode_stable_under_step

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasModeClassifier
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasConsumptionInterface
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasAbstractSrBridge
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasNonSharpInclusion
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasReflectiveSubuniverse
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasInvertibleInclusion
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasInternalFibrantReplacement
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasGenuineFibrantReplacementReflector
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasNegativeModalityDependentRightAdjoint
#assert_no_axioms FX1Poly.Tier0.fxFibrancy_hasKernelModeFibrationBridge

end FX1PolyAudit
