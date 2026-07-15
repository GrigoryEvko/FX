import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.FibrancyMode

/-! # FX1PolyAudit/Axis/Mode/FibrancyMode — zero-axiom gate for the fibrancy mode axis

Per-declaration zero-axiom gate for `FX1Poly/Axis/Mode/FibrancyMode.lean` — the 2LTT fibrant / exotype mode
structure (Shulman MATT Examples 2.5 / 3.6): the `f` / `e` mode classifier with the decidable subuniverse order
`fibrant ≤ exotype`, the consumption interface (`isFibrantMode` / `fibrancyOf`), the fibrancy mode 2-category
polygraph, the four MATT predicate classes (with `ι` sinister and NOT sharp proven cast-free), the negative
coercion `ι ◇→` with its terms-bijection, the fibrant reflective subuniverse (`mode-20`), the abstract SR-facing
bridge, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The two fibrancy modes + the subuniverse order
#assert_no_axioms FX1Poly.Axis.FibrancyKind
#assert_no_axioms FX1Poly.Axis.FibrancyKind.fibrancyRank
#assert_no_axioms FX1Poly.Axis.FibrancyKind.fibrancyRank_injective
#assert_no_axioms FX1Poly.Axis.FibrancyKind.le
#assert_no_axioms FX1Poly.Axis.FibrancyKind.le_refl
#assert_no_axioms FX1Poly.Axis.FibrancyKind.le_trans
#assert_no_axioms FX1Poly.Axis.FibrancyKind.le_antisymm
#assert_no_axioms FX1Poly.Axis.decidableFibrancyLe
#assert_no_axioms FX1Poly.Axis.fibrant_le_exotype
#assert_no_axioms FX1Poly.Axis.FibrancyKind.fibrant_le
#assert_no_axioms FX1Poly.Axis.FibrancyKind.le_exotype

-- The fibrancy propagation join
#assert_no_axioms FX1Poly.Axis.FibrancyKind.joinFibrancy
#assert_no_axioms FX1Poly.Axis.FibrancyKind.joinFibrancy_fibrant_left
#assert_no_axioms FX1Poly.Axis.FibrancyKind.joinFibrancy_exotype_left
#assert_no_axioms FX1Poly.Axis.FibrancyKind.joinFibrancy_exotype_right

-- ★ The consumption interface (kernel-facing)
#assert_no_axioms FX1Poly.Axis.FibrancyKind.isFibrant
#assert_no_axioms FX1Poly.Axis.FibrancyKind.IsFibrantMode
#assert_no_axioms FX1Poly.Axis.FibrancyKind.isFibrant_eq_true_iff
#assert_no_axioms FX1Poly.Axis.fibrancyOf
#assert_no_axioms FX1Poly.Axis.isFibrantMode
#assert_no_axioms FX1Poly.Axis.isFibrantMode_fibrant
#assert_no_axioms FX1Poly.Axis.isFibrantMode_exotype
#assert_no_axioms FX1Poly.Axis.isFibrantMode_eq_true_iff_fibrant
#assert_no_axioms FX1Poly.Axis.isFibrantMode_le_exotype
#assert_no_axioms FX1Poly.Axis.isFibrant_joinFibrancy

-- The fibrancy mode 2-category as a mode-0 polygraph
#assert_no_axioms FX1Poly.Axis.FibrancyModality
#assert_no_axioms FX1Poly.Axis.fibrancyModeGraph
#assert_no_axioms FX1Poly.Axis.fibrancyInclusionPath
#assert_no_axioms FX1Poly.Axis.fibrancyInclusionPath_length
#assert_no_axioms FX1Poly.Axis.fibrancyModeSignature
#assert_no_axioms FX1Poly.Axis.fibrancyModesDistinct
#assert_no_axioms FX1Poly.Axis.fibrancyHasDirectedInclusion

-- The four MATT predicate classes (ι sinister, NOT sharp)
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.sourceMode
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.targetMode
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.isIdentity
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.isTangible
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.isSharp
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.isTransparent
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.isSinister
#assert_no_axioms FX1Poly.Axis.fibrancyInclusion_isSinister
#assert_no_axioms FX1Poly.Axis.fibrancyInclusion_not_isSharp
#assert_no_axioms FX1Poly.Axis.fibrancyInclusion_not_isTransparent
#assert_no_axioms FX1Poly.Axis.fibrancyInclusion_sinister_and_not_sharp
#assert_no_axioms FX1Poly.Axis.identityFibrant_isSharp
#assert_no_axioms FX1Poly.Axis.identityExotype_isSharp
#assert_no_axioms FX1Poly.Axis.identityFibrant_isTransparent
#assert_no_axioms FX1Poly.Axis.identityExotype_isTransparent
#assert_no_axioms FX1Poly.Axis.isSharp_implies_isTangible
#assert_no_axioms FX1Poly.Axis.isTransparent_implies_isTangible
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.rightAdjoint
#assert_no_axioms FX1Poly.Axis.fibrancyInclusion_rightAdjoint
#assert_no_axioms FX1Poly.Axis.rightAdjoint_sourceMode_eq_targetMode
#assert_no_axioms FX1Poly.Axis.rightAdjoint_targetMode_eq_sourceMode

-- ★ Composition in the fibrancy mode 2-category — ι is an isomorphism (MATT Example 2.5)
#assert_no_axioms FX1Poly.Axis.FibrancyMorphismShape.compose
#assert_no_axioms FX1Poly.Axis.compose_identityExotype_fibrancyInclusion
#assert_no_axioms FX1Poly.Axis.compose_fibrancyInclusion_identityFibrant
#assert_no_axioms FX1Poly.Axis.compose_fibrancyInclusion_rightAdjoint
#assert_no_axioms FX1Poly.Axis.compose_rightAdjoint_fibrancyInclusion
#assert_no_axioms FX1Poly.Axis.fibrancyInclusion_isInvertible
#assert_no_axioms FX1Poly.Axis.rightAdjoint_involutive
#assert_no_axioms FX1Poly.Axis.compose_sharp_transparent_isTangible

-- The negative coercion ι ◇→ : 𝒰_f ↪ 𝒰_e + its terms-bijection
#assert_no_axioms FX1Poly.Axis.FibrantType
#assert_no_axioms FX1Poly.Axis.coerceFibrantToExotype
#assert_no_axioms FX1Poly.Axis.coerceFibrantToExotype_onTerms
#assert_no_axioms FX1Poly.Axis.coerceFibrantToExotype_termsBijection

-- The fibrant reflective subuniverse (mode-20 Modality)
#assert_no_axioms FX1Poly.Axis.fibrantReflectiveSubuniverse
#assert_no_axioms FX1Poly.Axis.exotypeComplementComodality
#assert_no_axioms FX1Poly.Axis.fibrantReflectiveSubuniverse_localize_isModal
#assert_no_axioms FX1Poly.Axis.fibrantReflectionAsFibrantType
#assert_no_axioms FX1Poly.Axis.fibrantReflectiveSubuniverse_idempotent

-- ★ The SR-facing bridge (abstract — instantiated by the Typed layer)
#assert_no_axioms FX1Poly.Axis.FibrancyModeAssignment
#assert_no_axioms FX1Poly.Axis.FibrancyModeBridge
#assert_no_axioms FX1Poly.Axis.FibrancyModeBridge.isAtFibrantMode
#assert_no_axioms FX1Poly.Axis.FibrancyModeBridge.isAtFibrantMode_not_conv_interval
#assert_no_axioms FX1Poly.Axis.FibrancyModeBridge.isAtFibrantMode_stable_under_step

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasModeClassifier
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasConsumptionInterface
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasAbstractSrBridge
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasNonSharpInclusion
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasReflectiveSubuniverse
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasInvertibleInclusion
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasInternalFibrantReplacement
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasGenuineFibrantReplacementReflector
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasNegativeModalityDependentRightAdjoint
#assert_no_axioms FX1Poly.Axis.fxFibrancy_hasKernelModeFibrationBridge

end FX1PolyAudit
