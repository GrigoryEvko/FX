import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.TypeAxis

/-! # FX1PolyAudit/AuditTier0TypeAxis — zero-axiom gate for type-0 (the standalone Tarski universe design-lock)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Type/TypeAxis.lean`: the standalone Tarski data model
(`UniverseCode` / `StandaloneTarskiUniverse` / `fxTarskiUniverse`), the type-axis bundle + witness (`TypeAxis`
/ `fxTypeAxis`) with its design-lock pins, the three backed flips (level normalization, predicative universe,
the universe flag ladder), and the deferral honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The standalone Tarski data model
#assert_no_axioms FX1Poly.Tier0.UniverseCode
#assert_no_axioms FX1Poly.Tier0.StandaloneTarskiUniverse
#assert_no_axioms FX1Poly.Tier0.fxTarskiUniverse

-- The type-axis bundle + witness + design-lock pins
#assert_no_axioms FX1Poly.Tier0.TypeAxis
#assert_no_axioms FX1Poly.Tier0.fxTypeAxis
#assert_no_axioms FX1Poly.Tier0.fxTypeAxis_universe_isTarski
#assert_no_axioms FX1Poly.Tier0.fxTypeAxis_normalizer_isSimplify
#assert_no_axioms FX1Poly.Tier0.fxTarskiUniverse_code_isUniverseCode

-- The three backed flips (the metatheory the standalone type layer genuinely earns)
#assert_no_axioms FX1Poly.Tier0.fxType_hasLevelNormalization
#assert_no_axioms FX1Poly.Tier0.fxType_levelNormalization_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasPredicativeUniverse
#assert_no_axioms FX1Poly.Tier0.fxType_predicativeUniverse_isBacked
#assert_no_axioms FX1Poly.Tier0.fxType_hasUniverseFlagLadder
#assert_no_axioms FX1Poly.Tier0.fxType_universeFlagLadder_isBacked

-- The deferral honesty markers (later type rungs / cross-axis Core gluing)
#assert_no_axioms FX1Poly.Tier0.fxType_hasInductiveTypes
#assert_no_axioms FX1Poly.Tier0.fxType_hasDisplayClassifier
#assert_no_axioms FX1Poly.Tier0.fxType_hasTarskiDecodeGluing
#assert_no_axioms FX1Poly.Tier0.fxType_hasDefinitionalUnivalence
#assert_no_axioms FX1Poly.Tier0.fxType_hasCumulativeSubtyping
#assert_no_axioms FX1Poly.Tier0.fxType_hasLargeCardinalAdmission
#assert_no_axioms FX1Poly.Tier0.fxType_hasTypeOmegaCategory

end FX1PolyAudit
