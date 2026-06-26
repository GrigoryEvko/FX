import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.TypeAxis

/-! # FX1PolyAudit/AuditTier0TypeAxis — zero-axiom gate for type-0 (the standalone Tarski universe design-lock)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Type/TypeAxis.lean`: the standalone Tarski data model
(`UniverseCode` / `StandaloneTarskiUniverse` / `fxTarskiUniverse`) and the type-axis bundle + witness
(`TypeAxis` / `fxTypeAxis`) with its three design-lock definitional pins.  Gating `fxTypeAxis` certifies that
the predicative Tarski model with a sound, idempotent level normalizer is inhabited zero-axiom — the witness
fields discharge the proof obligations with the home-module lemmas (`ne_lsucc_self`, `simplify_denote_eq`,
`simplify_idempotent`), themselves gated in `LevelExprSimplify` / `UniverseFlagStrength`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The standalone Tarski data model
#assert_no_axioms FX1Poly.Tier0.UniverseCode
#assert_no_axioms FX1Poly.Tier0.StandaloneTarskiUniverse
#assert_no_axioms FX1Poly.Tier0.fxTarskiUniverse

-- The type-axis bundle + witness + design-lock definitional pins
#assert_no_axioms FX1Poly.Tier0.TypeAxis
#assert_no_axioms FX1Poly.Tier0.fxTypeAxis
#assert_no_axioms FX1Poly.Tier0.fxTypeAxis_universe_isTarski
#assert_no_axioms FX1Poly.Tier0.fxTypeAxis_normalizer_isSimplify
#assert_no_axioms FX1Poly.Tier0.fxTarskiUniverse_code_isUniverseCode
#assert_no_axioms FX1Poly.Tier0.fxTarskiUniverse_levelTower_isUniverseLevelOfNat

end FX1PolyAudit
