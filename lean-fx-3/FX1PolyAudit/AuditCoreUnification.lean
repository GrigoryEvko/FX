import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Unification.PatternUnification

/-! # FX1PolyAudit/AuditCoreUnification — zero-axiom gate for term-11 (pattern unification)

Per-declaration zero-axiom gate for `FX1Poly/Core/Unification/PatternUnification.lean`: the higher-order
pattern fragment over the real `RawTerm` — the pattern predicate (`IsPatternSpine`) + its under-a-binder
stability (`patternSpine_lift`), MGU UNIQUENESS (`patternSolution_unique`, via the shipped term-level
renaming-injectivity), and the constructive INVERSION substitution (`findPreimageBelow` / `spineInverse`
with soundness `spineInverse_sound` and the round-trip `spineInverse_inverts`), plus the concrete spine
witness.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The pattern predicate + uniqueness (real `RawTerm`)
#assert_no_axioms FX1Poly.Core.IsPatternSpine
#assert_no_axioms FX1Poly.Core.patternSpine_lift
#assert_no_axioms FX1Poly.Core.patternSolution_unique

-- The inversion substitution `ρ⁻¹` + its two laws
#assert_no_axioms FX1Poly.Core.findPreimageBelow
#assert_no_axioms FX1Poly.Core.spineInverse
#assert_no_axioms FX1Poly.Core.findPreimageBelow_sound
#assert_no_axioms FX1Poly.Core.findPreimageBelow_finds
#assert_no_axioms FX1Poly.Core.spineInverse_sound
#assert_no_axioms FX1Poly.Core.spineInverse_inverts

-- The concrete injective-spine witness
#assert_no_axioms FX1Poly.Core.exampleSpine
#assert_no_axioms FX1Poly.Core.exampleSpine_isPattern
#assert_no_axioms FX1Poly.Core.exampleInversion_roundTrips

end FX1PolyAudit
