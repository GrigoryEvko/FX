import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Unification.PatternUnification

/-! # FX1PolyAudit.Core.Unification.PatternUnification

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Unification.PatternUnification`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

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

-- ★ The term-level solve: the inverse renaming + the recover theorem (ρ⁻¹[ρ[body]] = body)
#assert_no_axioms FX1Poly.Core.spineLeftInverse

#assert_no_axioms FX1Poly.Core.spineLeftInverse_comp

#assert_no_axioms FX1Poly.Core.patternSolution_recover

-- The concrete injective-spine witness
#assert_no_axioms FX1Poly.Core.exampleSpine

#assert_no_axioms FX1Poly.Core.exampleSpine_isPattern

#assert_no_axioms FX1Poly.Core.exampleInversion_roundTrips

end FX1PolyAudit
