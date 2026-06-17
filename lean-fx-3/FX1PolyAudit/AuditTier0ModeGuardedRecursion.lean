import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.GuardedRecursion

/-! # FX1PolyAudit/AuditTier0ModeGuardedRecursion — zero-axiom gate for mode-15

Per-declaration zero-axiom gate for `mode-15` (`FX1Poly/Tier0/Mode/GuardedRecursion.lean`): the later modality
+ Löb interface, the trivial witness + the constant-Löb smoke + the unique-fixpoint theorem, the single-clock
model with force / constant / clock irrelevance, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The later modality + Löb + the trivial witness
#assert_no_axioms FX1Poly.Tier0.LaterModality
#assert_no_axioms FX1Poly.Tier0.trivialLater
#assert_no_axioms FX1Poly.Tier0.trivialLater_lob_const
#assert_no_axioms FX1Poly.Tier0.trivialLater_lob_isUnique

-- The single-clock model + clock irrelevance
#assert_no_axioms FX1Poly.Tier0.ClockQuantified
#assert_no_axioms FX1Poly.Tier0.forceClock
#assert_no_axioms FX1Poly.Tier0.constantClock
#assert_no_axioms FX1Poly.Tier0.forceClock_constantClock
#assert_no_axioms FX1Poly.Tier0.clockIrrelevance

-- The genuine step-indexed later (the topos-of-trees model, non-trivial Lob)
#assert_no_axioms FX1Poly.Tier0.StepIndexedType
#assert_no_axioms FX1Poly.Tier0.laterShift
#assert_no_axioms FX1Poly.Tier0.stepIndexedLob
#assert_no_axioms FX1Poly.Tier0.stepIndexedLob_zero
#assert_no_axioms FX1Poly.Tier0.stepIndexedLob_succ
#assert_no_axioms FX1Poly.Tier0.streamApprox
#assert_no_axioms FX1Poly.Tier0.constStreamGenerator
#assert_no_axioms FX1Poly.Tier0.constStream_depth_two

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasToposOfTreesLater
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMultiClockModel
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGuardedCoinduction
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelLaterFormer

end FX1PolyAudit
