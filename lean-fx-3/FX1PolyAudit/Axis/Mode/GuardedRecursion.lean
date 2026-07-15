import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.GuardedRecursion

/-! # FX1PolyAudit/AuditAxisModeGuardedRecursion — zero-axiom gate for mode-15

Per-declaration zero-axiom gate for `mode-15` (`FX1Poly/Axis/Mode/GuardedRecursion.lean`): the later modality
+ Löb interface, the trivial witness + the constant-Löb smoke + the unique-fixpoint theorem, the single-clock
model with force / constant / clock irrelevance, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The later modality + Löb + the trivial witness
#assert_no_axioms FX1Poly.Axis.LaterModality
#assert_no_axioms FX1Poly.Axis.trivialLater
#assert_no_axioms FX1Poly.Axis.trivialLater_lob_const
#assert_no_axioms FX1Poly.Axis.trivialLater_lob_isUnique

-- The single-clock model + clock irrelevance
#assert_no_axioms FX1Poly.Axis.ClockQuantified
#assert_no_axioms FX1Poly.Axis.forceClock
#assert_no_axioms FX1Poly.Axis.constantClock
#assert_no_axioms FX1Poly.Axis.forceClock_constantClock
#assert_no_axioms FX1Poly.Axis.clockIrrelevance

-- The genuine step-indexed later (the topos-of-trees model, non-trivial Lob)
#assert_no_axioms FX1Poly.Axis.StepIndexedType
#assert_no_axioms FX1Poly.Axis.laterShift
#assert_no_axioms FX1Poly.Axis.stepIndexedLob
#assert_no_axioms FX1Poly.Axis.stepIndexedLob_zero
#assert_no_axioms FX1Poly.Axis.stepIndexedLob_succ
#assert_no_axioms FX1Poly.Axis.streamApprox
#assert_no_axioms FX1Poly.Axis.constStreamGenerator
#assert_no_axioms FX1Poly.Axis.constStream_depth_two

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasToposOfTreesLater
#assert_no_axioms FX1Poly.Axis.fxMode_hasMultiClockModel
#assert_no_axioms FX1Poly.Axis.fxMode_hasGuardedCoinduction
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelLaterFormer

end FX1PolyAudit
