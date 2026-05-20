import LeanFX2.Tools.Tactics.AuditBatch

/-! # Smoke/AuditTacticsAuditBatch

Smoke checks for the batched zero-axiom gate emitter
`#assert_no_axioms_batch`.  Exercises the macro with example
targets, confirming that the batch expands to individual gates
and each child gate elaborates successfully.
-/

namespace LeanFX2.Smoke.AuditTacticsAuditBatch

/-- Trivial first audit target. -/
theorem firstAuditTarget : 1 + 1 = 2 := rfl

/-- Trivial second audit target. -/
theorem secondAuditTarget : 2 + 2 = 4 := rfl

/-- Trivial third audit target — uses Prop-level truth introduction. -/
theorem thirdAuditTarget : True := True.intro

#assert_no_axioms_batch
  [LeanFX2.Smoke.AuditTacticsAuditBatch.firstAuditTarget,
   LeanFX2.Smoke.AuditTacticsAuditBatch.secondAuditTarget,
   LeanFX2.Smoke.AuditTacticsAuditBatch.thirdAuditTarget]

/-- Single-element batch behaves like the original single gate. -/
theorem singletonAuditTarget : 0 = 0 := rfl

#assert_no_axioms_batch
  [LeanFX2.Smoke.AuditTacticsAuditBatch.singletonAuditTarget]

end LeanFX2.Smoke.AuditTacticsAuditBatch
