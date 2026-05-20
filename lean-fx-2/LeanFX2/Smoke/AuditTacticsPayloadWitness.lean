import LeanFX2.Tools.Tactics.PayloadWitness

/-! # Smoke/AuditTacticsPayloadWitness

Smoke checks for the payload-substitution shorthand `fx_subst_payload`.
-/

namespace LeanFX2.Smoke.AuditTacticsPayloadWitness

/-- Both witnesses observing the same Option computation yield a
payload equality that immediately substitutes.  After substitution,
`leftValue` and `rightValue` are the same variable and `rfl` closes
the equality goal. -/
example {payloadType : Type} {leftValue rightValue : payloadType}
    {optionValue : Option payloadType}
    (leftSuccess : optionValue = some leftValue)
    (rightSuccess : optionValue = some rightValue) :
    rightValue = leftValue := by
  fx_subst_payload payloadEq from leftSuccess and rightSuccess
  rfl

/-- After substitution the named equation hypothesis is no longer in
context (substituted away).  The remainder of the proof sees the
unified variable. -/
example {payloadType : Type} {leftValue rightValue : payloadType}
    {optionValue : Option payloadType}
    (leftSuccess : optionValue = some leftValue)
    (rightSuccess : optionValue = some rightValue)
    (rightConsumer : rightValue = leftValue → Nat) :
    Nat := by
  fx_subst_payload payloadEq from leftSuccess and rightSuccess
  exact rightConsumer rfl

end LeanFX2.Smoke.AuditTacticsPayloadWitness
