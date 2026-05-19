import LeanFX2.Tools.Tactics.Cast

/-! # Smoke/AuditTacticsCast

Smoke checks for cast-transport tactic shorthands over `Step`, `Step.par`,
`StepStar`, and `Conv`.
-/

namespace LeanFX2.Smoke.AuditTacticsCast

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step (typeEquality ▸ sourceTerm) targetTerm := by
  fx_step_cast_source_type typeEquality using singleStep

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRawOriginal sourceRawReplacement targetRaw : RawTerm scope}
    (rawEquality : sourceRawOriginal = sourceRawReplacement)
    {sourceTerm : Term context sourceType sourceRawOriginal}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par (rawEquality ▸ sourceTerm) targetTerm := by
  fx_par_cast_source_raw rawEquality using parallelStep

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (chainStep : StepStar sourceTerm targetTerm) :
    StepStar sourceTerm (typeEquality ▸ targetTerm) := by
  fx_stepstar_cast_target_type typeEquality using chainStep

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (convertibility : Conv sourceTerm targetOriginal) :
    Conv sourceTerm targetReplacement := by
  fx_conv_cast_target_term targetEquality using convertibility

end LeanFX2.Smoke.AuditTacticsCast
