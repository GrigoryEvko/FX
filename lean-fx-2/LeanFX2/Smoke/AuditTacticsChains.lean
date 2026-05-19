import LeanFX2.Tools.Tactics.Chains

/-! # Smoke/AuditTacticsChains

Smoke checks for chain-building tactic shorthands.
-/

namespace LeanFX2.Smoke.AuditTacticsChains

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType middleType : Ty level scope}
    {sourceRaw targetRaw middleRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {middleTerm : Term context middleType middleRaw}
    (singleStep : Step sourceTerm middleTerm)
    (restChain : StepStar middleTerm targetTerm) :
    StepStar sourceTerm targetTerm := by
  fx_stepstar_step singleStep then restChain

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType middleType : Ty level scope}
    {sourceRaw targetRaw middleRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {middleTerm : Term context middleType middleRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm targetTerm) :
    StepStar sourceTerm targetTerm := by
  fx_stepstar_append firstChain then secondChain

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.parStar sourceTerm targetTerm := by
  fx_par_to_star parallelStep

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType middleType : Ty level scope}
    {sourceRaw targetRaw middleRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {middleTerm : Term context middleType middleRaw}
    (firstChain : Step.parStar sourceTerm middleTerm)
    (secondChain : Step.parStar middleTerm targetTerm) :
    Step.parStar sourceTerm targetTerm := by
  fx_chain_append firstChain then secondChain

example {scope : Nat}
    {sourceTerm middleTerm targetTerm : RawTerm scope}
    (chainProof : RawStep.parStar sourceTerm middleTerm)
    (parallelStep : RawStep.par middleTerm targetTerm) :
    RawStep.parStar sourceTerm targetTerm := by
  fx_raw_parstar_snoc chainProof using parallelStep

example {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (parallelStep : RawStep.par sourceTerm targetTerm) :
    RawStep.parStar sourceTerm targetTerm := by
  fx_chain_single parallelStep

end LeanFX2.Smoke.AuditTacticsChains
