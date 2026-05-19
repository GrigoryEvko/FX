import LeanFX2.Tools.Tactics.SN
import LeanFX2.Reducibility.NeutralSNIntro.Codes

/-! # Smoke/AuditTacticsSN

Smoke checks for strong-normalization choreography shorthands.
-/

namespace LeanFX2.Smoke.AuditTacticsSN

example {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval0 : RawTerm scope) := by
  fx_raw_atomic_sn_by_inv LeanFX2.RawStep.par.interval0_inv

example {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval1 : RawTerm scope) := by
  fx_raw_atomic_sn_by_inv LeanFX2.RawStep.par.interval1_inv

example {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (progressStep : RawStep.parProgress sourceTerm targetTerm)
    (sourceTargetEq : sourceTerm = targetTerm) : False := by
  fx_raw_progress_contra progressStep using sourceTargetEq

end LeanFX2.Smoke.AuditTacticsSN
