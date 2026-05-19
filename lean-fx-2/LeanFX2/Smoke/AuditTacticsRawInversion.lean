import LeanFX2.Tools.Tactics.RawInversion

/-! # Smoke/AuditTacticsRawInversion

Smoke checks for raw parallel inversion tactic shorthands.
-/

namespace LeanFX2.Smoke.AuditTacticsRawInversion

example {scope : Nat} {targetTerm : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.unit : RawTerm scope) targetTerm) :
    targetTerm = RawTerm.unit := by
  fx_raw_par_unit_inv parallelStep

example {scope : Nat} {targetTerm : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.boolTrue : RawTerm scope) targetTerm) :
    targetTerm = RawTerm.boolTrue := by
  fx_raw_par_inv parallelStep

example {scope : Nat} {position : Fin scope} {targetTerm : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.var position) targetTerm) :
    targetTerm = RawTerm.var position := by
  fx_raw_par_var_inv parallelStep

example {scope : Nat} {targetTerm : RawTerm scope}
    (chainProof :
      RawStep.parStar (RawTerm.optionNone : RawTerm scope) targetTerm) :
    targetTerm = RawTerm.optionNone := by
  fx_raw_parstar_canonical_inv chainProof

example {scope : Nat} {targetTerm : RawTerm scope}
    (chainProof : RawStep.parStar (RawTerm.natZero : RawTerm scope) targetTerm) :
    targetTerm = RawTerm.natZero := by
  fx_raw_parstar_natZero_inv chainProof

end LeanFX2.Smoke.AuditTacticsRawInversion
