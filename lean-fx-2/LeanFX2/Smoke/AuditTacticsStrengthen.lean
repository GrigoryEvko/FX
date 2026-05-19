import LeanFX2.Tools.Tactics.Strengthen

/-! # Smoke/AuditTacticsStrengthen

Smoke checks for strengthening and renaming-image tactic shorthands.
-/

namespace LeanFX2.Smoke.AuditTacticsStrengthen

example {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.strengthen? sourceTerm.weaken = some sourceTerm := by
  fx_rw_raw_strengthen_weaken

example {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.unweaken? sourceTerm.weaken = some sourceTerm := by
  fx_rw_raw_unweaken_weaken

example {level scope : Nat} (sourceType : Ty level scope) :
    sourceType.weaken.strengthen? = some sourceType := by
  fx_rw_ty_strengthen_weaken

example {scope : Nat} (sourceTerm : RawTerm scope) :
    sourceTerm.rename RawRenaming.identity = sourceTerm := by
  fx_rw_raw_rename_identity_once

example {level scope : Nat} (sourceType : Ty level scope) :
    sourceType.rename RawRenaming.identity = sourceType := by
  fx_rw_ty_rename_identity_once

example {scope : Nat} :
    ∀ (intermediatePos : Fin (scope + 1)) (sourcePos : Fin scope),
      PartialRawRenaming.dropNewest intermediatePos = some sourcePos →
      intermediatePos = RawRenaming.weaken sourcePos := by
  fx_exact_drop_newest_injects_back

end LeanFX2.Smoke.AuditTacticsStrengthen
