import LeanFX2.Tools.Tactics.RawCd

/-! # Smoke/AuditTacticsRawCd

Smoke checks for complete-development rewrite shorthands.
-/

namespace LeanFX2.Smoke.AuditTacticsRawCd

example {sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (developedGlued : RawTerm sourceScope) :
    (RawTerm.cdGlueElimCase developedGlued).rename sourceRenaming =
      RawTerm.cdGlueElimCase (developedGlued.rename sourceRenaming) := by
  fx_rw_cd_glue_elim_case_rename

example {sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    (RawTerm.cd sourceTerm).rename sourceRenaming =
      RawTerm.cd (sourceTerm.rename sourceRenaming) := by
  fx_rw_raw_cd_rename

end LeanFX2.Smoke.AuditTacticsRawCd
