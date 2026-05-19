import LeanFX2.Tools.Tactics.SimpStrip

/-! # Smoke/AuditTacticsSimpStrip

Smoke checks for local normalization tactic shorthands.
-/

namespace LeanFX2.Smoke.AuditTacticsSimpStrip

example {someValue : Nat} :
    Option.map id (some someValue) = some someValue := by
  fx_simp_option_maps
  rfl

example {sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope) :
    (RawTerm.unit (scope := sourceScope)).rename sourceRenaming =
      RawTerm.unit := by
  fx_simp_raw_rename

example {level sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope) :
    (Ty.unit (level := level) (scope := sourceScope)).rename sourceRenaming =
      Ty.unit := by
  fx_simp_ty_rename

example {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.unit (context := context)).toRaw = RawTerm.unit := by
  fx_simp_term_to_raw

example {sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (sourceRaw : RawTerm sourceScope) :
    sourceRaw.weaken.rename sourceRenaming.lift =
      (sourceRaw.rename sourceRenaming).weaken := by
  fx_rw_raw_weaken_rename_commute

example {sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (sourceRaw : RawTerm sourceScope) :
    (sourceRaw.rename sourceRenaming).weaken =
      sourceRaw.weaken.rename sourceRenaming.lift := by
  fx_rw_raw_weaken_rename_commute_symm

example {level sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (sourceType : Ty level sourceScope) :
    sourceType.weaken.rename sourceRenaming.lift =
      (sourceType.rename sourceRenaming).weaken := by
  fx_rw_ty_weaken_rename_commute

example {level sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (sourceType : Ty level sourceScope) :
    (sourceType.rename sourceRenaming).weaken =
      sourceType.weaken.rename sourceRenaming.lift := by
  fx_rw_ty_weaken_rename_commute_symm

example {level sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (codomainType : Ty level (sourceScope + 1))
    (argumentType : Ty level sourceScope)
    (argumentRaw : RawTerm sourceScope) :
    (codomainType.subst0 argumentType argumentRaw).rename sourceRenaming =
      (codomainType.rename sourceRenaming.lift).subst0
        (argumentType.rename sourceRenaming)
        (argumentRaw.rename sourceRenaming) := by
  fx_rw_ty_subst0_rename_commute

example {level sourceScope targetScope : Nat}
    (sourceRenaming : RawRenaming sourceScope targetScope)
    (codomainType : Ty level (sourceScope + 1))
    (argumentType : Ty level sourceScope)
    (argumentRaw : RawTerm sourceScope) :
    (codomainType.rename sourceRenaming.lift).subst0
        (argumentType.rename sourceRenaming)
        (argumentRaw.rename sourceRenaming) =
      (codomainType.subst0 argumentType argumentRaw).rename sourceRenaming := by
  fx_rw_ty_subst0_rename_commute_symm

end LeanFX2.Smoke.AuditTacticsSimpStrip
