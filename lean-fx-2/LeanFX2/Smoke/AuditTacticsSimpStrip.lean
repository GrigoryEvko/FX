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

end LeanFX2.Smoke.AuditTacticsSimpStrip
