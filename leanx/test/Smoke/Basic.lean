-- Phase 0 smoke test.  Verifies the library compiles and the version
-- string is accessible.  Expanded in Phase 1 to actually run programs.

import FX.Core

open FX

#eval s!"leanx Phase 0 smoke test — version {FX.version}"

/-- The version constant is non-empty. -/
example : FX.version ≠ "" := by
  simp [FX.version]
