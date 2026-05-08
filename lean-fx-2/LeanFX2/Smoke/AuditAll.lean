import LeanFX2.Tools.AuditAll
import LeanFX2.Smoke.AuditNamespace
import LeanFX2.Smoke.ImportSurface

/-! # Smoke/AuditAll - reviewer-facing audit entrypoint

Importing this module runs the same production zero-axiom gate as
`LeanFX2.Tools.AuditAll`, then loads the smoke audit suite and import-surface
checks.  It exists as the reviewer-facing target for the release smoke log:

* `LeanFX2.Tools.AuditAll` blocks on production axiom leaks, naming drift,
  import-family drift, raw/typed parity, and postulate-shaped hypotheses.
* `LeanFX2.Smoke.AuditNamespace` imports the smoke files and runs the
  build-failing namespace audit over `LeanFX2.Smoke`.
* `LeanFX2.Smoke.ImportSurface` keeps production import policy visible without
  requiring the broader `Smoke.ImportEverywhere` cone.

This file deliberately contains no hand-maintained duplicate assertion list;
the authoritative declaration gates live in the imported audit modules.
-/

namespace LeanFX2
namespace Smoke

-- Reviewer-facing smoke coverage must run after `Smoke.AuditNamespace`
-- imports the smoke files.  The Tools/AuditAll cone intentionally does not
-- load smoke modules, so this gate belongs here.
-- D3.6-P3: typed `Term.uaToEquiv` ctor + smoke audit; smoke gate
-- bumps from 47 to 48 (per-ctor census heuristic for the new ctor).
-- D3.6-P4: typed `Term.equivApply` ctor + smoke audit; smoke gate
-- bumps from 48 to 49 (per-ctor census heuristic for the new ctor).
#assert_smoke_reference_coverage_budget LeanFX2.Term 49

end Smoke
end LeanFX2
