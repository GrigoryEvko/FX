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

end Smoke
end LeanFX2
