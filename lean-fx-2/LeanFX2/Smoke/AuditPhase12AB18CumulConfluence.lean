import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Smoke.AuditPhase12AB17CumulReduction

/-! # Smoke/AuditPhase12AB18CumulConfluence — confluence cascade audit
(Phase CUMUL-2.6 Design D revision).

Phase 12.A.B18 (CUMUL-4.1..4.5).  Audits the typed-input/raw-output
confluence pipeline at `Term.cumulUp` / `Step.cumulUpInner` /
`Step.par.cumulUpInnerCong`.

Phase CUMUL-2.6 revises the audit: cumulUp now uses Design D (single
context, schematic codeRaw, output wrapped in cumulUpMarker).  The
confluence pipeline cascades transparently via `cumulUpMarkerCong`.

## Audit declarations
-/

namespace LeanFX2

#print axioms LeanFX2.Term.cumulUp
#print axioms LeanFX2.Step.cumulUpInner
#print axioms LeanFX2.Step.par.cumulUpInnerCong
#print axioms LeanFX2.RawStep.par.cumulUpMarkerCong
#print axioms LeanFX2.RawTerm.cumulUpMarker

end LeanFX2
